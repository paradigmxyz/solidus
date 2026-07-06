#!/usr/bin/env python3
"""Optimization harness for the verified EVM compiler.

Measures emitted bytecode sizes across a corpus of Solidity contracts compiled
through the *only* supported entry: the raw solc Standard JSON path
(`scripts/solc_lean_standard_json.py` -> `evm-compiler-backend raw-image`).
It also runs the correctness gate (proof-root build + axiom footprint check).

This is measurement + gating tooling only.  It never edits the compiler.

Subcommands
-----------
  baseline  Compile the corpus, record per-contract sizes, write
            benchmarks/opt_baseline.json.
  bench     Compile the corpus, diff against the baseline, print a table and
            write benchmarks/opt_last_run.json.  Nonzero exit if any corpus
            contract fails to compile.  With --fail-on-regression, also exits
            nonzero if total bytecode grew.
  check     Correctness gate: `lake build EvmCompiler.Verification` plus the
            axiom-footprint check on the public theorems pinned in
            proof_artifacts/stack_backend_production_smoke.lean.
  full      check, then bench (the grinder inner loop).

Exit codes
----------
  0   pass
  2   usage / configuration error
  10  correctness build failure (check)
  11  axiom-footprint failure     (check)
  20  a corpus contract failed to compile (bench)
  30  size regression with --fail-on-regression (bench)
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

REPO_ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = REPO_ROOT / "scripts"
BENCH_DIR = REPO_ROOT / "benchmarks"
CORPUS_MANIFEST = BENCH_DIR / "corpus.txt"
BASELINE_JSON = BENCH_DIR / "opt_baseline.json"
LAST_RUN_JSON = BENCH_DIR / "opt_last_run.json"

SMOKE_LEAN = REPO_ROOT / "proof_artifacts" / "stack_backend_production_smoke.lean"
PROOF_ROOT_MODULE = "EvmCompiler.Verification"
EXPECTED_AXIOMS = "[propext, Classical.choice, Quot.sound]"

# Exit codes.
EXIT_OK = 0
EXIT_USAGE = 2
EXIT_BUILD_FAIL = 10
EXIT_AXIOM_FAIL = 11
EXIT_COMPILE_FAIL = 20
EXIT_REGRESSION = 30


# --------------------------------------------------------------------------
# environment helpers
# --------------------------------------------------------------------------

def default_solc() -> str:
    local = Path.home() / ".local" / "bin" / "solc"
    return str(local) if local.exists() else "solc"


def default_lake() -> str:
    local = Path.home() / ".elan" / "bin" / "lake"
    return str(local) if local.exists() else "lake"


def tool_env() -> Dict[str, str]:
    """Environment for subprocesses: pin solc/lake and disable the optional
    jsonschema output validation (the harness parses the JSON directly)."""
    env = dict(os.environ)
    solc = env.get("SOLC", default_solc())
    lake = env.get("LAKE", default_lake())
    env.setdefault("SOLC_LEAN_REAL_SOLC", solc)
    env.setdefault("SOLC_LEAN_LAKE", lake)
    env["LAKE"] = lake
    env["SOLC"] = solc
    env["SOLC_LEAN_VALIDATE_OUTPUT"] = "0"
    # Make the pinned tools reachable on PATH too.
    extra = os.pathsep.join(
        [str(Path.home() / ".elan" / "bin"), str(Path.home() / ".local" / "bin")]
    )
    env["PATH"] = extra + os.pathsep + env.get("PATH", "")
    return env


def solc_version(env: Dict[str, str]) -> str:
    solc = env.get("SOLC_LEAN_REAL_SOLC", default_solc())
    try:
        out = subprocess.run(
            [solc, "--version"], capture_output=True, text=True, env=env
        ).stdout
    except FileNotFoundError:
        return "unknown"
    for line in out.splitlines():
        line = line.strip()
        if line.startswith("Version:"):
            return line[len("Version:"):].strip()
    return out.strip().splitlines()[-1] if out.strip() else "unknown"


def git_commit() -> str:
    try:
        return subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=str(REPO_ROOT), capture_output=True, text=True,
        ).stdout.strip() or "unknown"
    except Exception:
        return "unknown"


# --------------------------------------------------------------------------
# corpus manifest
# --------------------------------------------------------------------------

def read_corpus() -> List[str]:
    if not CORPUS_MANIFEST.exists():
        die(f"corpus manifest not found: {CORPUS_MANIFEST}", EXIT_USAGE)
    entries: List[str] = []
    for raw in CORPUS_MANIFEST.read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        entries.append(line)
    return entries


# --------------------------------------------------------------------------
# compilation / measurement
# --------------------------------------------------------------------------

def compile_source(rel_path: str, env: Dict[str, str]) -> Dict[str, Any]:
    """Compile one Solidity source file through the raw solc path.

    Returns a dict:
      {ok: bool, compile_ms: int, contracts: [{name, runtime_bytes,
       creation_bytes}], reason?: str}
    """
    src_path = REPO_ROOT / rel_path
    if not src_path.exists():
        return {"ok": False, "compile_ms": 0, "contracts": [],
                "reason": f"source file missing: {rel_path}"}
    name = src_path.name
    standard_input = {
        "language": "Solidity",
        "sources": {name: {"content": src_path.read_text()}},
        "settings": {
            "outputSelection": {
                "*": {"*": [
                    "evm.bytecode.object",
                    "evm.deployedBytecode.object",
                ]}
            }
        },
    }
    started = time.monotonic()
    try:
        proc = subprocess.run(
            [sys.executable, str(SCRIPTS / "solc_lean_standard_json.py"),
             "--standard-json"],
            input=json.dumps(standard_input),
            capture_output=True, text=True, env=env, cwd=str(REPO_ROOT),
        )
    except FileNotFoundError as exc:
        return {"ok": False, "compile_ms": 0, "contracts": [],
                "reason": f"driver not runnable: {exc}"}
    compile_ms = int((time.monotonic() - started) * 1000)

    if proc.returncode != 0:
        reason = (proc.stderr or proc.stdout or "").strip().splitlines()
        return {"ok": False, "compile_ms": compile_ms, "contracts": [],
                "reason": reason[-1] if reason else
                f"driver exit {proc.returncode}"}
    try:
        output = json.loads(proc.stdout or "")
    except json.JSONDecodeError as exc:
        return {"ok": False, "compile_ms": compile_ms, "contracts": [],
                "reason": f"unparseable driver output: {exc}"}

    # solc-level errors surface here.
    errors = [e for e in output.get("errors", [])
              if isinstance(e, dict) and e.get("severity") == "error"]
    if errors:
        msg = errors[0].get("formattedMessage") or errors[0].get("message") or ""
        return {"ok": False, "compile_ms": compile_ms, "contracts": [],
                "reason": "solc error: " + " ".join(msg.split())[:200]}

    contracts_out: List[Dict[str, Any]] = []
    for source_name, contracts in (output.get("contracts") or {}).items():
        if not isinstance(contracts, dict):
            continue
        for contract_name, cdata in contracts.items():
            ec = cdata.get("evmCompiler") if isinstance(cdata, dict) else None
            if not isinstance(ec, dict):
                continue
            sizes = ec.get("sizes") or {}
            contracts_out.append({
                "name": f"{source_name}:{contract_name}",
                "runtime_bytes": int(sizes.get("runtimeBytes", 0)),
                "creation_bytes": int(sizes.get("creationBytes", 0)),
                "compile_ms": compile_ms,
            })
    contracts_out.sort(key=lambda c: c["name"])
    return {"ok": True, "compile_ms": compile_ms, "contracts": contracts_out,
            "reason": None}


def measure_corpus(env: Dict[str, str]) -> Dict[str, Any]:
    corpus = read_corpus()
    contracts: List[Dict[str, Any]] = []
    excluded: List[Dict[str, str]] = []
    failures: List[str] = []
    empty_sources: List[str] = []
    started = time.monotonic()
    for rel in corpus:
        sys.stderr.write(f"[compile] {rel} ... ")
        sys.stderr.flush()
        result = compile_source(rel, env)
        if not result["ok"]:
            failures.append(rel)
            excluded.append({"source": rel, "reason": result["reason"]})
            sys.stderr.write(f"FAIL ({result['reason']})\n")
            continue
        if not result["contracts"]:
            empty_sources.append(rel)
            sys.stderr.write("no deployable contracts\n")
            continue
        contracts.extend(result["contracts"])
        names = ", ".join(c["name"].split(":")[-1] for c in result["contracts"])
        sys.stderr.write(f"ok [{names}] {result['compile_ms']}ms\n")
    wall_ms = int((time.monotonic() - started) * 1000)
    contracts.sort(key=lambda c: c["name"])
    return {
        "contracts": contracts,
        "excluded": excluded,
        "failures": failures,
        "empty_sources": empty_sources,
        "wall_ms": wall_ms,
        "total_runtime_bytes": sum(c["runtime_bytes"] for c in contracts),
        "total_creation_bytes": sum(c["creation_bytes"] for c in contracts),
    }


def build_record(env: Dict[str, str], measured: Dict[str, Any]) -> Dict[str, Any]:
    return {
        "commit": git_commit(),
        "date": datetime.datetime.now(datetime.timezone.utc)
                .strftime("%Y-%m-%dT%H:%M:%SZ"),
        "solc_version": solc_version(env),
        "contracts": [
            {k: c[k] for k in
             ("name", "runtime_bytes", "creation_bytes", "compile_ms")}
            for c in measured["contracts"]
        ],
        "excluded": measured["excluded"],
        "empty_sources": measured["empty_sources"],
        "total_runtime_bytes": measured["total_runtime_bytes"],
        "total_creation_bytes": measured["total_creation_bytes"],
        "wall_ms": measured["wall_ms"],
    }


# --------------------------------------------------------------------------
# subcommands: baseline / bench
# --------------------------------------------------------------------------

def cmd_baseline(args: argparse.Namespace) -> int:
    env = tool_env()
    measured = measure_corpus(env)
    record = build_record(env, measured)
    BENCH_DIR.mkdir(parents=True, exist_ok=True)
    BASELINE_JSON.write_text(json.dumps(record, indent=2) + "\n")
    print_summary("BASELINE", record, baseline=None)
    print(f"\nwrote {BASELINE_JSON.relative_to(REPO_ROOT)}")
    if measured["failures"]:
        print(f"\nWARNING: {len(measured['failures'])} corpus source(s) "
              f"failed to compile and are recorded under \"excluded\".",
              file=sys.stderr)
    return EXIT_OK


def cmd_bench(args: argparse.Namespace) -> int:
    env = tool_env()
    measured = measure_corpus(env)
    record = build_record(env, measured)
    BENCH_DIR.mkdir(parents=True, exist_ok=True)
    LAST_RUN_JSON.write_text(json.dumps(record, indent=2) + "\n")

    baseline = None
    if BASELINE_JSON.exists():
        try:
            baseline = json.loads(BASELINE_JSON.read_text())
        except json.JSONDecodeError:
            baseline = None

    print_summary("BENCH", record, baseline)
    print(f"\nwrote {LAST_RUN_JSON.relative_to(REPO_ROOT)}")

    if measured["failures"]:
        print(f"\nERROR: {len(measured['failures'])} corpus contract(s) failed "
              f"to compile: {', '.join(measured['failures'])}", file=sys.stderr)
        return EXIT_COMPILE_FAIL

    if args.fail_on_regression and baseline is not None:
        dr = record["total_runtime_bytes"] - baseline.get("total_runtime_bytes", 0)
        dc = record["total_creation_bytes"] - baseline.get("total_creation_bytes", 0)
        if dr > 0 or dc > 0:
            print(f"\nERROR: size regression (runtime {dr:+d}, "
                  f"creation {dc:+d})", file=sys.stderr)
            return EXIT_REGRESSION
    return EXIT_OK


def print_summary(title: str, record: Dict[str, Any],
                  baseline: Optional[Dict[str, Any]]) -> None:
    base_map: Dict[str, Dict[str, Any]] = {}
    if baseline is not None:
        base_map = {c["name"]: c for c in baseline.get("contracts", [])}

    print(f"\n=== {title} ===")
    print(f"commit {record['commit'][:12]}  {record['date']}  "
          f"solc {record['solc_version']}")
    print(f"contracts: {len(record['contracts'])}   "
          f"corpus wall time: {record['wall_ms']/1000:.1f}s")
    if record.get("excluded"):
        print(f"excluded sources: {len(record['excluded'])}   "
              f"empty sources: {len(record.get('empty_sources', []))}")

    have_base = baseline is not None
    header = f"{'contract':<44}{'runtime':>9}{'creation':>10}"
    if have_base:
        header += f"{'Δrun':>8}{'Δcre':>8}"
    print("\n" + header)
    print("-" * len(header))
    for c in record["contracts"]:
        row = f"{c['name']:<44}{c['runtime_bytes']:>9}{c['creation_bytes']:>10}"
        if have_base:
            b = base_map.get(c["name"])
            if b is None:
                row += f"{'new':>8}{'new':>8}"
            else:
                dr = c["runtime_bytes"] - b["runtime_bytes"]
                dc = c["creation_bytes"] - b["creation_bytes"]
                row += f"{dr:>+8}{dc:>+8}"
        print(row)
    print("-" * len(header))
    tr = record["total_runtime_bytes"]
    tc = record["total_creation_bytes"]
    total_row = f"{'TOTAL':<44}{tr:>9}{tc:>10}"
    if have_base:
        bdr = tr - baseline.get("total_runtime_bytes", 0)
        bdc = tc - baseline.get("total_creation_bytes", 0)
        total_row += f"{bdr:>+8}{bdc:>+8}"
    print(total_row)
    if have_base:
        btr = baseline.get("total_runtime_bytes", 0) or 1
        btc = baseline.get("total_creation_bytes", 0) or 1
        pr = 100.0 * (tr - baseline.get("total_runtime_bytes", 0)) / btr
        pc = 100.0 * (tc - baseline.get("total_creation_bytes", 0)) / btc
        print(f"{'% vs baseline':<44}{'':>9}{'':>10}{pr:>+7.2f}%{pc:>+7.2f}%")
        # Contracts present in baseline but missing now = compile regressions.
        missing = [n for n in base_map
                   if n not in {c['name'] for c in record['contracts']}]
        if missing:
            print(f"\nMISSING vs baseline (compile regressions): "
                  f"{', '.join(missing)}")


# --------------------------------------------------------------------------
# subcommand: check (correctness gate)
# --------------------------------------------------------------------------

def _collapse_axiom_reports(text: str) -> List[str]:
    """Rejoin Lean's wrapped `#print axioms` output and keep the axiom lines.

    Mirrors the awk in scripts/verify_layer.sh: continuation lines start with a
    space and belong to the previous logical line."""
    logical: List[str] = []
    buf = ""
    for line in text.splitlines():
        if line.startswith(" "):
            buf += " " + line.strip()
        else:
            if buf:
                logical.append(buf)
            buf = line
    if buf:
        logical.append(buf)
    return [ln for ln in logical if "depends on axioms" in ln]


def cmd_check(args: argparse.Namespace) -> int:
    env = tool_env()
    lake = env["LAKE"]
    result: Dict[str, Any] = {
        "commit": git_commit(),
        "date": datetime.datetime.now(datetime.timezone.utc)
                .strftime("%Y-%m-%dT%H:%M:%SZ"),
        "build_ok": False,
        "axiom_ok": False,
        "unexpected_axioms": [],
    }
    started = time.monotonic()

    print(f"[check] lake build {PROOF_ROOT_MODULE} ...", file=sys.stderr)
    build = subprocess.run([lake, "build", PROOF_ROOT_MODULE],
                           cwd=str(REPO_ROOT), env=env)
    if build.returncode != 0:
        result["build_ms"] = int((time.monotonic() - started) * 1000)
        _write_check(result)
        print("check: BUILD FAILED", file=sys.stderr)
        return EXIT_BUILD_FAIL
    result["build_ok"] = True

    print(f"[check] axiom footprint: lean {SMOKE_LEAN.name} ...", file=sys.stderr)
    smoke = subprocess.run([lake, "env", "lean", str(SMOKE_LEAN)],
                           cwd=str(REPO_ROOT), env=env,
                           capture_output=True, text=True)
    result["build_ms"] = int((time.monotonic() - started) * 1000)
    combined = (smoke.stdout or "") + "\n" + (smoke.stderr or "")
    if smoke.returncode != 0:
        result["axiom_check_error"] = combined.strip().splitlines()[-5:]
        _write_check(result)
        print("check: axiom smoke failed to elaborate", file=sys.stderr)
        return EXIT_AXIOM_FAIL

    reports = _collapse_axiom_reports(combined)
    if not reports:
        result["axiom_check_error"] = ["no axiom reports produced"]
        _write_check(result)
        print("check: no axiom reports produced", file=sys.stderr)
        return EXIT_AXIOM_FAIL
    expected_suffix = f"depends on axioms: {EXPECTED_AXIOMS}"
    unexpected = [r for r in reports if not r.endswith(expected_suffix)]
    result["axiom_reports_checked"] = len(reports)
    result["unexpected_axioms"] = unexpected
    if unexpected:
        _write_check(result)
        print(f"check: {len(unexpected)} theorem(s) with unexpected axioms:",
              file=sys.stderr)
        for u in unexpected:
            print("  " + u, file=sys.stderr)
        return EXIT_AXIOM_FAIL

    result["axiom_ok"] = True
    _write_check(result)
    print(f"check: OK  ({len(reports)} public theorems, "
          f"axioms = {EXPECTED_AXIOMS})")
    return EXIT_OK


def _write_check(result: Dict[str, Any]) -> None:
    BENCH_DIR.mkdir(parents=True, exist_ok=True)
    (BENCH_DIR / "opt_check.json").write_text(json.dumps(result, indent=2) + "\n")


# --------------------------------------------------------------------------
# subcommand: full
# --------------------------------------------------------------------------

def cmd_full(args: argparse.Namespace) -> int:
    rc = cmd_check(args)
    if rc != EXIT_OK:
        print("\nfull: correctness gate failed; skipping bench.", file=sys.stderr)
        return rc
    return cmd_bench(args)


# --------------------------------------------------------------------------

def die(msg: str, code: int) -> None:
    print(f"error: {msg}", file=sys.stderr)
    raise SystemExit(code)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(prog="opt_harness")
    sub = parser.add_subparsers(dest="command", required=True)
    for name in ("baseline", "bench", "check", "full"):
        p = sub.add_parser(name)
        p.add_argument("--fail-on-regression", action="store_true",
                       help="(bench/full) nonzero exit if total bytecode grew")
    args = parser.parse_args(argv)
    dispatch = {
        "baseline": cmd_baseline,
        "bench": cmd_bench,
        "check": cmd_check,
        "full": cmd_full,
    }
    return dispatch[args.command](args)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
