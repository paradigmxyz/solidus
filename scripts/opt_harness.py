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

Contest metric (total gas)
--------------------------
  Each contract scores  total_gas = deploy_gas + exec_gas.  ``deploy_gas`` is
  the deployment-transaction cost priced arithmetically (yellow paper,
  ``deploy_gas_model = "computed"``); ``exec_gas`` is the summed cost of a fixed
  ordered set of execution vectors replayed on a pinned Foundry executor.
  Deployment gas prices code size at the chain's real rate (200 gas/byte), so
  size-vs-runtime tradeoffs are priced by the metric itself.  EIP-170 (runtime
  <= 24576) and EIP-3860 (creation <= 49152) are NO LONGER validity caps: they
  are reported informationally only (a ``>24576`` FYI flag + byte counts), never
  a gate.  The gas machinery lives in ``scripts/opt_gas_runner.py``.

Solc-parity sentinel
--------------------
  Every run also compiles each contract with plain solc (same via-ir + Yul
  optimizer settings) and records ``solc_runtime_bytes`` and the per-contract
  ratio ``ours/solc``.  A ratio regression is the early-warning signal that a
  benchmark-configuration or codegen change went the wrong way.

Exit codes
----------
  0   pass
  2   usage / configuration error
  10  correctness build failure (check)
  11  axiom-footprint failure     (check)
  20  a corpus contract failed to compile (bench)
  30  total-gas regression with --fail-on-regression (bench)

(Exit 40 / EIP-170/EIP-3860 cap enforcement was removed: deployment-size caps
are no longer validity conditions.  ``--enforce-caps`` is retained as a
deprecated no-op.)
"""

from __future__ import annotations

import argparse
import datetime
import importlib.util
import json
import os
import shutil
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
BASELINE_SIZE_ONLY_JSON = BENCH_DIR / "opt_baseline_size_only.json"
LAST_RUN_JSON = BENCH_DIR / "opt_last_run.json"

SCHEMA_VERSION = 2  # v1: size-only.  v2: adds gas (deploy + exec vectors).


def _load_gas_runner() -> Any:
    spec = importlib.util.spec_from_file_location(
        "opt_gas_runner", SCRIPTS / "opt_gas_runner.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


GAS = _load_gas_runner()

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


def default_forge() -> str:
    local = Path.home() / ".foundry" / "bin" / "forge"
    return str(local) if local.exists() else "forge"


def tool_env() -> Dict[str, str]:
    """Environment for subprocesses: pin solc/lake and disable the optional
    jsonschema output validation (the harness parses the JSON directly)."""
    env = dict(os.environ)
    solc = env.get("SOLC", default_solc())
    lake = env.get("LAKE", default_lake())
    forge = env.get("FORGE", default_forge())
    env.setdefault("SOLC_LEAN_REAL_SOLC", solc)
    env.setdefault("SOLC_LEAN_LAKE", lake)
    env["LAKE"] = lake
    env["SOLC"] = solc
    env["FORGE"] = forge
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


def forge_version(env: Dict[str, str]) -> str:
    forge = env.get("FORGE", default_forge())
    try:
        out = subprocess.run(
            [forge, "--version"], capture_output=True, text=True, env=env
        ).stdout
    except FileNotFoundError:
        return "unknown"
    for line in out.splitlines():
        line = line.strip()
        if line.lower().startswith("forge"):
            return line
    return out.strip().splitlines()[0] if out.strip() else "unknown"


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
            # Match the production corpus scripts EXACTLY (via-ir + Yul
            # optimizer, details.yul not runs): this is the configuration the
            # whole `optimizedRawSolcIr*` proof spine was built for.  The
            # solc_lean wrapper additionally force-sets viaIR, but we set both
            # explicitly here so the benchmark input is unambiguous.
            "viaIR": True,
            "optimizer": {"enabled": True, "details": {"yul": True}},
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
            evm = cdata.get("evm") or {}
            creation_hex = (evm.get("bytecode") or {}).get("object") or ""
            runtime_hex = (evm.get("deployedBytecode") or {}).get("object") or ""
            contracts_out.append({
                "name": f"{source_name}:{contract_name}",
                "runtime_bytes": int(sizes.get("runtimeBytes", 0)),
                "creation_bytes": int(sizes.get("creationBytes", 0)),
                "creation_hex": creation_hex,
                "runtime_hex": runtime_hex,
                "compile_ms": compile_ms,
            })
    contracts_out.sort(key=lambda c: c["name"])
    return {"ok": True, "compile_ms": compile_ms, "contracts": contracts_out,
            "reason": None}


def solc_reference_sizes(rel_path: str, env: Dict[str, str]) -> Dict[str, int]:
    """Compile one source with plain (real) solc under the SAME settings our
    path feeds it (via-ir + Yul optimizer) and return
    {"Source.sol:Contract": solc_runtime_bytes}.

    This is the permanent solc-parity sentinel: comparing our runtime bytes to
    solc's own backend on the identical input makes a settings-level
    misconfiguration (e.g. feeding the backend unoptimized Yul) impossible to
    miss.  Size only, no gas — kept cheap.  Returns {} on any solc failure so a
    parity hiccup never fails the run."""
    src_path = REPO_ROOT / rel_path
    if not src_path.exists():
        return {}
    name = src_path.name
    solc = env.get("SOLC_LEAN_REAL_SOLC", default_solc())
    standard_input = {
        "language": "Solidity",
        "sources": {name: {"content": src_path.read_text()}},
        "settings": {
            "viaIR": True,
            "optimizer": {"enabled": True, "details": {"yul": True}},
            "outputSelection": {
                "*": {"*": ["evm.deployedBytecode.object"]}
            },
        },
    }
    try:
        proc = subprocess.run(
            [solc, "--standard-json"], input=json.dumps(standard_input),
            capture_output=True, text=True, env=env, cwd=str(REPO_ROOT))
    except (FileNotFoundError, OSError):
        return {}
    if proc.returncode != 0:
        return {}
    try:
        output = json.loads(proc.stdout or "")
    except json.JSONDecodeError:
        return {}
    sizes: Dict[str, int] = {}
    for source_name, contracts in (output.get("contracts") or {}).items():
        if not isinstance(contracts, dict):
            continue
        for contract_name, cdata in contracts.items():
            if not isinstance(cdata, dict):
                continue
            evm = cdata.get("evm") or {}
            obj = (evm.get("deployedBytecode") or {}).get("object")
            if isinstance(obj, str) and obj != "":
                sizes[f"{source_name}:{contract_name}"] = len(obj) // 2
    return sizes


def measure_corpus(env: Dict[str, str]) -> Dict[str, Any]:
    corpus = read_corpus()
    contracts: List[Dict[str, Any]] = []
    excluded: List[Dict[str, str]] = []
    failures: List[str] = []
    empty_sources: List[str] = []
    solc_sizes: Dict[str, int] = {}  # parity sentinel: solc's own runtime bytes
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
        # Parity sentinel: solc's own runtime bytes on the identical input.
        solc_sizes.update(solc_reference_sizes(rel, env))
        names = ", ".join(c["name"].split(":")[-1] for c in result["contracts"])
        sys.stderr.write(f"ok [{names}] {result['compile_ms']}ms\n")
    compile_wall_ms = int((time.monotonic() - started) * 1000)

    # Attach the per-contract solc-parity ratio (ours / solc runtime bytes).
    for c in contracts:
        solc_rt = solc_sizes.get(c["name"])
        c["solc_runtime_bytes"] = solc_rt
        c["solc_ratio"] = (round(c["runtime_bytes"] / solc_rt, 3)
                           if solc_rt else None)

    # Gas leg: price each compiled contract's deployment + execution vectors.
    forge = env.get("FORGE", default_forge())
    solc = env.get("SOLC", default_solc())
    gas_started = time.monotonic()
    cap_violations: List[Dict[str, Any]] = []
    for c in contracts:
        vspec = GAS.load_vectors(c["name"])
        sys.stderr.write(f"[gas] {c['name']} ({vspec.get('vectors') and len(vspec['vectors']) or 0} vec) ... ")
        sys.stderr.flush()
        try:
            gas = GAS.measure_contract(
                forge, solc, c["name"],
                c["creation_hex"], c["runtime_hex"],
                c["runtime_bytes"], c["creation_bytes"], vspec)
        except Exception as exc:  # measurement failure is not a compile failure
            sys.stderr.write(f"GAS-ERROR ({exc})\n")
            gas = {
                "deploy_gas": GAS.compute_deploy_gas(
                    c["creation_hex"], c["runtime_bytes"]),
                "deploy_gas_model": GAS.DEPLOY_GAS_MODEL,
                "exec_gas": 0, "exec_gas_model": GAS.EXEC_GAS_MODEL,
                "cap_ok": GAS.cap_ok(c["runtime_bytes"], c["creation_bytes"]),
                "eip170_ok": c["runtime_bytes"] <= GAS.EIP170_RUNTIME_CAP,
                "eip3860_ok": c["creation_bytes"] <= GAS.EIP3860_CREATION_CAP,
                "vectors": 0, "vector_source": vspec.get("source", "none"),
                "per_vector": [], "gas_error": str(exc)[:200],
            }
            gas["total_gas"] = gas["deploy_gas"] + gas["exec_gas"]
        # Fold gas fields into the contract record (drop bulky per-vector +
        # raw hex from the summary record).
        for k in ("deploy_gas", "deploy_gas_model", "exec_gas",
                  "exec_gas_model", "total_gas", "cap_ok", "eip170_ok",
                  "eip3860_ok", "vectors", "vector_source"):
            c[k] = gas[k]
        if gas.get("gas_error"):
            c["gas_error"] = gas["gas_error"]
        c.pop("creation_hex", None)
        c.pop("runtime_hex", None)
        if not gas["cap_ok"]:
            cap_violations.append({
                "name": c["name"], "runtime_bytes": c["runtime_bytes"],
                "creation_bytes": c["creation_bytes"],
                "eip170_ok": gas["eip170_ok"], "eip3860_ok": gas["eip3860_ok"],
            })
        flag = "" if gas["cap_ok"] else "  !!CAP"
        sys.stderr.write(f"total={gas['total_gas']}{flag}\n")
    gas_wall_ms = int((time.monotonic() - gas_started) * 1000)
    wall_ms = compile_wall_ms + gas_wall_ms

    contracts.sort(key=lambda c: c["name"])
    return {
        "contracts": contracts,
        "excluded": excluded,
        "failures": failures,
        "empty_sources": empty_sources,
        "cap_violations": cap_violations,
        "wall_ms": wall_ms,
        "compile_wall_ms": compile_wall_ms,
        "gas_wall_ms": gas_wall_ms,
        "total_runtime_bytes": sum(c["runtime_bytes"] for c in contracts),
        "total_creation_bytes": sum(c["creation_bytes"] for c in contracts),
        "total_deploy_gas": sum(c["deploy_gas"] for c in contracts),
        "total_exec_gas": sum(c["exec_gas"] for c in contracts),
        "total_gas": sum(c["total_gas"] for c in contracts),
        # Parity totals: only over contracts solc also produced (fair ratio).
        "total_solc_runtime_bytes": sum(
            c["solc_runtime_bytes"] for c in contracts
            if c.get("solc_runtime_bytes")),
        "parity_runtime_bytes": sum(
            c["runtime_bytes"] for c in contracts
            if c.get("solc_runtime_bytes")),
    }


def build_record(env: Dict[str, str], measured: Dict[str, Any]) -> Dict[str, Any]:
    contract_keys = (
        "name", "runtime_bytes", "creation_bytes",
        "deploy_gas", "exec_gas", "total_gas", "cap_ok",
        "eip170_ok", "eip3860_ok", "solc_runtime_bytes", "solc_ratio",
        "vectors", "vector_source", "compile_ms")
    return {
        "schema_version": SCHEMA_VERSION,
        # Marks the compiler input configuration.  "optimized-yul" = solc
        # via-ir + Yul optimizer (the configuration the proof spine targets);
        # any baseline lacking this field predates the settings fix (D-C) and
        # its numbers are unopt-epoch garbage — do not compare across epochs.
        "input_epoch": "optimized-yul",
        "commit": git_commit(),
        "date": datetime.datetime.now(datetime.timezone.utc)
                .strftime("%Y-%m-%dT%H:%M:%SZ"),
        "solc_version": solc_version(env),
        "executor": {
            "engine": "foundry-forge-test",
            "forge_version": forge_version(env),
            "evm_version": GAS.FORGE_EVM_VERSION,
            "deploy_gas_model": GAS.DEPLOY_GAS_MODEL,
            "deploy_gas_formula": GAS.DEPLOY_GAS_FORMULA,
            "exec_gas_model": GAS.EXEC_GAS_MODEL,
            "gas_budget_per_call": GAS.GAS_BUDGET_PER_CALL,
            "eip170_runtime_cap": GAS.EIP170_RUNTIME_CAP,
            "eip3860_creation_cap": GAS.EIP3860_CREATION_CAP,
        },
        "contracts": [
            {k: c.get(k) for k in contract_keys}
            for c in measured["contracts"]
        ],
        "excluded": measured["excluded"],
        "empty_sources": measured["empty_sources"],
        "cap_violations": measured["cap_violations"],
        "total_runtime_bytes": measured["total_runtime_bytes"],
        "total_creation_bytes": measured["total_creation_bytes"],
        "total_deploy_gas": measured["total_deploy_gas"],
        "total_exec_gas": measured["total_exec_gas"],
        "total_gas": measured["total_gas"],
        "total_solc_runtime_bytes": measured["total_solc_runtime_bytes"],
        "parity_runtime_bytes": measured["parity_runtime_bytes"],
        "solc_parity_ratio": (
            round(measured["parity_runtime_bytes"]
                  / measured["total_solc_runtime_bytes"], 3)
            if measured["total_solc_runtime_bytes"] else None),
        "wall_ms": measured["wall_ms"],
        "compile_wall_ms": measured.get("compile_wall_ms"),
        "gas_wall_ms": measured.get("gas_wall_ms"),
    }


# --------------------------------------------------------------------------
# subcommands: baseline / bench
# --------------------------------------------------------------------------

def cmd_baseline(args: argparse.Namespace) -> int:
    env = tool_env()
    measured = measure_corpus(env)
    record = build_record(env, measured)
    BENCH_DIR.mkdir(parents=True, exist_ok=True)
    # Preserve the pre-gas (size-only, schema v1) baseline for history, once.
    if BASELINE_JSON.exists() and not BASELINE_SIZE_ONLY_JSON.exists():
        try:
            prev = json.loads(BASELINE_JSON.read_text())
            if prev.get("schema_version", 1) < SCHEMA_VERSION:
                shutil.copyfile(BASELINE_JSON, BASELINE_SIZE_ONLY_JSON)
                print(f"kept prior size-only baseline as "
                      f"{BASELINE_SIZE_ONLY_JSON.relative_to(REPO_ROOT)}")
        except json.JSONDecodeError:
            pass
    BASELINE_JSON.write_text(json.dumps(record, indent=2) + "\n")
    print_summary("BASELINE", record, baseline=None)
    print(f"\nwrote {BASELINE_JSON.relative_to(REPO_ROOT)}")
    if measured["failures"]:
        print(f"\nWARNING: {len(measured['failures'])} corpus source(s) "
              f"failed to compile and are recorded under \"excluded\".",
              file=sys.stderr)
    if measured["cap_violations"]:
        print(f"\nFYI: {len(measured['cap_violations'])} contract(s) exceed "
              f"the historical EIP-170/EIP-3860 size (recorded under "
              f"\"cap_violations\"); informational only, not a validity gate.",
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

    if getattr(args, "enforce_caps", False):
        print("\nnote: --enforce-caps is a deprecated no-op — EIP-170/EIP-3860 "
              "deployment-size caps are no longer validity conditions "
              "(deployment gas prices size at 200 gas/byte).", file=sys.stderr)

    if measured["cap_violations"]:
        names = ", ".join(v["name"] for v in measured["cap_violations"])
        # Informational only (a >24576 FYI): oversized contracts pay real
        # measured CREATE gas via the metric, they are not disqualified.
        print(f"\nFYI: {len(measured['cap_violations'])} contract(s) exceed "
              f"the historical EIP-170/EIP-3860 size ({names}); informational "
              f"only, priced by deploy gas.", file=sys.stderr)

    if args.fail_on_regression and baseline is not None:
        dg = record["total_gas"] - baseline.get("total_gas", 0)
        if dg > 0:
            print(f"\nERROR: total-gas regression ({dg:+d} gas vs baseline)",
                  file=sys.stderr)
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
    ex = record.get("executor", {})
    print(f"executor: {ex.get('engine','?')} "
          f"{ex.get('forge_version','?')}  evm={ex.get('evm_version','?')}  "
          f"deploy={ex.get('deploy_gas_model','?')}")
    print(f"contracts: {len(record['contracts'])}   "
          f"wall time: {record['wall_ms']/1000:.1f}s "
          f"(compile {record.get('compile_wall_ms',0)/1000:.0f}s + "
          f"gas {record.get('gas_wall_ms',0)/1000:.0f}s)")
    if record.get("excluded"):
        print(f"excluded sources: {len(record['excluded'])}   "
              f"empty sources: {len(record.get('empty_sources', []))}")

    have_base = baseline is not None
    # Gas-first table.  A leading marker flags cap violations prominently.
    header = (f"{'':<2}{'contract':<42}{'total_gas':>12}{'deploy':>11}"
              f"{'exec':>10}{'runtime':>8}{'creat':>8}{'solcRT':>8}{'ratio':>7}")
    if have_base:
        header += f"{'Δtotal':>11}"
    print("\n" + header)
    print("-" * len(header))
    for c in record["contracts"]:
        # ">24576" is now an informational FYI flag only, not a validity gate.
        over = c["runtime_bytes"] > GAS.EIP170_RUNTIME_CAP
        mark = ">>" if over else "  "
        solc_rt = c.get("solc_runtime_bytes")
        ratio = c.get("solc_ratio")
        solc_s = str(solc_rt) if solc_rt else "-"
        ratio_s = f"{ratio:.2f}" if ratio else "-"
        row = (f"{mark:<2}{c['name']:<42}{c.get('total_gas',0):>12}"
               f"{c.get('deploy_gas',0):>11}{c.get('exec_gas',0):>10}"
               f"{c['runtime_bytes']:>8}{c['creation_bytes']:>8}"
               f"{solc_s:>8}{ratio_s:>7}")
        if have_base:
            b = base_map.get(c["name"])
            if b is None or "total_gas" not in b:
                row += f"{'new':>11}"
            else:
                dg = c.get("total_gas", 0) - b.get("total_gas", 0)
                row += f"{dg:>+11}"
        print(row)
    print("-" * len(header))
    tg = record.get("total_gas", 0)
    td = record.get("total_deploy_gas", 0)
    te = record.get("total_exec_gas", 0)
    tr = record["total_runtime_bytes"]
    tc = record["total_creation_bytes"]
    tsolc = record.get("total_solc_runtime_bytes") or 0
    overall_ratio = record.get("solc_parity_ratio")
    tsolc_s = str(tsolc) if tsolc else "-"
    oratio_s = f"{overall_ratio:.2f}" if overall_ratio else "-"
    total_row = (f"{'':<2}{'TOTAL':<42}{tg:>12}{td:>11}{te:>10}"
                 f"{tr:>8}{tc:>8}{tsolc_s:>8}{oratio_s:>7}")
    if have_base:
        total_row += f"{tg - baseline.get('total_gas', 0):>+11}"
    print(total_row)
    if overall_ratio is not None:
        print(f"{'':<2}{'solc-parity (ours/solc runtime bytes)':<42}"
              f"{'':>12}{'':>11}{'':>10}{'':>8}{'':>8}"
              f"{'':>8}{overall_ratio:>7.2f}  "
              f"(over {record.get('parity_runtime_bytes',0)} vs "
              f"{tsolc} solc bytes)")
    if have_base:
        btg = baseline.get("total_gas", 0) or 1
        pg = 100.0 * (tg - baseline.get("total_gas", 0)) / btg
        print(f"{'':<2}{'% total_gas vs baseline':<42}{'':>12}{'':>11}"
              f"{'':>10}{'':>8}{'':>8}{pg:>+10.2f}%")
        missing = [n for n in base_map
                   if n not in {c['name'] for c in record['contracts']}]
        if missing:
            print(f"\nMISSING vs baseline (compile regressions): "
                  f"{', '.join(missing)}")

    # Size FYI call-out (informational: not a validity gate).  A ">>" marker in
    # the table flags a runtime image over the historical EIP-170 size.
    violations = record.get("cap_violations", [])
    if violations:
        print(f"\nFYI: {len(violations)} contract(s) over the historical "
              f"EIP-170/EIP-3860 size [runtime {GAS.EIP170_RUNTIME_CAP}, "
              f"creation {GAS.EIP3860_CREATION_CAP}] — informational, priced "
              f"by deploy gas, NOT disqualified:")
        for v in violations:
            flags = []
            if not v["eip170_ok"]:
                flags.append(f"runtime={v['runtime_bytes']}")
            if not v["eip3860_ok"]:
                flags.append(f"creation={v['creation_bytes']}")
            print(f"   {v['name']}: {'; '.join(flags)}")


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
                       help="(bench/full) nonzero exit if total gas grew")
        p.add_argument("--enforce-caps", action="store_true",
                       help="DEPRECATED no-op: EIP-170/EIP-3860 deployment-size "
                            "caps are no longer validity conditions")
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
