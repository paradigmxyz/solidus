#!/usr/bin/env bash
# Library backend regression smoke.
#
# Leg 1 — libraries must compile through the raw solc path.  solc emits
# `setimmutable(_, "library_deploy_address", address())` in EVERY library's
# creation code, and under the production optimizer settings (viaIR +
# optimizer.details.yul) the matching runtime `loadimmutable` can be
# optimized away entirely, leaving the name with ZERO references.  That
# zero-reference `setimmutable` is a defined no-op in solc semantics; the
# backend must accept it (regression: commit 5576b086 rejected it and every
# library stopped compiling).  Covered shapes:
#   - internal-only library, trivial runtime      (examples/MathLib.sol)
#   - external-function library + consumer        (examples/ExternalMathLib.sol)
#   - contract + library in one source            (examples/AdvancedTypeSurfaceBox.sol)
#
# Leg 2 — the converse guard stays fail-closed: a creation object whose
# runtime reads an immutable name that no `setimmutable` site writes (a
# set/load name mismatch) must be REJECTED by `solidus-backend raw-image`.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="${PYTHON:-python3}"
LAKE_BIN="${LAKE:-$HOME/.elan/bin/lake}"
SOLC_826="${SOLC_826:-$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-library-smoke.XXXXXX")"
trap 'rm -rf "$OUTDIR"' EXIT

for executable in "$LAKE_BIN" "$SOLC_826"; do
  if [[ ! -x "$executable" ]]; then
    printf 'error: required executable not found: %s\n' "$executable" >&2
    exit 1
  fi
done

"$PYTHON_BIN" - "$ROOT" "$OUTDIR" "$SOLC_826" "$LAKE_BIN" <<'PY'
import json
import pathlib
import subprocess
import sys

root = pathlib.Path(sys.argv[1])
outdir = pathlib.Path(sys.argv[2])
solc = sys.argv[3]
lake = sys.argv[4]

SETTINGS = {
    "viaIR": True,
    "optimizer": {"enabled": True, "details": {"yul": True}},
    "outputSelection": {
        "*": {
            "*": [
                "irOptimizedAst",
                "metadata",
                "evm.bytecode.object",
                "evm.deployedBytecode.object",
            ]
        }
    },
}

# source file -> contracts that must compile (library objects included)
CASES = {
    "MathLib.sol": ["MathLib"],
    "ExternalMathLib.sol": ["ExternalMathLib", "ExternalMathBox"],
    "AdvancedTypeSurfaceBox.sol": ["PriceMath", "AdvancedTypeSurfaceBox"],
}


def run_solc(source_name):
    content = (root / "examples" / source_name).read_text()
    standard_input = {
        "language": "Solidity",
        "sources": {source_name: {"content": content}},
        "settings": SETTINGS,
    }
    proc = subprocess.run(
        [solc, "--standard-json"],
        input=json.dumps(standard_input),
        capture_output=True,
        text=True,
        check=True,
    )
    output = json.loads(proc.stdout)
    errors = [
        entry
        for entry in output.get("errors", [])
        if entry.get("severity") == "error"
    ]
    if errors:
        raise SystemExit(f"solc failed on {source_name}: {errors}")
    return output


def run_backend(raw_path, source_name, contract, selector):
    return subprocess.run(
        [
            lake,
            "exe",
            "solidus-backend",
            "raw-image",
            str(raw_path),
            source_name,
            contract,
            selector,
        ],
        cwd=str(root),
        capture_output=True,
        text=True,
    )


def expect_bytecode(raw_path, source_name, contract, selector):
    proc = run_backend(raw_path, source_name, contract, selector)
    if proc.returncode != 0:
        raise SystemExit(
            f"FAIL: {source_name}:{contract} ({selector}) did not compile:\n"
            + (proc.stderr or proc.stdout)
        )
    bytecode = None
    for line in proc.stdout.splitlines():
        if line.startswith("bytecode=0x"):
            bytecode = line[len("bytecode=0x"):]
    if not bytecode:
        raise SystemExit(
            f"FAIL: {source_name}:{contract} ({selector}) "
            f"produced empty bytecode"
        )
    print(f"ok {source_name}:{contract} ({selector}) {len(bytecode) // 2} bytes")


# ---- Leg 1: every library shape compiles, creation and runtime ----------
for source_name, contracts in CASES.items():
    raw_path = outdir / f"{source_name}.raw.json"
    raw_path.write_text(json.dumps(run_solc(source_name)))
    for contract in contracts:
        for selector in ("creation", "runtime"):
            expect_bytecode(raw_path, source_name, contract, selector)

# ---- Leg 2: set/load name mismatch is rejected on creation --------------
mangled = run_solc("ImmutableBox.sol")
count = 0


def mangle(node):
    global count
    if isinstance(node, dict):
        if (
            node.get("nodeType") == "YulFunctionCall"
            and node.get("functionName", {}).get("name") == "setimmutable"
        ):
            name_arg = node["arguments"][1]
            name_arg["value"] = name_arg["value"] + "_typo"
            count += 1
        for value in node.values():
            mangle(value)
    elif isinstance(node, list):
        for value in node:
            mangle(value)


mangle(mangled)
if count == 0:
    raise SystemExit("FAIL: found no setimmutable site to mangle")
mangled_path = outdir / "ImmutableBox.typo.json"
mangled_path.write_text(json.dumps(mangled))

proc = run_backend(mangled_path, "ImmutableBox.sol", "ImmutableBox", "creation")
if proc.returncode == 0:
    raise SystemExit(
        "FAIL: mangled setimmutable name was ACCEPTED on the creation object"
    )
message = (proc.stderr or "") + (proc.stdout or "")
if "no setimmutable site ever writes" not in message:
    raise SystemExit(
        "FAIL: mangled input was rejected, but not by the immutable-coverage "
        f"guard:\n{message}"
    )
print(f"ok ImmutableBox typo rejected by coverage guard "
      f"({count} setimmutable site mangled)")

print("library_backend_smoke=pass")
PY
