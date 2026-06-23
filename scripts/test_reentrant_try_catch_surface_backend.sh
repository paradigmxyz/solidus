#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="$("$ROOT/scripts/find_schema_python.sh")"
LAKE_BIN="${LAKE:-$HOME/.elan/bin/lake}"
SOLC_BIN="${SOLC:-$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26}"
FORGE_BIN="${FORGE:-forge}"
CAST_BIN="${CAST:-cast}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-reentrant-try-catch.XXXXXX")"

cleanup() {
  if [[ "${KEEP_TMP:-0}" == "1" ]]; then
    printf 'outdir=%s\n' "$OUTDIR"
  else
    rm -rf "$OUTDIR"
  fi
}
trap cleanup EXIT

SOURCE="$ROOT/examples/ReentrantTryCatchSurfaceBox.sol"
REPORT="$OUTDIR/reentrant-try-catch.lean-backend-check.json"
COMPARE="$OUTDIR/reentrant-try-catch.compare.txt"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$SOURCE" \
  --solc "$SOLC_BIN" \
  --yul-ast-solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --all-contracts \
  --optimized \
  --format lean-backend-check \
  --output "$REPORT"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$REPORT"

"$PYTHON_BIN" "$ROOT/scripts/compare_contract_call_bytecode.py" \
  "$SOURCE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --contract ReentrantTryCatchSurfaceBox \
  --optimized \
  --calldata "$("$CAST_BIN" calldata 'probe(uint8,uint256)' 0 2)" \
  --calldata "$("$CAST_BIN" calldata 'probe(uint8,uint256)' 1 2)" \
  --calldata "$("$CAST_BIN" calldata 'probe(uint8,uint256)' 2 1)" \
  --calldata "$("$CAST_BIN" calldata 'probe(uint8,uint256)' 3 1)" \
  --calldata "$("$CAST_BIN" calldata 'probe(uint8,uint256)' 4 1)" \
  --calldata "$("$CAST_BIN" calldata 'probe(uint8,uint256)' 5 0)" \
  --calldata "$("$CAST_BIN" calldata 'probe(uint8,uint256)' 0 1)" \
  --calldata "$("$CAST_BIN" calldata 'counter()')" \
  > "$COMPARE"

"$PYTHON_BIN" - "$REPORT" "$COMPARE" <<'PY'
import json
import sys
from pathlib import Path

report = json.loads(Path(sys.argv[1]).read_text())
compare = dict(
    line.split("=", 1)
    for line in Path(sys.argv[2]).read_text().splitlines()
    if "=" in line
)

counts = report.get("counts", {})
if counts.get("checkedObjects") != 2:
    raise SystemExit(f"expected creation and runtime checks: {counts!r}")
if counts.get("passedObjects") != 2 or counts.get("failedObjects") != 0:
    raise SystemExit(f"reentrant try/catch checked backend failed: {report!r}")
for item in report.get("checkedObjects", []):
    if item.get("status") != "pass" or item.get("firstNone") != "none":
        raise SystemExit(f"reentrant try/catch object is incomplete: {item!r}")

if compare.get("contract_call_compare") != "pass":
    raise SystemExit(f"reentrant try/catch execution mismatch: {compare!r}")
if compare.get("calls") != "8":
    raise SystemExit(f"reentrant try/catch call count changed: {compare!r}")
if compare.get("bridge_summary_1_backend_compatibility") != "ready":
    raise SystemExit(f"reentrant try/catch runtime is not backend-ready: {compare!r}")
if compare.get("bridge_summary_1_unsupported_primitives") != "none":
    raise SystemExit(f"reentrant try/catch has unsupported primitives: {compare!r}")

print("reentrant_try_catch_surface_backend=pass")
print("reentrant_try_catch_checked_objects=2")
print("reentrant_try_catch_compare_calls=8")
print("reentrant_try_catch_failure_kinds=error,panic,custom,raw,invalid")
print("reentrant_try_catch_storage_rollback=true")
PY
