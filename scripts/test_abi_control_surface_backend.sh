#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="$("$ROOT/scripts/find_schema_python.sh")"
LAKE_BIN="${LAKE:-$HOME/.elan/bin/lake}"
SOLC_BIN="${SOLC:-$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26}"
FORGE_BIN="${FORGE:-forge}"
CAST_BIN="${CAST:-cast}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-abi-control-surface.XXXXXX")"

cleanup() {
  if [[ "${KEEP_TMP:-0}" == "1" ]]; then
    printf 'outdir=%s\n' "$OUTDIR"
  else
    rm -rf "$OUTDIR"
  fi
}
trap cleanup EXIT

REPORT="$OUTDIR/abi-control.lean-backend-check.json"
COMPARE="$OUTDIR/abi-control.compare.txt"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$ROOT/examples/AbiControlSurfaceBox.sol" \
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
  "$ROOT/examples/AbiControlSurfaceBox.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --contract AbiControlSurfaceBox \
  --runtime-only \
  --optimized \
  --calldata "$("$CAST_BIN" calldata 'recursive(uint256)' 0)" \
  --calldata "$("$CAST_BIN" calldata 'recursive(uint256)' 7)" \
  --calldata "$("$CAST_BIN" calldata 'control(uint256[])' '[]')" \
  --calldata "$("$CAST_BIN" calldata \
    'control(uint256[])' '[1,0,3,4,5]')" \
  --calldata "$("$CAST_BIN" calldata 'indirect(uint256)' 13)" \
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
    raise SystemExit(f"ABI/control checked backend failed: {report!r}")
for item in report.get("checkedObjects", []):
    if item.get("status") != "pass" or item.get("firstNone") != "none":
        raise SystemExit(f"ABI/control object did not reach a checked artifact: {item!r}")

if compare.get("contract_call_compare") != "pass":
    raise SystemExit(f"ABI/control execution mismatch: {compare!r}")
if compare.get("calls") != "5":
    raise SystemExit(f"ABI/control execution count changed: {compare!r}")
if compare.get("bridge_summary_1_backend_compatibility") != "ready":
    raise SystemExit(f"ABI/control runtime is not backend-ready: {compare!r}")

print("abi_control_surface_backend=pass")
print("abi_control_surface_checked_objects=2")
print("abi_control_surface_execution_compare_calls=5")
PY
