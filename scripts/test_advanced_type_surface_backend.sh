#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="$("$ROOT/scripts/find_schema_python.sh")"
LAKE_BIN="${LAKE:-$HOME/.elan/bin/lake}"
SOLC_BIN="${SOLC:-$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26}"
FORGE_BIN="${FORGE:-forge}"
CAST_BIN="${CAST:-cast}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-advanced-type-surface.XXXXXX")"

cleanup() {
  if [[ "${KEEP_TMP:-0}" == "1" ]]; then
    printf 'outdir=%s\n' "$OUTDIR"
  else
    rm -rf "$OUTDIR"
  fi
}
trap cleanup EXIT

REPORT="$OUTDIR/advanced-types.lean-backend-check.json"
COMPARE="$OUTDIR/advanced-types.compare.txt"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$ROOT/examples/AdvancedTypeSurfaceBox.sol" \
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
  "$ROOT/examples/AdvancedTypeSurfaceBox.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --contract AdvancedTypeSurfaceBox \
  --runtime-only \
  --optimized \
  --calldata "$("$CAST_BIN" calldata 'adjust(uint256)' 9)" \
  --calldata "$("$CAST_BIN" calldata 'saturating(uint128,uint128)' 340282366920938463463374607431768211450 99)" \
  --calldata "$("$CAST_BIN" calldata 'modular(uint256,uint256,uint256)' 123456789 987654321 1000003)" \
  --calldata "$("$CAST_BIN" calldata 'sliceHash(bytes,uint256,uint256)' 0x00112233445566778899 2 8)" \
  --calldata "$("$CAST_BIN" calldata 'codec((uint128,uint64,bytes32))' '(42,7,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa)')" \
  --calldata "$("$CAST_BIN" calldata 'hashPrecompiles(bytes)' 0x010203040506)" \
  --calldata "$("$CAST_BIN" calldata 'encodeTargetCall(bytes32,uint256)' 0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb 17)" \
  --calldata "$("$CAST_BIN" calldata 'select(uint8,uint256,uint256)' 2 11 13)" \
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
if counts.get("checkedObjects") != 4 or counts.get("checkedContracts") != 2:
    raise SystemExit(f"expected two creation/runtime contract pairs: {counts!r}")
if counts.get("passedObjects") != 4 or counts.get("failedObjects") != 0:
    raise SystemExit(f"advanced-type checked backend failed: {report!r}")
for item in report.get("checkedObjects", []):
    if item.get("status") != "pass" or item.get("firstNone") != "none":
        raise SystemExit(f"advanced-type object did not reach a checked artifact: {item!r}")

if compare.get("contract_call_compare") != "pass":
    raise SystemExit(f"advanced-type execution mismatch: {compare!r}")
if compare.get("calls") != "8":
    raise SystemExit(f"advanced-type execution count changed: {compare!r}")
if compare.get("bridge_summary_1_backend_compatibility") != "ready":
    raise SystemExit(f"advanced-type runtime is not backend-ready: {compare!r}")

print("advanced_type_surface_backend=pass")
print("advanced_type_surface_checked_objects=4")
print("advanced_type_surface_execution_compare_calls=8")
PY
