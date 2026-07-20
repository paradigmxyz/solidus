#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="$("$ROOT/scripts/find_schema_python.sh")"
LAKE_BIN="${LAKE:-$HOME/.elan/bin/lake}"
SOLC_BIN="${SOLC:-$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26}"
FORGE_BIN="${FORGE:-forge}"
CAST_BIN="${CAST:-cast}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-dynamic-storage-surface.XXXXXX")"

cleanup() {
  if [[ "${KEEP_TMP:-0}" == "1" ]]; then
    printf 'outdir=%s\n' "$OUTDIR"
  else
    rm -rf "$OUTDIR"
  fi
}
trap cleanup EXIT

for executable in "$PYTHON_BIN" "$LAKE_BIN" "$SOLC_BIN" "$FORGE_BIN" "$CAST_BIN"; do
  if [[ ! -x "$executable" ]] && ! command -v "$executable" >/dev/null 2>&1; then
    printf 'error: required executable is unavailable: %s\n' "$executable" >&2
    exit 1
  fi
done

# Hoist cast out of argument position: a $(...) inside an argument list is
# not covered by set -e, so a failing cast would silently pass empty
# calldata while the call-count assertion still held.
CALLDATA_ARGS=()
add_calldata() {
  local encoded
  encoded="$("$CAST_BIN" calldata "$@")"
  CALLDATA_ARGS+=(--calldata "$encoded")
}

SOURCE="$ROOT/examples/DynamicStorageSurfaceBox.sol"
REPORT="$OUTDIR/dynamic-storage.lean-backend-check.json"
COMPARE="$OUTDIR/dynamic-storage.compare.txt"
KEY="0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
BYTES31="0x11111111111111111111111111111111111111111111111111111111111111"
BYTES32="0x2222222222222222222222222222222222222222222222222222222222222222"
BYTES33="0x333333333333333333333333333333333333333333333333333333333333333333"

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

add_calldata 'replaceBlob(bytes,string)' 0x01 short
add_calldata 'replaceBlob(bytes,string)' "$BYTES31" thirty-one
add_calldata 'replaceBlob(bytes,string)' "$BYTES32" thirty-two
add_calldata 'replaceBlob(bytes,string)' "$BYTES33" thirty-three-crosses-the-inline-storage-boundary
add_calldata 'patchBlob(uint256,bytes1)' 32 0xff
add_calldata 'blobSnapshot()'
add_calldata 'replaceBlob(bytes,string)' 0x empty
add_calldata 'pushRow(uint256[])' '[1,2,3,4]'
add_calldata 'replaceRow(uint256,uint256[])' 0 '[9,8]'
add_calldata 'rowSnapshot(uint256)' 0
add_calldata 'setEntry(bytes32,uint64,bool,bytes,uint256[])' "$KEY" 18446744073709551615 true "$BYTES31" '[5,6,7]'
add_calldata 'mutateEntry(bytes32,uint256,uint256,bytes1)' "$KEY" 1 99 0xee
add_calldata 'entrySnapshot(bytes32)' "$KEY"
add_calldata 'nestedHash(uint256[][],bytes[])' '[[1,2],[],[3,4,5]]' '[0x01,0xaabb,0x]'
add_calldata 'rowSnapshot(uint256)' 99

"$PYTHON_BIN" "$ROOT/scripts/compare_contract_call_bytecode.py" \
  "$SOURCE" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --contract DynamicStorageSurfaceBox \
  --optimized \
  "${CALLDATA_ARGS[@]}" \
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
    raise SystemExit(f"dynamic-storage checked backend failed: {report!r}")
for item in report.get("checkedObjects", []):
    if item.get("status") != "pass" or item.get("firstNone") != "none":
        raise SystemExit(f"dynamic-storage object did not reach a checked artifact: {item!r}")

if compare.get("contract_call_compare") != "pass":
    raise SystemExit(f"dynamic-storage execution mismatch: {compare!r}")
if compare.get("calls") != "15":
    raise SystemExit(f"dynamic-storage execution count changed: {compare!r}")
if compare.get("bridge_summary_1_backend_compatibility") != "ready":
    raise SystemExit(f"dynamic-storage runtime is not backend-ready: {compare!r}")
if compare.get("bridge_summary_1_unsupported_primitives") != "none":
    raise SystemExit(f"dynamic-storage runtime has unsupported primitives: {compare!r}")

print("dynamic_storage_surface_backend=pass")
print("dynamic_storage_surface_checked_objects=2")
print("dynamic_storage_surface_execution_compare_calls=15")
print("dynamic_storage_short_long_boundary=true")
print("dynamic_storage_intentional_panic=true")
PY
