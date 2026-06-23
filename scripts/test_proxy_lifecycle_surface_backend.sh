#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="$("$ROOT/scripts/find_schema_python.sh")"
LAKE_BIN="${LAKE:-$HOME/.elan/bin/lake}"
SOLC_BIN="${SOLC:-$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26}"
FORGE_BIN="${FORGE:-forge}"
CAST_BIN="${CAST:-cast}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-proxy-lifecycle.XXXXXX")"

cleanup() {
  if [[ "${KEEP_TMP:-0}" == "1" ]]; then
    printf 'outdir=%s\n' "$OUTDIR"
  else
    rm -rf "$OUTDIR"
  fi
}
trap cleanup EXIT

SOURCE="$ROOT/examples/ProxyLifecycleSurfaceBox.sol"
REPORT="$OUTDIR/proxy-lifecycle.lean-backend-check.json"
COMPARE="$OUTDIR/proxy-lifecycle.compare.txt"

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
  --contract ProxyLifecycleSurfaceBox \
  --optimized \
  --calldata "$("$CAST_BIN" calldata 'implementation()')" \
  --calldata "$("$CAST_BIN" calldata 'set(uint256)' 11)" \
  --calldata "$("$CAST_BIN" calldata 'value()')" \
  --calldata "$("$CAST_BIN" calldata 'reenter(uint256)' 22)" \
  --calldata "$("$CAST_BIN" calldata 'value()')" \
  --calldata "$("$CAST_BIN" calldata 'failAfterStore(uint256)' 33)" \
  --calldata "$("$CAST_BIN" calldata 'value()')" \
  --calldata "$("$CAST_BIN" calldata 'upgradeToV2()')" \
  --calldata "$("$CAST_BIN" calldata 'version()')" \
  --calldata "$("$CAST_BIN" calldata 'set(uint256)' 44)" \
  --calldata "$("$CAST_BIN" calldata 'value()')" \
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
if counts.get("checkedObjects") != 6:
    raise SystemExit(f"expected three creation/runtime object pairs: {counts!r}")
if counts.get("passedObjects") != 6 or counts.get("failedObjects") != 0:
    raise SystemExit(f"proxy lifecycle checked backend failed: {report!r}")
for item in report.get("checkedObjects", []):
    if item.get("status") != "pass" or item.get("firstNone") != "none":
        raise SystemExit(f"proxy lifecycle object is incomplete: {item!r}")

if compare.get("contract_call_compare") != "pass":
    raise SystemExit(f"proxy lifecycle execution mismatch: {compare!r}")
if compare.get("calls") != "11":
    raise SystemExit(f"proxy lifecycle call count changed: {compare!r}")
if compare.get("bridge_summary_1_backend_compatibility") != "ready":
    raise SystemExit(f"proxy lifecycle runtime is not backend-ready: {compare!r}")
if compare.get("bridge_summary_1_unsupported_primitives") != "none":
    raise SystemExit(f"proxy lifecycle has unsupported primitives: {compare!r}")

print("proxy_lifecycle_surface_backend=pass")
print("proxy_lifecycle_checked_objects=6")
print("proxy_lifecycle_compare_calls=11")
print("proxy_lifecycle_delegate_state=true")
print("proxy_lifecycle_reentrant_self_call=true")
print("proxy_lifecycle_revert_rollback=true")
print("proxy_lifecycle_create_upgrade=true")
PY
