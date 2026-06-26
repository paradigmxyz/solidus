#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="$("$ROOT/scripts/find_schema_python.sh")"
SOLC_BIN="${SOLC:-solc}"
if [[ -n "${LAKE:-}" ]]; then
  LAKE_BIN="$LAKE"
elif [[ -x "$HOME/.elan/bin/lake" ]]; then
  LAKE_BIN="$HOME/.elan/bin/lake"
else
  LAKE_BIN="lake"
fi

TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-frontend-decode-smoke.XXXXXX")"

cleanup() {
  if [[ "${KEEP_TMP:-0}" == "1" ]]; then
    printf 'outdir=%s\n' "$OUTDIR"
  else
    rm -rf "$OUTDIR"
  fi
}
trap cleanup EXIT

BRIDGE_DIR="$OUTDIR/bridge-json"
MANIFEST="$BRIDGE_DIR/manifest.json"
MANIFEST_CHECK="$OUTDIR/manifest.lean-json-check.json"
MANIFEST_SUMMARY="$OUTDIR/manifest.bridge-json-summary.json"
MANIFEST_BACKEND_CHECK="$OUTDIR/manifest.lean-backend-check.json"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/PackedStorageBox.sol" \
  --solc "$SOLC_BIN" \
  --format bridge-json \
  --all-contracts \
  --bridge-json-dir "$BRIDGE_DIR" \
  --output "$MANIFEST"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$MANIFEST"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" "$MANIFEST" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-json-check \
  --output "$MANIFEST_CHECK"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" "$MANIFEST" \
  --input-format bridge-json-manifest \
  --format bridge-json-summary \
  --contract PackedStorageBox \
  --object runtime \
  --output "$MANIFEST_SUMMARY"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$MANIFEST_SUMMARY"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" "$MANIFEST" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-backend-check \
  --output "$MANIFEST_BACKEND_CHECK"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$MANIFEST_BACKEND_CHECK"

"$PYTHON_BIN" - "$MANIFEST" "$BRIDGE_DIR" "$MANIFEST_CHECK" "$MANIFEST_SUMMARY" "$MANIFEST_BACKEND_CHECK" <<'PY'
import json
import sys
from pathlib import Path

manifest_path = Path(sys.argv[1])
bridge_dir = Path(sys.argv[2])
check_path = Path(sys.argv[3])
summary_path = Path(sys.argv[4])
backend_check_path = Path(sys.argv[5])

manifest = json.loads(manifest_path.read_text())
counts = manifest.get("counts", {})
if counts.get("entries") != 2 or counts.get("skippedContracts") != 0:
    raise SystemExit(f"unexpected packed-storage manifest counts: {counts!r}")

runtime_entries = [
    entry for entry in manifest.get("entries", [])
    if entry.get("contract") == "PackedStorageBox"
    and entry.get("selector") == "runtime"
]
if len(runtime_entries) != 1:
    raise SystemExit("expected exactly one PackedStorageBox runtime bridge entry")

runtime_bridge = json.loads((bridge_dir / runtime_entries[0]["path"]).read_text())
functions = runtime_bridge.get("selectedObject", {}).get("functions", [])
if not isinstance(functions, list) or len(functions) < 1:
    raise SystemExit("PackedStorageBox runtime bridge has no lowered functions")

summary = json.loads(summary_path.read_text())
if summary.get("schema") != "evm-compiler.solc-yul-bridge-manifest-summary.v1":
    raise SystemExit(f"unexpected bridge summary schema: {summary.get('schema')!r}")
summary_counts = summary.get("counts", {})
if summary_counts.get("objects") != 1:
    raise SystemExit(f"unexpected bridge summary counts: {summary_counts!r}")
summary_objects = summary.get("objects", [])
if len(summary_objects) != 1:
    raise SystemExit(f"unexpected bridge summary objects: {summary_objects!r}")
runtime_summary = summary_objects[0]
if runtime_summary.get("selector") != "runtime":
    raise SystemExit(f"unexpected bridge summary selector: {runtime_summary!r}")
compatibility = runtime_summary.get("backendCompatibility", {})
if compatibility.get("status") != "ready":
    raise SystemExit(
        f"unexpected PackedStorageBox backend compatibility: {compatibility!r}"
    )
unsupported = set(compatibility.get("unsupportedPrimitiveNames", []))
if "sstore" in unsupported:
    raise SystemExit(
        f"PackedStorageBox incorrectly marked sstore unsupported: {compatibility!r}"
    )
primitive_entries = runtime_summary.get("calls", {}).get("primitive", {}).get("names", [])
primitives = {
    entry.get("name")
    for entry in primitive_entries
    if isinstance(entry, dict)
}
required = {"sload", "sstore", "signextend", "shl", "shr", "and", "or", "caller"}
missing = sorted(required - primitives)
if missing:
    raise SystemExit(f"PackedStorageBox summary missing primitives: {missing!r}")

check = json.loads(check_path.read_text())
check_counts = check.get("counts", {})
if (
    check_counts.get("checkedObjects") != 2
    or check_counts.get("checkedContracts") != 1
    or check_counts.get("skippedContracts") != 0
):
    raise SystemExit(f"unexpected packed-storage Lean decode counts: {check_counts!r}")

backend_check = json.loads(backend_check_path.read_text())
if backend_check.get("schema") != "evm-compiler.lean-backend-check.v1":
    raise SystemExit(
        f"unexpected packed-storage backend-check schema: {backend_check.get('schema')!r}"
    )
backend_counts = backend_check.get("counts", {})
if (
    backend_counts.get("checkedObjects") != 2
    or backend_counts.get("failedObjects") != 0
    or backend_counts.get("passedObjects") != 2
):
    raise SystemExit(
        f"unexpected packed-storage backend-check counts: {backend_counts!r}"
    )
first_none_counts = backend_check.get("firstNoneCounts", {})
if first_none_counts:
    raise SystemExit(
        f"packed-storage backend-check unexpectedly reported blockers: {first_none_counts!r}"
    )
checked_objects = backend_check.get("checkedObjects", [])
actual_results = {
    entry.get("selector"): (entry.get("status"), entry.get("firstNone"))
    for entry in checked_objects
}
expected_results = {
    "creation": ("pass", "none"),
    "runtime": ("pass", "none"),
}
if actual_results != expected_results:
    raise SystemExit(
        f"unexpected packed-storage backend-check results: {actual_results!r}"
    )

print(f"frontend_decode_packed_bridge_entries={counts['entries']}")
print(f"frontend_decode_packed_lean_objects={check_counts['checkedObjects']}")
print(f"frontend_decode_packed_runtime_functions={len(functions)}")
print(f"frontend_decode_packed_summary_calls={runtime_summary['counts']['calls']}")
print("frontend_decode_packed_primitives=yes")
print("frontend_decode_packed_backend_compatibility=ready")
print("frontend_decode_packed_backend_check=pass")
PY
