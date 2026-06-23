#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="${PYTHON:-python3}"
BUNDLED_PYTHON="$HOME/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3"
if ! "$PYTHON_BIN" -c 'import jsonschema' >/dev/null 2>&1 && \
    [[ -x "$BUNDLED_PYTHON" ]]; then
  PYTHON_BIN="$BUNDLED_PYTHON"
fi
SOLC_BIN="${SOLC_826:-${SOLC:-$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26}}"
if [[ -n "${LAKE:-}" ]]; then
  LAKE_BIN="$LAKE"
elif [[ -x "$HOME/.elan/bin/lake" ]]; then
  LAKE_BIN="$HOME/.elan/bin/lake"
else
  LAKE_BIN="lake"
fi

TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-external-call-decode-smoke.XXXXXX")"

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
BACKEND_CHECK="$OUTDIR/manifest.lean-backend-check.json"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/ExternalCallBox.sol" \
  --solc "$SOLC_BIN" \
  --yul-ast-solc "$SOLC_BIN" \
  --optimized \
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
  --contract ExternalCallBox \
  --object runtime \
  --output "$MANIFEST_SUMMARY"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$MANIFEST_SUMMARY"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" "$MANIFEST" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-backend-check \
  --output "$BACKEND_CHECK"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$BACKEND_CHECK"

"$PYTHON_BIN" - "$MANIFEST" "$BRIDGE_DIR" "$MANIFEST_CHECK" "$MANIFEST_SUMMARY" "$BACKEND_CHECK" <<'PY'
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
    raise SystemExit(f"unexpected external-call manifest counts: {counts!r}")

runtime_entries = [
    entry for entry in manifest.get("entries", [])
    if entry.get("contract") == "ExternalCallBox"
    and entry.get("selector") == "runtime"
]
if len(runtime_entries) != 1:
    raise SystemExit("expected exactly one ExternalCallBox runtime bridge entry")

runtime_bridge = json.loads((bridge_dir / runtime_entries[0]["path"]).read_text())
functions = runtime_bridge.get("selectedObject", {}).get("functions", [])
if not isinstance(functions, list) or len(functions) < 1:
    raise SystemExit("ExternalCallBox runtime bridge has no lowered functions")

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
        f"unexpected ExternalCallBox backend compatibility: {compatibility!r}"
    )
unsupported = set(compatibility.get("unsupportedPrimitiveNames", []))
if unsupported:
    raise SystemExit(
        f"ExternalCallBox summary expected no backend blockers: "
        f"{unsupported!r}"
    )
notes = compatibility.get("notes", [])
if not any("open external-boundary" in note for note in notes):
    raise SystemExit(
        f"ExternalCallBox summary missing external-call note: {compatibility!r}"
    )

primitive_entries = runtime_summary.get("calls", {}).get("primitive", {}).get("names", [])
primitives = {
    entry.get("name")
    for entry in primitive_entries
    if isinstance(entry, dict)
}
required_primitives = {
    "call",
    "delegatecall",
    "staticcall",
    "returndatasize",
    "returndatacopy",
    "gas",
}
missing_primitives = sorted(required_primitives - primitives)
if missing_primitives:
    raise SystemExit(
        f"ExternalCallBox summary missing primitives: {missing_primitives!r}"
    )

check = json.loads(check_path.read_text())
check_counts = check.get("counts", {})
if (
    check_counts.get("checkedObjects") != 2
    or check_counts.get("checkedContracts") != 1
    or check_counts.get("skippedContracts") != 0
):
    raise SystemExit(f"unexpected external-call Lean decode counts: {check_counts!r}")

backend_check = json.loads(backend_check_path.read_text())
backend_counts = backend_check.get("counts", {})
if (
    backend_counts.get("checkedObjects") != 2
    or backend_counts.get("checkedContracts") != 1
    or backend_counts.get("skippedContracts") != 0
    or backend_counts.get("passedObjects") != 2
    or backend_counts.get("failedObjects") != 0
):
    raise SystemExit(f"unexpected external-call backend-check counts: {backend_counts!r}")

first_none_counts = backend_check.get("firstNoneCounts", {})
if first_none_counts:
    raise SystemExit(
        f"external-call backend unexpectedly reported blockers: {first_none_counts!r}"
    )

backend_status = {
    (item.get("contract"), item.get("selector")): (
        item.get("status"),
        item.get("firstNone"),
    )
    for item in backend_check.get("checkedObjects", [])
}
expected_backend_status = {
    ("ExternalCallBox", "creation"): ("pass", "none"),
    ("ExternalCallBox", "runtime"): ("pass", "none"),
}
if backend_status != expected_backend_status:
    raise SystemExit(
        f"unexpected external-call backend-check statuses: {backend_status!r}"
    )

print(f"external_call_decode_bridge_entries={counts['entries']}")
print(f"external_call_decode_lean_objects={check_counts['checkedObjects']}")
print(f"external_call_decode_backend_check_objects={backend_counts['checkedObjects']}")
print(f"external_call_decode_backend_check_failed={backend_counts['failedObjects']}")
print("external_call_decode_creation_backend_check=pass")
print("external_call_decode_runtime_backend_check=pass")
print(f"external_call_decode_runtime_functions={len(functions)}")
print(f"external_call_decode_summary_calls={runtime_summary['counts']['calls']}")
print("external_call_decode_primitives=yes")
print("external_call_decode_backend_compatibility=ready")
PY
