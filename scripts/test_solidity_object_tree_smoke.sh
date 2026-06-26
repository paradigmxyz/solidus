#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="$("$ROOT/scripts/find_schema_python.sh")"
SOLC_BIN="${SOLC_826:-${SOLC:-$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26}}"
if [[ -n "${LAKE:-}" ]]; then
  LAKE_BIN="$LAKE"
elif [[ -x "$HOME/.elan/bin/lake" ]]; then
  LAKE_BIN="$HOME/.elan/bin/lake"
else
  LAKE_BIN="lake"
fi

TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-object-tree-smoke.XXXXXX")"

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

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/FactoryBox.sol" \
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
  --contract FactoryBox \
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
if counts.get("entries") != 4 or counts.get("skippedContracts") != 0:
    raise SystemExit(f"unexpected object-tree manifest counts: {counts!r}")

labels = {
    (entry.get("source"), entry.get("contract"), entry.get("selector"))
    for entry in manifest.get("entries", [])
}
expected = {
    ("FactoryBox.sol", "ChildBox", "creation"),
    ("FactoryBox.sol", "ChildBox", "runtime"),
    ("FactoryBox.sol", "FactoryBox", "creation"),
    ("FactoryBox.sol", "FactoryBox", "runtime"),
}
if labels != expected:
    raise SystemExit(f"unexpected object-tree manifest labels: {sorted(labels)!r}")

runtime_entries = [
    entry for entry in manifest["entries"]
    if entry["contract"] == "FactoryBox" and entry["selector"] == "runtime"
]
if len(runtime_entries) != 1:
    raise SystemExit("expected exactly one FactoryBox runtime bridge entry")
runtime_bridge = json.loads((bridge_dir / runtime_entries[0]["path"]).read_text())
selected = runtime_bridge.get("selectedObject", {})
if selected.get("name") is None:
    raise SystemExit("FactoryBox runtime bridge is missing selected object name")
if len(selected.get("subobjects", [])) < 1:
    raise SystemExit("FactoryBox runtime bridge did not preserve child subobject")
if len(selected.get("data", [])) < 1:
    raise SystemExit("FactoryBox runtime bridge did not preserve child data payload")

summary = json.loads(summary_path.read_text())
if summary.get("schema") != "evm-compiler.solc-yul-bridge-manifest-summary.v1":
    raise SystemExit(f"unexpected object-tree summary schema: {summary.get('schema')!r}")
summary_counts = summary.get("counts", {})
if summary_counts.get("objects") != 1:
    raise SystemExit(f"unexpected object-tree summary counts: {summary_counts!r}")
summary_objects = summary.get("objects", [])
if len(summary_objects) != 1:
    raise SystemExit(f"unexpected object-tree summary objects: {summary_objects!r}")
runtime_summary = summary_objects[0]
compatibility = runtime_summary.get("backendCompatibility", {})
if compatibility.get("status") != "ready":
    raise SystemExit(
        f"unexpected FactoryBox backend compatibility: {compatibility!r}"
    )
unsupported = set(compatibility.get("unsupportedPrimitiveNames", []))
if unsupported:
    raise SystemExit(
        f"FactoryBox summary expected no backend blockers: "
        f"{unsupported!r}"
    )
primitive_entries = runtime_summary.get("calls", {}).get("primitive", {}).get("names", [])
primitives = {
    entry.get("name")
    for entry in primitive_entries
    if isinstance(entry, dict)
}
missing_primitives = sorted({"create", "create2", "gas"} - primitives)
if missing_primitives:
    raise SystemExit(
        f"FactoryBox summary missing create primitives: {missing_primitives!r}"
    )
notes = compatibility.get("notes", [])
if not any("open external-boundary" in note for note in notes):
    raise SystemExit(
        f"FactoryBox summary missing create/backend note: {compatibility!r}"
    )

check = json.loads(check_path.read_text())
check_counts = check.get("counts", {})
if (
    check_counts.get("checkedObjects") != 4
    or check_counts.get("checkedContracts") != 2
    or check_counts.get("skippedContracts") != 0
):
    raise SystemExit(f"unexpected object-tree Lean decode counts: {check_counts!r}")

backend_check = json.loads(backend_check_path.read_text())
backend_counts = backend_check.get("counts", {})
if (
    backend_counts.get("checkedObjects") != 4
    or backend_counts.get("checkedContracts") != 2
    or backend_counts.get("skippedContracts") != 0
    or backend_counts.get("passedObjects") != 4
    or backend_counts.get("failedObjects") != 0
):
    raise SystemExit(f"unexpected object-tree backend check counts: {backend_counts!r}")

backend_status = {
    (item.get("contract"), item.get("selector")): (
        item.get("status"),
        item.get("firstNone"),
    )
    for item in backend_check.get("checkedObjects", [])
}
expected_backend_status = {
    ("ChildBox", "creation"): ("pass", "none"),
    ("ChildBox", "runtime"): ("pass", "none"),
    ("FactoryBox", "creation"): ("pass", "none"),
    ("FactoryBox", "runtime"): ("pass", "none"),
}
if backend_status != expected_backend_status:
    raise SystemExit(
        f"unexpected object-tree backend check statuses: {backend_status!r}"
    )

print(f"object_tree_bridge_entries={counts['entries']}")
print(f"object_tree_lean_decode_objects={check_counts['checkedObjects']}")
print(f"object_tree_contracts={check_counts['checkedContracts']}")
print(f"object_tree_backend_check_objects={backend_counts['checkedObjects']}")
print(f"object_tree_backend_check_passed={backend_counts['passedObjects']}")
print(f"object_tree_backend_check_failed={backend_counts['failedObjects']}")
print("object_tree_child_creation_backend_check=pass")
print("object_tree_child_runtime_backend_check=pass")
print("object_tree_factory_creation_backend_check=pass")
print("object_tree_factory_runtime_backend_check=pass")
print(f"object_tree_summary_calls={runtime_summary['counts']['calls']}")
print("object_tree_factory_runtime_child_subobjects=yes")
print("object_tree_factory_runtime_data_payloads=yes")
print("object_tree_factory_create_primitives=yes")
print("object_tree_factory_backend_compatibility=ready")
PY
