#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOLC_BIN="${SOLC:-solc}"
if [[ -n "${LAKE:-}" ]]; then
  LAKE_BIN="$LAKE"
elif [[ -x "$HOME/.elan/bin/lake" ]]; then
  LAKE_BIN="$HOME/.elan/bin/lake"
else
  LAKE_BIN="lake"
fi

TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-try-catch-decode-smoke.XXXXXX")"

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

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/TryCatchBox.sol" \
  --solc "$SOLC_BIN" \
  --format bridge-json \
  --all-contracts \
  --bridge-json-dir "$BRIDGE_DIR" \
  --output "$MANIFEST"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$MANIFEST"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$MANIFEST" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-json-check \
  --output "$MANIFEST_CHECK"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$MANIFEST" \
  --input-format bridge-json-manifest \
  --format bridge-json-summary \
  --contract TryCatchBox \
  --object runtime \
  --output "$MANIFEST_SUMMARY"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$MANIFEST_SUMMARY"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$MANIFEST" \
  --input-format bridge-json-manifest \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --format lean-backend-check \
  --output "$BACKEND_CHECK"

python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$BACKEND_CHECK"

python3 - "$MANIFEST" "$BRIDGE_DIR" "$MANIFEST_CHECK" "$MANIFEST_SUMMARY" "$BACKEND_CHECK" <<'PY'
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
    raise SystemExit(f"unexpected try-catch manifest counts: {counts!r}")

labels = {
    (entry.get("source"), entry.get("contract"), entry.get("selector"))
    for entry in manifest.get("entries", [])
}
expected = {
    ("TryCatchBox.sol", "TryCatchBox", "creation"),
    ("TryCatchBox.sol", "TryCatchBox", "runtime"),
    ("TryCatchBox.sol", "TryCatchTarget", "creation"),
    ("TryCatchBox.sol", "TryCatchTarget", "runtime"),
}
if labels != expected:
    raise SystemExit(f"unexpected try-catch manifest labels: {sorted(labels)!r}")

runtime_entries = [
    entry for entry in manifest.get("entries", [])
    if entry.get("contract") == "TryCatchBox"
    and entry.get("selector") == "runtime"
]
if len(runtime_entries) != 1:
    raise SystemExit("expected exactly one TryCatchBox runtime bridge entry")

runtime_bridge = json.loads((bridge_dir / runtime_entries[0]["path"]).read_text())
functions = runtime_bridge.get("selectedObject", {}).get("functions", [])
if not isinstance(functions, list) or len(functions) < 1:
    raise SystemExit("TryCatchBox runtime bridge has no lowered functions")

summary = json.loads(summary_path.read_text())
if summary.get("schema") != "evm-compiler.solc-yul-bridge-manifest-summary.v1":
    raise SystemExit(f"unexpected try-catch summary schema: {summary.get('schema')!r}")
summary_counts = summary.get("counts", {})
if summary_counts.get("objects") != 1:
    raise SystemExit(f"unexpected try-catch summary counts: {summary_counts!r}")
summary_objects = summary.get("objects", [])
if len(summary_objects) != 1:
    raise SystemExit(f"unexpected try-catch summary objects: {summary_objects!r}")
runtime_summary = summary_objects[0]
if runtime_summary.get("selector") != "runtime":
    raise SystemExit(f"unexpected try-catch summary selector: {runtime_summary!r}")

primitive_entries = runtime_summary.get("calls", {}).get("primitive", {}).get("names", [])
primitives = {
    entry.get("name")
    for entry in primitive_entries
    if isinstance(entry, dict)
}
required_primitives = {
    "call",
    "returndatacopy",
    "returndatasize",
    "revert",
    "log2",
    "gas",
}
missing_primitives = sorted(required_primitives - primitives)
if missing_primitives:
    raise SystemExit(
        f"TryCatchBox summary missing primitives: {missing_primitives!r}"
    )

compatibility = runtime_summary.get("backendCompatibility", {})
if compatibility.get("status") != "ready":
    raise SystemExit(
        f"unexpected TryCatchBox backend compatibility: {compatibility!r}"
    )
unsupported = set(compatibility.get("unsupportedPrimitiveNames", []))
if unsupported:
    raise SystemExit(
        f"TryCatchBox summary expected no backend blockers: "
        f"{unsupported!r}"
    )
if "log2" in unsupported:
    raise SystemExit(
        f"TryCatchBox incorrectly marked log2 unsupported: {compatibility!r}"
    )
notes = compatibility.get("notes", [])
if not any("open external-boundary" in note for note in notes):
    raise SystemExit(
        f"TryCatchBox summary missing external-call proof note: {compatibility!r}"
    )

check = json.loads(check_path.read_text())
check_counts = check.get("counts", {})
if (
    check_counts.get("checkedObjects") != 4
    or check_counts.get("checkedContracts") != 2
    or check_counts.get("skippedContracts") != 0
):
    raise SystemExit(f"unexpected try-catch Lean decode counts: {check_counts!r}")

backend_check = json.loads(backend_check_path.read_text())
backend_counts = backend_check.get("counts", {})
if (
    backend_counts.get("checkedObjects") != 4
    or backend_counts.get("checkedContracts") != 2
    or backend_counts.get("skippedContracts") != 0
):
    raise SystemExit(f"unexpected try-catch backend-check counts: {backend_counts!r}")

backend_status = {
    (item.get("contract"), item.get("selector")): (
        item.get("status"),
        item.get("firstNone"),
    )
    for item in backend_check.get("checkedObjects", [])
}
expected_labels = {
    ("TryCatchBox", "creation"),
    ("TryCatchBox", "runtime"),
    ("TryCatchTarget", "creation"),
    ("TryCatchTarget", "runtime"),
}
if set(backend_status) != expected_labels:
    raise SystemExit(
        f"unexpected try-catch backend-check labels: {backend_status!r}"
    )
for label, (status, first_none) in backend_status.items():
    if status not in {"pass", "fail"}:
        raise SystemExit(f"unexpected try-catch backend status for {label}: {status!r}")
    if status == "pass" and first_none != "none":
        raise SystemExit(
            f"try-catch backend pass did not report firstNone=none: "
            f"{label!r} -> {first_none!r}"
        )
    if status == "fail" and first_none in {None, "none"}:
        raise SystemExit(
            f"try-catch backend failure missed firstNone blocker: "
            f"{label!r} -> {first_none!r}"
        )

box_runtime_status, box_runtime_first_none = backend_status[
    ("TryCatchBox", "runtime")
]
target_runtime_status, target_runtime_first_none = backend_status[
    ("TryCatchTarget", "runtime")
]

print(f"try_catch_decode_bridge_entries={counts['entries']}")
print(f"try_catch_decode_lean_objects={check_counts['checkedObjects']}")
print(f"try_catch_decode_contracts={check_counts['checkedContracts']}")
print(f"try_catch_decode_backend_check_objects={backend_counts['checkedObjects']}")
print(f"try_catch_decode_backend_check_passed={backend_counts['passedObjects']}")
print(f"try_catch_decode_backend_check_failed={backend_counts['failedObjects']}")
print(f"try_catch_decode_box_runtime_backend_status={box_runtime_status}")
print(f"try_catch_decode_box_runtime_first_none={box_runtime_first_none}")
print(f"try_catch_decode_target_runtime_backend_status={target_runtime_status}")
print(f"try_catch_decode_target_runtime_first_none={target_runtime_first_none}")
print(f"try_catch_decode_runtime_functions={len(functions)}")
print(f"try_catch_decode_summary_calls={runtime_summary['counts']['calls']}")
print("try_catch_decode_primitives=yes")
print("try_catch_decode_backend_compatibility=ready")
PY
