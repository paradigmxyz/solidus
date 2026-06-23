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
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-fallback-decode-smoke.XXXXXX")"

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

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/FallbackBox.sol" \
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
  --contract FallbackBox \
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
if counts.get("entries") != 2 or counts.get("skippedContracts") != 0:
    raise SystemExit(f"unexpected fallback manifest counts: {counts!r}")

runtime_entries = [
    entry for entry in manifest.get("entries", [])
    if entry.get("contract") == "FallbackBox"
    and entry.get("selector") == "runtime"
]
if len(runtime_entries) != 1:
    raise SystemExit("expected exactly one FallbackBox runtime bridge entry")

frontend = runtime_entries[0].get("frontend")
if frontend != {"producer": "solc", "ast": "irAst", "evmVersion": "cancun"}:
    raise SystemExit(f"unexpected FallbackBox manifest frontend metadata: {frontend!r}")

runtime_bridge = json.loads((bridge_dir / runtime_entries[0]["path"]).read_text())
if runtime_bridge.get("frontend") != frontend:
    raise SystemExit(
        f"FallbackBox bridge frontend drift: {runtime_bridge.get('frontend')!r}"
    )
functions = runtime_bridge.get("selectedObject", {}).get("functions", [])
if not isinstance(functions, list) or len(functions) < 1:
    raise SystemExit("FallbackBox runtime bridge has no lowered functions")

summary = json.loads(summary_path.read_text())
if summary.get("schema") != "evm-compiler.solc-yul-bridge-manifest-summary.v1":
    raise SystemExit(f"unexpected fallback summary schema: {summary.get('schema')!r}")
summary_counts = summary.get("counts", {})
if summary_counts.get("objects") != 1:
    raise SystemExit(f"unexpected fallback summary counts: {summary_counts!r}")
summary_objects = summary.get("objects", [])
if len(summary_objects) != 1:
    raise SystemExit(f"unexpected fallback summary objects: {summary_objects!r}")
runtime_summary = summary_objects[0]
if runtime_summary.get("selector") != "runtime":
    raise SystemExit(f"unexpected fallback summary selector: {runtime_summary!r}")
if runtime_summary.get("frontend") != frontend:
    raise SystemExit(
        f"FallbackBox summary frontend drift: {runtime_summary.get('frontend')!r}"
    )

primitive_entries = runtime_summary.get("calls", {}).get("primitive", {}).get("names", [])
primitives = {
    entry.get("name")
    for entry in primitive_entries
    if isinstance(entry, dict)
}
required_primitives = {
    "callvalue",
    "calldataload",
    "calldatasize",
    "log2",
    "return",
    "sstore",
}
missing_primitives = sorted(required_primitives - primitives)
if missing_primitives:
    raise SystemExit(f"FallbackBox summary missing primitives: {missing_primitives!r}")

compatibility = runtime_summary.get("backendCompatibility", {})
if compatibility.get("status") != "ready":
    raise SystemExit(
        f"unexpected FallbackBox backend compatibility: {compatibility!r}"
    )
unsupported = set(compatibility.get("unsupportedPrimitiveNames", []))
unexpected_blockers = sorted({"log2", "sstore"} & unsupported)
if unexpected_blockers:
    raise SystemExit(
        f"FallbackBox summary still marks supported primitives unsupported: "
        f"{unexpected_blockers!r}"
    )

check = json.loads(check_path.read_text())
check_counts = check.get("counts", {})
if (
    check_counts.get("checkedObjects") != 2
    or check_counts.get("checkedContracts") != 1
    or check_counts.get("skippedContracts") != 0
):
    raise SystemExit(f"unexpected fallback Lean decode counts: {check_counts!r}")
checked_frontends = {
    tuple(item.get("frontend", {}).items())
    for item in check.get("checkedObjects", [])
}
expected_frontend = tuple(frontend.items())
if checked_frontends != {expected_frontend}:
    raise SystemExit(
        f"FallbackBox Lean decode frontend metadata drift: {checked_frontends!r}"
    )

backend_check = json.loads(backend_check_path.read_text())
backend_counts = backend_check.get("counts", {})
if (
    backend_counts.get("checkedObjects") != 2
    or backend_counts.get("checkedContracts") != 1
    or backend_counts.get("skippedContracts") != 0
    or backend_counts.get("passedObjects") != 2
    or backend_counts.get("failedObjects") != 0
):
    raise SystemExit(f"unexpected fallback backend-check counts: {backend_counts!r}")
if backend_check.get("firstNoneCounts") not in ({}, None):
    raise SystemExit(
        f"fallback backend-check unexpectedly reported blockers: "
        f"{backend_check.get('firstNoneCounts')!r}"
    )

backend_status = {
    (item.get("contract"), item.get("selector")): (
        item.get("status"),
        item.get("firstNone"),
    )
    for item in backend_check.get("checkedObjects", [])
}
expected_backend_status = {
    ("FallbackBox", "creation"): ("pass", "none"),
    ("FallbackBox", "runtime"): ("pass", "none"),
}
if backend_status != expected_backend_status:
    raise SystemExit(
        f"unexpected fallback backend-check statuses: {backend_status!r}"
    )

print(f"fallback_decode_bridge_entries={counts['entries']}")
print(f"fallback_decode_lean_objects={check_counts['checkedObjects']}")
print(f"fallback_decode_backend_check_objects={backend_counts['checkedObjects']}")
print(f"fallback_decode_backend_check_passed={backend_counts['passedObjects']}")
print("fallback_decode_backend_check=pass")
print(f"fallback_decode_runtime_functions={len(functions)}")
print(f"fallback_decode_summary_calls={runtime_summary['counts']['calls']}")
print("fallback_decode_frontend_metadata=yes")
print("fallback_decode_primitives=yes")
print("fallback_decode_backend_compatibility=ready")
PY
