#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOLC_BIN="${SOLC:-solc}"
PYTHON_BIN="${PYTHON:-python3}"
BUNDLED_PYTHON="$HOME/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3"
if ! "$PYTHON_BIN" -c 'import jsonschema' >/dev/null 2>&1 && \
    [[ -x "$BUNDLED_PYTHON" ]]; then
  PYTHON_BIN="$BUNDLED_PYTHON"
fi

TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-frontend-optimized-summary-smoke.XXXXXX")"

cleanup() {
  if [[ "${KEEP_TMP:-0}" == "1" ]]; then
    printf 'outdir=%s\n' "$OUTDIR"
  else
    rm -rf "$OUTDIR"
  fi
}
trap cleanup EXIT

run_optimized_summary_case() {
  local name="$1"
  local source="$2"
  local contract="$3"
  local expected_entries="$4"
  local required_primitives="$5"
  local required_blockers="$6"

  local case_dir="$OUTDIR/$name"
  local bridge_dir="$case_dir/bridge-json"
  local manifest="$bridge_dir/manifest.json"
  local summary="$case_dir/manifest.bridge-json-summary.json"

  mkdir -p "$case_dir"
  printf 'frontend_optimized_summary_smoke=%s\n' "$name"

  "$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/$source" \
    --solc "$SOLC_BIN" \
    --optimized \
    --format bridge-json \
    --all-contracts \
    --bridge-json-dir "$bridge_dir" \
    --output "$manifest"

  "$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$manifest"

  "$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" "$manifest" \
    --input-format bridge-json-manifest \
    --format bridge-json-summary \
    --contract "$contract" \
    --object runtime \
    --output "$summary"

  "$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$summary"

  "$PYTHON_BIN" - \
    "$name" \
    "$manifest" \
    "$bridge_dir" \
    "$summary" \
    "$contract" \
    "$expected_entries" \
    "$required_primitives" \
    "$required_blockers" <<'PY'
import json
import sys
from pathlib import Path


def csv_set(value):
    return {part for part in value.split(",") if part}


name = sys.argv[1]
manifest_path = Path(sys.argv[2])
bridge_dir = Path(sys.argv[3])
summary_path = Path(sys.argv[4])
contract = sys.argv[5]
expected_entries = int(sys.argv[6])
required_primitives = csv_set(sys.argv[7])
required_blockers = csv_set(sys.argv[8])
expected_frontend = {"producer": "solc", "ast": "irOptimizedAst"}

manifest = json.loads(manifest_path.read_text())
counts = manifest.get("counts", {})
if counts.get("entries") != expected_entries or counts.get("skippedContracts") != 0:
    raise SystemExit(f"{name}: unexpected optimized manifest counts: {counts!r}")

runtime_entries = [
    entry for entry in manifest.get("entries", [])
    if entry.get("contract") == contract and entry.get("selector") == "runtime"
]
if len(runtime_entries) != 1:
    raise SystemExit(f"{name}: expected exactly one optimized runtime entry")
if runtime_entries[0].get("frontend") != expected_frontend:
    raise SystemExit(
        f"{name}: optimized manifest frontend drift: {runtime_entries[0].get('frontend')!r}"
    )

runtime_bridge = json.loads((bridge_dir / runtime_entries[0]["path"]).read_text())
if runtime_bridge.get("frontend") != expected_frontend:
    raise SystemExit(
        f"{name}: optimized bridge frontend drift: {runtime_bridge.get('frontend')!r}"
    )

summary = json.loads(summary_path.read_text())
if summary.get("schema") != "evm-compiler.solc-yul-bridge-manifest-summary.v1":
    raise SystemExit(f"{name}: unexpected optimized summary schema: {summary.get('schema')!r}")
summary_objects = summary.get("objects", [])
if len(summary_objects) != 1:
    raise SystemExit(f"{name}: unexpected optimized summary objects: {summary_objects!r}")

runtime_summary = summary_objects[0]
if runtime_summary.get("frontend") != expected_frontend:
    raise SystemExit(
        f"{name}: optimized summary frontend drift: {runtime_summary.get('frontend')!r}"
    )
if runtime_summary.get("contract") != contract or runtime_summary.get("selector") != "runtime":
    raise SystemExit(f"{name}: unexpected optimized summary label: {runtime_summary!r}")

primitive_entries = runtime_summary.get("calls", {}).get("primitive", {}).get("names", [])
primitives = {
    entry.get("name")
    for entry in primitive_entries
    if isinstance(entry, dict)
}
missing_primitives = sorted(required_primitives - primitives)
if missing_primitives:
    raise SystemExit(f"{name}: optimized summary missing primitives: {missing_primitives!r}")

compatibility = runtime_summary.get("backendCompatibility", {})
unsupported = set(compatibility.get("unsupportedPrimitiveNames", []))
missing_blockers = sorted(required_blockers - unsupported)
if missing_blockers:
    raise SystemExit(f"{name}: optimized summary missing blockers: {missing_blockers!r}")
unexpected_blockers = sorted(unsupported - required_blockers)
if unexpected_blockers:
    raise SystemExit(
        f"{name}: optimized summary reported supported primitives as unsupported: "
        f"{unexpected_blockers!r}"
    )
if required_blockers and compatibility.get("status") != "blocked":
    raise SystemExit(f"{name}: expected optimized backend compatibility to be blocked")

print(f"{name}_optimized_summary_entries={counts['entries']}")
print(f"{name}_optimized_summary_calls={runtime_summary['counts']['calls']}")
print(f"{name}_optimized_summary_frontend=irOptimizedAst")
print(f"{name}_optimized_summary_primitives=yes")
PY
}

run_optimized_summary_case \
  external_call \
  ExternalCallBox.sol \
  ExternalCallBox \
  2 \
  call,delegatecall,staticcall,returndatacopy,returndatasize,gas \
  ""

run_optimized_summary_case \
  event_matrix \
  EventMatrix.sol \
  EventMatrix \
  2 \
  log0,log1,log2,log3,log4 \
  ""

run_optimized_summary_case \
  inline_assembly \
  InlineAssemblyBox.sol \
  InlineAssemblyBox \
  2 \
  calldataload,keccak256,log2,revert,sload,sstore \
  ""

run_optimized_summary_case \
  mini_token \
  MiniToken.sol \
  MiniToken \
  2 \
  caller,keccak256,log3,revert,sload,sstore \
  ""

printf 'frontend_optimized_summary_smoke=pass\n'
printf 'frontend_optimized_summary_smoke_count=4\n'
