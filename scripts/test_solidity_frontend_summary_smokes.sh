#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOLC_BIN="${SOLC:-solc}"

TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-frontend-summary-smokes.XXXXXX")"

cleanup() {
  if [[ "${KEEP_TMP:-0}" == "1" ]]; then
    printf 'outdir=%s\n' "$OUTDIR"
  else
    rm -rf "$OUTDIR"
  fi
}
trap cleanup EXIT

run_summary_case() {
  local name="$1"
  local source="$2"
  local contract="$3"
  local expected_entries="$4"
  local expected_status="$5"
  local required_primitives="$6"
  local required_blockers="$7"
  local expected_note="$8"

  local case_dir="$OUTDIR/$name"
  local bridge_dir="$case_dir/bridge-json"
  local manifest="$bridge_dir/manifest.json"
  local summary="$case_dir/manifest.bridge-json-summary.json"

  mkdir -p "$case_dir"
  printf 'frontend_summary_smoke=%s\n' "$name"

  python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/$source" \
    --solc "$SOLC_BIN" \
    --format bridge-json \
    --all-contracts \
    --bridge-json-dir "$bridge_dir" \
    --output "$manifest"

  python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$manifest"

  python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$manifest" \
    --input-format bridge-json-manifest \
    --format bridge-json-summary \
    --contract "$contract" \
    --object runtime \
    --output "$summary"

  python3 "$ROOT/scripts/validate_bridge_json.py" --quiet "$summary"

  python3 - \
    "$name" \
    "$manifest" \
    "$bridge_dir" \
    "$summary" \
    "$contract" \
    "$expected_entries" \
    "$expected_status" \
    "$required_primitives" \
    "$required_blockers" \
    "$expected_note" <<'PY'
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
expected_status = sys.argv[7]
required_primitives = csv_set(sys.argv[8])
required_blockers = csv_set(sys.argv[9])
expected_note = sys.argv[10]

manifest = json.loads(manifest_path.read_text())
counts = manifest.get("counts", {})
if counts.get("entries") != expected_entries or counts.get("skippedContracts") != 0:
    raise SystemExit(f"{name}: unexpected manifest counts: {counts!r}")

runtime_entries = [
    entry for entry in manifest.get("entries", [])
    if entry.get("contract") == contract and entry.get("selector") == "runtime"
]
if len(runtime_entries) != 1:
    raise SystemExit(f"{name}: expected exactly one runtime bridge entry for {contract}")

frontend = runtime_entries[0].get("frontend")
if frontend != {"producer": "solc", "ast": "irAst", "evmVersion": "cancun"}:
    raise SystemExit(f"{name}: unexpected manifest frontend metadata: {frontend!r}")

runtime_bridge = json.loads((bridge_dir / runtime_entries[0]["path"]).read_text())
if runtime_bridge.get("frontend") != frontend:
    raise SystemExit(
        f"{name}: bridge frontend drift: {runtime_bridge.get('frontend')!r}"
    )
if not runtime_bridge.get("selectedObject", {}).get("name"):
    raise SystemExit(f"{name}: runtime bridge is missing selected object name")

summary = json.loads(summary_path.read_text())
if summary.get("schema") != "evm-compiler.solc-yul-bridge-manifest-summary.v1":
    raise SystemExit(f"{name}: unexpected summary schema: {summary.get('schema')!r}")
summary_counts = summary.get("counts", {})
if summary_counts.get("objects") != 1 or summary_counts.get("skippedContracts") != 0:
    raise SystemExit(f"{name}: unexpected summary counts: {summary_counts!r}")
summary_objects = summary.get("objects", [])
if len(summary_objects) != 1:
    raise SystemExit(f"{name}: unexpected summary objects: {summary_objects!r}")

runtime_summary = summary_objects[0]
if runtime_summary.get("contract") != contract or runtime_summary.get("selector") != "runtime":
    raise SystemExit(f"{name}: unexpected runtime summary label: {runtime_summary!r}")
if runtime_summary.get("frontend") != frontend:
    raise SystemExit(
        f"{name}: summary frontend drift: {runtime_summary.get('frontend')!r}"
    )
if runtime_summary.get("counts", {}).get("calls", 0) <= 0:
    raise SystemExit(f"{name}: summary did not record any Yul calls")

primitive_entries = runtime_summary.get("calls", {}).get("primitive", {}).get("names", [])
primitives = {
    entry.get("name")
    for entry in primitive_entries
    if isinstance(entry, dict)
}
missing_primitives = sorted(required_primitives - primitives)
if missing_primitives:
    raise SystemExit(f"{name}: summary missing primitives: {missing_primitives!r}")

compatibility = runtime_summary.get("backendCompatibility", {})
if compatibility.get("status") != expected_status:
    raise SystemExit(f"{name}: unexpected backend compatibility: {compatibility!r}")
unsupported = set(compatibility.get("unsupportedPrimitiveNames", []))
missing_blockers = sorted(required_blockers - unsupported)
if missing_blockers:
    raise SystemExit(f"{name}: summary missing backend blockers: {missing_blockers!r}")

if expected_note:
    text = "\n".join(compatibility.get("notes", []) + runtime_summary.get("backendHints", []))
    if expected_note not in text:
        raise SystemExit(
            f"{name}: expected note {expected_note!r} not found in {text!r}"
        )

print(f"{name}_summary_entries={counts['entries']}")
print(f"{name}_summary_calls={runtime_summary['counts']['calls']}")
print(f"{name}_summary_frontend_metadata=yes")
print(f"{name}_summary_primitives=yes")
print(f"{name}_summary_backend_compatibility={expected_status}")
PY
}

run_summary_case \
  packed_storage \
  PackedStorageBox.sol \
  PackedStorageBox \
  2 \
  ready \
  sload,sstore \
  "" \
  ""

run_summary_case \
  external_call \
  ExternalCallBox.sol \
  ExternalCallBox \
  2 \
  blocked \
  call,delegatecall,staticcall,returndatacopy,returndatasize,gas \
  gas \
  "open external-boundary"

run_summary_case \
  fallback_receive \
  FallbackBox.sol \
  FallbackBox \
  2 \
  ready \
  callvalue,calldataload,calldatasize,log2,return,sstore \
  "" \
  ""

run_summary_case \
  event_matrix \
  EventMatrix.sol \
  EventMatrix \
  2 \
  ready \
  log0,log1,log2,log3,log4 \
  "" \
  ""

run_summary_case \
  try_catch \
  TryCatchBox.sol \
  TryCatchBox \
  4 \
  blocked \
  call,returndatacopy,returndatasize,revert,log2,gas \
  gas \
  "open external-boundary"

run_summary_case \
  error_panic \
  ErrorPanicBox.sol \
  ErrorPanicBox \
  2 \
  ready \
  div,log2,mul,revert,sload,sstore \
  "" \
  ""

run_summary_case \
  mini_token \
  MiniToken.sol \
  MiniToken \
  2 \
  ready \
  caller,keccak256,log3,revert,sload,sstore \
  "" \
  ""

run_summary_case \
  factory_create \
  FactoryBox.sol \
  FactoryBox \
  4 \
  blocked \
  create,create2,gas \
  gas \
  "open external-boundary"

run_summary_case \
  storage_array \
  StorageArrayBox.sol \
  StorageArrayBox \
  2 \
  ready \
  keccak256,log2,sload,sstore \
  "" \
  ""

run_summary_case \
  abi_dynamic \
  AbiBox.sol \
  AbiBox \
  2 \
  ready \
  calldatacopy,keccak256,revert \
  "" \
  ""

run_summary_case \
  env_opcodes \
  EnvBox.sol \
  EnvBox \
  2 \
  ready \
  caller,origin,chainid,timestamp,callvalue \
  "" \
  ""

printf 'frontend_summary_smokes=pass\n'
printf 'frontend_summary_smokes_count=11\n'
