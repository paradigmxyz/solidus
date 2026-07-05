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
FORGE_BIN="${FORGE:-forge}"

TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-optimized-ast-smoke.XXXXXX")"

cleanup() {
  if [[ "${KEEP_TMP:-0}" == "1" ]]; then
    printf 'outdir=%s\n' "$OUTDIR"
  else
    rm -rf "$OUTDIR"
  fi
}
trap cleanup EXIT

COMPARE_OUT="$OUTDIR/simple.optimized.compare.txt"
BRIDGE_DIR="$OUTDIR/modifier-optimized-bridge-json"
MANIFEST="$BRIDGE_DIR/manifest.json"
MANIFEST_CHECK="$OUTDIR/modifier-optimized.manifest.lean-json-check.json"
WRAPPER_INPUT="$OUTDIR/simple.wrapper.standard.json"
WRAPPER_OUTPUT="$OUTDIR/simple.wrapper.optimized-output.json"

python3 "$ROOT/scripts/compare_contract_call_bytecode.py" "$ROOT/examples/Simple.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --forge "$FORGE_BIN" \
  --lake-cwd "$ROOT" \
  --contract Simple \
  --optimized \
  --calldata 0xc744c4860000000000000000000000000000000000000000000000000000000000000029 \
  > "$COMPARE_OUT"

python3 "$ROOT/scripts/solidity_to_yul_lean.py" "$ROOT/examples/ModifierBox.sol" \
  --solc "$SOLC_BIN" \
  --optimized \
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

python3 - "$ROOT/examples/Simple.sol" "$WRAPPER_INPUT" <<'PY'
import json
import sys
from pathlib import Path

source = Path(sys.argv[1]).read_text()
with open(sys.argv[2], "w") as handle:
    json.dump(
        {
            "language": "Solidity",
            "sources": {"Simple.sol": {"content": source}},
            "settings": {
                "viaIR": True,
                "optimizer": {"enabled": True, "details": {"yul": True}},
                "outputSelection": {"*": {"*": ["abi"]}},
            },
        },
        handle,
    )
PY

SOLC_LEAN_REAL_SOLC="$SOLC_BIN" \
SOLC_LEAN_LAKE="$LAKE_BIN" \
SOLC_LEAN_LAKE_CWD="$ROOT" \
  "$ROOT/scripts/solc_lean_standard_json.py" --standard-json \
  < "$WRAPPER_INPUT" > "$WRAPPER_OUTPUT"

python3 - "$COMPARE_OUT" "$MANIFEST" "$MANIFEST_CHECK" "$WRAPPER_OUTPUT" <<'PY'
import json
import sys
from pathlib import Path

compare_text = Path(sys.argv[1]).read_text()
manifest = json.loads(Path(sys.argv[2]).read_text())
check = json.loads(Path(sys.argv[3]).read_text())
wrapper_output = json.loads(Path(sys.argv[4]).read_text())

if "contract_call_compare=pass" not in compare_text:
    raise SystemExit("optimized Simple bytecode comparison did not pass")
if "calls=1" not in compare_text:
    raise SystemExit("optimized Simple comparison did not replay one call")

counts = manifest.get("counts", {})
if counts.get("entries") != 4 or counts.get("skippedContracts") != 0:
    raise SystemExit(f"unexpected optimized manifest counts: {counts!r}")
labels = {
    (entry.get("source"), entry.get("contract"), entry.get("selector"))
    for entry in manifest.get("entries", [])
}
expected = {
    ("ModifierBox.sol", "ModifierBase", "creation"),
    ("ModifierBox.sol", "ModifierBase", "runtime"),
    ("ModifierBox.sol", "ModifierBox", "creation"),
    ("ModifierBox.sol", "ModifierBox", "runtime"),
}
if labels != expected:
    raise SystemExit(f"unexpected optimized manifest labels: {sorted(labels)!r}")

check_counts = check.get("counts", {})
if (
    check_counts.get("checkedObjects") != 4
    or check_counts.get("checkedContracts") != 2
    or check_counts.get("skippedContracts") != 0
):
    raise SystemExit(f"unexpected optimized Lean decode counts: {check_counts!r}")

selected = wrapper_output["contracts"]["Simple.sol"]["Simple"]
if (
    selected.get("evmCompiler", {}).get("schema")
    != "evm-compiler.solc-standard-json-output.v1"
):
    raise SystemExit("optimized wrapper output missing compiler provenance")
creation = selected["evm"]["bytecode"]["object"]
runtime = selected["evm"]["deployedBytecode"]["object"]
if not creation or not runtime or not creation.endswith(runtime):
    raise SystemExit("optimized wrapper bytecode shape is invalid")

print("optimized_simple_compare=pass")
print(f"optimized_bridge_entries={counts['entries']}")
print(f"optimized_lean_decode_objects={check_counts['checkedObjects']}")
print(f"optimized_lean_decode_contracts={check_counts['checkedContracts']}")
print("optimized_wrapper_standard_json_output=yes")
PY
