#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="${PYTHON:-python3}"
LAKE_BIN="${LAKE:-$HOME/.elan/bin/lake}"
SOLC_BIN="${SOLC:-${SOLC_826:-$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26}}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-raw-solc-transition.XXXXXX")"
trap 'rm -rf "$OUTDIR"' EXIT

if ! command -v "$PYTHON_BIN" >/dev/null 2>&1; then
  printf 'error: required executable not found: %s\n' "$PYTHON_BIN" >&2
  exit 1
fi

for executable in "$LAKE_BIN" "$SOLC_BIN"; do
  if [[ ! -x "$executable" ]]; then
    printf 'error: required executable not found: %s\n' "$executable" >&2
    exit 1
  fi
done

"$PYTHON_BIN" - "$ROOT" "$OUTDIR" "$PYTHON_BIN" "$LAKE_BIN" "$SOLC_BIN" <<'PY'
import copy
import importlib.util
import json
import pathlib
import subprocess
import sys

root = pathlib.Path(sys.argv[1])
outdir = pathlib.Path(sys.argv[2])
python_bin = pathlib.Path(sys.argv[3])
lake_bin = pathlib.Path(sys.argv[4])
solc = pathlib.Path(sys.argv[5])
bridge_path = root / "scripts" / "solidity_to_yul_lean.py"
spec = importlib.util.spec_from_file_location("solidity_to_yul_lean", bridge_path)
bridge = importlib.util.module_from_spec(spec)
assert spec.loader is not None
sys.modules[spec.name] = bridge
spec.loader.exec_module(bridge)

source_name = "Simple.sol"
contract = "Simple"
request = bridge.standard_json_input(
    source_name,
    (root / "examples" / source_name).read_text(),
    via_ir=True,
    optimized=True,
    experimental=True,
    require_bytecode=True,
    evm_version="cancun",
)
request_path = outdir / "simple.standard-input.json"
request_path.write_text(json.dumps(request, separators=(",", ":")))
raw_output = bridge.run_solc(str(solc), copy.deepcopy(request), ())
raw_path = outdir / "simple.standard-output.json"
raw_path.write_text(json.dumps(raw_output, separators=(",", ":")))
bridge_json_path = outdir / "simple.runtime.bridge.json"
subprocess.run(
    [
        str(python_bin),
        str(bridge_path),
        str(request_path),
        "--input-format",
        "standard-json",
        "--solc",
        str(solc),
        "--lake",
        str(lake_bin),
        "--lake-cwd",
        str(root),
        "--source-name",
        source_name,
        "--contract",
        contract,
        "--object",
        "runtime",
        "--optimized",
        "--format",
        "bridge-json",
        "-o",
        str(bridge_json_path),
    ],
    check=True,
)
PY

RAW_JSON="$OUTDIR/simple.standard-output.json"
BRIDGE_JSON="$OUTDIR/simple.runtime.bridge.json"
RAW_BEFORE="$OUTDIR/raw-before.txt"
RAW_AFTER="$OUTDIR/raw-after.txt"
BRIDGE_BEFORE="$OUTDIR/bridge-before.txt"
BRIDGE_AFTER="$OUTDIR/bridge-after.txt"

"$LAKE_BIN" exe solidus-backend raw-summary \
  "$RAW_JSON" Simple.sol Simple runtime > "$RAW_BEFORE"
"$LAKE_BIN" exe solidus-backend summary \
  "$BRIDGE_JSON" > "$BRIDGE_BEFORE"

raw_before_bytes="$(sed -n 's/^bytecode_bytes=//p' "$RAW_BEFORE")"
bridge_before_bytes="$(sed -n 's/^bytecode_bytes=//p' "$BRIDGE_BEFORE")"
if [[ -z "$raw_before_bytes" || "$raw_before_bytes" -le 0 ]]; then
  echo "raw Standard JSON backend emitted no bytes before bridge mutation" >&2
  exit 1
fi
if [[ "$raw_before_bytes" != "$bridge_before_bytes" ]]; then
  printf 'raw/bridge byte length mismatch before mutation: %s != %s\n' \
    "$raw_before_bytes" "$bridge_before_bytes" >&2
  exit 1
fi

printf '{ "frontend": "mutated normalized bridge" }\n' > "$BRIDGE_JSON"
if "$LAKE_BIN" exe solidus-backend summary "$BRIDGE_JSON" \
    > "$BRIDGE_AFTER" 2>&1; then
  echo "mutated normalized bridge unexpectedly compiled" >&2
  exit 1
fi

"$LAKE_BIN" exe solidus-backend raw-summary \
  "$RAW_JSON" Simple.sol Simple runtime > "$RAW_AFTER"
raw_after_bytes="$(sed -n 's/^bytecode_bytes=//p' "$RAW_AFTER")"
if [[ "$raw_after_bytes" != "$raw_before_bytes" ]]; then
  printf 'raw byte length changed after bridge mutation: %s != %s\n' \
    "$raw_after_bytes" "$raw_before_bytes" >&2
  exit 1
fi

printf 'raw_solc_backend_transition_bytes=%s\n' "$raw_after_bytes"
printf 'raw_solc_backend_transition_bridge_mutation=isolated\n'
printf 'raw_solc_backend_transition=pass\n'
