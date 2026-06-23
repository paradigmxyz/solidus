#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="$("$ROOT/scripts/find_schema_python.sh")"
LAKE_BIN="${LAKE:-$HOME/.elan/bin/lake}"
SOLC_BIN="${SOLC:-${SOLC_826:-$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26}}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-fork-validation.XXXXXX")"

cleanup() {
  if [[ "${KEEP_TMP:-0}" == "1" ]]; then
    printf 'outdir=%s\n' "$OUTDIR"
  else
    rm -rf "$OUTDIR"
  fi
}
trap cleanup EXIT

compile_bridge() {
  local source="$1"
  local contract="$2"
  local fork="$3"
  local output="$4"

  "$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
    "$ROOT/examples/$source" \
    --input-format solidity \
    --source-name "examples/$source" \
    --solc "$SOLC_BIN" \
    --yul-ast-solc "$SOLC_BIN" \
    --contract "$contract" \
    --object runtime \
    --optimized \
    --evm-version "$fork" \
    --format bridge-json \
    --output "$output"
  "$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$output"
}

check_pass() {
  local bridge="$1"
  local report="$2"
  "$LAKE_BIN" exe evm-compiler-backend check "$bridge" > "$report"
  grep -qx 'lean_backend_check=pass' "$report"
  grep -qx 'first_none=none' "$report"
}

LONDON_BRIDGE="$OUTDIR/london.bridge.json"
CANCUN_BRIDGE="$OUTDIR/cancun.bridge.json"
RELABELLED_BRIDGE="$OUTDIR/cancun-labelled-london.bridge.json"
LONDON_REPORT="$OUTDIR/london.report"
CANCUN_REPORT="$OUTDIR/cancun.report"
RELABELLED_REPORT="$OUTDIR/cancun-labelled-london.report"

compile_bridge ForkNeutralBox.sol ForkNeutralBox london "$LONDON_BRIDGE"
compile_bridge CancunOpcodeSurface.sol CancunOpcodeSurface cancun "$CANCUN_BRIDGE"
check_pass "$LONDON_BRIDGE" "$LONDON_REPORT"
check_pass "$CANCUN_BRIDGE" "$CANCUN_REPORT"

"$PYTHON_BIN" - "$CANCUN_BRIDGE" "$RELABELLED_BRIDGE" <<'PY'
import json
import sys
from pathlib import Path

source = Path(sys.argv[1])
target = Path(sys.argv[2])
document = json.loads(source.read_text())
document["frontend"]["evmVersion"] = "london"
target.write_text(json.dumps(document, indent=2) + "\n")
PY

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" \
  --quiet "$RELABELLED_BRIDGE"
"$LAKE_BIN" exe evm-compiler-backend check "$RELABELLED_BRIDGE" \
  > "$RELABELLED_REPORT"
grep -qx 'lean_backend_check=fail' "$RELABELLED_REPORT"
grep -qx 'first_none=object_image' "$RELABELLED_REPORT"

"$PYTHON_BIN" - "$CANCUN_BRIDGE" "$RELABELLED_BRIDGE" <<'PY'
import json
import sys
from pathlib import Path

cancun = json.loads(Path(sys.argv[1]).read_text())
relabeled = json.loads(Path(sys.argv[2]).read_text())

def primitive_names(value):
    if isinstance(value, dict):
        if value.get("node") == "call" and value.get("calleeKind") == "primitive":
            yield value.get("callee")
        for child in value.values():
            yield from primitive_names(child)
    elif isinstance(value, list):
        for child in value:
            yield from primitive_names(child)

names = set(primitive_names(cancun["selectedObject"]))
required = {"mcopy", "tstore", "tload"}
missing = sorted(required - names)
if missing:
    raise SystemExit(f"Cancun fixture lost required primitives: {missing!r}")
if cancun["frontend"]["evmVersion"] != "cancun":
    raise SystemExit("honest Cancun bridge metadata changed")
if relabeled["frontend"]["evmVersion"] != "london":
    raise SystemExit("adversarial London relabel did not persist")
PY

printf 'fork_validation_backend=pass\n'
printf 'fork_validation_honest_london=pass\n'
printf 'fork_validation_honest_cancun=pass\n'
printf 'fork_validation_cancun_as_london=rejected\n'
printf 'fork_validation_rejection_stage=object_image\n'
