#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="$("$ROOT/scripts/find_schema_python.sh")"
LAKE_BIN="${LAKE:-$HOME/.elan/bin/lake}"
SOLC_BIN="${SOLC:-$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-effect-ordering.XXXXXX")"

cleanup() {
  if [[ "${KEEP_TMP:-0}" == "1" ]]; then
    printf 'outdir=%s\n' "$OUTDIR"
  else
    rm -rf "$OUTDIR"
  fi
}
trap cleanup EXIT

RUNTIME_BRIDGE="$OUTDIR/effect-ordering.runtime.bridge.json"
RUNTIME_DIAGNOSTICS="$OUTDIR/effect-ordering.runtime.diagnostics.txt"
CREATION_IMAGE="$OUTDIR/effect-ordering.creation.image.txt"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$ROOT/examples/EffectOrderingSurfaceBox.sol" \
  --solc "$SOLC_BIN" \
  --yul-ast-solc "$SOLC_BIN" \
  --contract EffectOrderingSurfaceBox \
  --object runtime \
  --optimized \
  --format bridge-json \
  --output "$RUNTIME_BRIDGE"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" \
  --quiet "$RUNTIME_BRIDGE"
"$LAKE_BIN" exe evm-compiler-backend stack-diagnostics \
  "$RUNTIME_BRIDGE" > "$RUNTIME_DIAGNOSTICS"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$ROOT/examples/EffectOrderingSurfaceBox.sol" \
  --solc "$SOLC_BIN" \
  --yul-ast-solc "$SOLC_BIN" \
  --contract EffectOrderingSurfaceBox \
  --object creation \
  --optimized \
  --format bridge-json \
  --output "$OUTDIR/effect-ordering.creation.bridge.json"
"$LAKE_BIN" exe evm-compiler-backend image \
  "$OUTDIR/effect-ordering.creation.bridge.json" > "$CREATION_IMAGE"

"$PYTHON_BIN" - \
  "$RUNTIME_BRIDGE" "$RUNTIME_DIAGNOSTICS" "$CREATION_IMAGE" <<'PY'
import json
import sys
from pathlib import Path

bridge = json.loads(Path(sys.argv[1]).read_text())
runtime = Path(sys.argv[2]).read_text().splitlines()
creation = Path(sys.argv[3]).read_text().splitlines()

calls = []


def walk(value):
    if isinstance(value, dict):
        if value.get("node") == "call" and isinstance(value.get("callee"), str):
            calls.append(value["callee"])
        for child in value.values():
            walk(child)
    elif isinstance(value, list):
        for child in value:
            walk(child)


walk(bridge)
required_order = ["log1", "call", "log2", "create2", "log3"]
cursor = 0
for name in calls:
    if name == required_order[cursor]:
        cursor += 1
        if cursor == len(required_order):
            break
if cursor != len(required_order):
    raise SystemExit(
        f"ordered effect subsequence was not retained: calls={calls!r}"
    )

for primitive in (
    "delegatecall", "gas", "returndatasize", "returndatacopy", "revert", "return"
):
    if primitive not in calls:
        raise SystemExit(f"proxy path dropped {primitive!r}: calls={calls!r}")

for expected in (
    "stack_frontend_object_artifact=true",
    "stack_frontend_code_artifact=true",
    "stack_program_artifact=true",
):
    if expected not in runtime:
        raise SystemExit(f"runtime checked artifact failed: {expected}")
creation_bytes = [line for line in creation if line.startswith("bytecode_bytes=")]
if len(creation_bytes) != 1 or int(creation_bytes[0].split("=", 1)[1]) <= 0:
    raise SystemExit("creation checked artifact emitted no bytecode")

print("effect_ordering_surface_backend=pass")
print("effect_ordering_subsequence=log1,call,log2,create2,log3")
print("proxy_terminal_effects=delegatecall,returndatacopy,revert,return")
PY
