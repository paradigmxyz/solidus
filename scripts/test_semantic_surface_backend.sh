#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="${PYTHON:-python3}"
BUNDLED_PYTHON="$HOME/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3"
if ! "$PYTHON_BIN" -c 'import jsonschema' >/dev/null 2>&1 && \
    [[ -x "$BUNDLED_PYTHON" ]]; then
  PYTHON_BIN="$BUNDLED_PYTHON"
fi
LAKE_BIN="${LAKE:-$HOME/.elan/bin/lake}"
SOLC_BIN="${SOLC_826:-$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-semantic-surface.XXXXXX")"

cleanup() {
  if [[ "${KEEP_TMP:-0}" == "1" ]]; then
    printf 'outdir=%s\n' "$OUTDIR"
  else
    rm -rf "$OUTDIR"
  fi
}
trap cleanup EXIT

for executable in "$PYTHON_BIN" "$LAKE_BIN" "$SOLC_BIN"; do
  if [[ ! -x "$executable" ]] && ! command -v "$executable" >/dev/null 2>&1; then
    printf 'error: required executable is unavailable: %s\n' "$executable" >&2
    exit 1
  fi
done

compile_object() {
  local kind="$1"
  local bridge="$OUTDIR/semantic-surface-$kind.bridge.json"
  local diagnostics="$OUTDIR/semantic-surface-$kind.diagnostics.txt"

  "$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
    "$ROOT/examples/SemanticSurfaceBox.sol" \
    --input-format solidity \
    --source-name examples/SemanticSurfaceBox.sol \
    --solc "$SOLC_BIN" \
    --yul-ast-solc "$SOLC_BIN" \
    --contract SemanticSurfaceBox \
    --object "$kind" \
    --optimized \
    --format bridge-json \
    --output "$bridge"

  "$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$bridge"
  if [[ "$kind" == "runtime" ]]; then
    "$LAKE_BIN" exe evm-compiler-backend stack-diagnostics "$bridge" \
      > "$diagnostics"
  else
    "$LAKE_BIN" exe evm-compiler-backend image "$bridge" > "$diagnostics"
  fi
}

compile_object runtime
compile_object creation

MSIZE_ERROR="$OUTDIR/optimized-msize.stderr"
if "$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
    "$ROOT/examples/ResourceObserverBox.sol" \
    --input-format solidity \
    --source-name examples/ResourceObserverBox.sol \
    --solc "$SOLC_BIN" \
    --yul-ast-solc "$SOLC_BIN" \
    --contract ResourceObserverBox \
    --object runtime \
    --optimized \
    --format bridge-json \
    --output "$OUTDIR/optimized-msize.bridge.json" \
    2> "$MSIZE_ERROR"; then
  printf 'error: pinned solc unexpectedly accepted optimized explicit msize()\n' >&2
  exit 1
fi

"$PYTHON_BIN" - \
  "$OUTDIR/semantic-surface-runtime.bridge.json" \
  "$OUTDIR/semantic-surface-runtime.diagnostics.txt" \
  "$OUTDIR/semantic-surface-creation.diagnostics.txt" \
  "$MSIZE_ERROR" <<'PY'
import json
import sys
from pathlib import Path

bridge = json.loads(Path(sys.argv[1]).read_text())
runtime = Path(sys.argv[2]).read_text().splitlines()
creation = Path(sys.argv[3]).read_text().splitlines()
msize_error = Path(sys.argv[4]).read_text()


def require_line(lines, expected):
    if expected not in lines:
        raise SystemExit(f"missing backend result: {expected}")


for expected in (
    "stack_frontend_object_artifact=true",
    "stack_frontend_code_artifact=true",
    "stack_frontend_compact_code_artifact=true",
    "stack_program_artifact=true",
):
    require_line(runtime, expected)

creation_bytes = [
    line for line in creation if line.startswith("bytecode_bytes=")
]
if len(creation_bytes) != 1 or int(creation_bytes[0].split("=", 1)[1]) <= 0:
    raise SystemExit("semantic-surface creation emitted no checked bytecode")

stage_lines = [
    line for line in runtime
    if line.startswith("stack_program_production_stages=")
]
if len(stage_lines) != 1:
    raise SystemExit("missing normalized production-stage diagnostics")
for field in (
    "source_accepted=true",
    "normalized_accepted=true",
    "normalized_lowering=true",
    "normalized_expressions=true",
    "normalized_structured_wf=true",
    "normalized_cfg=true",
    "normalized_independent=true",
    "normalized_certified=true",
    "normalized_executable=true",
    "decode_window=true",
    "source_open=true",
    "normalized_open=true",
):
    if field not in stage_lines[0]:
        raise SystemExit(f"production stage failed: {field}")

callees = set()


def walk(value):
    if isinstance(value, dict):
        if value.get("node") == "call" and isinstance(value.get("callee"), str):
            callees.add(value["callee"])
        for child in value.values():
            walk(child)
    elif isinstance(value, list):
        for child in value:
            walk(child)


walk(bridge)
required = {
    "tstore", "tload", "blobhash", "blobbasefee", "mcopy",
    "codesize", "codecopy", "extcodesize", "extcodecopy", "extcodehash",
    "call", "callcode", "delegatecall", "staticcall", "gas",
    "returndatasize", "returndatacopy", "create", "create2",
    "log0", "log1", "log2", "log3", "log4",
    "stop", "selfdestruct", "invalid",
}
missing = sorted(required - callees)
if missing:
    raise SystemExit(f"optimized Yul dropped semantic-surface calls: {missing!r}")

if "msize instruction cannot be used when the Yul optimizer is activated" not in msize_error:
    raise SystemExit("optimized explicit msize rejection changed unexpectedly")

bytecode_lines = [
    line for line in runtime
    if line.startswith("stack_frontend_object_bytecode_bytes=")
]
if len(bytecode_lines) != 1 or int(bytecode_lines[0].split("=", 1)[1]) <= 0:
    raise SystemExit("semantic-surface runtime emitted no checked bytecode")

print("semantic_surface_backend=pass")
print(f"retained_primitives={len(required)}")
print(f"runtime_bytecode_bytes={bytecode_lines[0].split('=', 1)[1]}")
print("creation_artifact=true")
print("optimized_explicit_msize=solc_rejected")
PY
