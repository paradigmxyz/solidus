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
SOLC_BIN="${SOLC:-${SOLC_826:-$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26}}"
FORGE_BIN="${FORGE:-forge}"
CAST_BIN="${CAST:-cast}"
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

for executable in "$PYTHON_BIN" "$LAKE_BIN" "$SOLC_BIN" "$FORGE_BIN" "$CAST_BIN"; do
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

ARITHMETIC_COMPARE="$OUTDIR/semantic-surface-arithmetic.compare.txt"
"$PYTHON_BIN" "$ROOT/scripts/compare_contract_call_bytecode.py" \
  "$ROOT/examples/SemanticSurfaceBox.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --contract SemanticSurfaceBox \
  --runtime-only \
  --optimized \
  --calldata "$("$CAST_BIN" calldata \
    'arithmetic(uint256,uint256,uint256)' 0 0 0)" \
  --calldata "$("$CAST_BIN" calldata \
    'arithmetic(uint256,uint256,uint256)' 2 256 17)" \
  --calldata "$("$CAST_BIN" calldata \
    'arithmetic(uint256,uint256,uint256)' \
    0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff \
    1 \
    0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)" \
  > "$ARITHMETIC_COMPARE"

SURFACE_COMPARE="$OUTDIR/semantic-surface-execution.compare.txt"
"$PYTHON_BIN" "$ROOT/scripts/compare_contract_call_bytecode.py" \
  "$ROOT/examples/SemanticSurfaceBox.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --contract SemanticSurfaceBox \
  --optimized \
  --calldata "$("$CAST_BIN" calldata \
    'contextSummary(address,uint256)' \
    0x0000000000000000000000000000000000000000 0)" \
  --calldata "$("$CAST_BIN" calldata \
    'storageAndBytes(bytes32,uint256)' \
    0x0000000000000000000000000000000000000000000000000000000000000001 \
    123)" \
  --calldata "$("$CAST_BIN" calldata \
    'loadStorage(bytes32)' \
    0x0000000000000000000000000000000000000000000000000000000000000001)" \
  --calldata "$("$CAST_BIN" calldata \
    'transientAndBlob(bytes32,uint256,uint256)' \
    0x0000000000000000000000000000000000000000000000000000000000000002 \
    456 0)" \
  --calldata "$("$CAST_BIN" calldata 'memoryCopy(uint256,uint256)' 11 22)" \
  --calldata "$("$CAST_BIN" calldata \
    'codeSummary(address)' \
    0x0000000000000000000000000000000000000000)" \
  --calldata "$("$CAST_BIN" calldata \
    'calls(address,bytes)' \
    0x0000000000000000000000000000000000000000 0x)" \
  --calldata "$("$CAST_BIN" calldata \
    'createsSummary(bytes,bytes32)' \
    0x6001600c60003960016000f300 \
    0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb)" \
  --calldata "$("$CAST_BIN" calldata \
    'logs(bytes32,bytes32,bytes32,bytes32)' \
    0x0000000000000000000000000000000000000000000000000000000000000011 \
    0x0000000000000000000000000000000000000000000000000000000000000022 \
    0x0000000000000000000000000000000000000000000000000000000000000033 \
    0x0000000000000000000000000000000000000000000000000000000000000044)" \
  > "$SURFACE_COMPARE"

TERMINAL_COMPARE="$OUTDIR/semantic-surface-terminal.compare.txt"
"$PYTHON_BIN" "$ROOT/scripts/compare_contract_call_bytecode.py" \
  "$ROOT/examples/SemanticSurfaceBox.sol" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --lake-cwd "$ROOT" \
  --forge "$FORGE_BIN" \
  --contract SemanticSurfaceBox \
  --runtime-only \
  --optimized \
  --calldata "$("$CAST_BIN" calldata \
    'terminate(uint256,address)' 0 0x0000000000000000000000000000000000000000)" \
  --calldata "$("$CAST_BIN" calldata \
    'terminate(uint256,address)' 2 0x0000000000000000000000000000000000000000)" \
  --calldata "$("$CAST_BIN" calldata \
    'terminate(uint256,address)' 1 0x0000000000000000000000000000000000000000)" \
  > "$TERMINAL_COMPARE"

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
  "$MSIZE_ERROR" \
  "$ARITHMETIC_COMPARE" \
  "$SURFACE_COMPARE" \
  "$TERMINAL_COMPARE" <<'PY'
import json
import sys
from pathlib import Path

bridge = json.loads(Path(sys.argv[1]).read_text())
runtime = Path(sys.argv[2]).read_text().splitlines()
creation = Path(sys.argv[3]).read_text().splitlines()
msize_error = Path(sys.argv[4]).read_text()
arithmetic_compare = dict(
    line.split("=", 1)
    for line in Path(sys.argv[5]).read_text().splitlines()
    if "=" in line
)
surface_compare = dict(
    line.split("=", 1)
    for line in Path(sys.argv[6]).read_text().splitlines()
    if "=" in line
)
terminal_compare = dict(
    line.split("=", 1)
    for line in Path(sys.argv[7]).read_text().splitlines()
    if "=" in line
)


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
    "pop",
    "add", "mul", "sub", "div", "sdiv", "mod", "smod",
    "addmod", "mulmod", "exp", "signextend",
    "lt", "gt", "slt", "sgt", "eq", "iszero",
    "and", "or", "xor", "not", "byte", "shl", "shr", "sar",
    "address", "balance", "origin", "caller", "callvalue",
    "calldataload", "calldatasize", "calldatacopy", "gasprice",
    "blockhash", "coinbase", "timestamp", "number", "prevrandao",
    "gaslimit", "chainid", "selfbalance", "basefee",
    "mload", "mstore", "mstore8", "sload", "sstore", "keccak256",
    "tstore", "tload", "blobhash", "blobbasefee", "mcopy",
    "codesize", "codecopy", "extcodesize", "extcodecopy", "extcodehash",
    "call", "callcode", "delegatecall", "staticcall", "gas",
    "returndatasize", "returndatacopy", "create", "create2",
    "log0", "log1", "log2", "log3", "log4",
    "stop", "return", "revert", "selfdestruct", "invalid",
}
missing = sorted(required - callees)
if missing:
    raise SystemExit(f"optimized Yul dropped semantic-surface calls: {missing!r}")

if "msize instruction cannot be used when the Yul optimizer is activated" not in msize_error:
    raise SystemExit("optimized explicit msize rejection changed unexpectedly")

if arithmetic_compare.get("contract_call_compare") != "pass":
    raise SystemExit(f"semantic-surface arithmetic mismatch: {arithmetic_compare!r}")
if arithmetic_compare.get("calls") != "3":
    raise SystemExit(f"semantic-surface arithmetic call count changed: {arithmetic_compare!r}")
if arithmetic_compare.get("bridge_summary_1_unsupported_primitives") != "none":
    raise SystemExit(f"semantic-surface arithmetic reported unsupported calls: {arithmetic_compare!r}")

if surface_compare.get("contract_call_compare") != "pass":
    raise SystemExit(f"semantic-surface execution mismatch: {surface_compare!r}")
if surface_compare.get("calls") != "9":
    raise SystemExit(f"semantic-surface execution call count changed: {surface_compare!r}")
if surface_compare.get("bridge_summary_1_unsupported_primitives") != "none":
    raise SystemExit(f"semantic-surface execution reported unsupported calls: {surface_compare!r}")

if terminal_compare.get("contract_call_compare") != "pass":
    raise SystemExit(f"semantic-surface terminal mismatch: {terminal_compare!r}")
if terminal_compare.get("calls") != "3":
    raise SystemExit(f"semantic-surface terminal call count changed: {terminal_compare!r}")
if terminal_compare.get("bridge_summary_1_unsupported_primitives") != "none":
    raise SystemExit(f"semantic-surface terminal reported unsupported calls: {terminal_compare!r}")

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
print("arithmetic_execution_compare_calls=3")
print("semantic_execution_compare_calls=9")
print("terminal_execution_compare=stop-success,invalid-failure,selfdestruct-success")
print("optimized_explicit_msize=solc_rejected")
PY
