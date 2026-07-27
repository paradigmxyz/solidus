#!/usr/bin/env bash
# Regression: creation objects with child datasize/dataoffset must be
# introspectable via stack-diagnostics (same Functions program the verified
# object-image planner already compiled).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="$("$ROOT/scripts/find_schema_python.sh")"
LAKE_BIN="${LAKE:-$HOME/.elan/bin/lake}"
SOLC_BIN="${SOLC:-$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-creation-stack-diagnostics.XXXXXX")"

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

contracts=(
  "CreateLifecycleSurfaceBox:examples/CreateLifecycleSurfaceBox.sol"
  "FactoryBox:examples/FactoryBox.sol"
  "ProxyLifecycleSurfaceBox:examples/ProxyLifecycleSurfaceBox.sol"
)

for entry in "${contracts[@]}"; do
  contract="${entry%%:*}"
  rel="${entry#*:}"
  source="$ROOT/$rel"
  bridge="$OUTDIR/${contract}.creation.bridge.json"
  diagnostics="$OUTDIR/${contract}.creation.diagnostics.txt"

  "$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
    "$source" \
    --solc "$SOLC_BIN" \
    --yul-ast-solc "$SOLC_BIN" \
    --contract "$contract" \
    --object creation \
    --optimized \
    --format bridge-json \
    --output "$bridge"

  "$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$bridge"

  if ! "$LAKE_BIN" exe solidus-backend stack-diagnostics \
      "$bridge" > "$diagnostics" 2>"$OUTDIR/${contract}.stderr.txt"; then
    printf 'error: stack-diagnostics failed for creation object %s\n' "$contract" >&2
    cat "$OUTDIR/${contract}.stderr.txt" >&2
    exit 1
  fi

  if ! grep -qx 'stack_diagnostics=complete' "$diagnostics"; then
    printf 'error: %s diagnostics missing stack_diagnostics=complete\n' "$contract" >&2
    cat "$diagnostics" >&2
    exit 1
  fi
  if ! grep -q 'stack_frontend_object_artifact=true' "$diagnostics"; then
    printf 'error: %s did not produce a verified object artifact\n' "$contract" >&2
    cat "$diagnostics" >&2
    exit 1
  fi
  if ! grep -q 'stack_program_artifact=true' "$diagnostics"; then
    printf 'error: %s Functions program failed to re-enter StackArtifact.compile?\n' \
      "$contract" >&2
    cat "$diagnostics" >&2
    exit 1
  fi

  printf 'creation_stack_diagnostics_ok=%s\n' "$contract"
done

printf 'creation_stack_diagnostics=pass\n'
