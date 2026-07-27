#!/usr/bin/env bash
# Optional stack-diagnostics / stack-analysis must soft-fail when the Yul→Functions
# probe cannot normalize, instead of aborting the process (exit ≠ 0). Creation
# objects with child datasize/dataoffset currently hit this path on main.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON_BIN="$("$ROOT/scripts/find_schema_python.sh")"
LAKE_BIN="${LAKE:-$HOME/.elan/bin/lake}"
SOLC_BIN="${SOLC:-$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26}"
TMPDIR="${TMPDIR:-/tmp}"
OUTDIR="$(mktemp -d "$TMPDIR/evm-compiler-stack-diagnostics-soft-fail.XXXXXX")"
trap 'rm -rf "$OUTDIR"' EXIT

for executable in "$PYTHON_BIN" "$LAKE_BIN" "$SOLC_BIN"; do
  if [[ ! -x "$executable" ]] && ! command -v "$executable" >/dev/null 2>&1; then
    printf 'error: required executable is unavailable: %s\n' "$executable" >&2
    exit 1
  fi
done

SOURCE="$ROOT/examples/FactoryBox.sol"
BRIDGE="$OUTDIR/FactoryBox.creation.bridge.json"
DIAG="$OUTDIR/diagnostics.txt"
ANALYSIS="$OUTDIR/analysis.txt"

"$PYTHON_BIN" "$ROOT/scripts/solidity_to_yul_lean.py" \
  "$SOURCE" \
  --solc "$SOLC_BIN" \
  --yul-ast-solc "$SOLC_BIN" \
  --contract FactoryBox \
  --object creation \
  --optimized \
  --format bridge-json \
  --output "$BRIDGE"

"$PYTHON_BIN" "$ROOT/scripts/validate_bridge_json.py" --quiet "$BRIDGE"

set +e
"$LAKE_BIN" exe solidus-backend stack-diagnostics "$BRIDGE" \
  >"$DIAG" 2>"$OUTDIR/diag.stderr"
diag_rc=$?
"$LAKE_BIN" exe solidus-backend stack-analysis "$BRIDGE" \
  >"$ANALYSIS" 2>"$OUTDIR/analysis.stderr"
analysis_rc=$?
set -e

if [[ "$diag_rc" != "0" ]]; then
  printf 'error: stack-diagnostics soft-fail must exit 0, got %s\n' "$diag_rc" >&2
  cat "$OUTDIR/diag.stderr" "$DIAG" >&2
  exit 1
fi
if ! grep -qx 'stack_diagnostics=unavailable' "$DIAG"; then
  # If a later fix makes creation diagnostics succeed, accept complete too.
  if ! grep -qx 'stack_diagnostics=complete' "$DIAG"; then
    printf 'error: expected unavailable or complete diagnostics status\n' >&2
    cat "$DIAG" >&2
    exit 1
  fi
  printf 'stack_diagnostics_soft_fail=complete_ok\n'
else
  if ! grep -q 'stack_diagnostics_reason=yul_to_functions_normalization_none' "$DIAG"; then
    printf 'error: unavailable diagnostics missing reason\n' >&2
    cat "$DIAG" >&2
    exit 1
  fi
  printf 'stack_diagnostics_soft_fail=unavailable_ok\n'
fi

if [[ "$analysis_rc" != "0" ]]; then
  printf 'error: stack-analysis soft-fail must exit 0, got %s\n' "$analysis_rc" >&2
  cat "$OUTDIR/analysis.stderr" "$ANALYSIS" >&2
  exit 1
fi
if ! grep -Eqx 'stack_analysis=(unavailable|complete)' "$ANALYSIS"; then
  printf 'error: expected unavailable or complete analysis status\n' >&2
  cat "$ANALYSIS" >&2
  exit 1
fi

printf 'stack_diagnostics_soft_fail=pass\n'
