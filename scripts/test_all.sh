#!/usr/bin/env bash
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

export PATH="$ROOT/.venv/bin:$HOME/.local/bin:$HOME/.elan/bin:$HOME/.foundry/bin:$PATH"

missing=()
for command_name in uv git jq lake forge cast solc solc-select; do
  if ! command -v "$command_name" >/dev/null 2>&1; then
    missing+=("$command_name")
  fi
done
if (( ${#missing[@]} > 0 )); then
  printf 'error: missing test dependencies: %s\n' "${missing[*]}" >&2
  printf 'run ./scripts/setup.sh first\n' >&2
  exit 2
fi

if ! uv sync --locked; then
  printf 'error: failed to sync the locked Python environment\n' >&2
  exit 2
fi

PYTHON_BIN="$ROOT/.venv/bin/python"
if ! "$PYTHON_BIN" -c 'import jsonschema' >/dev/null 2>&1; then
  printf 'error: the uv environment is missing jsonschema\n' >&2
  exit 2
fi

export PYTHON="$PYTHON_BIN"
export LAKE="$(command -v lake)"
export FORGE="$(command -v forge)"
export CAST="$(command -v cast)"
export SOLC_817="$HOME/.solc-select/artifacts/solc-0.8.17/solc-0.8.17"
export SOLC_826="$HOME/.solc-select/artifacts/solc-0.8.26/solc-0.8.26"
export SOLC_835="$HOME/.solc-select/artifacts/solc-0.8.35/solc-0.8.35"
export YUL_AST_SOLC="$SOLC_826"
export SOLC_VERSION=0.8.26
export INSTALL_SOLC=0
unset SOLC

for compiler in "$SOLC_817" "$SOLC_826" "$SOLC_835"; do
  if [[ ! -x "$compiler" ]]; then
    printf 'error: pinned compiler is missing: %s\n' "$compiler" >&2
    printf 'run ./scripts/setup.sh first\n' >&2
    exit 2
  fi
done
if ! SOLC_VERSION=0.8.19 solc --version >/dev/null 2>&1; then
  printf 'error: pinned solc 0.8.19 is missing; run ./scripts/setup.sh\n' >&2
  exit 2
fi

timestamp="$(date -u '+%Y%m%dT%H%M%SZ')"
RESULT_DIR="$ROOT/.test-results/$timestamp"
mkdir -p "$RESULT_DIR"

passed=0
failed=0
failures=()

run_case() {
  local label="$1"
  shift
  local log="$RESULT_DIR/$label.log"
  printf '\n===== %s =====\n' "$label"
  if "$@" 2>&1 | tee "$log"; then
    passed=$((passed + 1))
    printf 'PASS %s\n' "$label"
  else
    failed=$((failed + 1))
    failures+=("$label ($log)")
    printf 'FAIL %s\n' "$label" >&2
  fi
}

is_aggregate() {
  case "$1" in
    test_all.sh|\
    test_famous_repo_bridge_smokes.sh|\
    test_solidity_forge_compare_all.sh|\
    test_solidity_frontend_decode_smokes.sh|\
    test_solidity_frontend_summary_all.sh|\
    test_solidity_local_smokes.sh|\
    test_solidity_target_bytecode_smokes.sh|\
    test_supported_solc_versions.sh)
      return 0
      ;;
  esac
  return 1
}

is_version_matrix_child() {
  case "$1" in
    test_abi_control_surface_backend.sh|\
    test_advanced_type_surface_backend.sh|\
    test_create_lifecycle_surface_backend.sh|\
    test_dynamic_storage_surface_backend.sh|\
    test_effect_ordering_surface_backend.sh|\
    test_fork_validation_backend.sh|\
    test_proxy_lifecycle_surface_backend.sh|\
    test_reentrant_try_catch_surface_backend.sh|\
    test_semantic_surface_backend.sh)
      return 0
      ;;
  esac
  return 1
}

run_case lean-verification "$ROOT/scripts/verify_layer.sh" all
run_case python-unit "$PYTHON_BIN" "$ROOT/scripts/test_solidity_to_yul_lean.py" -v

for script in "$ROOT"/scripts/test_*.sh; do
  name="$(basename "$script")"
  if is_aggregate "$name" || is_version_matrix_child "$name"; then
    continue
  fi
  run_case "shell-${name%.sh}" "$script"
done

run_case supported-solc-matrix "$ROOT/scripts/test_supported_solc_versions.sh"

printf '\n===== full-suite summary =====\n'
printf 'passed=%s\n' "$passed"
printf 'failed=%s\n' "$failed"
printf 'logs=%s\n' "$RESULT_DIR"

if (( failed > 0 )); then
  printf 'failures:\n' >&2
  for failure in "${failures[@]}"; do
    printf '  - %s\n' "$failure" >&2
  done
  exit 1
fi

printf 'full_test_suite=pass\n'
