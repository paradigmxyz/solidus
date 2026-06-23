#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
INSTALL_SOLC="${INSTALL_SOLC:-1}"
read -r -a VERSIONS <<< "${SUPPORTED_SOLC_VERSIONS:-0.8.26 0.8.35}"

for version in "${VERSIONS[@]}"; do
  compiler="$HOME/.solc-select/artifacts/solc-$version/solc-$version"
  if [[ ! -x "$compiler" ]]; then
    if [[ "$INSTALL_SOLC" != "1" ]] || ! command -v solc-select >/dev/null 2>&1; then
      printf 'error: pinned solc %s is unavailable\n' "$version" >&2
      exit 1
    fi
    solc-select install "$version"
  fi

  output="$(SOLC="$compiler" "$ROOT/scripts/test_semantic_surface_backend.sh")"
  if [[ "$output" != *"semantic_surface_backend=pass"* ]] ||
      [[ "$output" != *"arithmetic_execution_compare_calls=3"* ]] ||
      [[ "$output" != *"semantic_execution_compare_calls=8"* ]] ||
      [[ "$output" != *"terminal_execution_compare=stop-success,invalid-failure,selfdestruct-success"* ]]; then
    printf 'error: pinned solc %s failed the checked semantic surface\n%s\n' \
      "$version" "$output" >&2
    exit 1
  fi
  printf '%s\n' "$output"

  abi_output="$(SOLC="$compiler" "$ROOT/scripts/test_abi_control_surface_backend.sh")"
  if [[ "$abi_output" != *"abi_control_surface_backend=pass"* ]] ||
      [[ "$abi_output" != *"abi_control_surface_execution_compare_calls=5"* ]] ||
      [[ "$abi_output" != *"abi_control_surface_malformed_compare_calls=6"* ]]; then
    printf 'error: pinned solc %s failed the ABI/control surface\n%s\n' \
      "$version" "$abi_output" >&2
    exit 1
  fi
  printf '%s\n' "$abi_output"

  advanced_output="$(SOLC="$compiler" \
    "$ROOT/scripts/test_advanced_type_surface_backend.sh")"
  if [[ "$advanced_output" != *"advanced_type_surface_backend=pass"* ]] ||
      [[ "$advanced_output" != *"advanced_type_surface_execution_compare_calls=9"* ]] ||
      [[ "$advanced_output" != *"advanced_type_surface_invalid_enum=true"* ]]; then
    printf 'error: pinned solc %s failed the advanced-type surface\n%s\n' \
      "$version" "$advanced_output" >&2
    exit 1
  fi
  printf '%s\n' "$advanced_output"

  storage_output="$(SOLC="$compiler" \
    "$ROOT/scripts/test_dynamic_storage_surface_backend.sh")"
  if [[ "$storage_output" != *"dynamic_storage_surface_backend=pass"* ]] ||
      [[ "$storage_output" != *"dynamic_storage_surface_execution_compare_calls=15"* ]] ||
      [[ "$storage_output" != *"dynamic_storage_short_long_boundary=true"* ]] ||
      [[ "$storage_output" != *"dynamic_storage_intentional_panic=true"* ]]; then
    printf 'error: pinned solc %s failed the dynamic-storage surface\n%s\n' \
      "$version" "$storage_output" >&2
    exit 1
  fi
  printf '%s\n' "$storage_output"

  reentrant_output="$(SOLC="$compiler" \
    "$ROOT/scripts/test_reentrant_try_catch_surface_backend.sh")"
  if [[ "$reentrant_output" != *"reentrant_try_catch_surface_backend=pass"* ]] ||
      [[ "$reentrant_output" != *"reentrant_try_catch_compare_calls=8"* ]] ||
      [[ "$reentrant_output" != *"reentrant_try_catch_storage_rollback=true"* ]]; then
    printf 'error: pinned solc %s failed reentrant try/catch coverage\n%s\n' \
      "$version" "$reentrant_output" >&2
    exit 1
  fi
  printf '%s\n' "$reentrant_output"

  effect_output="$(SOLC="$compiler" \
    "$ROOT/scripts/test_effect_ordering_surface_backend.sh")"
  if [[ "$effect_output" != *"effect_ordering_surface_backend=pass"* ]] ||
      [[ "$effect_output" != *"effect_ordering_execution_compare_calls=2"* ]]; then
    printf 'error: pinned solc %s failed ordered-effect coverage\n%s\n' \
      "$version" "$effect_output" >&2
    exit 1
  fi
  printf '%s\n' "$effect_output"
  printf 'supported_solc_version=%s\n' "$version"
done

printf 'supported_solc_versions=pass\n'
printf 'supported_solc_versions_count=%s\n' "${#VERSIONS[@]}"
