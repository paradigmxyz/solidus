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
      [[ "$output" != *"arithmetic_execution_compare_calls=3"* ]]; then
    printf 'error: pinned solc %s failed the checked semantic surface\n%s\n' \
      "$version" "$output" >&2
    exit 1
  fi
  printf '%s\n' "$output"

  abi_output="$(SOLC="$compiler" "$ROOT/scripts/test_abi_control_surface_backend.sh")"
  if [[ "$abi_output" != *"abi_control_surface_backend=pass"* ]] ||
      [[ "$abi_output" != *"abi_control_surface_execution_compare_calls=5"* ]]; then
    printf 'error: pinned solc %s failed the ABI/control surface\n%s\n' \
      "$version" "$abi_output" >&2
    exit 1
  fi
  printf '%s\n' "$abi_output"

  effect_output="$(SOLC="$compiler" \
    "$ROOT/scripts/test_effect_ordering_surface_backend.sh")"
  if [[ "$effect_output" != *"effect_ordering_surface_backend=pass"* ]]; then
    printf 'error: pinned solc %s failed ordered-effect coverage\n%s\n' \
      "$version" "$effect_output" >&2
    exit 1
  fi
  printf '%s\n' "$effect_output"
  printf 'supported_solc_version=%s\n' "$version"
done

printf 'supported_solc_versions=pass\n'
printf 'supported_solc_versions_count=%s\n' "${#VERSIONS[@]}"
