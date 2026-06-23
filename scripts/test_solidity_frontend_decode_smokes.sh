#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

smokes=(
  test_raw_solc_frontend_smoke.sh
  test_raw_solc_frontend_differential.sh
  test_raw_solc_backend_transition.sh
  test_solidity_object_tree_smoke.sh
  test_solidity_frontend_decode_smoke.sh
  test_solidity_external_call_decode_smoke.sh
  test_solidity_fallback_decode_smoke.sh
  test_solidity_event_matrix_decode_smoke.sh
  test_solidity_selfdestruct_decode_smoke.sh
  test_solidity_try_catch_decode_smoke.sh
  test_solidity_error_panic_decode_smoke.sh
  test_solidity_minitoken_decode_smoke.sh
)

printf 'frontend_decode_smokes_start=%s\n' "${#smokes[@]}"

count=0
for smoke in "${smokes[@]}"; do
  printf 'frontend_decode_smoke=%s\n' "$smoke"
  "$ROOT/scripts/$smoke"
  count=$((count + 1))
done

printf 'frontend_decode_smokes=pass\n'
printf 'frontend_decode_smokes_count=%s\n' "$count"
