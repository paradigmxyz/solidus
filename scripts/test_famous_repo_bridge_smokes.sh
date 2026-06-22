#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

SMOKES=(
  test_uniswap_v4_extload_summary_smoke.sh
  test_uniswap_v4_bridge_smoke.sh
  test_uniswap_v4_position_bridge_smoke.sh
  test_uniswap_universal_router_smoke.sh
  test_uniswap_permit2_bridge_smoke.sh
  test_aave_v3_bridge_smoke.sh
  test_compound_comet_bridge_smoke.sh
  test_solmate_bridge_smoke.sh
  test_solady_bridge_smoke.sh
  test_openzeppelin_bridge_smoke.sh
  test_chainlink_cbor_bridge_smoke.sh
  test_additional_real_contracts_bridge_smoke.sh
  test_protocol_diversity_bridge_smoke.sh
)

printf 'famous_repo_bridge_smokes_start=%s\n' "${#SMOKES[@]}"
for smoke in "${SMOKES[@]}"; do
  printf 'famous_repo_bridge_smoke=%s\n' "$smoke"
  "$ROOT/scripts/$smoke"
done
printf 'famous_repo_bridge_smokes=pass\n'
printf 'famous_repo_bridge_smokes_count=%s\n' "${#SMOKES[@]}"
