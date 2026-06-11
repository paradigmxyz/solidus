#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

layer="${1:-}"
case "$layer" in
  core)
    modules=(
      EvmCompiler.Core.Except
      EvmCompiler.Compiler.Artifact
      EvmCompiler.Simulation.Outcome
    )
    ;;
  effects)
    modules=(
      EvmCompiler.Locals.EffectSemantics
      EvmCompiler.Functions.EffectSemantics
      EvmCompiler.Functions.ObserverSemantics
      EvmCompiler.Yul.EffectSemantics
      EvmCompiler.Yul.ObserverSemantics
    )
    ;;
  allocator)
    modules=(
      EvmCompiler.Locals.Allocation
      EvmCompiler.Functions.AllocationSupport
      EvmCompiler.Functions.MixedAllocation
      EvmCompiler.Functions.AllocationLowering
      EvmCompiler.Objects.Compiler
    )
    ;;
  typedcfg)
    modules=(
      EvmCompiler.TypedCfg
      EvmCompiler.TypedCfg.Preservation
      EvmCompiler.Compiler.AllocatedTypedCfg
      EvmCompiler.Structured.ControlLabels
      EvmCompiler.Structured.TypedCfgCompiler
    )
    ;;
  public)
    modules=(
      EvmCompiler.Objects.Compiler
      EvmCompiler.Yul.Compiler
      EvmCompiler.Public
      EvmCompiler
    )
    ;;
  verification)
    modules=(EvmCompiler.Verification)
    ;;
  frontend)
    modules=(
      EvmCompiler.Solidity.Frontend
      EvmCompiler.Solidity.Public
      EvmCompiler.Solidity.BridgeJson
    )
    ;;
  proofs)
    modules=(
      EvmCompiler.Verification
    )
    ;;
  all)
    modules=()
    ;;
  *)
    printf 'usage: scripts/verify_layer.sh {core|effects|allocator|typedcfg|public|verification|frontend|proofs|all}\n' >&2
    exit 2
    ;;
esac

if [[ "$layer" == "all" ]]; then
  scripts/verify.sh
else
  scripts/verify.sh "${modules[@]}"
fi

if [[ "$layer" == "typedcfg" || "$layer" == "all" ]]; then
  lake env lean proof_artifacts/typedcfg_lowering_invariants_smoke.lean
fi

if [[ "$layer" == "proofs" || "$layer" == "all" ]]; then
  lake env lean proof_artifacts/public_artifact_simulation_smoke.lean
  lake env lean proof_artifacts/resource_observer_oracle_smoke.lean
fi
