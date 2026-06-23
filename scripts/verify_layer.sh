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
      EvmCompiler.Functions.AllocationLiveness
      EvmCompiler.Functions.AllocationLayout
      EvmCompiler.Functions.StackSchedule
      EvmCompiler.Functions.StackLowering
      EvmCompiler.Functions.StackRecursivePreservation
      EvmCompiler.Compiler.StackArtifact
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
      EvmCompiler.Public
      EvmCompiler.Compiler.OpenInteractionComposition
      EvmCompiler.Solidity.Public
      EvmCompiler.Yul.EndToEnd
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
  lake env lean proof_artifacts/stack_backend_production_smoke.lean
fi
