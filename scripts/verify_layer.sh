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
    modules=(EvmCompiler.Locals.EffectSemantics EvmCompiler.Yul.ObserverOracle)
    ;;
  allocator)
    modules=(
      EvmCompiler.Locals.Allocation
      EvmCompiler.Functions.CallAwareSpill
      EvmCompiler.Functions.ScratchFrameSpill
      EvmCompiler.Objects.Compiler
    )
    ;;
  typedcfg)
    modules=(
      EvmCompiler.TypedCfg
      EvmCompiler.Compiler.AllocatedTypedCfg
      EvmCompiler.Structured.TypedCfgBridge
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
  legacy)
    modules=(EvmCompiler.Legacy)
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
      EvmCompiler.Functions.CallAwareSpill
      EvmCompiler.Yul.ObserverOracle
      EvmCompiler.Legacy
    )
    ;;
  all)
    modules=()
    ;;
  *)
    printf 'usage: scripts/verify_layer.sh {core|effects|allocator|typedcfg|public|legacy|frontend|proofs|all}\n' >&2
    exit 2
    ;;
esac

if [[ "$layer" == "all" ]]; then
  scripts/verify.sh
else
  scripts/verify.sh "${modules[@]}"
fi
