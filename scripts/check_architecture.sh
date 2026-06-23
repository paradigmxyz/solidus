#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

fail() {
  printf 'architecture error: %s\n' "$1" >&2
  exit 1
}

if find EvmCompiler/Functions -maxdepth 1 \
    \( -name 'AllocationInteraction*.lean' -o \
       -name 'AllocationObserver*.lean' -o \
       -name 'MixedAllocation.lean' -o \
       -name 'AllocationLowering.lean' -o \
       -name 'AllocationSupport.lean' -o \
       -name 'AllocationContext.lean' \) | grep -q .; then
  fail 'compiler-owned mixed/scratch allocation modules must remain deleted'
fi

for removed in \
  EvmCompiler/Objects/Compiler.lean \
  EvmCompiler/Compiler/AllocatedTypedCfg.lean \
  EvmCompiler/Public/Observer.lean \
  EvmCompiler/Public/ObserverComposition.lean; do
  [[ ! -e "$removed" ]] || fail "obsolete production module returned: $removed"
done

if find EvmCompiler/Yul -maxdepth 1 \
    \( -name 'FunctionsObserver*.lean' -o \
       -name 'AllocationInteractionSafe*.lean' -o \
       -name 'FunctionsAllocationInteractionSafety.lean' -o \
       -name 'FunctionsInteraction*Mode.lean' \) | grep -q .; then
  fail 'observer/scratch-specific Yul compiler corridor must remain deleted'
fi

production_roots=(
  EvmCompiler/Public.lean
  EvmCompiler/BackendCli.lean
  EvmCompiler/Compiler/StackArtifact.lean
  EvmCompiler/Compiler/OpenInteractionComposition.lean
  EvmCompiler/Solidity/Frontend.lean
  EvmCompiler/Solidity/VerifiedStackObjectArtifact.lean
  EvmCompiler/Solidity/Public.lean
  EvmCompiler/Yul/EndToEnd.lean
)

if rg -n 'MixedAllocation|AllocationInteraction|AllocationObserver|AllocationLowering|Objects\.Compiler|Public\.Observer' \
    "${production_roots[@]}"; then
  fail 'production stack-only roots must not reference the archived allocation corridor'
fi

if rg -n 'defaultReservedWords|8193|scratch-reservation|scratch_reservation' \
    "${production_roots[@]}" scripts/solidity_to_yul_lean.py \
    scripts/bridge-json-v3.schema.json; then
  fail 'fixed or user-supplied compiler scratch reservations are forbidden'
fi

rg -q 'some \(\.lit size\)' EvmCompiler/Solidity/Frontend.lean ||
  fail 'memoryguard(size) must resolve to size'
rg -q 'theorem resolveObjectBuiltins_memoryguard' \
  EvmCompiler/Solidity/Frontend.lean ||
  fail 'the frontend must own the checked memoryguard identity theorem'

[[ "$(rg -c '^import ' EvmCompiler/Yul/EndToEnd.lean)" == "1" ]] ||
  fail 'Yul.EndToEnd must remain a short one-import composition module'
rg -q '^import EvmCompiler\.Compiler\.OpenInteractionComposition$' \
  EvmCompiler/Yul/EndToEnd.lean ||
  fail 'Yul.EndToEnd must compose only the adjacent public stack spine'

if rg -ni 'permit2|aave|poolmanager' \
    EvmCompiler/Functions/Stack*.lean \
    EvmCompiler/Compiler/StackArtifact.lean; then
  fail 'stack allocation must not contain contract-specific behavior'
fi

if rg -n '\b(sorry|admit|sorryAx)\b' EvmCompiler --glob '*.lean'; then
  fail 'production Lean tree contains a proof hole'
fi

printf 'architecture dependency check passed\n'
