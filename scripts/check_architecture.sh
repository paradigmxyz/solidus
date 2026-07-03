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
  EvmCompiler/Compiler/MemoryRelation.lean \
  EvmCompiler/Functions/ObserverSafety.lean \
  EvmCompiler/Locals/Allocation.lean \
  EvmCompiler/Public/Observer.lean \
  EvmCompiler/Public/ObserverComposition.lean \
  EvmCompiler/Public.lean \
  EvmCompiler/Simulation/MemorySafety.lean \
  EvmCompiler/Yul/ObjectModel.lean \
  EvmCompiler/Yul/ObjectSemantics.lean \
  EvmCompiler/Yul/ObserverSafety.lean; do
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
  EvmCompiler/Solidity/RawAstPublic.lean
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

if rg -n 'ScratchReservation|allocatorCell|ofMemoryGuard\?' EvmCompiler; then
  fail 'compiler scratch reservation machinery must remain deleted'
fi

if rg -n 'bindScratch' EvmCompiler/Functions EvmCompiler/Locals \
    EvmCompiler/Expressions EvmCompiler/Yul EvmCompiler/Solidity \
    EvmCompiler/Compiler/StackArtifact.lean; then
  fail 'the production upper pipeline must not emit lower-IR scratch operations'
fi

rg -q 'some \(\.lit size\)' EvmCompiler/Solidity/Frontend.lean ||
  fail 'memoryguard(size) must resolve to size'
rg -q 'theorem resolveObjectBuiltins_memoryguard' \
  EvmCompiler/Solidity/Frontend.lean ||
  fail 'the frontend must own the checked memoryguard identity theorem'

if rg -n 'defaultDialectProfile' \
    EvmCompiler/Solidity/Frontend.lean \
    EvmCompiler/Compiler/OpenInteractionComposition.lean; then
  fail 'production frontend composition must validate the declared EVM fork'
fi
rg -q 'evmVersion : Yul\.SolcValidation\.EvmVersion' \
  EvmCompiler/Solidity/Frontend.lean ||
  fail 'frontend objects must retain their declared EVM fork'
rg -q 'codeArtifact\.resolved\.dialectProfile' \
  EvmCompiler/Compiler/OpenInteractionComposition.lean ||
  fail 'public composition must use the resolved object fork profile'
rg -q '^theorem toSolcYulOrderedProgram\?_forkSpellingOk' \
  EvmCompiler/Solidity/Frontend.lean ||
  fail 'checked frontend conversion must derive raw fork-spelling validity'
rg -q 'object\.forkSpellingOk?' EvmCompiler/Solidity/Frontend.lean ||
  fail 'frontend conversion must validate difficulty/prevrandao before erasure'
rg -q '"required": \["schema", "source", "contract", "frontend", "selectedObject"\]' \
  scripts/bridge-json-v3.schema.json ||
  fail 'bridge JSON must require explicit frontend/fork metadata'

[[ "$(rg -c '^import ' EvmCompiler/Yul/EndToEnd.lean)" == "1" ]] ||
  fail 'Yul.EndToEnd must remain a short one-import composition module'
rg -q '^import EvmCompiler\.Compiler\.OpenInteractionComposition$' \
  EvmCompiler/Yul/EndToEnd.lean ||
  fail 'Yul.EndToEnd must compose only the adjacent public stack spine'
if rg -n 'GeneratedContext|YulStackCompactDoneRel' \
    EvmCompiler/Yul/EndToEnd.lean; then
  fail 'Yul.EndToEnd must not expose lower-pass generated evidence'
fi
rg -q 'VerifiedStackObjectDoneRel' EvmCompiler/Yul/EndToEnd.lean ||
  fail 'Yul.EndToEnd must use the artifact-level public outcome relation'
rg -q 'VerifiedStackObjectPrefixDoneRel' EvmCompiler/Yul/EndToEnd.lean ||
  fail 'Yul.EndToEnd must use the artifact-level finite-prefix relation'

public_forward_theorem="$(sed -n \
  '/^theorem optimizedSolcYulToRawBytecode$/,/^theorem optimizedSolcYulToRawBytecodeFinished$/p' \
  EvmCompiler/Yul/EndToEnd.lean)"
[[ "$public_forward_theorem" == *"(hObject :"* ]] ||
  fail 'the canonical forward theorem must be driven by checked compilation'
[[ "$public_forward_theorem" == *"Simulation.Interaction.ForwardRel"* ]] ||
  fail 'the canonical theorem must expose unconditional finite-prefix preservation'
[[ "$public_forward_theorem" == *"VerifiedStackObjectPrefixDoneRel"* ]] ||
  fail 'the canonical theorem must hide generated context behind the artifact prefix relation'
if printf '%s\n' "$public_forward_theorem" | rg -n \
    'hFinished|hTerminal|hYulInitial|hYulDomain|hStackInitial|ExecutionSafe|SourceSafety|Scratch|GeneratedContext|certificate|oracle|replay'; then
  fail 'the canonical forward theorem regained a completion, derived, generated, or replay premise'
fi

public_finished_theorem="$(sed -n \
  '/^theorem optimizedSolcYulToRawBytecodeFinished$/,/^end EndToEnd$/p' \
  EvmCompiler/Yul/EndToEnd.lean)"
[[ "$public_finished_theorem" == *"(hObject :"* ]] ||
  fail 'the canonical all-finished theorem must be driven by checked compilation'
[[ "$public_finished_theorem" == *"(hFinished :"* ]] ||
  fail 'the canonical all-finished theorem must state its actual source-run condition'
if printf '%s\n' "$public_finished_theorem" | rg -n \
    'hYulInitial|hYulDomain|hStackInitial|ExecutionSafe|SourceSafety|Scratch|GeneratedContext|certificate|oracle'; then
  fail 'the canonical all-finished theorem regained a derived or generated premise'
fi

if rg -ni 'permit2|aave|poolmanager' \
    EvmCompiler/Functions/Stack*.lean \
    EvmCompiler/Compiler/StackArtifact.lean; then
  fail 'stack allocation must not contain contract-specific behavior'
fi

if rg -n 'FunctionsInteractionExpression\.(compilerDirectAt|directAt)' \
    EvmCompiler/Yul/FunctionsInteractionPrepared*.lean \
    EvmCompiler/Yul/FunctionsInteractionRecursive*.lean \
    EvmCompiler/Yul/FunctionsInteractionSelected*.lean \
    EvmCompiler/Yul/FunctionsInteractionProgram.lean; then
  fail 'validated Yul preservation must retain scoped variable-definedness'
fi

if ! rg -q '^theorem truncated_iff_outOfFuel' \
    EvmCompiler/Yul/FunctionsInteractionPrimitive.lean; then
  fail 'public Yul truncation must remain exactly structural source OutOfFuel'
fi

if rg -n '\b(sorry|admit|sorryAx)\b' EvmCompiler --glob '*.lean'; then
  fail 'production Lean tree contains a proof hole'
fi

# Orphaned oleans (build artifacts whose source module was deleted) silently
# resolve deleted API for generated code on this machine while fresh clones
# fail; refuse to let them accumulate after refactors.
if [ -d .lake/build/lib/lean/EvmCompiler ]; then
  orphaned_oleans="$(find .lake/build/lib/lean/EvmCompiler -name '*.olean' | \
    while read -r olean; do
      rel="${olean#.lake/build/lib/lean/}"
      [ -f "${rel%.olean}.lean" ] || printf '%s\n' "$rel"
    done)"
  if [ -n "$orphaned_oleans" ]; then
    printf '%s\n' "$orphaned_oleans" >&2
    fail 'orphaned oleans without source modules; delete them (see PROGRESS_LOG tooling/orphan-olean-purge)'
  fi
fi

printf 'architecture dependency check passed\n'
