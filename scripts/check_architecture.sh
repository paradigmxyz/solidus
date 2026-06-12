#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

failed=0

report_matches() {
  local title="$1"
  shift
  local matches
  matches="$(rg -n "$@" 2>/dev/null || true)"
  if [[ -n "$matches" ]]; then
    printf '%s\n%s\n\n' "$title" "$matches" >&2
    failed=1
  fi
}

report_matches \
  'Syntax modules must not import aggregate layer modules:' \
  '^import EvmCompiler\.(Assembly|TypedCfg|Structured|Expressions|Locals|Functions|Objects|Yul|Solidity)$' \
  EvmCompiler -g '*Syntax.lean'

report_matches \
  'Syntax modules must not import compiler or proof modules:' \
  '^import EvmCompiler\..*(Compiler|Preservation|SourceLowering|Semantics)' \
  EvmCompiler -g '*Syntax.lean'

report_matches \
  'Semantic modules must not import compiler or proof modules:' \
  '^import EvmCompiler\..*(Compiler|Preservation|SourceLowering)' \
  EvmCompiler -g '*Semantics.lean'

report_matches \
  'Semantic modules must not import aggregate layer modules:' \
  '^import EvmCompiler\.(Assembly|TypedCfg|Structured|Expressions|Locals|Functions|Objects|Yul|Solidity)$' \
  EvmCompiler -g '*Semantics.lean'

report_matches \
  'The stable root must import only stable API modules:' \
  '^import EvmCompiler\.(Assembly|Structured|Expressions|Locals|Functions|Objects|Yul|Solidity|LayerAudit)$' \
  EvmCompiler.lean

report_matches \
  'Stable public modules must not import verification or retired theorem corridors:' \
  '^import EvmCompiler\.(LayerAudit|Yul\.(NoCallRuntime|OpenLowering|OpenGasAware|OpenRuntime|ObserverOracle))' \
  EvmCompiler.lean EvmCompiler/Public.lean

retired_modules=(
  EvmCompiler/Assembly/GasAware.lean
  EvmCompiler/Structured/Compiler.lean
  EvmCompiler/Structured/TypedContinuations.lean
  EvmCompiler/Structured/TypedCfgBridge.lean
  EvmCompiler/Structured/Preservation.lean
  EvmCompiler/Structured/StackResource.lean
  EvmCompiler/Expressions/Preservation.lean
  EvmCompiler/Locals/Preservation.lean
  EvmCompiler/Locals/SourceLowering.lean
  EvmCompiler/Locals/StackLowering.lean
  EvmCompiler/Functions/SourceDirect.lean
  EvmCompiler/Functions/SourceLowering.lean
  EvmCompiler/Functions/ScratchFrameMemory.lean
  EvmCompiler/Functions/CallDepth.lean
  EvmCompiler/Functions/CallDepthExamples.lean
  EvmCompiler/Functions/CallDepthRanked.lean
  EvmCompiler/Yul/ArgSlots.lean
  EvmCompiler/Yul/PrimSemantics.lean
  EvmCompiler/Yul/OpenExternal.lean
  EvmCompiler/Yul/OpenAssembly.lean
  EvmCompiler/Yul/OpenFuelAdequacy.lean
  EvmCompiler/Yul/OpenGasAware.lean
  EvmCompiler/Yul/OpenStackResource.lean
  EvmCompiler/Functions/CallAwareSpill.lean
  EvmCompiler/Functions/LiveLayout.lean
  EvmCompiler/Functions/LiveLayoutBridge.lean
  EvmCompiler/Functions/LiveLayoutPreservation.lean
  EvmCompiler/Functions/Preservation.lean
  EvmCompiler/Objects/Preservation.lean
  EvmCompiler/Yul/Preservation.lean
  EvmCompiler/Yul/Reference.lean
  EvmCompiler/Yul/RecursiveBridge.lean
  EvmCompiler/Yul/RecursiveBridgeSupport.lean
  EvmCompiler/Yul/NoCallCreate.lean
  EvmCompiler/Yul/NoCallRuntime.lean
  EvmCompiler/Yul/CompilerOpen.lean
  EvmCompiler/Yul/OpenTargetFuel.lean
  EvmCompiler/Yul/OpenLowering.lean
  EvmCompiler/Yul/OpenRuntime.lean
  EvmCompiler/Yul/ObjectPreservation.lean
  EvmCompiler/Yul/ObjectRuntime.lean
  EvmCompiler/Yul/ObserverOracle.lean
  EvmCompiler/Yul/ObserverPreservation.lean
  EvmCompiler/LayerAudit.lean
  EvmCompiler/StackGuardAudit.lean
  EvmCompiler/Legacy.lean
  EvmCompiler/Functions/ScratchFrameSpill.lean
)
for module in "${retired_modules[@]}"; do
  if [[ -e "$module" ]]; then
    printf 'Retired architecture module was restored: %s\n\n' "$module" >&2
    failed=1
  fi
done

report_matches \
  'The verification root must not restore retired architecture imports:' \
  '^import EvmCompiler\.(Legacy|LayerAudit|StackGuardAudit|Functions\.(CallAwareSpill|LiveLayout|LiveLayoutBridge|LiveLayoutPreservation|Preservation)|Objects\.Preservation|Yul\.(Preservation|Reference|RecursiveBridge|RecursiveBridgeSupport|NoCallCreate|NoCallRuntime|CompilerOpen|OpenTargetFuel|OpenLowering|OpenRuntime|ObjectPreservation|ObjectRuntime))' \
  EvmCompiler/Verification.lean

report_matches \
  'The observer specialization must not define another Yul control evaluator:' \
  '^[[:space:]]*def (evalTail|evalArgs|evalValues|eval|call|callDispatcher|execSeq|exec|loop)[[:space:]]' \
  EvmCompiler/Yul/ObserverOracle.lean

report_matches \
  'Observer modules must not define observer-specific compiler implementations:' \
  '^[[:space:]]*(noncomputable[[:space:]]+)?def[[:space:]].*(compile|lower|emit|assemble)[^:]*[:=]' \
  EvmCompiler -g '*Observer*.lean'

report_matches \
  'The Yul observer boundary must target Functions directly, not lower compiler passes:' \
  '^import EvmCompiler\.(Locals|Expressions|Structured|TypedCfg|Assembly\.(Preservation|StackShuffle|StackShufflePreservation)|Public)' \
  EvmCompiler/Yul/FunctionsObserverPreservation.lean

report_matches \
  'The Yul-to-Functions observer proof must not reason directly about lower pass semantics:' \
  '(Locals\.(ObserverSemantics|Source\.Effectful)|TypedCfg\.|Structured\.TypedCfg|Assembly\.(Source|Compiled|Preservation))' \
  EvmCompiler/Yul/FunctionsObserverPreservation.lean

report_matches \
  'Retired vertical observer namespaces must not remain in checked Lean artifacts:' \
  'EvmCompiler\.Yul\.(ObserverOracle|ObserverPreservation)' \
  EvmCompiler proof_artifacts -g '*.lean'

report_matches \
  'The end-to-end theorem must compose public adjacent boundaries, not import lower pass proofs:' \
  '^import EvmCompiler\.(Functions|Locals|Expressions|Structured|TypedCfg|Assembly\.(Preservation|ObserverPreservation|StackShuffle))' \
  EvmCompiler/Yul/EndToEnd.lean

report_matches \
  'The end-to-end theorem must not perform recursive lower-pass execution reasoning:' \
  '(TypedCfg\.|Structured\.TypedCfg|Assembly\.(Source|Compiled|Preservation)|runNResultWithOracle|lowerBodyFrom\?)' \
  EvmCompiler/Yul/EndToEnd.lean

if ! rg -q '^import EvmCompiler\.TypedCfg\.EffectSemantics$' \
    EvmCompiler/TypedCfg/ObserverSemantics.lean ||
    ! rg -q 'EffectSemantics\.Program\.runN' \
      EvmCompiler/TypedCfg/ObserverSemantics.lean; then
  printf '%s\n\n' \
    'TypedCfg observer execution must specialize the shared effect interpreter.' \
    >&2
  failed=1
fi

report_matches \
  'TypedCfg observer semantics must not restore a recursive observer-only control interpreter:' \
  '^[[:space:]]*\|[[:space:]]*(fuel[[:space:]]*\+[[:space:]]*1|instr[[:space:]]*::[[:space:]]*rest)' \
  EvmCompiler/TypedCfg/ObserverSemantics.lean

report_matches \
  'TypedCfg observer preservation must remain owned by the adjacent Assembly boundary:' \
  '^import EvmCompiler\.(Structured|Expressions|Locals|Functions|Objects|Yul|Public)' \
  EvmCompiler/TypedCfg/ObserverPreservation.lean

if ! rg -q '^import EvmCompiler\.Structured\.EffectSemantics$' \
    EvmCompiler/Structured/ObserverSemantics.lean ||
    ! rg -q 'EffectSemantics\.Program\.runState' \
      EvmCompiler/Structured/ObserverSemantics.lean; then
  printf '%s\n\n' \
    'Structured observer execution must specialize the shared effect interpreter.' \
    >&2
  failed=1
fi

report_matches \
  'Structured observer semantics must not restore a recursive observer-only control interpreter:' \
  '^[[:space:]]*\|[[:space:]]*(fuel[[:space:]]*\+[[:space:]]*1|instr[[:space:]]*::[[:space:]]*rest)' \
  EvmCompiler/Structured/ObserverSemantics.lean

report_matches \
  'Structured observer preservation must remain owned by the adjacent TypedCfg boundary:' \
  '^import EvmCompiler\.(Assembly\.(Preservation|ObserverPreservation|StackShuffle|StackShufflePreservation)|Expressions|Locals|Functions|Objects|Yul|Public)' \
  EvmCompiler/Structured/ObserverPreservation.lean

report_matches \
  'Structured observer preservation must not reason through Assembly execution or lower-pass preservation:' \
  '(TypedCfg\.ObserverPreservation|Assembly\.(Source|Compiled|Preservation|ObserverPreservation|StackShufflePreservation))' \
  EvmCompiler/Structured/ObserverPreservation.lean

report_matches \
  'Structured observer adequacy must remain owned by the adjacent TypedCfg boundary:' \
  '^import EvmCompiler\.(Assembly\.(Preservation|ObserverPreservation|StackShuffle|StackShufflePreservation)|Expressions|Locals|Functions|Objects|Yul|Public)' \
  EvmCompiler/Structured/ObserverAdequacy.lean \
  EvmCompiler/Structured/ObserverFirstReaches.lean \
  EvmCompiler/Structured/ObserverSequenceAdequacy.lean \
  EvmCompiler/Structured/ObserverSwitchAdequacy.lean \
  EvmCompiler/Structured/ObserverAdequacyArtifact.lean \
  EvmCompiler/Structured/ObserverFrameInvariant.lean \
  EvmCompiler/Structured/ObserverActivationBoundary.lean \
  EvmCompiler/Structured/ObserverGeneratedBoundary.lean \
  EvmCompiler/Structured/ObserverGeneratedAdequacy.lean \
  EvmCompiler/Structured/ObserverProgramAdequacy.lean \
  EvmCompiler/Structured/ObserverTerminalAdequacy.lean \
  EvmCompiler/Structured/ObserverLoopAdequacy.lean \
  EvmCompiler/Structured/ObserverCallAdequacy.lean

report_matches \
  'Structured observer adequacy must not reason through Assembly execution or lower-pass preservation:' \
  '(TypedCfg\.ObserverPreservation|Assembly\.(Source|Compiled|Preservation|ObserverPreservation|StackShufflePreservation))' \
  EvmCompiler/Structured/ObserverAdequacy.lean \
  EvmCompiler/Structured/ObserverFirstReaches.lean \
  EvmCompiler/Structured/ObserverSequenceAdequacy.lean \
  EvmCompiler/Structured/ObserverSwitchAdequacy.lean \
  EvmCompiler/Structured/ObserverAdequacyArtifact.lean \
  EvmCompiler/Structured/ObserverFrameInvariant.lean \
  EvmCompiler/Structured/ObserverActivationBoundary.lean \
  EvmCompiler/Structured/ObserverGeneratedBoundary.lean \
  EvmCompiler/Structured/ObserverGeneratedAdequacy.lean \
  EvmCompiler/Structured/ObserverProgramAdequacy.lean \
  EvmCompiler/Structured/ObserverTerminalAdequacy.lean \
  EvmCompiler/Structured/ObserverLoopAdequacy.lean \
  EvmCompiler/Structured/ObserverCallAdequacy.lean

report_matches \
  'Structured observer adequacy must invert the shared TypedCfg interpreter, not define an observer-specific target interpreter:' \
  '^[[:space:]]*(private[[:space:]]+)?def[[:space:]]+(runN|step)([^A-Za-z0-9_]|$)' \
  EvmCompiler/Structured/ObserverAdequacy.lean \
  EvmCompiler/Structured/ObserverFirstReaches.lean \
  EvmCompiler/Structured/ObserverSequenceAdequacy.lean \
  EvmCompiler/Structured/ObserverSwitchAdequacy.lean \
  EvmCompiler/Structured/ObserverAdequacyArtifact.lean \
  EvmCompiler/Structured/ObserverFrameInvariant.lean \
  EvmCompiler/Structured/ObserverActivationBoundary.lean \
  EvmCompiler/Structured/ObserverGeneratedBoundary.lean \
  EvmCompiler/Structured/ObserverGeneratedAdequacy.lean \
  EvmCompiler/Structured/ObserverProgramAdequacy.lean \
  EvmCompiler/Structured/ObserverTerminalAdequacy.lean \
  EvmCompiler/Structured/ObserverLoopAdequacy.lean \
  EvmCompiler/Structured/ObserverCallAdequacy.lean

report_matches \
  'Structured recursive observer composition must not restore label-only JumpOr boundaries:' \
  '\bJumpOr\b' \
  EvmCompiler/Structured/ObserverAdequacy.lean \
  EvmCompiler/Structured/ObserverFirstReaches.lean \
  EvmCompiler/Structured/ObserverSequenceAdequacy.lean \
  EvmCompiler/Structured/ObserverSwitchAdequacy.lean \
  EvmCompiler/Structured/ObserverAdequacyArtifact.lean \
  EvmCompiler/Structured/ObserverFrameInvariant.lean \
  EvmCompiler/Structured/ObserverActivationBoundary.lean \
  EvmCompiler/Structured/ObserverGeneratedBoundary.lean \
  EvmCompiler/Structured/ObserverGeneratedAdequacy.lean \
  EvmCompiler/Structured/ObserverProgramAdequacy.lean \
  EvmCompiler/Structured/ObserverTerminalAdequacy.lean \
  EvmCompiler/Structured/ObserverLoopAdequacy.lean \
  EvmCompiler/Structured/ObserverCallAdequacy.lean

report_matches \
  'Structured observer adequacy must derive stack-shape soundness instead of accepting generated evidence:' \
  'h[A-Za-z0-9_]*[[:space:]]*:[[:space:]]*.*ShapeSound' \
  EvmCompiler/Structured/ObserverAdequacy.lean \
  EvmCompiler/Structured/ObserverFirstReaches.lean \
  EvmCompiler/Structured/ObserverSequenceAdequacy.lean \
  EvmCompiler/Structured/ObserverSwitchAdequacy.lean \
  EvmCompiler/Structured/ObserverAdequacyArtifact.lean \
  EvmCompiler/Structured/ObserverFrameInvariant.lean \
  EvmCompiler/Structured/ObserverActivationBoundary.lean \
  EvmCompiler/Structured/ObserverGeneratedBoundary.lean \
  EvmCompiler/Structured/ObserverGeneratedAdequacy.lean \
  EvmCompiler/Structured/ObserverProgramAdequacy.lean \
  EvmCompiler/Structured/ObserverTerminalAdequacy.lean \
  EvmCompiler/Structured/ObserverLoopAdequacy.lean \
  EvmCompiler/Structured/ObserverCallAdequacy.lean

report_matches \
  'Structured observer semantics must not restore an unindexed backward frame-reflection contract:' \
  '(def|inductive)[[:space:]].*FrameReflecting([^A-Za-z]|$)' \
  EvmCompiler/Structured/ObserverSemantics.lean

report_matches \
  'Structured observer adequacy must derive frame reflection from typing instead of accepting it as a premise:' \
  'hFrameReflecting[[:space:]]*:' \
  EvmCompiler/Structured/ObserverAdequacy.lean \
  EvmCompiler/Structured/ObserverFirstReaches.lean \
  EvmCompiler/Structured/ObserverSequenceAdequacy.lean \
  EvmCompiler/Structured/ObserverSwitchAdequacy.lean \
  EvmCompiler/Structured/ObserverAdequacyArtifact.lean \
  EvmCompiler/Structured/ObserverFrameInvariant.lean \
  EvmCompiler/Structured/ObserverActivationBoundary.lean \
  EvmCompiler/Structured/ObserverGeneratedBoundary.lean \
  EvmCompiler/Structured/ObserverGeneratedAdequacy.lean \
  EvmCompiler/Structured/ObserverProgramAdequacy.lean \
  EvmCompiler/Structured/ObserverTerminalAdequacy.lean \
  EvmCompiler/Structured/ObserverLoopAdequacy.lean \
  EvmCompiler/Structured/ObserverCallAdequacy.lean

report_matches \
  'Structured terminal frame safety must remain a proved semantic fact, not a public premise:' \
  'Terminal\.RelSafe|hTerminal[[:space:]]*:[[:space:]]*.*RelSafe' \
  EvmCompiler/Structured/TypedCfgPreservation.lean \
  EvmCompiler/Structured/ObserverPreservation.lean \
  EvmCompiler/PublicVerification.lean

if ! rg -q '^import EvmCompiler\.Functions\.EffectSemantics$' \
    EvmCompiler/Functions.lean ||
    ! rg -q '^namespace Canonical$' \
      EvmCompiler/Functions/EffectSemantics.lean; then
  printf '%s\n\n' \
    'Functions.Source.Effectful must remain the canonical exported parameterized semantics.' \
    >&2
  failed=1
fi

report_matches \
  'The stable Solidity frontend must compile through public artifacts, not legacy preservation corridors:' \
  '^import EvmCompiler\..*Preservation|Objects\.Source\.Program\.compileChecked\?|Functions\.Source\.Program\.compileChecked\?' \
  EvmCompiler/Solidity/Frontend.lean

report_matches \
  'The Objects public compiler must not call legacy backend target emitters:' \
  'Functions\.(CallAwareSpill|ScratchFrameSpill)\..*compile(Target|Executable)' \
  EvmCompiler/Objects/Compiler.lean

if ! rg -q 'Structured\.TypedCfgCompiler\.lowerWithProcEntryShapes\?' \
    EvmCompiler/Objects/Compiler.lean ||
    ! rg -q 'planned\.procEntryShapes\?' \
      EvmCompiler/Objects/Compiler.lean ||
    ! rg -q 'AllocatedTypedCfg\.Program\.ofAllocation' \
      EvmCompiler/Objects/Compiler.lean ||
    ! rg -q 'AllocatedTypedCfg\.Program\.compileCertified\?' \
      EvmCompiler/Objects/Compiler.lean; then
  printf '%s\n\n' \
    'The Objects public compiler must construct and lower through the certified allocation-derived TypedCfg pass.' \
    >&2
  failed=1
fi
report_matches \
  'The Objects public compiler must not bypass the allocated TypedCfg pass through the Expressions convenience compiler:' \
  'Expressions\.Program\.compileTypedArtifact\?' \
  EvmCompiler/Objects/Compiler.lean

report_matches \
  'The Objects public compiler must not call the legacy two-pass scratch-frame emitter:' \
  'ScratchFrameSpill\.compileExpressionsProgram\?' \
  EvmCompiler/Objects/Compiler.lean

planned_program="$(
  sed -n '/^structure PlannedProgram where$/,/^namespace PlannedProgram$/p' \
    EvmCompiler/Objects/Compiler.lean
)"
if rg -q 'expressions[[:space:]]*:[[:space:]]*Expressions\.Program' \
    <<<"$planned_program"; then
  printf '%s\n\n' \
    'The public allocation planner must not carry an already emitted Expressions program.' \
    >&2
  failed=1
fi
if ! rg -q 'source[[:space:]]*:[[:space:]]*Functions\.Program' \
    <<<"$planned_program" ||
    ! rg -q 'allocation[[:space:]]*:[[:space:]]*Locals\.Allocation\.ProgramPlan' \
      <<<"$planned_program"; then
  printf '%s\n\n' \
    'The public planned artifact must carry the Functions source and scoped canonical allocation.' \
    >&2
  failed=1
fi
if ! rg -q 'def lowerExpressions\?' EvmCompiler/Objects/Compiler.lean ||
    ! rg -q 'def allocationLowerer' EvmCompiler/Objects/Compiler.lean ||
    ! rg -q 'def LoweredFrom' EvmCompiler/Objects/Compiler.lean; then
  printf '%s\n\n' \
    'The Objects compiler must expose one allocation-consuming lowerer and its executable certificate relation.' \
    >&2
  failed=1
fi
if ! rg -q 'MixedAllocation\.allScratchPlanner' \
      EvmCompiler/Objects/Compiler.lean ||
    ! rg -q 'AllocationLowering\.allocationLowerer' \
      EvmCompiler/Objects/Compiler.lean; then
  printf '%s\n\n' \
    'The public scratch-frame route must use canonical scoped planning and the shared allocation-driven lowerer.' \
    >&2
  failed=1
fi
report_matches \
  'The canonical allocation lowerer must not restore free-memory-pointer frame allocation:' \
  'freePtrWord|frameBumpCode|frameInitCode|ScratchRegionBase\.freeMemoryPointer' \
  EvmCompiler/Functions/AllocationSupport.lean \
  EvmCompiler/Functions/AllocationLowering.lean
report_matches \
  'Objects inline planning must not restore the hard-coded empty allocation:' \
  'stackOnlyProgramAllocation|stackOnlyAllocation' \
  EvmCompiler/Objects/Compiler.lean
report_matches \
  'The stable Objects compiler must not restore parallel CallAware emitters or planner discovery:' \
  'CallAwareSpill|callAwareSpill|callAwareSwitchSpill|compileCallAwareCandidates' \
  EvmCompiler/Objects/Compiler.lean
report_matches \
  'User-facing bridge diagnostics must not restore retired parallel backends:' \
  'Functions\.(LiveLayout|CallAwareSpill|ScratchFrameSpill)|live_layout_|call_aware_|adaptive_spill|scratch_frame_spill' \
  scripts/solidity_to_yul_lean.py
report_matches \
  'Generated Lean modules must not restore legacy preservation imports or Assembly intermediates:' \
  'Yul\.Preservation|compileSolcChecked|CheckedAssembly' \
  scripts/solidity_to_yul_lean.py
report_matches \
  'Successful public compiler metadata must not make allocation or TypedCfg certificates optional:' \
  '(allocation|typedCfg)\?[[:space:]]*:[[:space:]]*Option' \
  EvmCompiler/Objects/Compiler.lean

report_matches \
  'Stable layer aggregates must not import preservation or legacy runtime corridors:' \
  '^import EvmCompiler\..*(Preservation|StackResource|SourceLowering|SourceDirect|RecursiveBridgeSupport|ObjectRuntime|OpenExternal|OpenAssembly|OpenLowering|ObserverOracle|NoCallCreate|NoCallRuntime)' \
  EvmCompiler/Assembly.lean \
  EvmCompiler/Structured.lean \
  EvmCompiler/Expressions.lean \
  EvmCompiler/Locals.lean \
  EvmCompiler/Functions.lean \
  EvmCompiler/Objects.lean \
  EvmCompiler/Yul.lean

report_matches \
  'The stable compiler spine must not import direct Structured emission or its preservation corridor:' \
  '^import EvmCompiler\.(Structured\.(Compiler|Preservation|TypedContinuations|TypedCfgBridge)|Expressions\.Preservation|Locals\.Preservation)' \
  EvmCompiler/Structured.lean \
  EvmCompiler/Expressions/Compiler.lean \
  EvmCompiler/Locals/Compiler.lean \
  EvmCompiler/Functions/Compiler.lean \
  EvmCompiler/Functions/AllocationSupport.lean \
  EvmCompiler/Functions/MixedAllocation.lean \
  EvmCompiler/Functions/AllocationLowering.lean \
  EvmCompiler/Objects/Compiler.lean \
  EvmCompiler/Public.lean \
  EvmCompiler.lean

report_matches \
  'Migrated architecture modules must not contain proof holes:' \
  '\b(sorry|admit|sorryAx)\b' \
  EvmCompiler/Core \
  EvmCompiler/Compiler \
  EvmCompiler/Public.lean \
  EvmCompiler/Simulation \
  EvmCompiler/Locals/Allocation.lean \
  EvmCompiler/Locals/EffectSemantics.lean \
  EvmCompiler/Yul/EffectSemantics.lean \
  EvmCompiler/TypedCfg \
  EvmCompiler/Structured/TypedCfgCompiler.lean \
  EvmCompiler/Structured/TypedCfgCompilerFreshness.lean \
  EvmCompiler/Structured/TypedCfgCompilerActive.lean \
  EvmCompiler/Structured/TypedCfgCompilerEntry.lean \
  EvmCompiler/Structured/ObserverAdequacy.lean \
  EvmCompiler/Structured/ObserverFirstReaches.lean \
  EvmCompiler/Structured/ObserverSequenceAdequacy.lean \
  EvmCompiler/Structured/ObserverSwitchAdequacy.lean \
  EvmCompiler/Structured/ObserverAdequacyArtifact.lean \
  EvmCompiler/Structured/ObserverFrameInvariant.lean \
  EvmCompiler/Structured/ObserverActivationBoundary.lean \
  EvmCompiler/Structured/ObserverGeneratedBoundary.lean \
  EvmCompiler/Structured/ObserverGeneratedAdequacy.lean \
  EvmCompiler/Structured/ObserverProgramAdequacy.lean \
  EvmCompiler/Structured/ObserverTerminalAdequacy.lean \
  EvmCompiler/Structured/ObserverLoopAdequacy.lean \
  EvmCompiler/Structured/ObserverCallAdequacy.lean

oversized="$(
  find EvmCompiler -type f -name '*.lean' -print0 |
    xargs -0 wc -l |
    awk '$1 > 5000 && $2 != "total" { print $1 " " $2 }' |
    sort -nr
)"
if [[ -n "$oversized" ]]; then
  printf 'Architecture debt: modules above the 5K-line soft limit:\n%s\n\n' \
    "$oversized"
fi

if ((failed != 0)); then
  printf 'architecture dependency check failed\n' >&2
  exit 1
fi

printf 'architecture dependency check passed\n'
