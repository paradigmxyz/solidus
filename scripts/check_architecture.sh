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

require_single_owner() {
  local title="$1"
  local pattern="$2"
  local owner="$3"
  local matches
  local count
  matches="$(rg -n "$pattern" EvmCompiler -g '*.lean' 2>/dev/null || true)"
  count="$(printf '%s\n' "$matches" | sed '/^$/d' | wc -l | tr -d ' ')"
  if [[ "$count" != "1" ]] ||
      ! printf '%s\n' "$matches" | rg -q "^${owner}:"; then
    printf '%s\n%s\n\n' "$title" "$matches" >&2
    failed=1
  fi
}

require_single_owner \
  'OpenWorld must have exactly one shared Simulation owner:' \
  '^structure OpenWorld where$' \
  'EvmCompiler/Simulation/OpenWorld.lean'

require_single_owner \
  'Open-effect Query must have exactly one shared Simulation owner:' \
  '^inductive Query where$' \
  'EvmCompiler/Simulation/Interaction.lean'

require_single_owner \
  'Open-effect Answer must have exactly one shared Simulation owner:' \
  '^def Answer : Query → Type$' \
  'EvmCompiler/Simulation/Interaction.lean'

require_single_owner \
  'Interaction must have exactly one shared Simulation owner:' \
  '^inductive Interaction \(Error' \
  'EvmCompiler/Simulation/Interaction.lean'

require_single_owner \
  'Structured activation matching must have exactly one adjacent-pass owner:' \
  '^def ActivationFrameMatches$' \
  'EvmCompiler/Structured/TypedCfgPreservation/Core.lean'

require_single_owner \
  'Structured compiler label freshness must have exactly one pass owner:' \
  '^def LabelBeforeSupply$' \
  'EvmCompiler/Structured/TypedCfgCompilerFreshness.lean'

require_single_owner \
  'Structured regular-label freshness must have exactly one pass owner:' \
  '^def RegularAtSupply$' \
  'EvmCompiler/Structured/TypedCfgCompilerFreshness.lean'

external_opcodes=(
  call
  callcode
  delegatecall
  staticcall
  create
  create2
)
for opcode in "${external_opcodes[@]}"; do
  if ! rg -q \
      "^#check EvmCompiler\\.Assembly\\.InteractionSemantics\\.PrimOp\\.openStep_${opcode}$" \
      EvmCompiler/Verification.lean; then
    printf 'Verification root is missing Assembly open semantics for %s.\n\n' \
      "$opcode" >&2
    failed=1
  fi
  if ! rg -q \
      "^#check EvmCompiler\\.Assembly\\.TargetInstr\\.ofDecoded\\?_${opcode}$" \
      EvmCompiler/Verification.lean; then
    printf 'Verification root is missing bytecode decoding for %s.\n\n' \
      "$opcode" >&2
    failed=1
  fi
  if ! rg -q \
      "^#check EvmCompiler\\.TypedCfg\\.InteractionPreservation\\.Instr\\.${opcode}_lowerAt_openRunNResult_eq$" \
      EvmCompiler/Verification.lean; then
    printf 'Verification root is missing TypedCfg open preservation for %s.\n\n' \
      "$opcode" >&2
    failed=1
  fi
done

for theorem in \
    lower?_openRunN_rel \
    compileCertified?_entry_openRunN_rel; do
  if ! rg -Fq \
      "#check EvmCompiler.TypedCfg.InteractionPreservation.Program.${theorem}" \
      EvmCompiler/Verification.lean; then
    printf 'Verification root is missing TypedCfg whole-program open preservation theorem %s.\n\n' \
      "$theorem" >&2
    failed=1
  fi
done

if ! rg -Fq \
    '#check EvmCompiler.Structured.InteractionPreservation.Code.openRun_toCfg' \
    EvmCompiler/Verification.lean; then
  printf '%s\n\n' \
    'Verification root is missing Structured straight-line open preservation.' \
    >&2
  failed=1
fi

if ! rg -Fq \
    '#check EvmCompiler.Structured.TypedCfgPreservation.ActivationFrameMatches.of_stateRel' \
    EvmCompiler/Verification.lean; then
  printf '%s\n\n' \
    'Verification root is missing the pass-owned Structured activation-frame theorem.' \
    >&2
  failed=1
fi

for theorem in \
    'OpenOutcome.target_allStopped' \
    'OpenOutcome.PreservesWithin.sequence' \
    'OpenOutcome.PreservesWithin.ignore_tail_of_no_fallthrough' \
    'OpenOutcome.PreservesWithin.pad_stop' \
    'OpenOutcome.PreservesWithin.of_openStep' \
    'Stmt.openStep_code_of_compileStmtFuel?' \
    'Stmt.openRun_code_within_stop_of_compileStmtFuel?' \
    'Stmt.openRun_code_within_resume_of_compileStmtFuel?' \
    'Stmt.openRun_code_of_compileStmtFuel?' \
    'Block.openRun_nil_of_compileStmtListFuel?' \
    'Block.openRun_cons_within_of_compileStmtListFuel?' \
    'Block.openRun_code_cons_within_of_compileStmtListFuel?'; do
  if ! rg -Fq \
      "#check EvmCompiler.Structured.InteractionControlPreservation.${theorem}" \
      EvmCompiler/Verification.lean; then
    printf 'Verification root is missing Structured open control theorem %s.\n\n' \
      "$theorem" >&2
    failed=1
  fi
done

for theorem in \
    'openRunNResultWithStop_add' \
    'openRunNResultWithStop_add_eq_of_allStopped'; do
  if ! rg -Fq \
      "#check EvmCompiler.TypedCfg.InteractionSemantics.Program.${theorem}" \
      EvmCompiler/Verification.lean; then
    printf 'Verification root is missing canonical tagged control theorem %s.\n\n' \
      "$theorem" >&2
    failed=1
  fi
done

report_matches \
  'Open-effect proofs must not restore context bisimulation or per-pass equivalence wrappers:' \
  'ExternalContext\.Rel|OpenEffectEquiv' \
  EvmCompiler -g '*.lean'

report_matches \
  'The shared open-effect foundation must not import compiler layers:' \
  '^import EvmCompiler\.(Assembly|TypedCfg|Structured|Expressions|Locals|Functions|Objects|Yul|Public)' \
  EvmCompiler/Simulation/OpenWorld.lean \
  EvmCompiler/Simulation/Interaction.lean

report_matches \
  'Open-effect specialization modules must not add recursive control evaluators:' \
  '^[[:space:]]*(partial[[:space:]]+)?def[[:space:]]+(run|runN|runList|exec|eval|loop)([^A-Za-z0-9_]|$)' \
  EvmCompiler -g '*InteractionSemantics.lean'

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
  'The allocation observer boundary must stop at allocated Expressions/Structured code:' \
  '^import EvmCompiler\.(TypedCfg|Assembly\.(Preservation|ObserverPreservation|StackShuffle|StackShufflePreservation)|Objects|Yul|Public)' \
  EvmCompiler/Functions/AllocationObserverRelation.lean \
  EvmCompiler/Functions/AllocationObserverSafety.lean \
  EvmCompiler/Functions/AllocationObserverPreservation.lean \
  EvmCompiler/Functions/AllocationObserverContext.lean \
  EvmCompiler/Functions/AllocationObserverExpression.lean \
  EvmCompiler/Functions/AllocationObserverPrimitive.lean \
  EvmCompiler/Functions/AllocationObserverTerminal.lean \
  EvmCompiler/Functions/AllocationObserverStatement.lean \
  EvmCompiler/Functions/AllocationObserverSwitch.lean \
  EvmCompiler/Functions/AllocationObserverLoop.lean \
  EvmCompiler/Functions/AllocationObserverOutcome.lean \
  EvmCompiler/Functions/AllocationObserverForward.lean \
  EvmCompiler/Functions/AllocationObserverDispatcher.lean \
  EvmCompiler/Functions/AllocationObserverCall.lean \
  EvmCompiler/Functions/AllocationObserverRecursive.lean \
  EvmCompiler/Functions/AllocationObserverProgram.lean

report_matches \
  'Canonical guarded Functions semantics must not depend on allocation or lower-pass proof modules:' \
  '^import EvmCompiler\.(Functions\.Allocation|Expressions\.ObserverPreservation|Structured\.(Observer|TypedCfg)|TypedCfg|Assembly\.(Preservation|ObserverPreservation|StackShuffle)|Objects|Yul|Public)' \
  EvmCompiler/Functions/ObserverSafety.lean

report_matches \
  'The recursive Functions observer dispatcher must stay on its adjacent pass boundary:' \
  '^import EvmCompiler\.(TypedCfg|Assembly|Objects|Yul|Public)' \
  EvmCompiler/Functions/AllocationObserverDispatcher.lean \
  EvmCompiler/Functions/AllocationObserverRecursive.lean \
  EvmCompiler/Functions/AllocationObserverProgram.lean

main_forward_signature="$(
  sed -n '/^theorem mainForward/,/ := by$/p' \
    EvmCompiler/Functions/AllocationObserverProgram.lean
)"
if [[ -z "$main_forward_signature" ]]; then
  printf 'Missing public Functions whole-main observer theorem: mainForward\n\n' >&2
  failed=1
else
  main_forward_leaks="$(
    printf '%s\n' "$main_forward_signature" |
      rg -n \
        '(MainArtifact|MainPrepared|MainRoot|AllocationObserverForward\.Compilation|Certificate|Replay|CallOracle|Evidence|bodyCode|cleanupCode)' \
        2>/dev/null || true
  )"
  if [[ -n "$main_forward_leaks" ]]; then
    printf '%s\n%s\n\n' \
      'The public Functions whole-main theorem must not accept generated proof or code evidence:' \
      "$main_forward_leaks" >&2
    failed=1
  fi
  if ! printf '%s\n' "$main_forward_signature" |
      rg -q 'AllocationLowering\.lowerExpressionsFromAllocation\?'; then
    printf '%s\n\n' \
      'The public Functions whole-main theorem must consume the ordinary allocation lowering equation.' \
      >&2
    failed=1
  fi
fi

report_matches \
  'The allocation loop boundary must not publicly expose a whole-loop proof callback:' \
  '^[[:space:]]*theorem[[:space:]]+for_regular_of_components' \
  EvmCompiler/Functions/AllocationObserverLoop.lean

report_matches \
  'The Yul observer boundary must target Functions directly, not lower compiler passes:' \
  '^import EvmCompiler\.(Locals|Expressions|Structured|TypedCfg|Assembly\.(Preservation|StackShuffle|StackShufflePreservation)|Public)' \
  EvmCompiler/Yul/FunctionsObserverCompiler.lean \
  EvmCompiler/Yul/CompilerCallDecomposition.lean \
  EvmCompiler/Yul/CompilerExpressionDecomposition.lean \
  EvmCompiler/Yul/CompilerStatementDecomposition.lean \
  EvmCompiler/Yul/FunctionsObserverExpression.lean \
  EvmCompiler/Yul/FunctionsObserverExpressionBackward.lean \
  EvmCompiler/Yul/FunctionsObserverCallBackward.lean \
  EvmCompiler/Yul/FunctionsObserverListBackward.lean \
  EvmCompiler/Yul/FunctionsObserverCompoundBackward.lean \
  EvmCompiler/Yul/FunctionsObserverStatementBackward.lean \
  EvmCompiler/Yul/FunctionsObserverCallTerminal.lean \
  EvmCompiler/Yul/FunctionsObserverTerminal.lean \
  EvmCompiler/Yul/FunctionsObserverTerminalForward.lean \
  EvmCompiler/Yul/FunctionsObserverTerminalFuel.lean \
  EvmCompiler/Yul/FunctionsObserverCall.lean \
  EvmCompiler/Yul/FunctionsObserverOutcome.lean \
  EvmCompiler/Yul/FunctionsObserverStatement.lean \
  EvmCompiler/Yul/FunctionsObserverExpressionFuel.lean \
  EvmCompiler/Yul/FunctionsObserverForward.lean \
  EvmCompiler/Yul/FunctionsObserverPrimitive.lean \
  EvmCompiler/Yul/FunctionsObserverPrimitive \
  EvmCompiler/Yul/FunctionsObserverPreservation.lean \
  EvmCompiler/Yul/FunctionsObserverTraceAdequacy.lean \
  EvmCompiler/Yul/FunctionsObserverResourceSafety.lean

report_matches \
  'The Yul-to-Functions observer proof must not reason directly about lower pass semantics:' \
  '(Locals\.(ObserverSemantics|Source\.Effectful)|TypedCfg\.|Structured\.TypedCfg|Assembly\.(Source|Compiled|Preservation))' \
  EvmCompiler/Yul/FunctionsObserverCompiler.lean \
  EvmCompiler/Yul/CompilerExpressionDecomposition.lean \
  EvmCompiler/Yul/FunctionsObserverExpressionBackward.lean \
  EvmCompiler/Yul/FunctionsObserverCallBackward.lean \
  EvmCompiler/Yul/FunctionsObserverListBackward.lean \
  EvmCompiler/Yul/FunctionsObserverCompoundBackward.lean \
  EvmCompiler/Yul/FunctionsObserverStatementBackward.lean \
  EvmCompiler/Yul/FunctionsObserverCallTerminal.lean \
  EvmCompiler/Yul/FunctionsObserverTerminal.lean \
  EvmCompiler/Yul/FunctionsObserverTerminalForward.lean \
  EvmCompiler/Yul/FunctionsObserverTerminalFuel.lean \
  EvmCompiler/Yul/FunctionsObserverCall.lean \
  EvmCompiler/Yul/FunctionsObserverOutcome.lean \
  EvmCompiler/Yul/FunctionsObserverStatement.lean \
  EvmCompiler/Yul/FunctionsObserverForward.lean \
  EvmCompiler/Yul/FunctionsObserverPrimitive.lean \
  EvmCompiler/Yul/FunctionsObserverPrimitive \
  EvmCompiler/Yul/FunctionsObserverPreservation.lean \
  EvmCompiler/Yul/FunctionsObserverTraceAdequacy.lean \
  EvmCompiler/Yul/FunctionsObserverResourceSafety.lean

report_matches \
  'The Yul observer boundary must not implement a parallel compiler:' \
  '^[[:space:]]*(noncomputable[[:space:]]+)?def[[:space:]]+(toObjectsWithObservers\?|compileWithObservers\?|toFunctionsListUncheckedFuel\?|toFunDefsUncheckedFuel\?)' \
  EvmCompiler/Yul/FunctionsObserverCompiler.lean \
  EvmCompiler/Yul/CompilerExpressionDecomposition.lean \
  EvmCompiler/Yul/FunctionsObserverExpression.lean \
  EvmCompiler/Yul/FunctionsObserverExpressionBackward.lean \
  EvmCompiler/Yul/FunctionsObserverCallBackward.lean \
  EvmCompiler/Yul/FunctionsObserverListBackward.lean \
  EvmCompiler/Yul/FunctionsObserverCompoundBackward.lean \
  EvmCompiler/Yul/FunctionsObserverStatementBackward.lean \
  EvmCompiler/Yul/FunctionsObserverCallTerminal.lean \
  EvmCompiler/Yul/FunctionsObserverTerminal.lean \
  EvmCompiler/Yul/FunctionsObserverTerminalForward.lean \
  EvmCompiler/Yul/FunctionsObserverTerminalFuel.lean \
  EvmCompiler/Yul/FunctionsObserverCall.lean \
  EvmCompiler/Yul/FunctionsObserverOutcome.lean \
  EvmCompiler/Yul/FunctionsObserverStatement.lean \
  EvmCompiler/Yul/FunctionsObserverForward.lean \
  EvmCompiler/Yul/FunctionsObserverPrimitive.lean \
  EvmCompiler/Yul/FunctionsObserverPrimitive \
  EvmCompiler/Yul/FunctionsObserverPreservation.lean \
  EvmCompiler/Yul/FunctionsObserverTraceAdequacy.lean \
  EvmCompiler/Yul/FunctionsObserverResourceSafety.lean

trace_adequacy_signature="$(
  sed -n '/^theorem compileProgramTraceAdequate/,/ := by$/p' \
    EvmCompiler/Yul/FunctionsObserverTraceAdequacy.lean
)"
if [[ -z "$trace_adequacy_signature" ]]; then
  printf 'Missing narrow Yul-to-Functions trace theorem: compileProgramTraceAdequate\n\n' >&2
  failed=1
else
  trace_adequacy_leaks="$(
    printf '%s\n' "$trace_adequacy_signature" |
      rg -n \
        '(Certificate|CompileArtifact|Allocation|ReplayCertificate|CallOracle|Evidence|TypedCfg|Assembly\.Program)' \
        2>/dev/null || true
  )"
  if [[ -n "$trace_adequacy_leaks" ]]; then
    printf '%s\n%s\n\n' \
      'The narrow Yul trace theorem must not expose generated or lower-pass evidence:' \
      "$trace_adequacy_leaks" >&2
    failed=1
  fi
  if ! printf '%s\n' "$trace_adequacy_signature" |
      rg -q 'SourceExecutionSafe'; then
    printf '%s\n\n' \
      'The narrow Yul trace theorem must expose the source-facing execution-safety premise.' \
      >&2
    failed=1
  fi
  if ! printf '%s\n' "$trace_adequacy_signature" |
      rg -q 'hTargetExhausted'; then
    printf '%s\n\n' \
      'The narrow Yul trace theorem must derive exact replay from target cursor exhaustion.' \
      >&2
    failed=1
  fi
fi

report_matches \
  'Shared Yul observer control relations belong to FunctionsObserverOutcome, not the forward corridor:' \
  '^(def ScopeOptionWithin|structure ControlContextRel|inductive CompoundStmt)' \
  EvmCompiler/Yul/FunctionsObserverForward.lean

report_matches \
  'Yul backward adequacy must consume pass-owned interfaces without importing the forward corridor:' \
  '^import EvmCompiler\.Yul\.FunctionsObserverForward' \
  EvmCompiler/Yul/FunctionsObserverExpressionBackward.lean \
  EvmCompiler/Yul/FunctionsObserverCallBackward.lean \
  EvmCompiler/Yul/FunctionsObserverListBackward.lean \
  EvmCompiler/Yul/FunctionsObserverCompoundBackward.lean \
  EvmCompiler/Yul/FunctionsObserverStatementBackward.lean

report_matches \
  'Yul effect refinement must remain semantic-only and adjacent to canonical Yul semantics:' \
  '^import EvmCompiler\.(Functions|Locals|Expressions|Structured|TypedCfg|Assembly|Objects|Public)' \
  EvmCompiler/Yul/EffectRefinement.lean \
  EvmCompiler/Yul/EffectRefinement

report_matches \
  'Yul effect refinement must not define a compiler or duplicate the canonical control evaluator:' \
  '^[[:space:]]*(noncomputable[[:space:]]+)?def[[:space:]]+(evalTail|evalArgs|evalValues|eval|call|callDispatcher|execSeq|exec|loop|.*compile.*|.*lower.*|.*emit.*|.*assemble.*)[[:space:]:=]' \
  EvmCompiler/Yul/EffectRefinement.lean \
  EvmCompiler/Yul/EffectRefinement

call_dispatcher_refines_signature="$(
  sed -n '/^theorem callDispatcher_refines/,/ :=/p' \
    EvmCompiler/Yul/EffectRefinement/Recursive.lean
)"
if [[ -z "$call_dispatcher_refines_signature" ]]; then
  printf 'Missing public canonical Yul control-refinement theorem: callDispatcher_refines\n\n' >&2
  failed=1
else
  if printf '%s\n' "$call_dispatcher_refines_signature" |
      rg -q '(RefinementAt|Replay|Certificate|Oracle|Evidence)'; then
    printf '%s\n%s\n\n' \
      'The public canonical Yul refinement theorem must construct its recursive proof package internally:' \
      "$call_dispatcher_refines_signature" >&2
    failed=1
  fi
  if ! printf '%s\n' "$call_dispatcher_refines_signature" |
      rg -q 'ObservableRefines'; then
    printf '%s\n\n' \
      'The public canonical Yul refinement theorem must consume the primitive refinement interface.' \
      >&2
    failed=1
  fi
fi

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

report_matches \
  'The public observer composition must not import Yul or bypass pass-owned lower interfaces:' \
  '^import EvmCompiler\.(Yul|Locals|Expressions|Assembly)' \
  EvmCompiler/Public/ObserverComposition.lean

closed_resource_signature="$(
  sed -n '/^def ClosedResourceCorrect/,/^\/--$/p' \
    EvmCompiler/Yul/EndToEnd.lean |
    sed '$d'
)"
if [[ -z "$closed_resource_signature" ]] ||
    ! printf '%s\n' "$closed_resource_signature" |
      rg -q 'SourceExecutionResourceSafe'; then
  printf '%s\n\n' \
    'ClosedResourceCorrect must expose source-facing execution and reservation safety explicitly.' \
    >&2
  failed=1
fi
if printf '%s\n' "$closed_resource_signature" |
    rg -q '(Certificate|LoweredFrom|allocation|generated|Evidence|CallOracle)'; then
  printf '%s\n%s\n\n' \
    'ClosedResourceCorrect must not accept compiler-generated evidence:' \
    "$closed_resource_signature" >&2
    failed=1
fi

if ! rg -q '^theorem closedResourceCorrect : ClosedResourceCorrect := by$' \
    EvmCompiler/Yul/EndToEnd.lean; then
  printf '%s\n\n' \
    'The public observer proposition must have a checked composition theorem.' \
    >&2
  failed=1
fi

closed_artifact_signature="$(
  sed -n '/^structure ClosedArtifact/,/^theorem ClosedArtifact.valid/p' \
    EvmCompiler/Yul/EndToEnd.lean |
    sed '$d'
)"
if [[ -z "$closed_artifact_signature" ]]; then
  printf '%s\n\n' \
    'Missing ClosedArtifact public boundary.' \
    >&2
  failed=1
fi
if printf '%s\n' "$closed_artifact_signature" |
    rg -q 'stackOnly'; then
  printf '%s\n%s\n\n' \
    'ClosedArtifact must not retain the obsolete stack-only restriction:' \
    "$closed_artifact_signature" >&2
  failed=1
fi
if ! rg -q 'Public\.ObserverComposition\.terminalWithResourceSafety' \
    EvmCompiler/Yul/EndToEnd.lean ||
    rg -q 'Public\.ObserverComposition\.terminalStackOnly' \
      EvmCompiler/Yul/EndToEnd.lean; then
  printf '%s\n\n' \
    'EndToEnd must compose compiler-selected resource safety, not the stack-only specialization.' \
    >&2
  failed=1
fi

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

if ! rg -q '^import EvmCompiler\.TypedCfg\.Control$' \
    EvmCompiler/TypedCfg/InteractionSemantics.lean ||
    ! rg -q 'Control\.Block\.runBody' \
      EvmCompiler/TypedCfg/InteractionSemantics.lean ||
    ! rg -q 'Control\.Program\.runN' \
      EvmCompiler/TypedCfg/InteractionSemantics.lean; then
  printf '%s\n\n' \
    'TypedCfg open execution must specialize the shared control interpreter.' \
    >&2
  failed=1
fi

report_matches \
  'TypedCfg open semantics must not define a second recursive control interpreter:' \
  '^[[:space:]]*\|[[:space:]]*(fuel[[:space:]]*\+[[:space:]]*1|instr[[:space:]]*::[[:space:]]*rest)' \
  EvmCompiler/TypedCfg/InteractionSemantics.lean

report_matches \
  'TypedCfg open preservation must remain owned by the adjacent Assembly boundary:' \
  '^import EvmCompiler\.(Structured|Expressions|Locals|Functions|Objects|Yul|Public)' \
  EvmCompiler/TypedCfg/InteractionPreservation.lean

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
  EvmCompiler/Assembly/Syntax.lean \
  EvmCompiler/Assembly/Assembler.lean \
  EvmCompiler/Assembly/InteractionSemantics.lean \
  EvmCompiler/Assembly/InteractionPreservation.lean \
  EvmCompiler/Assembly/InteractionBytecode.lean \
  EvmCompiler/Structured/InteractionSemantics.lean \
  EvmCompiler/Structured/InteractionPreservation.lean \
  EvmCompiler/Structured/InteractionControlPreservation.lean \
  EvmCompiler/Locals/Allocation.lean \
  EvmCompiler/Locals/EffectSemantics.lean \
  EvmCompiler/Functions/AllocationObserverRelation.lean \
  EvmCompiler/Functions/ObserverSafety.lean \
  EvmCompiler/Functions/AllocationObserverSafety.lean \
  EvmCompiler/Functions/AllocationObserverPreservation.lean \
  EvmCompiler/Functions/AllocationObserverContext.lean \
  EvmCompiler/Functions/AllocationObserverExpression.lean \
  EvmCompiler/Functions/AllocationObserverPrimitive.lean \
  EvmCompiler/Functions/AllocationObserverTerminal.lean \
  EvmCompiler/Functions/AllocationObserverStatement.lean \
  EvmCompiler/Functions/AllocationObserverSwitch.lean \
  EvmCompiler/Functions/AllocationObserverLoop.lean \
  EvmCompiler/Functions/AllocationObserverOutcome.lean \
  EvmCompiler/Functions/AllocationObserverForward.lean \
  EvmCompiler/Functions/AllocationObserverDispatcher.lean \
  EvmCompiler/Functions/AllocationObserverCall.lean \
  EvmCompiler/Functions/AllocationObserverRecursive.lean \
  EvmCompiler/Functions/AllocationObserverProgram.lean \
  EvmCompiler/Locals/PrimitivePreservation.lean \
  EvmCompiler/Yul/EffectSemantics.lean \
  EvmCompiler/Yul/EffectRefinement/Failure.lean \
  EvmCompiler/Yul/ObserverSafety.lean \
  EvmCompiler/Yul/FunctionsObserverExpressionBackward.lean \
  EvmCompiler/Yul/FunctionsObserverCallBackward.lean \
  EvmCompiler/Yul/FunctionsObserverListBackward.lean \
  EvmCompiler/Yul/FunctionsObserverCompoundBackward.lean \
  EvmCompiler/Yul/FunctionsObserverStatementBackward.lean \
  EvmCompiler/Yul/FunctionsObserverCallTerminal.lean \
  EvmCompiler/Yul/FunctionsObserverTerminal.lean \
  EvmCompiler/Yul/FunctionsObserverTerminalForward.lean \
  EvmCompiler/Yul/FunctionsObserverTerminalFuel.lean \
  EvmCompiler/Yul/FunctionsObserverCall.lean \
  EvmCompiler/Yul/FunctionsObserverOutcome.lean \
  EvmCompiler/Yul/FunctionsObserverStatement.lean \
  EvmCompiler/Yul/FunctionsObserverForward.lean \
  EvmCompiler/Yul/FunctionsObserverPrimitive.lean \
  EvmCompiler/Yul/FunctionsObserverPrimitive \
  EvmCompiler/Yul/FunctionsObserverPreservation.lean \
  EvmCompiler/Yul/FunctionsObserverTraceAdequacy.lean \
  EvmCompiler/Yul/FunctionsObserverResourceSafety.lean \
  EvmCompiler/Yul/EndToEnd.lean \
  EvmCompiler/Public/ObserverComposition.lean \
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
