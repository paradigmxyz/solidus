#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

failed=0

for theorem in \
    '#check EvmCompiler.Simulation.Interaction.Successful' \
    '#check EvmCompiler.Simulation.Interaction.Successful.bind_inv' \
    '#check EvmCompiler.Simulation.Interaction.Rel.bind_pure_left_inv' \
    '#check EvmCompiler.Simulation.Interaction.ForwardRel.bind_pure_left_inv'; do
  if ! rg -Fq "$theorem" EvmCompiler/Verification.lean; then
    printf 'Verification root is missing shared interaction-safety interface: %s\n\n' \
      "$theorem" >&2
    failed=1
  fi
done

if ! rg -Fq \
    '#check EvmCompiler.Functions.StackRecursivePreservation.compiledListAtOne' \
    EvmCompiler/Verification.lean; then
  printf '%s\n\n' \
    'Verification root is missing compiler-owned recursive stack preservation.' >&2
  failed=1
fi

if ! rg -Fq \
    '#check EvmCompiler.Functions.StackRecursivePreservation.compiledProgramBodyOpenAt' \
    EvmCompiler/Verification.lean; then
  printf '%s\n\n' \
    'Verification root is missing callback-free whole-program stack preservation.' >&2
  failed=1
fi

if ! rg -Fq \
    '#check EvmCompiler.Functions.StackRecursivePreservation.compiledProgramBodyAt' \
    EvmCompiler/Verification.lean; then
  printf '%s\n\n' \
    'Verification root is missing closed whole-program stack preservation.' >&2
  failed=1
fi

if sed -n \
    '/^theorem compiledProgramBodyOpenAt/,/^[[:space:]]*finalCtx.layout.Nodup := by$/p' \
    EvmCompiler/Functions/StackRecursivePreservation.lean | \
    rg -q 'CalleePreservesAt|hCallees|hSchedule|hLowerFunctions|hCompileFunctions'; then
  printf '%s\n\n' \
    'Public stack preservation exposes recursive or compiler-generated evidence.' >&2
  failed=1
fi

if sed -n \
    '/^theorem compiledProgramBodyAt/,/^[[:space:]]*(Expressions.InteractionSemantics.Block.openRun$/p' \
    EvmCompiler/Functions/StackRecursivePreservation.lean | \
    rg -q 'CalleePreservesAt|hCallees|hSchedule|hLowerFunctions|hCompileFunctions'; then
  printf '%s\n\n' \
    'Closed public stack preservation exposes compiler-generated evidence.' >&2
  failed=1
fi

for theorem in \
    'controlListAtZero' \
    'blockPointAt_of_compilers' \
    'blockConsAt_of_compilers' \
    'compiledGrowingRegionAt_of_compilers' \
    'exprConsAt_of_compilers' \
    'letConsAt_of_compilers' \
    'assignConsAt_of_compilers'; do
  if ! rg -Fq \
      "#check EvmCompiler.Functions.StackExactFuelPreservation.${theorem}" \
      EvmCompiler/Verification.lean; then
    printf 'Verification root is missing exact-fuel stack theorem %s.\n\n' \
      "$theorem" >&2
    failed=1
  fi
done

for theorem in \
    'programStride' \
    'proc_body_size_add_length_add_eight_le_programStride' \
    'Covers' \
    'Covers.length_lt' \
    'Covers.weaken_source' \
    'Covers.weaken_target' \
    'Covers.proc_body_after_three' \
    'Covers.head_after_one_append' \
    'Covers.head_of_succ_append' \
    'Covers.tail_after_succ_append' \
    'Covers.if_body_after_two' \
    'Covers.for_init_after_two' \
    'Covers.for_loop_after_two' \
    'Covers.for_post_after_one' \
    'Covers.for_body_after_one' \
    'Covers.for_loop_after_one'; do
  if ! rg -Fq \
      "#check EvmCompiler.Expressions.TargetFuel.${theorem}" \
      EvmCompiler/Verification.lean; then
    printf 'Verification root is missing structural target-fuel interface %s.\n\n' \
      "$theorem" >&2
    failed=1
  fi
done

for theorem in \
    'regularEmpty' \
    'regularCons' \
    'regularConsOfPoint' \
    'regularLeafTargetCost' \
    'RegularListPreserves' \
    'regularConsResult' \
    'RegularLeafList' \
    'regularLeafList_of_compilers' \
    'OpenListPreserves' \
    'ControlScheduledListPreserves' \
    'ControlScheduledListPreservesAt' \
    'controlOrdering' \
    'controlOrderingAt' \
    'controlNil' \
    'controlNilAt' \
    'controlCons' \
    'controlConsAt' \
    'controlOrderedCons' \
    'controlOrderedConsAt' \
    'controlFallthroughCons_of_compilers' \
    'controlFallthroughConsAt_of_compilers' \
    'compiledNonfallPoint_of_compilers' \
    'controlNonfallPointToList' \
    'controlScheduledRegion' \
    'controlScheduledRegionAsBlock' \
    'compiledScheduledRegion_of_compilers' \
    'controlGrowingRegionAsBlock' \
    'controlOpenRegionAsBlock' \
    'compiledOpenRegion_of_compilers' \
    'ControlSwitchBranchPreserves' \
    'ControlSwitchBranchPreserves.toPoint' \
    'SwitchBranchRel' \
    'compiledSwitchBranch_of_compilers' \
    'switchDefaultRel_of_compilers' \
    'switchCasesRel_of_compilers' \
    'switchBranchRelToPreserve' \
    'blockPoint_of_compilers' \
    'ifPoint_of_compilers' \
    'switchPoint_of_compilers' \
    'forPoint_of_compilers' \
    'blockCons_of_compilers' \
    'ifCons_of_compilers' \
    'switchCons_of_compilers' \
    'forCons_of_compilers' \
    'exprCons_of_compilers' \
    'letCons_of_compilers' \
    'assignCons_of_compilers' \
    'callConsAtOne_of_compilers' \
    'callConsAtSucc_of_compilers' \
    'brkControlList_of_compilers' \
    'contControlList_of_compilers' \
    'leaveControlList_of_compilers' \
    'terminalControlList_of_compilers' \
    'terminalArgsControlList_of_compilers' \
    'RegularListPreserves.toOpenList' \
    'terminalList_of_compilers' \
    'terminalArgsList_of_compilers'; do
  if ! rg -Fq \
      "#check EvmCompiler.Functions.StackBlockPreservation.${theorem}" \
      EvmCompiler/Verification.lean; then
    printf 'Verification root is missing dynamic-layout block theorem %s.\n\n' \
      "$theorem" >&2
    failed=1
  fi
done

if ! rg -Fq \
    '#check EvmCompiler.Functions.StackLowering.lowerBlock?_components' \
    EvmCompiler/Verification.lean; then
  printf '%s\n\n' \
    'Verification root is missing checked Functions stack lowering components.' >&2
  failed=1
fi

for theorem in \
    'lowerStmtListFuel_cons_components' \
    'lowerStmtListFuel_cons_fallsThrough_components' \
    'lowerStmtListFuel_cons_nonfallthrough_components' \
    'lowerStmtListFuel_nil_components' \
    'lowerStmtListFuel_expr_components' \
    'lowerStmtListFuel_let_components' \
    'lowerStmtListFuel_assign_components' \
    'lowerStmtListFuel_terminal_components' \
    'lowerStmtListFuel_terminalArgs_components' \
    'lowerPointFuel_expr_components' \
    'lowerPointFuel_let_components' \
    'lowerPointFuel_assign_components' \
    'lowerPointFuel_terminal_components' \
    'lowerPointFuel_terminalArgs_components' \
    'lowerPointFuel_leave_components' \
    'lowerPointFuel_switch_components' \
    'lowerCasesFuel_nil_components' \
    'lowerCasesFuel_cons_components' \
    'lowerCasesFuel_nil_shape' \
    'lowerCasesFuel_cons_shape' \
    'lowerDefaultFuel_none_components' \
    'lowerDefaultFuel_some_components' \
    'lowerDefaultFuel_none_shape' \
    'lowerDefaultFuel_some_shape' \
    'lowerPointFuel_for_components'; do
  if ! rg -Fq \
      "#check EvmCompiler.Functions.StackLowering.${theorem}" \
      EvmCompiler/Verification.lean; then
    printf 'Verification root is missing stack-lowering decomposition %s.\n\n' \
      "$theorem" >&2
    failed=1
  fi
done

if ! rg -Fq \
    '#check EvmCompiler.Functions.StackSchedule.scheduleStmtListFuelWithTargets_cons_fallsThrough_components' \
    EvmCompiler/Verification.lean; then
  printf '%s\n\n' \
    'Verification root is missing checked fallthrough scheduler inversion.' >&2
  failed=1
fi

if ! rg -Fq \
    '#check EvmCompiler.Functions.StackAccessLowering.callSequence_compile_of_check' \
    EvmCompiler/Verification.lean; then
  printf '%s\n\n' \
    'Verification root is missing checked Functions stack-access lowering.' >&2
  failed=1
fi

if ! rg -Fq \
    '#check EvmCompiler.Functions.StackTransitionCompilation.Transition.compiledOpenRun' \
    EvmCompiler/Verification.lean; then
  printf '%s\n\n' \
    'Verification root is missing generated-evidence-free stack transition preservation.' >&2
  failed=1
fi

if ! rg -Fq 'retain? : Option RegularTransition' \
    EvmCompiler/Functions/StackSchedule.lean; then
  printf '%s\n\n' \
    'Regular stack-schedule points must use direct regular transitions.' >&2
  failed=1
fi

if ! rg -Fq 'retain : Transition' \
    EvmCompiler/Functions/AllocationLayout.lean; then
  printf '%s\n\n' \
    'Canonical control joins must retain the canonical transition owner.' >&2
  failed=1
fi

if ! rg -Fq \
    '#check EvmCompiler.Functions.StackTransitionCompilation.RegularTransition.compiledOpenRun' \
    EvmCompiler/Verification.lean; then
  printf '%s\n\n' \
    'Verification root is missing direct regular-transition preservation.' >&2
  failed=1
fi

if ! rg -Fq \
    '#check EvmCompiler.Functions.StackTransitionCompilation.Ordering.compiledOpenRun' \
    EvmCompiler/Verification.lean; then
  printf '%s\n\n' \
    'Verification root is missing generated-evidence-free ordering preservation.' >&2
  failed=1
fi

if ! rg -Fq \
    '#check EvmCompiler.Functions.StackTransitionCompilation.Join.compiledOpenRun' \
    EvmCompiler/Verification.lean; then
  printf '%s\n\n' \
    'Verification root is missing generated-evidence-free canonical join preservation.' >&2
  failed=1
fi

if ! rg -Fq \
    '#check EvmCompiler.Functions.StackTransitionCompilation.Transition.compiledBlockOpenRun' \
    EvmCompiler/Verification.lean; then
  printf '%s\n\n' \
    'Verification root is missing target-block stack transition preservation.' >&2
  failed=1
fi

if ! rg -Fq \
    '#check EvmCompiler.Functions.StackExpressionPreservation.openEvalZero_compileCode' \
    EvmCompiler/Verification.lean; then
  printf '%s\n\n' \
    'Verification root is missing dynamic-layout open expression preservation.' >&2
  failed=1
fi

if ! rg -Fq \
    '#check EvmCompiler.Functions.StackExpressionPreservation.openEvalSeq_compileCode' \
    EvmCompiler/Verification.lean; then
  printf '%s\n\n' \
    'Verification root is missing dynamic-layout open expression-sequence preservation.' >&2
  failed=1
fi

if ! rg -Fq \
    '#check EvmCompiler.Functions.StackExpressionPreservation.openEvalOnePop_compileCode' \
    EvmCompiler/Verification.lean; then
  printf '%s\n\n' \
    'Verification root is missing dynamic-layout one-word pop preservation.' >&2
  failed=1
fi

for theorem in \
    'Block.openRun_terminal_cons' \
    'Block.openRun_terminalArgs_cons' \
    'Stmt.openRunForLoop_succ' \
    'Stmt.openRun_block_eq_scoped_pair'; do
  if ! rg -Fq \
      "#check EvmCompiler.Functions.InteractionSemantics.${theorem}" \
      EvmCompiler/Verification.lean; then
    printf 'Verification root is missing canonical Functions semantic equation %s.\n\n' \
      "$theorem" >&2
    failed=1
  fi
done

if ! rg -Fq \
    '#check EvmCompiler.Expressions.InteractionSemantics.Stmt.openRunForLoop_succ' \
    EvmCompiler/Verification.lean; then
  printf '%s\n\n' \
    'Verification root is missing the Expressions-owned loop equation.' >&2
  failed=1
fi

if ! rg -Fq \
    '#check EvmCompiler.Expressions.InteractionSemantics.Stmt.openRun_for' \
    EvmCompiler/Verification.lean; then
  printf '%s\n\n' \
    'Verification root is missing the Expressions-owned outer for equation.' >&2
  failed=1
fi

for theorem in \
    'OpenResultRel' \
    'openRun_terminal_generated' \
    'compiledTerminalPointOfEquations' \
    'openRun_terminalArgs_generated' \
    'compiledTerminalArgsPointOfEquations' \
    'openRun_expr_generated' \
    'openRun_transition_generated' \
    'openRun_transition_block_generated' \
    'regularThenTransition' \
    'exprThenTransition' \
    'letThenTransition' \
    'assignThenTransition' \
    'RegularPointPreserves.compiledLowered' \
    'compiledExprPoint' \
    'compiledLetPoint' \
    'compiledAssignPoint' \
    'compiledExprPointOfEquations' \
    'compiledLetPointOfEquations' \
    'compiledAssignPointOfEquations' \
    'returnWords_openEval' \
    'returnWords_openSupported' \
    'openRun_leave_returnCode' \
    'openRun_leave_noReturns' \
    'compiledLeaveControlPointOfEquations' \
    'controlThenTransitionForward' \
    'controlAppendEmptyCodeForward' \
    'controlIf' \
    'SwitchBranchesPreserve' \
    'controlSwitch' \
    'ControlScopedOutcomeRel' \
    'ControlBlockPreserves' \
    'ForCoreResultRel' \
    'controlBlockToScoped' \
    'controlBlockToScopedBlock' \
    'controlForLoop' \
    'controlForCore' \
    'controlFor' \
    'RuntimeCtxCovers.withoutLoopControl' \
    'RuntimeCtxCovers.withLoopControl' \
    'RuntimeCtxCovers.afterJoin' \
    'ReturnCtxCovers' \
    'ReturnCtxCovers.afterLayout' \
    'ReturnCtxCovers.ofSameControl' \
    'openRun_let_generated' \
    'openRun_assign_generated'; do
  if ! rg -Fq \
      "#check EvmCompiler.Functions.StackStatementPreservation.${theorem}" \
      EvmCompiler/Verification.lean; then
    printf 'Verification root is missing dynamic-layout statement theorem %s.\n\n' \
      "$theorem" >&2
    failed=1
  fi
done

for theorem in \
    'build_run' \
    'scheduleRetain?_sound' \
    'Transition.build?_sound' \
    'Transition.target_nodup' \
    'Ordering.build?' \
    'Ordering.valid' \
    'Join.build?'; do
  if ! rg -Fq \
      "#check EvmCompiler.Functions.AllocationLayout.${theorem}" \
      EvmCompiler/Verification.lean; then
    printf 'Verification root is missing Functions layout theorem %s.\n\n' \
      "$theorem" >&2
    failed=1
  fi
done

for theorem in \
    'programReports' \
    'NextUse.block'; do
  if ! rg -Fq \
      "#check EvmCompiler.Functions.StackDiagnostics.${theorem}" \
      EvmCompiler/Verification.lean; then
    printf 'Verification root is missing stack diagnostic interface %s.\n\n' \
      "$theorem" >&2
    failed=1
  fi
done

for theorem in \
    'Expr.scoped_of_check' \
    'assign_components'; do
  if ! rg -Fq \
      "#check EvmCompiler.Functions.StackAccess.${theorem}" \
      EvmCompiler/Verification.lean; then
    printf 'Verification root is missing stack-access theorem %s.\n\n' \
      "$theorem" >&2
    failed=1
  fi
done

if ! rg -Fq \
    '#check EvmCompiler.Functions.AllocationLayoutLowering.Schedule.compile' \
    EvmCompiler/Verification.lean; then
  printf '%s\n\n' \
    'Verification root is missing checked Functions layout lowering.' >&2
  failed=1
fi

if ! rg -Fq \
    '#check EvmCompiler.Functions.AllocationLayoutLowering.Ordering.compile' \
    EvmCompiler/Verification.lean; then
  printf '%s\n\n' \
    'Verification root is missing checked next-use ordering lowering.' >&2
  failed=1
fi

if ! rg -Fq \
    '#check EvmCompiler.Functions.AllocationLayoutLowering.Join.compile' \
    EvmCompiler/Verification.lean; then
  printf '%s\n\n' \
    'Verification root is missing checked canonical join lowering.' >&2
  failed=1
fi

for theorem in \
    'loopBaseline' \
    'loopBaseline_suffix' \
    'scheduleBlockFuel_entry_sound' \
    'scheduleBlock?_entry_sound' \
    'scheduleStmtListFuelWithTargets_cons_components' \
    'scheduleStmtListFuel_cons_components' \
    'scheduleStmtListFuel_cons_nonempty' \
    'scheduleStmtListFuel_nil_components' \
    'scheduleStmtListFuel_expr_components' \
    'scheduleStmtListFuel_let_components' \
    'scheduleStmtListFuel_assign_components' \
    'scheduleStmtListFuel_terminal_components' \
    'scheduleStmtListFuel_terminalArgs_components' \
    'scheduleStmtFuel_expr_components' \
    'scheduleStmtFuel_let_components' \
    'scheduleStmtFuel_assign_components' \
    'scheduleStmtFuel_terminal_components' \
    'scheduleStmtFuel_terminalArgs_components' \
    'scheduleStmtFuelWithTargets_brk_components' \
    'scheduleStmtFuelWithTargets_cont_components' \
    'scheduleStmtFuelWithTargets_block_components' \
    'scheduleStmtFuelWithTargets_if_components' \
    'scheduleStmtFuelWithTargets_switch_components' \
    'scheduleCaseRegionsFuelWithTargets_nil_components' \
    'scheduleCaseRegionsFuelWithTargets_cons_components' \
    'scheduleCaseRegionsFuelWithTargets_nil_shape' \
    'scheduleCaseRegionsFuelWithTargets_cons_shape' \
    'scheduleCaseRegionsFuelWithTargets_length' \
    'scheduleDefaultRegionFuelWithTargets_none_components' \
    'scheduleDefaultRegionFuelWithTargets_some_components' \
    'scheduleDefaultRegionFuelWithTargets_none_shape' \
    'scheduleDefaultRegionFuelWithTargets_some_shape' \
    'scheduleStmtFuelWithTargets_for_components' \
    'scheduleBlockFuelWithTargets_components' \
    'scheduleStmtListFuelWithTargets_brk_components' \
    'scheduleStmtListFuelWithTargets_cont_components'; do
  if ! rg -Fq \
      "#check EvmCompiler.Functions.StackSchedule.${theorem}" \
      EvmCompiler/Verification.lean; then
    printf 'Verification root is missing Functions stack scheduler theorem %s.\n\n' \
      "$theorem" >&2
    failed=1
  fi
done

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
  'Open primitive memory safety must have exactly one shared Simulation owner:' \
  '^def OpenPrimitiveMemorySafe \(contract : MemoryContract\.Contract\)$' \
  'EvmCompiler/Simulation/MemorySafety.lean'

require_single_owner \
  'Zero-aware memory windows must have exactly one shared Simulation owner:' \
  '^def WindowSafe \(contract : MemoryContract\.Contract\)$' \
  'EvmCompiler/Simulation/MemorySafety.lean'

require_single_owner \
  'Structured activation matching must have exactly one adjacent-pass owner:' \
  '^def ActivationFrameMatches$' \
  'EvmCompiler/Structured/TypedCfgPreservation/Core.lean'

require_single_owner \
  'Structured activation input classification must have exactly one adjacent-pass owner:' \
  '^def ActivationInput$' \
  'EvmCompiler/Structured/TypedCfgPreservation/GeneratedBoundary.lean'

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

if ! rg -Fq \
    '#check EvmCompiler.Assembly.InteractionPreservation.compile_openRunNResult_target_rel_terminal' \
    EvmCompiler/Verification.lean; then
  printf '%s\n\n' \
    'Verification root is missing uniform terminal Assembly-to-bytecode preservation.' \
    >&2
  failed=1
fi

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

if ! rg -Fq \
    '#check EvmCompiler.Structured.InteractionOwnerPreservation.OpenOutcome.GeneratedProgram.generateWithProcEntryShapes?_main_exec' \
    EvmCompiler/Verification.lean; then
  printf '%s\n\n' \
    'Verification root is missing the checked Structured whole-program open preservation wrapper.' \
    >&2
  failed=1
fi

for theorem in \
    'OpenOutcome.target_allStopped' \
    'OpenOutcome.BoundedExecPreservesUnder.uniform' \
    'OpenOutcome.BoundedExecPreservesUnder.sequence' \
    'OpenOutcome.UniformExecPreservesUnder.preserves' \
    'OpenOutcome.PreservesWithin.sequence' \
    'OpenOutcome.PreservesWithin.ignore_tail_of_no_fallthrough' \
    'OpenOutcome.PreservesWithin.pad_stop' \
    'OpenOutcome.PreservesWithin.change_result_of_required_fallthrough' \
    'OpenOutcome.PreservesWithin.prepend_closed_jump' \
    'OpenOutcome.PreservesWithin.of_openStep' \
    'Stmt.openStep_code_of_compileStmtFuel?' \
    'Stmt.openRun_code_within_stop_of_compileStmtFuel?' \
    'Stmt.openRun_code_within_resume_of_compileStmtFuel?' \
    'Stmt.openRun_code_of_compileStmtFuel?' \
    'Block.openRun_nil_of_compileStmtListFuel?' \
    'Block.openRun_nil_bounded_under_of_compileStmtListFuel?' \
    'Block.openRun_cons_bounded_under_of_compileStmtListFuel?' \
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

if ! rg -Fq \
    '#check EvmCompiler.Structured.InteractionLoopPreservation.Loop.openRunForLoop_bounded_under' \
    EvmCompiler/Verification.lean; then
  printf '%s\n\n' \
    'Verification root is missing the source-budgeted Structured loop theorem.' \
    >&2
  failed=1
fi

for theorem in \
    'EvmCompiler.Structured.InteractionBranchPreservation.Stmt.openRun_if_bounded_under_of_compileStmtFuel?' \
    'EvmCompiler.Structured.InteractionSwitchPreservation.Stmt.openRun_switch_bounded_under_of_compileStmtFuel?' \
    'EvmCompiler.Structured.InteractionLoopPreservation.Loop.Stmt.openRun_for_bounded_under_of_compileStmtFuel?' \
    'EvmCompiler.Structured.InteractionBoundedOwnerPreservation.OpenOutcome.block_owner' \
    'EvmCompiler.Structured.InteractionBoundedOwnerPreservation.OpenOutcome.GeneratedProgram.generateWithProcEntryShapes?_main_uniform' \
    'EvmCompiler.Structured.InteractionBoundedOwnerPreservation.OpenOutcome.GeneratedProgram.generateWithProcEntryShapes?_main_preserves' \
    'EvmCompiler.Structured.InteractionTerminalPreservation.OpenOutcome.PreservesUnder.outcomes' \
    'EvmCompiler.Structured.InteractionTerminalPreservation.OpenOutcome.PreservesUnder.terminal' \
    'EvmCompiler.Structured.InteractionTerminalPreservation.OpenOutcome.GeneratedProgram.generateWithProcEntryShapes?_main_terminal'; do
  if ! rg -Fq "#check ${theorem}" EvmCompiler/Verification.lean; then
    printf 'Verification root is missing bounded Structured theorem %s.\n\n' \
      "$theorem" >&2
    failed=1
  fi
done

for theorem in \
    'Stmt.openStep_brk_of_compileStmtFuel?' \
    'Stmt.openRun_brk_within_of_compileStmtFuel?' \
    'Stmt.openStep_cont_of_compileStmtFuel?' \
    'Stmt.openRun_cont_within_of_compileStmtFuel?' \
    'Stmt.openStep_leave_of_compileStmtFuel?' \
    'Stmt.openRun_leave_within_of_compileStmtFuel?' \
    'Stmt.openStep_terminal_of_compileStmtFuel?' \
    'Stmt.openRun_terminal_within_of_compileStmtFuel?'; do
  if ! rg -Fq \
      "#check EvmCompiler.Structured.InteractionLeafPreservation.${theorem}" \
      EvmCompiler/Verification.lean; then
    printf 'Verification root is missing Structured open leaf theorem %s.\n\n' \
      "$theorem" >&2
    failed=1
  fi
done

for theorem in \
    'Code.openRun_jump_toCfg' \
    'Condition.openRunCondition_jumpi_toCfg' \
    'Condition.openStep_if_of_compileStmtFuel?' \
    'Stmt.openRun_if_within_stop_of_compileStmtFuel?'; do
  if ! rg -Fq \
      "#check EvmCompiler.Structured.InteractionBranchPreservation.${theorem}" \
      EvmCompiler/Verification.lean; then
    printf 'Verification root is missing Structured open branch theorem %s.\n\n' \
      "$theorem" >&2
    failed=1
  fi
done

for theorem in \
    'Switch.openStep_test' \
    'Switch.openStep_pop_jump' \
    'Switch.openRun_default_none_of_compileDefaultFuel?' \
    'Switch.openRun_default_some_of_compileDefaultFuel?' \
    'Switch.openRun_cases_some_of_compileCasesFuel?' \
    'Switch.openRun_cases_none_of_compileCasesFuel?' \
    'Stmt.openRun_switch_within_stop_of_compileStmtFuel?'; do
  if ! rg -Fq \
      "#check EvmCompiler.Structured.InteractionSwitchPreservation.${theorem}" \
      EvmCompiler/Verification.lean; then
    printf 'Verification root is missing Structured open switch theorem %s.\n\n' \
      "$theorem" >&2
    failed=1
  fi
done

for theorem in \
    'openRunNResultWithStop_add' \
    'openRunNResultWithRefinedStop_add' \
    'openRunNResultWithStop_add_eq_map_addFuel_of_allStopped'; do
  if ! rg -Fq \
      "#check EvmCompiler.TypedCfg.InteractionSemantics.Program.${theorem}" \
      EvmCompiler/Verification.lean; then
    printf 'Verification root is missing canonical tagged control theorem %s.\n\n' \
      "$theorem" >&2
    failed=1
  fi
done

canonical_yul_surface="$(
  sed -n '/^namespace Canonical$/,/^end Canonical$/p' \
    EvmCompiler/Yul/EffectSemantics.lean
)"
canonical_yul_code_reads="$(
  printf '%s\n' "$canonical_yul_surface" |
    rg -n 'resolveActiveCode\?|executionEnv\.code' 2>/dev/null || true
)"
if [[ -n "$canonical_yul_code_reads" ]]; then
  printf '%s\n%s\n\n' \
    'Canonical Yul semantics must not read active AST code from mutable account state:' \
    "$canonical_yul_code_reads" >&2
  failed=1
fi
if ! printf '%s\n' "$canonical_yul_surface" |
    rg -Uq 'def run[\s\S]*Effectful\.call model prim fuel \[\] none \(some code\) state'; then
  printf '%s\n\n' \
    'Canonical Yul Program.run must pass its immutable active contract explicitly.' \
    >&2
  failed=1
fi

if ! rg -q '@\[implemented_by lowerFunctionsFast\?\]' \
      EvmCompiler/Functions/AllocationLowering.lean ||
    ! rg -q 'theorem lowerFunctionsFast_eq' \
      EvmCompiler/Functions/AllocationLowering.lean ||
    ! rg -q '@\[implemented_by scopeLayoutsWitnessedFast\?\]' \
      EvmCompiler/Compiler/AllocatedTypedCfg.lean ||
    ! rg -q 'theorem scopeLayoutsWitnessedFast_eq' \
      EvmCompiler/Compiler/AllocatedTypedCfg.lean ||
    ! rg -q '@\[implemented_by findOccurrencesFast\]' \
      EvmCompiler/Solidity/Frontend.lean ||
    ! rg -q 'theorem findOccurrencesFast_eq' \
      EvmCompiler/Solidity/Frontend.lean ||
    ! rg -q '@\[implemented_by toExpressionsFast\?\]' \
      EvmCompiler/Locals/Compiler.lean ||
    ! rg -q 'theorem toExpressionsFast\?_eq' \
      EvmCompiler/Locals/Compiler.lean ||
    ! rg -q '@\[implemented_by prepareFast\]' \
      EvmCompiler/Assembly/Compact.lean ||
    ! rg -q 'theorem prepareFast_eq' \
      EvmCompiler/Assembly/Compact.lean ||
    ! rg -q '@\[implemented_by alignPreparationFast\?\]' \
      EvmCompiler/Assembly/Compact.lean ||
    ! rg -q 'theorem alignPreparationFast_eq' \
      EvmCompiler/Assembly/Compact.lean ||
    ! rg -q '@\[implemented_by emitBlocksFast\?\]' \
      EvmCompiler/Assembly/Compact.lean ||
    ! rg -q 'theorem emitBlocksFast_eq' \
      EvmCompiler/Assembly/Compact.lean ||
    ! rg -q '@\[implemented_by wellFormedFast\?\]' \
      EvmCompiler/Assembly/Compact.lean ||
    ! rg -q 'theorem wellFormedFast\?_eq' \
      EvmCompiler/Assembly/Compact.lean ||
    ! rg -q '@\[implemented_by codeByteLengthFast\]' \
      EvmCompiler/Assembly/Bytecode.lean ||
    ! rg -q 'theorem codeByteLengthFast_eq' \
      EvmCompiler/Assembly/Bytecode.lean ||
    ! rg -q '@\[implemented_by encodeTargetFast\]' \
      EvmCompiler/Assembly/Bytecode.lean ||
    ! rg -q 'theorem encodeTargetFast_eq' \
      EvmCompiler/Assembly/Bytecode.lean; then
  printf '%s\n\n' \
    'Large-contract runtime optimizations must remain proved implementations of their logical specifications.' \
    >&2
  failed=1
fi

if ! rg -Fq 'Functions.StackPressureNormalization.Program.normalize source' \
      EvmCompiler/Compiler/StackArtifact.lean ||
    ! rg -q 'theorem Program\.normalize_openRunState' \
      EvmCompiler/Functions/StackPressureNormalizationProgram.lean ||
    ! rg -Fq 'yulToNormalizedStackStructuredTerminal' \
      EvmCompiler/Compiler/OpenInteractionComposition.lean; then
  printf '%s\n\n' \
    'Functions stack-pressure normalization must remain a checked adjacent pass in the public stack artifact.' \
    >&2
  failed=1
fi

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
  'Functions interaction/observer modules must not add another control kernel:' \
  '^[[:space:]]*(partial[[:space:]]+)?def[[:space:]]+(Block\.runOpen|Block\.runScoped|FunDef\.runBody|Stmt\.runForLoop|Stmt\.run|Program\.runState)([^A-Za-z0-9_]|$)' \
  EvmCompiler/Functions -g '*Interaction*.lean' -g '*Observer*.lean'

for theorem in \
    '#check EvmCompiler.Yul.Source.Effectful.resolveActiveCode?_some' \
    '#check EvmCompiler.Yul.Source.Effectful.call_succ_of_explicit_parts' \
    '#check EvmCompiler.Yul.Source.Canonical.Program.run' \
    '#check EvmCompiler.Yul.InteractionSemantics.primitiveSemantics' \
    '#check EvmCompiler.Yul.InteractionSemantics.Program.openRun'; do
  if ! rg -Fq "$theorem" EvmCompiler/Verification.lean; then
    printf 'Verification root is missing the canonical open-Yul interface: %s\n\n' \
      "$theorem" >&2
    failed=1
  fi
done

report_matches \
  'The canonical Functions allocation relation must not depend on observers:' \
  '^import .*Observer' \
  EvmCompiler/Functions/AllocationInteractionRelation.lean

report_matches \
  'The canonical Functions allocation context must not depend on observers:' \
  '^import .*Observer' \
  EvmCompiler/Functions/AllocationContext.lean

report_matches \
  'The canonical Functions allocation relation must not define a compiler or evaluator:' \
  '^[[:space:]]*(noncomputable[[:space:]]+)?def[[:space:]].*(compile|lower|emit|assemble|run|eval)[^:]*[:=]' \
  EvmCompiler/Functions/AllocationInteractionRelation.lean

report_matches \
  'Canonical Functions allocation interaction proofs must not depend on observer modules:' \
  '^import .*Observer' \
  EvmCompiler/Functions/AllocationInteraction*.lean

report_matches \
  'Canonical Functions allocation interaction proofs must stop at the adjacent Expressions/Structured boundary:' \
  '^import EvmCompiler\.(TypedCfg|Assembly\.(Preservation|ObserverPreservation)|Objects|Yul|Public)' \
  EvmCompiler/Functions/AllocationInteraction*.lean

if ! rg -Fq \
    '#check EvmCompiler.Functions.AllocationInteractionRecursive.SelectedCallee.body_of_cursor' \
    EvmCompiler/Verification.lean; then
  printf '%s\n\n' \
    'Verification root is missing the fuel-decreasing canonical callee-body theorem.' \
    >&2
  failed=1
fi

for theorem in \
    '#check EvmCompiler.Functions.AllocationInteractionControl.block_of_components' \
    '#check EvmCompiler.Functions.AllocationInteractionControl.blockScoped_of_components' \
    '#check EvmCompiler.Functions.AllocationInteractionRecursive.CursorForwardAt.block' \
    '#check EvmCompiler.Functions.AllocationInteractionControl.if_of_components' \
    '#check EvmCompiler.Functions.AllocationInteractionRecursive.CursorForwardAt.if_' \
    '#check EvmCompiler.Functions.AllocationInteractionControl.switch_of_components' \
    '#check EvmCompiler.Functions.AllocationInteractionRecursive.CursorForwardAt.switch' \
    '#check EvmCompiler.Functions.AllocationInteractionLoop.forward' \
    '#check EvmCompiler.Functions.AllocationInteractionFor.forward' \
    '#check EvmCompiler.Functions.AllocationInteractionCursor.CoreCursor.ForComponents' \
    '#check EvmCompiler.Functions.AllocationInteractionCursor.CoreCursor.forComponents' \
    '#check EvmCompiler.Functions.AllocationInteractionRecursive.ForFuelCapacity' \
    '#check EvmCompiler.Functions.AllocationInteractionRecursive.CursorForwardAt.for_' \
    '#check EvmCompiler.Functions.AllocationInteractionRecursive.RecursiveOpenForward' \
    '#check EvmCompiler.Functions.AllocationInteractionRecursive.RecursiveOpenForward.at_targetFuel' \
    '#check EvmCompiler.Functions.AllocationInteractionStatement.ControlScopesWithin.withoutLoopControl' \
    '#check EvmCompiler.Functions.AllocationInteractionStatement.ControlScopesWithin.withLoopControl' \
    '#check EvmCompiler.Functions.AllocationInteractionStatement.ControlScopesWithin.scopeUpdate' \
    '#check EvmCompiler.Functions.AllocationContext.ActivationInvariant.transport_locals' \
    '#check EvmCompiler.Functions.InteractionSemantics.Block.openRunScoped_append' \
    '#check EvmCompiler.Functions.AllocationInteractionPrelude.forward' \
    '#check EvmCompiler.Functions.AllocationInteractionProgram.StackSetupResult.closedBody' \
    '#check EvmCompiler.Functions.AllocationInteractionProgram.ScratchSetupResult.closedBody' \
    '#check EvmCompiler.Functions.AllocationInteractionProgram.mainForward' \
    '#check EvmCompiler.Functions.AllocationInteractionExpressionRecursive.forwardOne'; do
  if ! rg -Fq "$theorem" EvmCompiler/Verification.lean; then
    printf 'Verification root is missing horizontal lexical-control theorem: %s\n\n' \
      "$theorem" >&2
    failed=1
  fi
done

for wrapper in \
    'Block.runOpen' \
    'Block.runScoped' \
    'FunDef.runBody' \
    'Stmt.runForLoop' \
    'Stmt.run'; do
  if ! rg -q \
      "^abbrev ${wrapper//./\\.} " \
      EvmCompiler/Functions/EffectSemantics.lean; then
    printf 'Legacy Functions control API %s must remain a transparent abbreviation.\n\n' \
      "$wrapper" >&2
    failed=1
  fi
done

report_matches \
  'The Locals interaction owner must consume only the adjacent Structured preservation interface:' \
  '^import EvmCompiler\.Assembly\..*Preservation' \
  EvmCompiler/Locals/InteractionPreservation.lean

report_matches \
  'Horizontal open-effect proofs must not depend on observer proof corridors:' \
  '^import .*Observer' \
  EvmCompiler/Assembly/*Interaction*.lean \
  EvmCompiler/TypedCfg/*Interaction*.lean \
  EvmCompiler/Structured/*Interaction*.lean

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
  'Canonical Structured interaction boundaries must not import observer modules:' \
  '^import EvmCompiler\.Structured\.Observer' \
  EvmCompiler/Structured/InteractionBoundaryPreservation.lean \
  EvmCompiler/Structured/TypedCfgPreservation/GeneratedBoundary.lean

report_matches \
  'Observer compatibility boundaries must not re-own canonical activation or CFG-shape relations:' \
  '^[[:space:]]*(inductive[[:space:]]+(ActivationExtension|ActivationAncestor)|def[[:space:]]+LabelShape)' \
  EvmCompiler/Structured/ObserverActivationBoundary.lean \
  EvmCompiler/Structured/ObserverGeneratedBoundary.lean

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
  'The canonical Yul-to-Functions interaction boundary must not import lower pass modules:' \
  '^import EvmCompiler\.(Locals|Expressions|Structured|TypedCfg|Assembly)' \
  EvmCompiler/Yul/FunctionsInteractionRelation.lean \
  EvmCompiler/Yul/FunctionsInteractionFuel.lean \
  EvmCompiler/Yul/FunctionsInteractionStaticCost.lean \
  EvmCompiler/Yul/FunctionsInteractionTargetCost.lean \
  EvmCompiler/Yul/VarStoreRestriction.lean \
  EvmCompiler/Yul/FunctionsInteractionControlRelation.lean \
  EvmCompiler/Yul/FunctionsInteractionPrimitive.lean \
  EvmCompiler/Yul/FunctionsInteractionClosedPrimitive.lean \
  EvmCompiler/Yul/FunctionsInteractionExpression.lean \
  EvmCompiler/Yul/FunctionsInteractionStatement.lean \
  EvmCompiler/Yul/FunctionsInteractionPreparedArgs.lean \
  EvmCompiler/Yul/FunctionsInteractionPreparedCondition.lean \
  EvmCompiler/Yul/FunctionsInteractionLoop.lean \
  EvmCompiler/Yul/FunctionsInteractionPreparedPrimitive.lean \
  EvmCompiler/Yul/FunctionsInteractionPreparedCall.lean \
  EvmCompiler/Yul/FunctionsCompilerArtifact.lean \
  EvmCompiler/Yul/FunctionsInteractionCall.lean \
  EvmCompiler/Yul/FunctionsInteractionSelectedCall.lean \
  EvmCompiler/Yul/FunctionsInteractionRecursiveExpression.lean \
  EvmCompiler/Yul/FunctionsInteractionPreparedStatement.lean \
  EvmCompiler/Yul/FunctionsInteractionSelectedStatementCall.lean \
  EvmCompiler/Yul/FunctionsInteractionRecursiveStatement.lean \
  EvmCompiler/Yul/FunctionsInteractionCompilerCost.lean \
  EvmCompiler/Yul/FunctionsInteractionRecursiveBody.lean \
  EvmCompiler/Yul/FunctionsInteractionProgram.lean

report_matches \
  'Horizontal open-interaction composition must not import observer, replay, or oracle corridors:' \
  '^import EvmCompiler\..*(Observer|Replay|Oracle)' \
  EvmCompiler/Compiler/OpenInteractionComposition.lean

report_matches \
  'Horizontal open-interaction composition must not define compilers or recursive interpreters:' \
  '^[[:space:]]*(partial[[:space:]]+)?def[[:space:]]+.*(compile|lower|emit|assemble|evalTail|evalArgs|evalValues|execSeq|loop)[^:]*[:=]' \
  EvmCompiler/Compiler/OpenInteractionComposition.lean

for theorem in \
    'yulToStackExpressionsTerminal' \
    'stackExpressionsToStructuredTerminal' \
    'yulToStackStructuredTerminal' \
    'yulStackToEncodedBytecode' \
    'stackEncodedToRawBytecode'; do
  if ! rg -Fq \
      "#check EvmCompiler.Compiler.OpenInteractionComposition.${theorem}" \
      EvmCompiler/Verification.lean; then
    printf 'Verification root is missing stack composition theorem %s.\n\n' \
      "$theorem" >&2
    failed=1
  fi
done

for theorem in \
    'compiledVerifiedStackCodeToRawBytecode' \
    'compiledVerifiedStackObjectToRawBytecode'; do
  if ! rg -Fq \
      "#check EvmCompiler.Compiler.OpenInteractionComposition.${theorem}" \
      EvmCompiler/Verification.lean; then
    printf 'Verification root is missing checked stack-artifact theorem %s.\n\n' \
      "$theorem" >&2
    failed=1
  fi
done

if sed -n \
    '/^theorem compiledVerifiedStackCodeToRawBytecode/,/:= by$/p' \
    EvmCompiler/Compiler/OpenInteractionComposition.lean | \
    rg -q 'hWF|hScoped|hSupported|hFrameSafe|Certificate|Schedule|Layout|Evidence|Oracle'; then
  printf '%s\n\n' \
    'Checked stack-artifact theorem exposes compiler-generated semantic evidence.' >&2
  failed=1
fi

if sed -n \
    '/^theorem compiledVerifiedStackObjectToRawBytecode/,/:= by$/p' \
    EvmCompiler/Compiler/OpenInteractionComposition.lean | \
    rg -q 'hWF|hScoped|hSupported|hFrameSafe|Certificate|Schedule|Layout|Evidence|Oracle'; then
  printf '%s\n\n' \
    'Checked recursive stack-object theorem exposes compiler-generated evidence.' >&2
  failed=1
fi

report_matches \
  'Functions open-support checking must remain a semantic-owner check:' \
  '^import EvmCompiler\..*(Compiler|Yul|Solidity|Objects|Observer|Replay|Oracle|TypedCfg|Assembly\.(Assembler|Compiler))' \
  EvmCompiler/Functions/OpenSupportCheck.lean

report_matches \
  'The production stack artifact must not depend on frontend or observer corridors:' \
  '^import EvmCompiler\..*(Yul|Solidity|Objects|Observer|Replay|Oracle)' \
  EvmCompiler/Compiler/StackArtifact.lean

report_matches \
  'The production stack artifact must not define source or target interpreters:' \
  '^[[:space:]]*(partial[[:space:]]+)?def[[:space:]]+.*(eval|exec|run|step|replay)[^:]*[:=]' \
  EvmCompiler/Compiler/StackArtifact.lean

if ! rg -Fq \
    'Functions.SourceAcceptedCheck.Program.sourceAccepted? source' \
    EvmCompiler/Compiler/StackArtifact.lean; then
  printf '%s\n\n' \
    'The production stack artifact must check Functions source acceptance.' >&2
  failed=1
fi

if ! rg -Fq 'evm-compiler-backend stack-diagnostics' \
    scripts/test_full_contract_backend_smoke.sh; then
  printf '%s\n\n' \
    'The exact-contract gate must exercise the verified stack artifact.' >&2
  failed=1
fi

report_matches \
  'The exact-contract stack gate must not inject scratch or enforce deployability:' \
  'scratch-reservation|AAVE_SCRATCH|permit_bytes[[:space:]]*[<>]|aave_bytes[[:space:]]*[<>]|stack_frontend_compact_code_artifact=true' \
  scripts/test_full_contract_backend_smoke.sh

if ! rg -Fq 'finishScopedOrAbrupt ctx bodyCtx body bodyCode' \
      EvmCompiler/Locals/Compiler.lean ||
    ! rg -Fq 'Region.close?' EvmCompiler/Functions/StackSchedule.lean; then
  printf '%s\n\n' \
    'Abrupt-only conditional regions must not require unreachable layout cleanup.' >&2
  failed=1
fi

report_matches \
  'Stack allocation must not contain contract-specific behavior:' \
  'Permit2|Aave|Balancer|Seaport|OpenZeppelin|Compound|Solady|Solmate|Uniswap|TickMath|PoolManager|Morpho|SafeCreate|ENSBytes|AccountAbstraction' \
  EvmCompiler/Functions/AllocationLiveness.lean \
  EvmCompiler/Functions/AllocationLivenessFacts.lean \
  EvmCompiler/Functions/AllocationLayout.lean \
  EvmCompiler/Functions/StackAccess.lean \
  EvmCompiler/Functions/StackSchedule.lean \
  EvmCompiler/Functions/StackLowering.lean \
  EvmCompiler/Functions/StackBlockPreservation.lean \
  EvmCompiler/Functions/StackExactFuelPreservation.lean

report_matches \
  'Functions stack-pressure normalization must not contain contract-specific behavior:' \
  'Permit2|Aave|Balancer|Seaport|OpenZeppelin|Compound|Solady|Solmate|Uniswap|TickMath|PoolManager|Morpho|SafeCreate|ENSBytes|AccountAbstraction' \
  EvmCompiler/Functions/StackPressureNormalization.lean \
  EvmCompiler/Functions/StackPressureNormalizationProgram.lean

report_matches \
  'Verified stack object construction must not reuse legacy allocation artifacts:' \
  'CompiledObjectArtifact|Objects\.Program\.CompileArtifact|Allocation\.ProgramPlan|compileOrderedCodeArtifactIn' \
  EvmCompiler/Solidity/VerifiedStackObjectArtifact.lean

report_matches \
  'Verified stack object construction must not import observer or replay corridors:' \
  '^import EvmCompiler\..*(Observer|Replay|Oracle)' \
  EvmCompiler/Solidity/VerifiedStackObjectArtifact.lean

report_matches \
  'Compact physical layout must remain Assembly-owned:' \
  '^import EvmCompiler\.(Functions|Locals|Expressions|Structured|TypedCfg|Objects|Yul|Solidity|Compiler|Public)' \
  EvmCompiler/Assembly/Compact.lean

report_matches \
  'Compact physical layout must not introduce observer or replay machinery:' \
  '(Observer|Replay|Oracle|CallOracle)' \
  EvmCompiler/Assembly/Compact.lean

report_matches \
  'Concrete-resource/open-external target semantics must remain Assembly-owned:' \
  '^import EvmCompiler\.(Functions|Locals|Expressions|Structured|TypedCfg|Objects|Yul|Public)' \
  EvmCompiler/Assembly/InteractionConcreteResources.lean

report_matches \
  'Concrete-resource/open-external target semantics must not define a compiler:' \
  '^[[:space:]]*(partial[[:space:]]+)?def[[:space:]]+.*(compile|lower|emit|assemble)[^:]*[:=]' \
  EvmCompiler/Assembly/InteractionConcreteResources.lean

if ! rg -q 'InteractionConcreteResources\.openRunNResult' \
      EvmCompiler/Compiler/OpenInteractionComposition.lean ||
    ! rg -q 'CodeImageInstalled' \
      EvmCompiler/Compiler/OpenInteractionComposition.lean; then
  printf '%s\n\n' \
    'Raw object composition must retain concrete resource replay and exact source code-image installation.' \
    >&2
  failed=1
fi

report_matches \
  'The canonical Yul-to-Functions interaction boundary must not define a compiler or recursive evaluator:' \
  '^[[:space:]]*(partial[[:space:]]+)?def[[:space:]]+.*(compile|lower|emit|assemble|evalTail|evalArgs|evalValues|execSeq|loop)[^:]*[:=]' \
  EvmCompiler/Yul/FunctionsInteractionRelation.lean \
  EvmCompiler/Yul/FunctionsInteractionFuel.lean \
  EvmCompiler/Yul/FunctionsInteractionStaticCost.lean \
  EvmCompiler/Yul/FunctionsInteractionTargetCost.lean \
  EvmCompiler/Yul/VarStoreRestriction.lean \
  EvmCompiler/Yul/FunctionsInteractionControlRelation.lean \
  EvmCompiler/Yul/FunctionsInteractionPrimitive.lean \
  EvmCompiler/Yul/FunctionsInteractionClosedPrimitive.lean \
  EvmCompiler/Yul/FunctionsInteractionExpression.lean \
  EvmCompiler/Yul/FunctionsInteractionStatement.lean \
  EvmCompiler/Yul/FunctionsInteractionPreparedArgs.lean \
  EvmCompiler/Yul/FunctionsInteractionPreparedCondition.lean \
  EvmCompiler/Yul/FunctionsInteractionLoop.lean \
  EvmCompiler/Yul/FunctionsInteractionPreparedPrimitive.lean \
  EvmCompiler/Yul/FunctionsInteractionPreparedCall.lean \
  EvmCompiler/Yul/FunctionsCompilerArtifact.lean \
  EvmCompiler/Yul/FunctionsInteractionCall.lean \
  EvmCompiler/Yul/FunctionsInteractionSelectedCall.lean \
  EvmCompiler/Yul/FunctionsInteractionRecursiveExpression.lean \
  EvmCompiler/Yul/FunctionsInteractionPreparedStatement.lean \
  EvmCompiler/Yul/FunctionsInteractionSelectedStatementCall.lean \
  EvmCompiler/Yul/FunctionsInteractionRecursiveStatement.lean \
  EvmCompiler/Yul/FunctionsInteractionCompilerCost.lean \
  EvmCompiler/Yul/FunctionsInteractionRecursiveBody.lean \
  EvmCompiler/Yul/FunctionsInteractionProgram.lean

report_matches \
  'The canonical Yul-to-Functions interaction boundary must not import observer or replay modules:' \
  '^import EvmCompiler\..*(Observer|Replay|Oracle)' \
  EvmCompiler/Yul/FunctionsInteractionRelation.lean \
  EvmCompiler/Yul/FunctionsInteractionFuel.lean \
  EvmCompiler/Yul/FunctionsInteractionStaticCost.lean \
  EvmCompiler/Yul/FunctionsInteractionTargetCost.lean \
  EvmCompiler/Yul/VarStoreRestriction.lean \
  EvmCompiler/Yul/FunctionsInteractionControlRelation.lean \
  EvmCompiler/Yul/FunctionsInteractionPrimitive.lean \
  EvmCompiler/Yul/FunctionsInteractionClosedPrimitive.lean \
  EvmCompiler/Yul/FunctionsInteractionExpression.lean \
  EvmCompiler/Yul/FunctionsInteractionStatement.lean \
  EvmCompiler/Yul/FunctionsInteractionPreparedArgs.lean \
  EvmCompiler/Yul/FunctionsInteractionPreparedCondition.lean \
  EvmCompiler/Yul/FunctionsInteractionLoop.lean \
  EvmCompiler/Yul/FunctionsInteractionPreparedPrimitive.lean \
  EvmCompiler/Yul/FunctionsInteractionPreparedCall.lean \
  EvmCompiler/Yul/FunctionsCompilerArtifact.lean \
  EvmCompiler/Yul/FunctionsInteractionCall.lean \
  EvmCompiler/Yul/FunctionsInteractionSelectedCall.lean \
  EvmCompiler/Yul/FunctionsInteractionRecursiveExpression.lean \
  EvmCompiler/Yul/FunctionsInteractionPreparedStatement.lean \
  EvmCompiler/Yul/FunctionsInteractionSelectedStatementCall.lean \
  EvmCompiler/Yul/FunctionsInteractionRecursiveStatement.lean \
  EvmCompiler/Yul/FunctionsInteractionCompilerCost.lean \
  EvmCompiler/Yul/FunctionsInteractionRecursiveBody.lean \
  EvmCompiler/Yul/FunctionsInteractionProgram.lean

report_matches \
  'The Yul-to-Functions observer proof must not reason directly about lower pass semantics:' \
  '(Locals\.(ObserverSemantics|Source\.Effectful)|TypedCfg\.|Structured\.TypedCfg|Assembly\.(Source|Compiled|Preservation))' \
  EvmCompiler/Yul/FunctionsObserverCompiler.lean \
  EvmCompiler/Yul/FunctionsCompilerArtifact.lean \
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

if rg -q '(OpenWorldTerminalCorrect|openWorldTerminalCorrect)' \
      EvmCompiler/Compiler/OpenInteractionComposition.lean \
      EvmCompiler/Yul/EndToEnd.lean; then
  printf '%s\n\n' \
    'The uninstantiable global-SourceSafety public theorem must not be reintroduced.' \
    >&2
    failed=1
fi
report_matches \
  'The impossible globally quantified SourceSafety interface must not return:' \
  'SourceSafety' \
  EvmCompiler
report_matches \
  'The obsolete contradiction-based recursive allocation runtime must not return:' \
  'AllocationInteractionRecursiveRuntime' \
  EvmCompiler
report_matches \
  'Canonical Yul allocation safety must not depend on observer/replay proof corridors:' \
  '^import EvmCompiler\.Yul\.(Observer|FunctionsObserver)' \
  EvmCompiler/Yul/AllocationInteractionSafeSemantics.lean \
  EvmCompiler/Yul/AllocationInteractionSafeRefinement.lean \
  EvmCompiler/Yul/FunctionsAllocationInteractionSafety.lean \
  EvmCompiler/Yul/FunctionsInteractionMode.lean \
  EvmCompiler/Yul/FunctionsInteractionExpressionMode.lean
if ! sed -n '/^noncomputable def toObjectsWithObservers? (program/,/^[[:space:]]*toObjectsCanonical? program$/p' \
      EvmCompiler/Yul/Compiler.lean |
    rg -q 'toObjectsCanonical\? program'; then
  printf '%s\n\n' \
    'The legacy observer-named Yul lowering must remain a thin alias of the canonical compiler.' \
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
    ! rg -q 'MixedAllocation\.planPressure\?' \
      EvmCompiler/Objects/Compiler.lean ||
    ! rg -q 'def compilePressureFirst\?' \
      EvmCompiler/Objects/Compiler.lean ||
    ! rg -q 'theorem compilePressureFirst\?_loweredFrom' \
      EvmCompiler/Objects/Compiler.lean ||
    ! rg -q 'AllocationLowering\.allocationLowerer' \
      EvmCompiler/Objects/Compiler.lean; then
  printf '%s\n\n' \
    'The public scratch-frame route must use canonical scoped planning and the shared allocation-driven lowerer.' \
    >&2
  failed=1
fi
if ! rg -q 'def pressureStackSlots' \
      EvmCompiler/Functions/MixedAllocation.lean ||
    ! rg -q 'def returnSlots' \
      EvmCompiler/Functions/MixedAllocation.lean ||
    ! rg -q 'theorem planPressure\?_wellFormed' \
      EvmCompiler/Functions/MixedAllocation.lean; then
  printf '%s\n\n' \
    'Pressure candidates must remain allocation-pass owned, exclude procedure returns, and pass canonical plan validation.' \
    >&2
  failed=1
fi
report_matches \
  'The canonical allocation lowerer must not restore free-memory-pointer frame allocation:' \
  'freePtrWord|frameBumpCode|frameInitCode|ScratchRegionBase\.freeMemoryPointer' \
  EvmCompiler/Functions/AllocationSupport.lean \
  EvmCompiler/Functions/AllocationLowering.lean
if ! rg -q 'def decodeMemoryContract' \
      EvmCompiler/Solidity/BridgeJson.lean ||
    rg -q 'defaultReservedWords|ofMemoryGuard\?' \
      EvmCompiler/Solidity/BridgeJson.lean; then
  printf '%s\n\n' \
    'Bridge JSON may decode an explicit source reservation but must not infer or default one.' \
    >&2
  failed=1
fi
if ! rg -q 'structure OrderedProgram' EvmCompiler/Yul/Compiler.lean ||
    ! rg -q 'def toObjects\? \(ordered : OrderedProgram\)' \
      EvmCompiler/Yul/Compiler.lean ||
    ! rg -q 'toSolcYulOrderedProgram\?' \
      EvmCompiler/Solidity/Frontend.lean; then
  printf '%s\n\n' \
    'The executable Solidity path must enter the Yul-owned ordered-program compiler.' \
    >&2
  failed=1
fi
ordered_lowering="$({
  sed -n '/def lowerCodeUnchecked?/,/def lowerCodeUncheckedWithLayout?/p' \
    EvmCompiler/Solidity/Frontend.lean
} || true)"
if printf '%s\n' "$ordered_lowering" |
    rg -q 'simplifyForUnchecked|FunctionPrep|toFunctionsUncheckedFuel|toFunDefsUncheckedFuel'; then
  printf '%s\n\n' \
    'Frontend executable lowering must not duplicate or preprocess the Yul-owned ordered compiler.' \
    >&2
  failed=1
fi
if ! rg -q 'compileVerifiedStackObjectArtifactWithLinkerSymbols\?' \
      EvmCompiler/BackendCli.lean ||
    rg -q 'compileObjectArtifactWithLinkerSymbols\?' \
      EvmCompiler/BackendCli.lean ||
    rg -q 'computedImageUncheckedWithLinkerSymbols\?' \
      EvmCompiler/BackendCli.lean; then
  printf '%s\n\n' \
    'The native object-image backend must select the verified stack object artifact.' \
    >&2
  failed=1
fi
if ! rg -q 'semantic promise, not an' \
      scripts/solidity_to_yul_lean.py ||
    rg -q 'scratch-reservation-(base|words).*default=' \
      scripts/solidity_to_yul_lean.py; then
  printf '%s\n\n' \
    'The CLI scratch reservation must remain an explicit source-facing promise with no default.' \
    >&2
  failed=1
fi
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

if ! rg -q '@\[implemented_by labelsFast\]' \
      EvmCompiler/Assembly/Accepted.lean ||
    ! rg -q 'theorem labelsFast_eq_labels' \
      EvmCompiler/Assembly/Accepted.lean ||
    ! rg -q 'emitFromTableRev\?' \
      EvmCompiler/Assembly/Assembler.lean ||
    ! rg -q 'theorem lookupLabel\?_labelTable_eq_labelPc' \
      EvmCompiler/Assembly/Assembler.lean; then
  printf '%s\n\n' \
    'Large-program Assembly checks must retain proved stack-safe label collection and indexed executable emission.' \
    >&2
  failed=1
fi

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

for theorem in \
    'Close.run_sound' \
    'analyzeBlock?_sound'; do
  if ! rg -Fq \
      "#check EvmCompiler.Functions.AllocationLiveness.${theorem}" \
      EvmCompiler/Verification.lean; then
    printf 'Verification root is missing Functions liveness theorem %s.\n\n' \
      "$theorem" >&2
    failed=1
  fi
done

if ! rg -Fq \
    '#check EvmCompiler.Functions.AllocationLivenessFacts.annotateBlock?_sound' \
    EvmCompiler/Verification.lean; then
  printf '%s\n\n' \
    'Verification root is missing checked Functions liveness facts.' >&2
  failed=1
fi

report_matches \
  'Functions allocation liveness must remain a source-owned analysis:' \
  '^import EvmCompiler\..*(AllocationLowering|MixedAllocation|Objects|Observer|Interaction|EffectSemantics|Structured|TypedCfg|Assembly\.(Assembler|Compiler))' \
  EvmCompiler/Functions/AllocationLiveness.lean

report_matches \
  'Functions liveness facts must remain a source-owned annotation pass:' \
  '^import EvmCompiler\..*(AllocationLowering|MixedAllocation|Objects|Observer|Interaction|EffectSemantics|Structured|TypedCfg|Assembly\.(Assembler|Compiler)|Locals\.Compiler)' \
  EvmCompiler/Functions/AllocationLivenessFacts.lean

report_matches \
  'Functions allocation layout must remain an adjacent symbolic-stack owner:' \
  '^import EvmCompiler\..*(AllocationLowering|MixedAllocation|Objects|Observer|Interaction|EffectSemantics|TypedCfg|Assembly\.(Assembler|Compiler))' \
  EvmCompiler/Functions/AllocationLayout.lean

report_matches \
  'Functions layout lowering may import only its owner and adjacent Locals compiler:' \
  '^import EvmCompiler\..*(AllocationLowering|MixedAllocation|Objects|Observer|Interaction|EffectSemantics|TypedCfg|Assembly\.(Assembler|Compiler))' \
  EvmCompiler/Functions/AllocationLayoutLowering.lean

report_matches \
  'Functions stack scheduling must remain owned by liveness and symbolic layout:' \
  '^import EvmCompiler\..*(AllocationLowering|MixedAllocation|Objects|Observer|StackDiagnostics|Interaction|EffectSemantics|TypedCfg|Assembly\.(Assembler|Compiler)|Locals\.Compiler)' \
  EvmCompiler/Functions/StackSchedule.lean

report_matches \
  'Expressions target-fuel analysis must not depend on Functions allocation corridors:' \
  '^import EvmCompiler\.Functions\.' \
  EvmCompiler/Expressions/TargetFuel.lean

report_matches \
  'Functions stack accessibility must remain a compiler-free symbolic owner:' \
  '^import EvmCompiler\..*(AllocationLowering|MixedAllocation|Objects|Observer|Interaction|EffectSemantics|TypedCfg|Assembly\.(Assembler|Compiler)|Locals\.Compiler)' \
  EvmCompiler/Functions/StackAccess.lean

report_matches \
  'Functions stack-access lowering may import only its owner and adjacent Locals compiler:' \
  '^import EvmCompiler\..*(AllocationLowering|MixedAllocation|Objects|Observer|Interaction|EffectSemantics|TypedCfg|Assembly\.(Assembler|Compiler))' \
  EvmCompiler/Functions/StackAccessLowering.lean

report_matches \
  'Functions dynamic stack relation must remain adjacent to Locals semantics:' \
  '^import EvmCompiler\..*(AllocationLowering|MixedAllocation|Objects|Observer|TypedCfg|Assembly\.(Assembler|Compiler))' \
  EvmCompiler/Functions/StackRelation.lean

report_matches \
  'Functions stack-transition preservation must not import a compiler or observer corridor:' \
  '^import EvmCompiler\..*(AllocationLowering|MixedAllocation|Objects|Observer|TypedCfg|Assembly\.(Assembler|Compiler)|Locals\.Compiler)' \
  EvmCompiler/Functions/StackTransitionPreservation.lean

report_matches \
  'Functions stack-expression preservation must reuse adjacent Locals semantics:' \
  '^import EvmCompiler\..*(AllocationLowering|MixedAllocation|Objects|Observer|TypedCfg|Assembly\.(Assembler|Compiler)|Locals\.Compiler)' \
  EvmCompiler/Functions/StackExpressionPreservation.lean

report_matches \
  'Functions stack-statement preservation must remain an adjacent open-semantics proof:' \
  '^import EvmCompiler\..*(AllocationLowering|MixedAllocation|Objects|Observer|TypedCfg|Assembly\.(Assembler|Compiler)|Locals\.Compiler)' \
  EvmCompiler/Functions/StackStatementPreservation.lean

report_matches \
  'Functions stack-call preservation must remain an adjacent open-semantics proof:' \
  '^import EvmCompiler\..*(AllocationLowering|MixedAllocation|Objects|Observer|TypedCfg|Assembly\.(Assembler|Compiler)|Locals\.Compiler)' \
  EvmCompiler/Functions/StackCallPreservation.lean

report_matches \
  'Functions stack-block preservation must compose only adjacent statement proofs:' \
  '^import EvmCompiler\..*(AllocationLowering|MixedAllocation|Objects|Observer|TypedCfg|Assembly\.(Assembler|Compiler)|Locals\.Compiler)' \
  EvmCompiler/Functions/StackBlockPreservation.lean

report_matches \
  'Functions recursive stack preservation must remain inside the adjacent allocation boundary:' \
  '^import EvmCompiler\..*(AllocationLowering|MixedAllocation|Objects|Observer|TypedCfg|Assembly\.(Assembler|Compiler)|Locals\.Compiler|Yul)' \
  EvmCompiler/Functions/StackRecursivePreservation.lean

report_matches \
  'Dynamic Functions preservation must use canonical Functions source semantics:' \
  'CtxCovers \(source : Locals\.Source\.Ctx\)|sourceProgram : Locals\.Program|Locals\.InteractionSemantics\.(Stmt|Block)\.openRun' \
  EvmCompiler/Functions/StackStatementPreservation.lean \
  EvmCompiler/Functions/StackCallPreservation.lean \
  EvmCompiler/Functions/StackBlockPreservation.lean \
  EvmCompiler/Functions/StackExactFuelPreservation.lean \
  EvmCompiler/Functions/StackRecursivePreservation.lean

report_matches \
  'Functions stack-transition compilation must remain an adjacent compiler bridge:' \
  '^import EvmCompiler\..*(AllocationLowering|MixedAllocation|Objects|Observer|TypedCfg|Assembly\.(Assembler|Compiler))' \
  EvmCompiler/Functions/StackTransitionCompilation.lean

report_matches \
  'Functions stack lowering must remain a syntax-only adjacent pass:' \
  '^import EvmCompiler\..*(AllocationLowering|MixedAllocation|Objects|Observer|Interaction|EffectSemantics|TypedCfg|Assembly\.(Assembler|Compiler)|Locals\.Compiler)' \
  EvmCompiler/Functions/StackLowering.lean

report_matches \
  'Functions stack compilation bridge must use only the adjacent Locals compiler:' \
  '^import EvmCompiler\..*(AllocationLowering|MixedAllocation|Objects|Observer|Interaction|EffectSemantics|TypedCfg|Assembly\.(Assembler|Compiler))' \
  EvmCompiler/Functions/StackLoweringCompilation.lean

report_matches \
  'Functions stack diagnostics must remain read-only and allocator-local:' \
  '^import EvmCompiler\..*(AllocationLowering|MixedAllocation|Objects|Observer|Interaction|EffectSemantics|TypedCfg|Assembly\.(Assembler|Compiler)|Locals\.Compiler)' \
  EvmCompiler/Functions/StackDiagnostics.lean

report_matches \
  'Canonical Expressions semantics must interpret Expressions syntax directly, not compile through Structured:' \
  '\b(toStructured|compile)\b' \
  EvmCompiler/Expressions/EffectSemantics.lean \
  EvmCompiler/Expressions/InteractionSemantics.lean

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
  EvmCompiler/Assembly/InteractionConcreteResources.lean \
  EvmCompiler/Structured/InteractionSemantics.lean \
  EvmCompiler/Structured/InteractionPrimitivePreservation.lean \
  EvmCompiler/Structured/InteractionPreservation.lean \
  EvmCompiler/Structured/InteractionStaticCost.lean \
  EvmCompiler/Structured/InteractionControlPreservation.lean \
  EvmCompiler/Structured/InteractionBoundedBlockPreservation.lean \
  EvmCompiler/Structured/InteractionLeafPreservation.lean \
  EvmCompiler/Structured/InteractionBranchPreservation.lean \
  EvmCompiler/Structured/InteractionBoundedBranchPreservation.lean \
  EvmCompiler/Structured/InteractionSwitchPreservation.lean \
  EvmCompiler/Structured/InteractionBoundedSwitchPreservation.lean \
  EvmCompiler/Structured/InteractionLoopPreservation.lean \
  EvmCompiler/Structured/InteractionBoundedLoopPreservation.lean \
  EvmCompiler/Structured/InteractionCallPreservation.lean \
  EvmCompiler/Structured/InteractionBoundedOwnerPreservation.lean \
  EvmCompiler/Structured/InteractionTerminalPreservation.lean \
  EvmCompiler/Expressions/EffectSemantics.lean \
  EvmCompiler/Expressions/InteractionSemantics.lean \
  EvmCompiler/Expressions/InteractionPreservation.lean \
  EvmCompiler/Locals/Allocation.lean \
  EvmCompiler/Locals/EffectSemantics.lean \
  EvmCompiler/Locals/InteractionSemantics.lean \
  EvmCompiler/Locals/InteractionStatePreservation.lean \
  EvmCompiler/Locals/InteractionPreservation.lean \
  EvmCompiler/Functions/AllocationInteraction*.lean \
  EvmCompiler/Functions/AllocationLiveness.lean \
  EvmCompiler/Functions/AllocationLivenessFacts.lean \
  EvmCompiler/Functions/AllocationLayout.lean \
  EvmCompiler/Functions/AllocationLayoutLowering.lean \
  EvmCompiler/Functions/StackSchedule.lean \
  EvmCompiler/Functions/StackAccess.lean \
  EvmCompiler/Functions/StackAccessLowering.lean \
  EvmCompiler/Functions/StackRelation.lean \
  EvmCompiler/Functions/StackExpressionPreservation.lean \
  EvmCompiler/Functions/StackStatementPreservation.lean \
  EvmCompiler/Functions/StackCallPreservation.lean \
  EvmCompiler/Functions/StackBlockPreservation.lean \
  EvmCompiler/Functions/StackExactFuelPreservation.lean \
  EvmCompiler/Functions/StackRecursivePreservation.lean \
  EvmCompiler/Functions/StackTransitionPreservation.lean \
  EvmCompiler/Functions/StackTransitionCompilation.lean \
  EvmCompiler/Functions/StackLowering.lean \
  EvmCompiler/Functions/StackLoweringCompilation.lean \
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
  EvmCompiler/Yul/VarStoreRestriction.lean \
  EvmCompiler/Yul/FunctionsInteraction*.lean \
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
