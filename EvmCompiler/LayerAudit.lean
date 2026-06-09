import EvmCompiler.Yul.NoCallRuntime
import EvmCompiler.Yul.OpenLowering
import EvmCompiler.Yul.OpenGasAware
import EvmCompiler.Yul.OpenRuntime
import EvmCompiler.Yul.ObserverOracle
import EvmCompiler.Functions.LiveLayout
import EvmCompiler.Functions.LiveLayoutBridge
import EvmCompiler.Functions.LiveLayoutPreservation

/-!
Current public theorem spine.

This module intentionally exposes only the preferred public imported-Yul to
gas-aware EVM theorem roots. Solidity and object/Yul-object interfaces live in
their own modules; this audit file should not keep stale theorem routes alive.
-/

namespace EvmCompiler
namespace LayerAudit

abbrev sourceStateRelOpenExternalPrimitiveCallSiteEqOfArgs :=
  @Yul.Reference.SourceBridgeFacts.SourceStateRel.openExternalPrimitiveCallSite_eq_of_args

abbrev sourceStateRelOpenExternalPrimitiveCreateSiteEqOfArgs :=
  @Yul.Reference.SourceBridgeFacts.SourceStateRel.openExternalPrimitiveCreateSite_eq_of_args

abbrev sourceOpenTargetCommittedObservationRelStorageEq :=
  @Yul.Program.SourceOpenTargetCommittedObservationRel.storage_eq

abbrev sourceOpenTargetCommittedObservationRelTransientStorageEq :=
  @Yul.Program.SourceOpenTargetCommittedObservationRel.transientStorage_eq

abbrev sourceOpenTargetCommittedObservationRelExternalCodeEq :=
  @Yul.Program.SourceOpenTargetCommittedObservationRel.externalCode_eq

abbrev sourceOpenTargetCommittedObservationRelBalanceEq :=
  @Yul.Program.SourceOpenTargetCommittedObservationRel.balance_eq

abbrev sourceOpenTargetCommittedObservationRelTransactionReceiptsEq :=
  @Yul.Program.SourceOpenTargetCommittedObservationRel.transactionReceipts_eq

abbrev sourceOpenTargetCommittedObservationRelSubstateEq :=
  @Yul.Program.SourceOpenTargetCommittedObservationRel.substate_eq

namespace ImportedYulResourceObserverBoundary

/-!
Audit pins for the explicit `gas()`/`msize()` dry-run oracle route.

This is intentionally not the ordinary checked imported-Yul theorem surface:
it exposes a replay oracle boundary for values observed by an unchecked target
run, and the ordinary exact-preservation theorems may continue to reject visible
resource observers.
-/

abbrev targetDryRun :=
  Yul.ObserverOracle.TargetDryRun

abbrev targetDryRunOrdinaryRun :=
  @Yul.ObserverOracle.TargetDryRun.ordinary_run

abbrev targetDryRunOracleRun :=
  @Yul.ObserverOracle.TargetDryRun.oracle_run

abbrev targetDryRunOracleRunEmpty :=
  @Yul.ObserverOracle.TargetDryRun.oracle_run_empty

  abbrev targetDryRunResultEqOfTargetOracleRun :=
    @Yul.ObserverOracle.TargetDryRun.result_eq_of_targetOracle_run

  abbrev targetDryRunResultEqOfHaltedTargetOracleRunLe :=
    @Yul.ObserverOracle.TargetDryRun.result_eq_of_halted_targetOracle_run_le

  abbrev targetDryRunResultEqOfHaltedTargetOracleRunOfDryRunHalted :=
    @Yul.ObserverOracle.TargetDryRun.result_eq_of_halted_targetOracle_run_of_dryRun_halted

  abbrev targetDryRunResultEqOfHaltedSourceOracleRunOfCompileByteLengthLt :=
    @Yul.ObserverOracle.TargetDryRun.result_eq_of_halted_sourceOracle_run_of_compile_byteLength_lt

  abbrev targetDryRunResultEqOfHaltedSourceOracleRunOfCompileByteLengthLtOfDryRunHalted :=
    @Yul.ObserverOracle.TargetDryRun.result_eq_of_halted_sourceOracle_run_of_compile_byteLength_lt_of_dryRun_halted

  abbrev targetDryRunResultEqOfHaltedSourceOracleRunEmptyOfCompileByteLengthLtOfDryRunHalted :=
    @Yul.ObserverOracle.TargetDryRun.result_eq_of_halted_sourceOracle_run_empty_of_compile_byteLength_lt_of_dryRun_halted

  abbrev targetDryRunResultEqOfHaltedSourceObserverRunOfCompileByteLengthLtOfDryRunHalted :=
    @Yul.ObserverOracle.TargetDryRun.result_eq_of_halted_sourceObserver_run_of_compile_byteLength_lt_of_dryRun_halted

  abbrev targetDryRunResultEqOfHaltedStructuredMainOracleRunOfCompileByteLengthLtOfDryRunHalted :=
    @Yul.ObserverOracle.TargetDryRun.result_eq_of_halted_structuredMainOracle_run_of_compile_byteLength_lt_of_dryRun_halted

  abbrev targetDryRunResultEqOfHaltedStructuredMainOracleRunOfMainBlockOracleSafeOfCompileByteLengthLtOfDryRunHalted :=
    @Yul.ObserverOracle.TargetDryRun.result_eq_of_halted_structuredMainOracle_run_of_main_block_oracleSafe_of_compile_byteLength_lt_of_dryRun_halted

  abbrev targetDryRunResultEqOfHaltedExpressionsMainOracleRunOfProgramOracleSafeOfCompileByteLengthLtOfDryRunHalted :=
    @Yul.ObserverOracle.TargetDryRun.result_eq_of_halted_expressionsMainOracle_run_of_program_oracleSafe_of_compile_byteLength_lt_of_dryRun_halted

  abbrev targetDryRunSourceOracleRunMatchesTargetOracleOfCompile :=
    @Yul.ObserverOracle.TargetDryRun.sourceOracle_run_matches_targetOracle_of_compile

abbrev targetDryRunSourceOracleRunEmptyMatchesTargetOracleOfCompile :=
  @Yul.ObserverOracle.TargetDryRun.sourceOracle_run_empty_matches_targetOracle_of_compile

abbrev observerAssemblyOracleSourceRunPreservedByCompile :=
  @Yul.ObserverOracle.AssemblyOracle.source_run_preserved_by_compile

abbrev observerAssemblyOracleTargetRunResultUnique :=
  @Yul.ObserverOracle.AssemblyOracle.target_run_result_unique

  abbrev observerAssemblyOracleSourceRunMatchesTargetRunOfCompile :=
    @Yul.ObserverOracle.AssemblyOracle.source_run_matches_target_run_of_compile

  abbrev observerAssemblyOracleBlockTraceInducesTargetRunExistsOfCompile :=
    @Yul.ObserverOracle.AssemblyOracle.block_trace_induces_target_run_exists_of_compile

  abbrev observerAssemblyOracleBlockTraceInducesTargetRunExistsOfCompileByteLengthLt :=
    @Yul.ObserverOracle.AssemblyOracle.block_trace_induces_target_run_exists_of_compile_byteLength_lt

  abbrev observerAssemblyOracleSourceRunInducesTargetRunExistsOfCompileByteLengthLt :=
    @Yul.ObserverOracle.AssemblyOracle.source_run_induces_target_run_exists_of_compile_byteLength_lt

abbrev assemblySourceRunNResultWithObservers :=
  @Assembly.Source.runNResultWithObservers

abbrev assemblySourceRunNResultWithObserversSound :=
  @Assembly.Source.runNResultWithObservers_sound

abbrev assemblySourceRunNResultWithOracle :=
  @Assembly.Source.runNResultWithOracle

abbrev assemblySourceRunNResultWithOracleOfWithObservers :=
  @Assembly.Source.runNResultWithOracle_of_withObservers

abbrev assemblySourceRunNResultWithOracleRunningBind :=
  @Assembly.Source.runNResultWithOracle_running_bind

abbrev assemblySourceStepResultWithOracleOfStepResultObserverNone :=
  @Assembly.Source.stepResultWithOracle_of_stepResult_observer_none

abbrev assemblyCompiledRunNResultWithObserversSound :=
  @Assembly.Compiled.runNResultWithObservers_sound

abbrev assemblySourceCompiledRunNResultWithObserversSound :=
  @Assembly.Preservation.source_compiled_runN_result_withObservers_sound

abbrev assemblySourceCompiledRunNResultWithOracleSound :=
  @Assembly.Preservation.source_compiled_runN_result_withOracle_sound

abbrev assemblySourceCompiledRunNResultWithOracleSoundOfSourceOracle :=
  @Assembly.Preservation.source_compiled_runN_result_withOracle_sound_of_sourceOracle

abbrev assemblyBlockTraceResultWithOracle :=
  Assembly.Preservation.BlockTraceResultWithOracle

abbrev assemblyAssembleSourceStepCurrentResultWithOracleSound :=
  @Assembly.Preservation.assemble_source_step_current_result_withOracle_sound

abbrev assemblyAssembleRunNResultBlockTraceWithOracleSound :=
  @Assembly.Preservation.assemble_runN_result_block_trace_withOracle_sound

abbrev assemblyCompileRunNResultBlockTraceWithOracleSound :=
  @Assembly.Preservation.compile_runN_result_block_trace_withOracle_sound

abbrev assemblyTargetRunNResultWithOracle :=
  @Assembly.Target.runNResultWithOracle

abbrev assemblyTargetRunNResultWithOracleOfWithObservers :=
  @Assembly.Target.runNResultWithOracle_of_withObservers

abbrev assemblyCompiledRunNResultWithOracle :=
  @Assembly.Compiled.runNResultWithOracle

abbrev assemblyCompiledRunNResultWithOracleOfWithObservers :=
  @Assembly.Compiled.runNResultWithOracle_of_withObservers

abbrev assemblyResourceObserverOverwriteTopPC :=
  @Assembly.ResourceObserver.overwriteTop_pc

abbrev assemblyResourceObserverApplyOracleFromPostStatePC :=
  @Assembly.ResourceObserver.applyOracleFromPostState_pc

abbrev assemblyInstrAtPcFromPCEq :=
  @Assembly.Program.instrAtPcFrom_pc_eq

abbrev assemblyInstrAtPcFromBaseLeQuery :=
  @Assembly.Program.instrAtPcFrom_base_le_query

abbrev assemblyInstrAtPcFromEndLeBaseByteLength :=
  @Assembly.Program.instrAtPcFrom_end_le_base_byteLength

abbrev assemblyInstrAtPcPCEq :=
  @Assembly.Program.instrAtPc_pc_eq

abbrev assemblyInstrAtPcEndLeByteLength :=
  @Assembly.Program.instrAtPc_end_le_byteLength

abbrev assemblyEmitInstrFirst :=
  @Assembly.emitInstr?_first

abbrev assemblyEmitInstrFindNoneOfByteSizeLe :=
  @Assembly.emitInstr?_find?_none_of_byteSize_le

abbrev assemblyTargetProgramFetchConsSame :=
  @Assembly.TargetProgram.fetch_cons_same

abbrev assemblyTargetProgramFetchAppendOfFetchLeft :=
  @Assembly.TargetProgram.fetch_append_of_fetch_left

abbrev assemblyEmitFromFetchSomeOfInstrAtPcFrom :=
  @Assembly.emitFrom?_fetch_some_of_instrAtPcFrom

abbrev assemblyEmitFromFetchFirstOfInstrAtPcFrom :=
  @Assembly.emitFrom?_fetch_first_of_instrAtPcFrom

abbrev assemblyAssembleFetchFirstOfInstrAtPc :=
  @Assembly.assemble?_fetch_first_of_instrAtPc

abbrev assemblyEmitFromFetchOfInstrAtPcFromEmittedFetch :=
  @Assembly.emitFrom?_fetch_of_instrAtPcFrom_emitted_fetch

abbrev assemblyAssembleFetchOfInstrAtPcEmittedFetch :=
  @Assembly.assemble?_fetch_of_instrAtPc_emitted_fetch

abbrev assemblyEmitInstrFetchJumpSecond :=
  @Assembly.emitInstr?_fetch_jump_second

abbrev assemblyEmitInstrFetchJumpiSecond :=
  @Assembly.emitInstr?_fetch_jumpi_second

abbrev assemblyAssembleFetchJumpSecondOfInstrAtPc :=
  @Assembly.assemble?_fetch_jump_second_of_instrAtPc

  abbrev assemblyAssembleFetchJumpiSecondOfInstrAtPc :=
    @Assembly.assemble?_fetch_jumpi_second_of_instrAtPc

  abbrev assemblyTargetRunNResultWithOracleRunningBind :=
    @Assembly.Target.runNResultWithOracle_running_bind

  abbrev assemblyTargetRunNResultWithOracleHaltedAdd :=
    @Assembly.Target.runNResultWithOracle_halted_add

  abbrev assemblyReplaceStackAndIncrPCPCToNatOfNoOverflow :=
    @Assembly.Preservation.replaceStackAndIncrPC_pc_toNat_of_no_overflow

  abbrev assemblyTargetRunNResultWithOracleSingleOfFetch :=
    @Assembly.Preservation.target_runNResultWithOracle_single_of_fetch

  abbrev assemblyTargetRunNResultWithOraclePushJumpOfFetch :=
    @Assembly.Preservation.target_runNResultWithOracle_push_jump_of_fetch

  abbrev assemblyTargetRunNResultWithOraclePushJumpiOfFetch :=
    @Assembly.Preservation.target_runNResultWithOracle_push_jumpi_of_fetch

  abbrev assemblyTargetBlockPcSafe :=
    @Assembly.Preservation.TargetBlockPcSafe

  abbrev assemblyTargetBlockPcSafeOfInstrAtPcOfByteLengthLt :=
    @Assembly.Preservation.targetBlockPcSafe_of_instrAtPc_of_byteLength_lt

  abbrev assemblyTargetRunNResultWithOracleOfEmitInstrRunList :=
    @Assembly.Preservation.target_runNResultWithOracle_of_emitInstr?_runList

  abbrev assemblyBlockTraceResultWithOracleTargetPcSafe :=
    @Assembly.Preservation.BlockTraceResultWithOracle.TargetPcSafe

  abbrev assemblyBlockTraceResultWithOracleTargetPcSafeOfByteLengthLt :=
    @Assembly.Preservation.BlockTraceResultWithOracle.targetPcSafe_of_byteLength_lt

  abbrev assemblyBlockTraceResultWithOracleTargetRunNResultWithOracleExists :=
    @Assembly.Preservation.BlockTraceResultWithOracle.target_runNResultWithOracle_exists

  abbrev assemblyBlockTraceResultWithOracleTargetRunNResultWithOracleExistsOfByteLengthLt :=
    @Assembly.Preservation.BlockTraceResultWithOracle.target_runNResultWithOracle_exists_of_byteLength_lt

  abbrev replayEvalGasCons :=
    @Yul.ObserverOracle.replay_eval_gas_cons

abbrev replayEvalMsizeCons :=
  @Yul.ObserverOracle.replay_eval_msize_cons

abbrev replayEvalNonObserverPreservesTrace :=
  @Yul.ObserverOracle.replay_eval_nonObserver_preserves_trace

abbrev replayTerminalPreservesTrace :=
  @Yul.ObserverOracle.replay_terminal_preserves_trace

abbrev replayEvalLength :=
  @Yul.ObserverOracle.replay_eval_length

abbrev replayPrimitiveStepTrace :=
  @Yul.ObserverOracle.ReplayPrimitiveStep.stepTrace

abbrev replayPrimitiveStepNonObserverSound :=
  @Yul.ObserverOracle.ReplayPrimitiveStep.eval_step_nonObserver_sound

abbrev replayPrimitiveStepGasSound :=
  @Yul.ObserverOracle.ReplayPrimitiveStep.eval_step_gas_sound

abbrev replayPrimitiveStepMsizeSound :=
  @Yul.ObserverOracle.ReplayPrimitiveStep.eval_step_msize_sound

abbrev replayPrimitiveStepTraceSound :=
  @Yul.ObserverOracle.ReplayPrimitiveStep.eval_step_trace_sound

abbrev replayPrimitiveAssemblyStepExists :=
  @Yul.ObserverOracle.ReplayPrimitiveStep.eval_assembly_prim_step_exists

abbrev replayPrimitiveTerminalAssemblyStepExists :=
  @Yul.ObserverOracle.ReplayPrimitiveStep.terminal_assembly_step_exists

abbrev primitiveAssemblyOracleSound :=
  @Yul.ObserverOracle.PrimitiveAssemblyOracleSound

abbrev replayPrimitiveAssemblySound :=
  @Yul.ObserverOracle.replayPrimitiveAssemblySound

abbrev structuredReplayBasicInstrStepWithOracle :=
  @Yul.ObserverOracle.StructuredReplay.BasicInstr.stepWithOracle

abbrev structuredReplayBasicInstrStepWithOraclePush :=
  @Yul.ObserverOracle.StructuredReplay.BasicInstr.stepWithOracle_push

abbrev structuredReplayBasicInstrStepWithOracleOpOfReplay :=
  @Yul.ObserverOracle.StructuredReplay.BasicInstr.stepWithOracle_op_of_replay

abbrev structuredReplayBasicInstrStepWithOracleOpNonObserverOfStep :=
  @Yul.ObserverOracle.StructuredReplay.BasicInstr.stepWithOracle_op_nonObserver_of_step

abbrev structuredReplayBasicInstrStepWithOracleOpNonObserver :=
  @Yul.ObserverOracle.StructuredReplay.BasicInstr.stepWithOracle_op_nonObserver

abbrev structuredReplayBasicInstrOracleStepPC :=
  @Yul.ObserverOracle.StructuredReplay.BasicInstr.OracleStepPC

abbrev structuredReplayBasicInstrStepWithOraclePCOfStepPC :=
  @Yul.ObserverOracle.StructuredReplay.BasicInstr.stepWithOracle_pc_of_stepPC

abbrev structuredReplayBasicInstrOracleStepPCOfRunnerSafe :=
  @Yul.ObserverOracle.StructuredReplay.BasicInstr.oracleStepPC_of_runnerSafe

abbrev structuredReplayBasicInstrSourceStepResultWithOracleOfSegmentStepWithOracle :=
  @Yul.ObserverOracle.StructuredReplay.BasicInstr.source_stepResultWithOracle_of_segment_stepWithOracle

abbrev structuredReplayARunResultWithOracle :=
  @Yul.ObserverOracle.StructuredReplay.ARunResultWithOracle

abbrev structuredReplayARunResultWithOracleExact :=
  @Yul.ObserverOracle.StructuredReplay.ARunResultWithOracle.exact

abbrev structuredReplayARunResultWithOraclePure :=
  @Yul.ObserverOracle.StructuredReplay.ARunResultWithOracle.pure

abbrev structuredReplayARunResultWithOracleBindRunning :=
  @Yul.ObserverOracle.StructuredReplay.ARunResultWithOracle.bind_running

abbrev structuredReplayARunResultWithOracleMono :=
  @Yul.ObserverOracle.StructuredReplay.ARunResultWithOracle.mono

abbrev structuredReplayFrameStateRelOfSameDataTarget :=
  @Yul.ObserverOracle.StructuredReplay.Frame.StateRel.of_sameData_target

abbrev structuredReplayFrameStateRelLabelRunResultWithOracleAt :=
  @Yul.ObserverOracle.StructuredReplay.Frame.StateRel.label_runResultWithOracle_at

abbrev structuredReplayFrameStateRelJumpThenLabelRunResultWithOracleAt :=
  @Yul.ObserverOracle.StructuredReplay.Frame.StateRel.jump_then_label_runResultWithOracle_at

abbrev structuredReplayFrameStateRelPopRunResultWithOracleAt :=
  @Yul.ObserverOracle.StructuredReplay.Frame.StateRel.pop_runResultWithOracle_at

abbrev structuredReplayFrameStateRelRunConditionWithOracleJumpiResultCtx :=
  @Yul.ObserverOracle.StructuredReplay.Frame.StateRel.runConditionWithOracle_jumpi_result_ctx

abbrev structuredReplayCodeOracleStepPC :=
  @Yul.ObserverOracle.StructuredReplay.Code.OracleStepPC

abbrev structuredReplayCodeOracleStepPCOfRunnerSafe :=
  @Yul.ObserverOracle.StructuredReplay.Code.oracleStepPC_of_runnerSafe

abbrev structuredReplayCodeOracleStepPCNil :=
  @Yul.ObserverOracle.StructuredReplay.Code.oracleStepPC_nil

abbrev structuredReplayCodeOracleStepPCAppend :=
  @Yul.ObserverOracle.StructuredReplay.Code.oracleStepPC_append

abbrev structuredReplayCodeOracleStepPCCons :=
  @Yul.ObserverOracle.StructuredReplay.Code.oracleStepPC_cons

abbrev structuredReplayCodeRunWithOracle :=
  @Yul.ObserverOracle.StructuredReplay.Code.runWithOracle

abbrev structuredReplayCodeRunStateWithOracle :=
  @Yul.ObserverOracle.StructuredReplay.Code.runStateWithOracle

abbrev structuredReplayCodeRunConditionWithOracle :=
  @Yul.ObserverOracle.StructuredReplay.Code.runConditionWithOracle

abbrev structuredReplayCodeRunConditionWithOracleOracleFrameSafeHiddenPopExists :=
  @Yul.ObserverOracle.StructuredReplay.Code.runConditionWithOracle_oracleFrameSafe_hidden_pop_exists

abbrev structuredReplayCodeRunConditionWithOracleOracleFrameSafeHiddenExists :=
  @Yul.ObserverOracle.StructuredReplay.Code.runConditionWithOracle_oracleFrameSafe_hidden_exists

abbrev structuredReplayCodeRunWithOracleSourceRunNResultWithOracleSegment :=
  @Yul.ObserverOracle.StructuredReplay.Code.runWithOracle_source_runNResultWithOracle_segment

abbrev structuredReplayCodeRunWithOracleSourceRunNResultWithOracleSegmentOfOracleStepPC :=
  @Yul.ObserverOracle.StructuredReplay.Code.runWithOracle_source_runNResultWithOracle_segment_of_oracleStepPC

abbrev structuredReplayCodeRunWithOracleSourceRunNResultWithOracleSegmentOfRunnerSafe :=
  @Yul.ObserverOracle.StructuredReplay.Code.runWithOracle_source_runNResultWithOracle_segment_of_runnerSafe

abbrev structuredReplayCodeRunWithOracleSourceRunNResultWithOracleSegmentOfCodeSegment :=
  @Yul.ObserverOracle.StructuredReplay.Code.runWithOracle_source_runNResultWithOracle_segment_of_codeSegment

abbrev structuredReplayCodeRunWithOracleSourceRunNResultWithOracleSegmentOfCodeSegmentOfOracleStepPC :=
  @Yul.ObserverOracle.StructuredReplay.Code.runWithOracle_source_runNResultWithOracle_segment_of_codeSegment_of_oracleStepPC

abbrev structuredReplayCodeRunWithOracleSourceRunNResultWithOracleBindOfCodeSegment :=
  @Yul.ObserverOracle.StructuredReplay.Code.runWithOracle_source_runNResultWithOracle_bind_of_codeSegment

abbrev structuredReplayCodeRunWithOracleSourceRunNResultWithOracleBindOfCodeSegmentOfOracleStepPC :=
  @Yul.ObserverOracle.StructuredReplay.Code.runWithOracle_source_runNResultWithOracle_bind_of_codeSegment_of_oracleStepPC

abbrev structuredReplayCodeRunStateWithOracleSourceRunNResultWithOracleSegmentOfCodeSegment :=
  @Yul.ObserverOracle.StructuredReplay.Code.runStateWithOracle_source_runNResultWithOracle_segment_of_codeSegment

abbrev structuredReplayCodeRunStateWithOracleSourceRunNResultWithOracleSegmentOfCodeSegmentOfOracleStepPC :=
  @Yul.ObserverOracle.StructuredReplay.Code.runStateWithOracle_source_runNResultWithOracle_segment_of_codeSegment_of_oracleStepPC

abbrev structuredReplayCodeOracleFrameSafe :=
  @Yul.ObserverOracle.StructuredReplay.Code.OracleFrameSafe

abbrev structuredReplayCodeRunWithOracleHiddenSuffixOfOracleFrameSafe :=
  @Yul.ObserverOracle.StructuredReplay.Code.runWithOracle_hidden_suffix_of_oracleFrameSafe

abbrev structuredReplayCodeRunStateWithOracleHiddenSuffixOfOracleFrameSafe :=
  @Yul.ObserverOracle.StructuredReplay.Code.runStateWithOracle_hidden_suffix_of_oracleFrameSafe

abbrev structuredReplayCodeRunStateWithOracleOracleFrameSafeHiddenExists :=
  @Yul.ObserverOracle.StructuredReplay.Code.runStateWithOracle_oracleFrameSafe_hidden_exists

abbrev structuredReplayCodeRunWithOracleAppend :=
  @Yul.ObserverOracle.StructuredReplay.Code.runWithOracle_append

abbrev structuredReplayCodeOracleFrameSafeNil :=
  @Yul.ObserverOracle.StructuredReplay.Code.oracleFrameSafe_nil

abbrev structuredReplayCodeOracleFrameSafeAppend :=
  @Yul.ObserverOracle.StructuredReplay.Code.oracleFrameSafe_append

abbrev structuredReplayCodeOracleFrameSafeOfFrameSafeObserverFree :=
  @Yul.ObserverOracle.StructuredReplay.Code.oracleFrameSafe_of_frameSafe_observer_free

abbrev structuredReplayCodeObserverFree :=
  @Yul.ObserverOracle.StructuredReplay.Code.ObserverFree

abbrev structuredReplayCodeObserverFreeAppend :=
  @Yul.ObserverOracle.StructuredReplay.Code.observerFree_append

abbrev structuredReplayCodeObserverFreeSingletonPop :=
  @Yul.ObserverOracle.StructuredReplay.Code.observerFree_singleton_pop

abbrev structuredReplayCodeObserverFreeSingletonStackSwap :=
  @Yul.ObserverOracle.StructuredReplay.Code.observerFree_singleton_stackSwap?

abbrev structuredReplayCodeObserverFreeReplicatePop :=
  @Yul.ObserverOracle.StructuredReplay.Code.observerFree_replicate_pop

abbrev structuredReplayCodeRunnerSafeReplicatePop :=
  @Yul.ObserverOracle.StructuredReplay.Code.runnerSafe_replicate_pop

abbrev structuredReplayCodeFrameSafeNil :=
  @Yul.ObserverOracle.StructuredReplay.Code.frameSafe_nil

abbrev structuredReplayCodeFrameSafeReplicatePop :=
  @Yul.ObserverOracle.StructuredReplay.Code.frameSafe_replicate_pop

abbrev structuredReplayCodeRunnerSafeSingletonStackSwap :=
  @Yul.ObserverOracle.StructuredReplay.Code.runnerSafe_singleton_stackSwap?

abbrev structuredReplayCodeFrameSafeSingletonStackSwap :=
  @Yul.ObserverOracle.StructuredReplay.Code.frameSafe_singleton_stackSwap?

abbrev structuredReplayCodeRunnerSafeSwapRestoreUpTo :=
  @Yul.ObserverOracle.StructuredReplay.Code.runnerSafe_swapRestoreUpTo?

abbrev structuredReplayCodeFrameSafeSwapRestoreUpTo :=
  @Yul.ObserverOracle.StructuredReplay.Code.frameSafe_swapRestoreUpTo?

abbrev structuredReplayCodeObserverFreeSwapRestoreUpTo :=
  @Yul.ObserverOracle.StructuredReplay.Code.observerFree_swapRestoreUpTo?

abbrev structuredReplayCodeRunnerSafeCleanupOnePreserving :=
  @Yul.ObserverOracle.StructuredReplay.Code.runnerSafe_cleanupOnePreserving?

abbrev structuredReplayCodeFrameSafeCleanupOnePreserving :=
  @Yul.ObserverOracle.StructuredReplay.Code.frameSafe_cleanupOnePreserving?

abbrev structuredReplayCodeObserverFreeCleanupOnePreserving :=
  @Yul.ObserverOracle.StructuredReplay.Code.observerFree_cleanupOnePreserving?

abbrev structuredReplayCodeRunnerSafeCleanupManyPreserving :=
  @Yul.ObserverOracle.StructuredReplay.Code.runnerSafe_cleanupManyPreserving?

abbrev structuredReplayCodeFrameSafeCleanupManyPreserving :=
  @Yul.ObserverOracle.StructuredReplay.Code.frameSafe_cleanupManyPreserving?

abbrev structuredReplayCodeObserverFreeCleanupManyPreserving :=
  @Yul.ObserverOracle.StructuredReplay.Code.observerFree_cleanupManyPreserving?

abbrev structuredReplayCodeRunnerSafeCleanupTo :=
  @Yul.ObserverOracle.StructuredReplay.Code.runnerSafe_cleanupTo?

abbrev structuredReplayCodeFrameSafeCleanupTo :=
  @Yul.ObserverOracle.StructuredReplay.Code.frameSafe_cleanupTo?

abbrev structuredReplayCodeObserverFreeCleanupTo :=
  @Yul.ObserverOracle.StructuredReplay.Code.observerFree_cleanupTo?

abbrev structuredReplayCodeRunnerSafeCleanupToPreserving :=
  @Yul.ObserverOracle.StructuredReplay.Code.runnerSafe_cleanupToPreserving?

abbrev structuredReplayCodeFrameSafeCleanupToPreserving :=
  @Yul.ObserverOracle.StructuredReplay.Code.frameSafe_cleanupToPreserving?

abbrev structuredReplayCodeObserverFreeCleanupToPreserving :=
  @Yul.ObserverOracle.StructuredReplay.Code.observerFree_cleanupToPreserving?

abbrev structuredReplayCodeRunnerSafeCleanupAll :=
  @Yul.ObserverOracle.StructuredReplay.Code.runnerSafe_cleanupAll

abbrev structuredReplayCodeFrameSafeCleanupAll :=
  @Yul.ObserverOracle.StructuredReplay.Code.frameSafe_cleanupAll

abbrev structuredReplayCodeObserverFreeCleanupAll :=
  @Yul.ObserverOracle.StructuredReplay.Code.observerFree_cleanupAll

abbrev structuredReplayCodeOracleFrameSafeCons :=
  @Yul.ObserverOracle.StructuredReplay.Code.oracleFrameSafe_cons

abbrev structuredReplayCodeRunWithOracleSingletonPush :=
  @Yul.ObserverOracle.StructuredReplay.Code.runWithOracle_singleton_push

abbrev structuredReplayCodeOracleFrameSafeSingletonPush :=
  @Yul.ObserverOracle.StructuredReplay.Code.oracleFrameSafe_singleton_push

abbrev structuredReplayCodeOracleStepPCSingletonPush :=
  @Yul.ObserverOracle.StructuredReplay.Code.oracleStepPC_singleton_push

abbrev structuredReplayCodeRunWithOracleSingletonOpOfReplay :=
  @Yul.ObserverOracle.StructuredReplay.Code.runWithOracle_singleton_op_of_replay

abbrev structuredReplayCodeRunWithOracleSingletonOpNonObserverOfStep :=
  @Yul.ObserverOracle.StructuredReplay.Code.runWithOracle_singleton_op_nonObserver_of_step

abbrev structuredReplayCodeRunWithOracleSingletonOpNonObserver :=
  @Yul.ObserverOracle.StructuredReplay.Code.runWithOracle_singleton_op_nonObserver

abbrev structuredReplayCodeOracleFrameSafeSingletonOpNonObserver :=
  @Yul.ObserverOracle.StructuredReplay.Code.oracleFrameSafe_singleton_op_nonObserver

abbrev structuredReplayCodeFrameSafeSingletonOpOfSourceContinuingStep :=
  @Yul.ObserverOracle.StructuredReplay.Code.frameSafe_singleton_op_of_sourceContinuingStep

abbrev structuredReplayCodeOracleFrameSafeSingletonOpNonObserverOfSourceContinuingStep :=
  @Yul.ObserverOracle.StructuredReplay.Code.oracleFrameSafe_singleton_op_nonObserver_of_sourceContinuingStep

abbrev structuredReplayCodeStepPCOpOfSourceContinuingStep :=
  @Yul.ObserverOracle.StructuredReplay.Code.stepPC_op_of_sourceContinuingStep

abbrev structuredReplayCodeOracleStepPCSingletonOpOfSourceContinuingStep :=
  @Yul.ObserverOracle.StructuredReplay.Code.oracleStepPC_singleton_op_of_sourceContinuingStep

abbrev structuredReplayCodeOracleFrameSafeSingletonOpOfReplay :=
  @Yul.ObserverOracle.StructuredReplay.Code.oracleFrameSafe_singleton_op_of_replay

abbrev structuredReplayCodeOracleStepPCSingletonOpOfReplay :=
  @Yul.ObserverOracle.StructuredReplay.Code.oracleStepPC_singleton_op_of_replay

abbrev structuredReplayCodeStepWithOracleGas :=
  @Yul.ObserverOracle.StructuredReplay.Code.stepWithOracle_gas

abbrev structuredReplayCodeOracleFrameSafeSingletonGas :=
  @Yul.ObserverOracle.StructuredReplay.Code.oracleFrameSafe_singleton_gas

abbrev structuredReplayCodeOracleStepPCSingletonGas :=
  @Yul.ObserverOracle.StructuredReplay.Code.oracleStepPC_singleton_gas

abbrev structuredReplayCodeStepWithOracleMsize :=
  @Yul.ObserverOracle.StructuredReplay.Code.stepWithOracle_msize

abbrev structuredReplayCodeOracleFrameSafeSingletonMsize :=
  @Yul.ObserverOracle.StructuredReplay.Code.oracleFrameSafe_singleton_msize

abbrev structuredReplayCodeOracleStepPCSingletonMsize :=
  @Yul.ObserverOracle.StructuredReplay.Code.oracleStepPC_singleton_msize

abbrev structuredReplayCodeRunWithOracleReplicatePopExists :=
  @Yul.ObserverOracle.StructuredReplay.Code.runWithOracle_replicate_pop_exists

abbrev structuredReplayBlockRunWithOracle :=
  @Yul.ObserverOracle.StructuredReplay.Block.runWithOracle

abbrev structuredReplayStmtRunForLoopWithOracle :=
  @Yul.ObserverOracle.StructuredReplay.Stmt.runForLoopWithOracle

abbrev structuredReplayStmtRunWithOracle :=
  @Yul.ObserverOracle.StructuredReplay.Stmt.runWithOracle

abbrev structuredReplayStmtRunWithOracleCodeSourceRunNResultWithOracleSegmentOfCodeSegment :=
  @Yul.ObserverOracle.StructuredReplay.Stmt.runWithOracle_code_source_runNResultWithOracle_segment_of_codeSegment

abbrev structuredReplayStmtRunWithOracleCodeSourceRunNResultWithOracleBindOfCodeSegment :=
  @Yul.ObserverOracle.StructuredReplay.Stmt.runWithOracle_code_source_runNResultWithOracle_bind_of_codeSegment

abbrev structuredReplayStmtRunWithOracleCodeSourceRunNResultWithOracleSegmentOfCodeSegmentOfOracleStepPC :=
  @Yul.ObserverOracle.StructuredReplay.Stmt.runWithOracle_code_source_runNResultWithOracle_segment_of_codeSegment_of_oracleStepPC

abbrev structuredReplayStmtRunWithOracleCodeSourceRunNResultWithOracleBindOfCodeSegmentOfOracleStepPC :=
  @Yul.ObserverOracle.StructuredReplay.Stmt.runWithOracle_code_source_runNResultWithOracle_bind_of_codeSegment_of_oracleStepPC

abbrev structuredReplayCodeRunWithOracleOfObserverFree :=
  @Yul.ObserverOracle.StructuredReplay.Code.runWithOracle_of_observer_free

abbrev structuredReplayCodeRunConditionWithOracleOfObserverFree :=
  @Yul.ObserverOracle.StructuredReplay.Code.runConditionWithOracle_of_observer_free

abbrev structuredReplaySwitchPreservationWithOracleCasesPreservesWithOracle :=
  @Yul.ObserverOracle.StructuredReplay.SwitchPreservationWithOracle.CasesPreservesWithOracle

abbrev structuredReplaySwitchPreservationWithOracleDefaultPreservesWithOracle :=
  @Yul.ObserverOracle.StructuredReplay.SwitchPreservationWithOracle.DefaultPreservesWithOracle

abbrev structuredReplaySwitchPreservationWithOracleCasesPreservesWithOracleHead :=
  @Yul.ObserverOracle.StructuredReplay.SwitchPreservationWithOracle.casesPreservesWithOracle_head

abbrev structuredReplaySwitchPreservationWithOracleCasesPreservesWithOracleTail :=
  @Yul.ObserverOracle.StructuredReplay.SwitchPreservationWithOracle.casesPreservesWithOracle_tail

abbrev structuredReplaySwitchPreservationWithOracleDefaultPreservesWithOracleSome :=
  @Yul.ObserverOracle.StructuredReplay.SwitchPreservationWithOracle.defaultPreservesWithOracle_some

abbrev structuredReplaySwitchPreservationWithOracleSwitchTestCodeObserverFree :=
  @Yul.ObserverOracle.StructuredReplay.SwitchPreservationWithOracle.switchTestCode_observer_free

abbrev structuredReplaySwitchPreservationWithOracleSwitchTestCodeOracleRelSafe :=
  @Yul.ObserverOracle.StructuredReplay.SwitchPreservationWithOracle.switchTestCode_oracleRelSafe

abbrev structuredReplaySwitchPreservationWithOracleFrameSafeSingletonEq :=
  @Yul.ObserverOracle.StructuredReplay.SwitchPreservationWithOracle.frameSafe_singleton_eq

abbrev structuredReplaySwitchPreservationWithOracleSwitchTestCodeOracleFrameSafe :=
  @Yul.ObserverOracle.StructuredReplay.SwitchPreservationWithOracle.switchTestCode_oracleFrameSafe

abbrev structuredReplaySwitchPreservationWithOracleSwitchTestCodeRunConditionWithOracle :=
  @Yul.ObserverOracle.StructuredReplay.SwitchPreservationWithOracle.switchTestCode_runConditionWithOracle

abbrev structuredReplaySwitchPreservationWithOracleTestJumpiResultCtx :=
  @Yul.ObserverOracle.StructuredReplay.SwitchPreservationWithOracle.test_jumpi_result_ctx

abbrev structuredReplaySwitchPreservationWithOracleTestTrueResultCtx :=
  @Yul.ObserverOracle.StructuredReplay.SwitchPreservationWithOracle.test_true_result_ctx

abbrev structuredReplaySwitchPreservationWithOracleTestFalseResultCtx :=
  @Yul.ObserverOracle.StructuredReplay.SwitchPreservationWithOracle.test_false_result_ctx

abbrev structuredReplaySwitchPreservationWithOracleTestsFallthroughResultCtx :=
  @Yul.ObserverOracle.StructuredReplay.SwitchPreservationWithOracle.tests_fallthrough_result_ctx

abbrev structuredReplaySwitchPreservationWithOracleDefaultNoneTailResultCtx :=
  @Yul.ObserverOracle.StructuredReplay.SwitchPreservationWithOracle.default_none_tail_result_ctx

abbrev structuredReplaySwitchPreservationWithOracleDefaultSomeTailResultCtx :=
  @Yul.ObserverOracle.StructuredReplay.SwitchPreservationWithOracle.default_some_tail_result_ctx

abbrev structuredReplaySwitchPreservationWithOracleDefaultSelectedTailResultCtx :=
  @Yul.ObserverOracle.StructuredReplay.SwitchPreservationWithOracle.default_selected_tail_result_ctx

abbrev structuredReplaySwitchPreservationWithOracleDefaultSelectedTailResultCtxOfBodyTailRun :=
  @Yul.ObserverOracle.StructuredReplay.SwitchPreservationWithOracle.default_selected_tail_result_ctx_of_body_tail_run

abbrev structuredReplaySwitchPreservationWithOracleLabeledBodyTailResultCtx :=
  @Yul.ObserverOracle.StructuredReplay.SwitchPreservationWithOracle.labeled_body_tail_result_ctx

abbrev structuredReplaySwitchPreservationWithOracleLabeledBodyTailResultCtxOfBodyTailRun :=
  @Yul.ObserverOracle.StructuredReplay.SwitchPreservationWithOracle.labeled_body_tail_result_ctx_of_body_tail_run

abbrev structuredReplaySwitchPreservationWithOracleHeadCaseFromTestsResultCtxOfTailRun :=
  @Yul.ObserverOracle.StructuredReplay.SwitchPreservationWithOracle.head_case_from_tests_result_ctx_of_tail_run

abbrev structuredReplaySwitchPreservationWithOracleTailCaseFromTestsResultCtxOfTailRun :=
  @Yul.ObserverOracle.StructuredReplay.SwitchPreservationWithOracle.tail_case_from_tests_result_ctx_of_tail_run

abbrev structuredReplaySwitchPreservationWithOracleHeadCaseFromTestsResultCtx :=
  @Yul.ObserverOracle.StructuredReplay.SwitchPreservationWithOracle.head_case_from_tests_result_ctx

abbrev structuredReplaySwitchPreservationWithOracleSelectedCasesResultCtx :=
  @Yul.ObserverOracle.StructuredReplay.SwitchPreservationWithOracle.selected_cases_result_ctx

abbrev structuredReplaySwitchPreservationWithOracleSwitchNoneResultCtx :=
  @Yul.ObserverOracle.StructuredReplay.SwitchPreservationWithOracle.switch_none_result_ctx

abbrev structuredReplayForLoopPreservationWithOraclePreservesRun :=
  @Yul.ObserverOracle.StructuredReplay.ForLoopPreservationWithOracle.preserves_run

abbrev structuredReplayStmtPreservationWithOraclePreservesCode :=
  @Yul.ObserverOracle.StructuredReplay.StmtPreservationWithOracle.preserves_code

abbrev structuredReplayStmtPreservationWithOraclePreservesBrk :=
  @Yul.ObserverOracle.StructuredReplay.StmtPreservationWithOracle.preserves_brk

abbrev structuredReplayStmtPreservationWithOraclePreservesCont :=
  @Yul.ObserverOracle.StructuredReplay.StmtPreservationWithOracle.preserves_cont

abbrev structuredReplayStmtPreservationWithOraclePreservesLeave :=
  @Yul.ObserverOracle.StructuredReplay.StmtPreservationWithOracle.preserves_leave

abbrev structuredReplayStmtPreservationWithOraclePreservesTerminal :=
  @Yul.ObserverOracle.StructuredReplay.StmtPreservationWithOracle.preserves_terminal

abbrev structuredReplayStmtPreservationWithOraclePreservesIfFalseOfCondition :=
  @Yul.ObserverOracle.StructuredReplay.StmtPreservationWithOracle.preserves_if_false_of_condition

abbrev structuredReplayStmtPreservationWithOraclePreservesIfTrueOfConditionBodyRun :=
  @Yul.ObserverOracle.StructuredReplay.StmtPreservationWithOracle.preserves_if_true_of_condition_body_run

abbrev structuredReplayStmtPreservationWithOraclePreservesIf :=
  @Yul.ObserverOracle.StructuredReplay.StmtPreservationWithOracle.preserves_if

abbrev structuredReplayStmtPreservationWithOraclePreservesSwitchNoneOfScrutinee :=
  @Yul.ObserverOracle.StructuredReplay.StmtPreservationWithOracle.preserves_switch_none_of_scrutinee

abbrev structuredReplayStmtPreservationWithOraclePreservesSwitch :=
  @Yul.ObserverOracle.StructuredReplay.StmtPreservationWithOracle.preserves_switch

abbrev structuredReplayStmtPreservationWithOraclePreservesFor :=
  @Yul.ObserverOracle.StructuredReplay.StmtPreservationWithOracle.preserves_for

abbrev structuredReplayBlockPreservationWithOraclePreservesNil :=
  @Yul.ObserverOracle.StructuredReplay.BlockPreservationWithOracle.preserves_nil

abbrev structuredReplayBlockPreservationWithOracleCons :=
  @Yul.ObserverOracle.StructuredReplay.BlockPreservationWithOracle.cons

abbrev structuredReplaySwitchPreservationWithOracleCasesPreservesOfAll :=
  @Yul.ObserverOracle.StructuredReplay.SwitchPreservationWithOracle.casesPreservesWithOracle_of_all

abbrev structuredReplayOracleSafeBlock :=
  Yul.ObserverOracle.StructuredReplay.OracleSafe.Block

abbrev structuredReplayOracleSafeStmt :=
  Yul.ObserverOracle.StructuredReplay.OracleSafe.Stmt

abbrev structuredReplayOracleSafeBlockAppend :=
  @Yul.ObserverOracle.StructuredReplay.OracleSafe.block_append

abbrev structuredReplayOracleSafeBlockPreserves :=
  @Yul.ObserverOracle.StructuredReplay.OracleSafe.blockPreserves

abbrev structuredReplayOracleSafeStmtPreserves :=
  @Yul.ObserverOracle.StructuredReplay.OracleSafe.stmtPreserves

abbrev structuredReplayOracleSafeMainBlockPreserves :=
  @Yul.ObserverOracle.StructuredReplay.OracleSafe.mainBlockPreserves

abbrev structuredReplayProgramPreservationWithOracleHaltedSourceOracleRunOfMainBlockPreserves :=
  @Yul.ObserverOracle.StructuredReplay.ProgramPreservationWithOracle.halted_sourceOracle_run_of_main_block_preserves

abbrev structuredReplayProgramPreservationWithOracleHaltedSourceOracleRunOfMainOracleSafe :=
  @Yul.ObserverOracle.StructuredReplay.ProgramPreservationWithOracle.halted_sourceOracle_run_of_main_oracleSafe

abbrev expressionsReplayExprCodeShaped :=
  @Yul.ObserverOracle.ExpressionsReplay.ExprCodeShaped

abbrev expressionsReplayBlockCodeShaped :=
  @Yul.ObserverOracle.ExpressionsReplay.BlockCodeShaped

abbrev expressionsReplayStmtCodeShaped :=
  @Yul.ObserverOracle.ExpressionsReplay.StmtCodeShaped

abbrev expressionsReplayStmtListCodeShaped :=
  @Yul.ObserverOracle.ExpressionsReplay.StmtListCodeShaped

abbrev expressionsReplayStmtListCodeShapedAppend :=
  @Yul.ObserverOracle.ExpressionsReplay.StmtListCodeShaped_append

abbrev expressionsReplayStmtListToStructuredAppend :=
  @Yul.ObserverOracle.ExpressionsReplay.stmtList_toStructured_append

abbrev expressionsReplayCaseListCodeShaped :=
  @Yul.ObserverOracle.ExpressionsReplay.CaseListCodeShaped

abbrev expressionsReplayDefaultCodeShaped :=
  @Yul.ObserverOracle.ExpressionsReplay.DefaultCodeShaped

abbrev expressionsReplayProcCodeShaped :=
  @Yul.ObserverOracle.ExpressionsReplay.ProcCodeShaped

abbrev expressionsReplayProcListCodeShaped :=
  @Yul.ObserverOracle.ExpressionsReplay.ProcListCodeShaped

abbrev expressionsReplayProgramCodeShaped :=
  @Yul.ObserverOracle.ExpressionsReplay.ProgramCodeShaped

abbrev expressionsReplayOracleSafeExpr :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.Expr

abbrev expressionsReplayOracleSafeBlock :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.Block

abbrev expressionsReplayOracleSafeStmt :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.Stmt

abbrev expressionsReplayOracleSafeProc :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.Proc

abbrev expressionsReplayOracleSafeProcList :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.ProcList

abbrev expressionsReplayOracleSafeProgram :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.Program

abbrev expressionsReplayOracleSafeExprCodeShaped :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.exprCodeShaped

abbrev expressionsReplayOracleSafeBlockCodeShaped :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.blockCodeShaped

abbrev expressionsReplayOracleSafeStmtCodeShaped :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.stmtCodeShaped

abbrev expressionsReplayOracleSafeProcCodeShaped :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.procCodeShaped

abbrev expressionsReplayOracleSafeProcListCodeShaped :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.procListCodeShaped

abbrev expressionsReplayOracleSafeProgramCodeShaped :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.programCodeShaped

abbrev expressionsReplayOracleSafeBlockToStructured :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.blockToStructured

abbrev expressionsReplayOracleSafeStmtToStructured :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.stmtToStructured

abbrev expressionsReplayOracleSafeProgramBodyToStructured :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.programBodyToStructured

abbrev expressionsReplayOracleSafeBlockAppend :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.block_append

abbrev expressionsReplayOracleSafeCodeStmtBlock :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.codeStmtBlock

abbrev expressionsReplayOracleSafeCodeStmtBlockOfRunnerFrameObserverFree :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.codeStmtBlock_of_runnerFrame_observer_free

abbrev expressionsReplayOracleSafeStmtBlock :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.stmtBlock

abbrev expressionsReplayOracleSafeExprStmt :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.exprStmt

abbrev expressionsReplayOracleSafeExprBlock :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.exprBlock

abbrev expressionsReplayOracleSafeBrkStmt :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.brkStmt

abbrev expressionsReplayOracleSafeContStmt :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.contStmt

abbrev expressionsReplayOracleSafeLeaveStmt :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.leaveStmt

abbrev expressionsReplayOracleSafeTerminalStmt :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.terminalStmt

abbrev expressionsReplayOracleSafeBrkBlock :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.brkBlock

abbrev expressionsReplayOracleSafeContBlock :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.contBlock

abbrev expressionsReplayOracleSafeLeaveBlock :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.leaveBlock

abbrev expressionsReplayOracleSafeTerminalBlock :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.terminalBlock

abbrev expressionsReplayOracleSafeCodeStmtBrkBlock :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.codeStmtBrkBlock

abbrev expressionsReplayOracleSafeCodeStmtContBlock :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.codeStmtContBlock

abbrev expressionsReplayOracleSafeCodeStmtLeaveBlock :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.codeStmtLeaveBlock

abbrev expressionsReplayOracleSafeCodeStmtTerminalBlock :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.codeStmtTerminalBlock

abbrev expressionsReplayOracleSafeCleanupToBlock :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.cleanupToBlock

abbrev expressionsReplayOracleSafeCleanupToPreservingBlock :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.cleanupToPreservingBlock

abbrev expressionsReplayOracleSafeCleanupAllBlock :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.cleanupAllBlock

abbrev expressionsReplayOracleSafeCleanupToBrkBlock :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.cleanupToBrkBlock

abbrev expressionsReplayOracleSafeCleanupToContBlock :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.cleanupToContBlock

abbrev expressionsReplayOracleSafeCleanupToPreservingLeaveBlock :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.cleanupToPreservingLeaveBlock

abbrev expressionsReplayOracleSafeCleanupAllTerminalBlock :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.cleanupAllTerminalBlock

abbrev expressionsReplayOracleSafeFinishToBlock :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.finishToBlock

abbrev expressionsReplayOracleSafeFinishToPreservingBlock :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.finishToPreservingBlock

abbrev expressionsReplayOracleSafeFinishScopedBlock :=
  @Yul.ObserverOracle.ExpressionsReplay.OracleSafe.finishScopedBlock

abbrev expressionsReplayProcListCodeShapedOfLookup :=
  @Yul.ObserverOracle.ExpressionsReplay.ProcListCodeShaped.of_lookup?

abbrev expressionsReplayCaseListCodeShapedOfSelect :=
  @Yul.ObserverOracle.ExpressionsReplay.CaseListCodeShaped.of_select

abbrev expressionsReplayExprRunCodeExprWithOracle :=
  @Yul.ObserverOracle.ExpressionsReplay.Expr.runCodeExprWithOracle

abbrev expressionsReplayExprRunCodeConditionWithOracle :=
  @Yul.ObserverOracle.ExpressionsReplay.Expr.runCodeConditionWithOracle

abbrev expressionsReplayExprRunCodeExprWithOracleCodeEqStructured :=
  @Yul.ObserverOracle.ExpressionsReplay.Expr.runCodeExprWithOracle_code_eq_structured

abbrev expressionsReplayExprRunCodeConditionWithOracleCodeEqStructured :=
  @Yul.ObserverOracle.ExpressionsReplay.Expr.runCodeConditionWithOracle_code_eq_structured

abbrev expressionsReplayExprRunCodeExprWithOracleEqCompileOfCodeShaped :=
  @Yul.ObserverOracle.ExpressionsReplay.Expr.runCodeExprWithOracle_eq_compile_of_codeShaped

abbrev expressionsReplayExprRunCodeConditionWithOracleEqCompileOfCodeShaped :=
  @Yul.ObserverOracle.ExpressionsReplay.Expr.runCodeConditionWithOracle_eq_compile_of_codeShaped

abbrev expressionsReplayBlockRunWithOracleToStructuredOfCodeShaped :=
  @Yul.ObserverOracle.ExpressionsReplay.Block.runWithOracle_toStructured_of_codeShaped

abbrev expressionsReplayStmtRunForLoopWithOracleToStructuredOfCodeShaped :=
  @Yul.ObserverOracle.ExpressionsReplay.Stmt.runForLoopWithOracle_toStructured_of_codeShaped

abbrev expressionsReplayStmtRunWithOracleToStructuredOfCodeShaped :=
  @Yul.ObserverOracle.ExpressionsReplay.Stmt.runWithOracle_toStructured_of_codeShaped

abbrev expressionsReplayExprRunCodeExprWithOracleCodeOfRun :=
  @Yul.ObserverOracle.ExpressionsReplay.Expr.runCodeExprWithOracle_code_of_run

abbrev expressionsReplayExprRunCodeConditionWithOracleCodeOfRun :=
  @Yul.ObserverOracle.ExpressionsReplay.Expr.runCodeConditionWithOracle_code_of_run

abbrev expressionsReplayStmtRunCodeStmtWithOracle :=
  @Yul.ObserverOracle.ExpressionsReplay.Stmt.runCodeStmtWithOracle

abbrev expressionsReplayStmtRunCodeStmtWithOracleCodeOfRun :=
  @Yul.ObserverOracle.ExpressionsReplay.Stmt.runCodeStmtWithOracle_code_of_run

abbrev expressionsReplayStmtListRunCodeWithOracle :=
  @Yul.ObserverOracle.ExpressionsReplay.StmtList.runCodeWithOracle

abbrev expressionsReplayStmtListByteLength :=
  @Yul.ObserverOracle.ExpressionsReplay.StmtList.byteLength

abbrev expressionsReplayStmtListByteLengthAppend :=
  @Yul.ObserverOracle.ExpressionsReplay.StmtList.byteLength_append

abbrev expressionsReplayStmtListByteLengthCodeStmt :=
  @Yul.ObserverOracle.ExpressionsReplay.StmtList.byteLength_codeStmt

abbrev expressionsReplayStmtListRunCodeWithOracleNil :=
  @Yul.ObserverOracle.ExpressionsReplay.StmtList.runCodeWithOracle_nil

abbrev expressionsReplayStmtListRunCodeWithOracleAppend :=
  @Yul.ObserverOracle.ExpressionsReplay.StmtList.runCodeWithOracle_append

abbrev expressionsReplayStmtListRunCodeWithOracleAppendRegularOfRun :=
  @Yul.ObserverOracle.ExpressionsReplay.StmtList.runCodeWithOracle_append_regular_of_run

abbrev expressionsReplayStmtListRunCodeWithOracleCodeStmtOfRun :=
  @Yul.ObserverOracle.ExpressionsReplay.StmtList.runCodeWithOracle_codeStmt_of_run

abbrev expressionsReplayStmtListRunCodeWithOracleCodeStmtSourceRunNResultWithOracleSegmentOfRunnerSafe :=
  @Yul.ObserverOracle.ExpressionsReplay.StmtList.runCodeWithOracle_codeStmt_source_runNResultWithOracle_segment_of_runnerSafe

abbrev expressionsReplayStmtListRunCodeWithOracleCodeStmtSourceRunNResultWithOracleSegmentOfOracleStepPC :=
  @Yul.ObserverOracle.ExpressionsReplay.StmtList.runCodeWithOracle_codeStmt_source_runNResultWithOracle_segment_of_oracleStepPC

abbrev expressionsReplayStmtListRunCodeWithOracleCodeStmtSourceRunNResultWithOracleBindOfRunnerSafe :=
  @Yul.ObserverOracle.ExpressionsReplay.StmtList.runCodeWithOracle_codeStmt_source_runNResultWithOracle_bind_of_runnerSafe

abbrev expressionsReplayStmtListRunCodeWithOracleCodeStmtSourceRunNResultWithOracleBindOfOracleStepPC :=
  @Yul.ObserverOracle.ExpressionsReplay.StmtList.runCodeWithOracle_codeStmt_source_runNResultWithOracle_bind_of_oracleStepPC

abbrev expressionsReplayStmtListRunCodeWithOracleCodeStmtAppendOfRun :=
  @Yul.ObserverOracle.ExpressionsReplay.StmtList.runCodeWithOracle_codeStmt_append_of_run

abbrev expressionsReplayStmtListRunCodeWithOracleCleanupToScopeExists :=
  @Yul.ObserverOracle.ExpressionsReplay.StmtList.runCodeWithOracle_cleanupTo_scope_exists

abbrev expressionsReplayBlockRunWithOracle :=
  @Yul.ObserverOracle.ExpressionsReplay.Block.runWithOracle

abbrev expressionsReplayBlockRunWithOracleNil :=
  @Yul.ObserverOracle.ExpressionsReplay.Block.runWithOracle_nil

abbrev expressionsReplayBlockRunWithOracleConsRegularOfRuns :=
  @Yul.ObserverOracle.ExpressionsReplay.Block.runWithOracle_cons_regular_of_runs

abbrev expressionsReplayBlockRunWithOracleConsCodeStmtAppendRegularOfRuns :=
  @Yul.ObserverOracle.ExpressionsReplay.Block.runWithOracle_cons_codeStmt_append_regular_of_runs

abbrev expressionsReplayBlockRunWithOracleConsCodeStmtAppendRegularOfRunsSlack :=
  @Yul.ObserverOracle.ExpressionsReplay.Block.runWithOracle_cons_codeStmt_append_regular_of_runs_slack

abbrev expressionsReplayBlockRunWithOracleConsCodeStmtAppendRegularOfRunsRestSlack :=
  @Yul.ObserverOracle.ExpressionsReplay.Block.runWithOracle_cons_codeStmt_append_regular_of_runs_restSlack

abbrev expressionsReplayBlockRunWithOracleCodeStmtOfRun :=
  @Yul.ObserverOracle.ExpressionsReplay.Block.runWithOracle_codeStmt_of_run

abbrev expressionsReplayBlockRunWithOracleCodeStmtSourceRunNResultWithOracleSegmentOfRunnerSafe :=
  @Yul.ObserverOracle.ExpressionsReplay.Block.runWithOracle_codeStmt_source_runNResultWithOracle_segment_of_runnerSafe

abbrev expressionsReplayBlockRunWithOracleCodeStmtSourceRunNResultWithOracleSegmentOfOracleStepPC :=
  @Yul.ObserverOracle.ExpressionsReplay.Block.runWithOracle_codeStmt_source_runNResultWithOracle_segment_of_oracleStepPC

abbrev expressionsReplayBlockRunWithOracleCodeStmtSourceRunNResultWithOracleBindOfRunnerSafe :=
  @Yul.ObserverOracle.ExpressionsReplay.Block.runWithOracle_codeStmt_source_runNResultWithOracle_bind_of_runnerSafe

abbrev expressionsReplayBlockRunWithOracleCodeStmtSourceRunNResultWithOracleBindOfOracleStepPC :=
  @Yul.ObserverOracle.ExpressionsReplay.Block.runWithOracle_codeStmt_source_runNResultWithOracle_bind_of_oracleStepPC

abbrev expressionsReplayBlockRunWithOracleCleanupToScopeExists :=
  @Yul.ObserverOracle.ExpressionsReplay.Block.runWithOracle_cleanupTo_scope_exists

abbrev expressionsReplayStmtRunWithOracle :=
  @Yul.ObserverOracle.ExpressionsReplay.Stmt.runWithOracle

abbrev expressionsReplayStmtRunForLoopWithOracle :=
  @Yul.ObserverOracle.ExpressionsReplay.Stmt.runForLoopWithOracle

abbrev expressionsReplayStmtRunWithOracleCodeOfRun :=
  @Yul.ObserverOracle.ExpressionsReplay.Stmt.runWithOracle_code_of_run

abbrev expressionsReplayStmtRunWithOracleExprCodeOfRun :=
  @Yul.ObserverOracle.ExpressionsReplay.Stmt.runWithOracle_expr_code_of_run

abbrev expressionsReplayStmtRunWithOracleIfFalseOfCondition :=
  @Yul.ObserverOracle.ExpressionsReplay.Stmt.runWithOracle_if_false_of_condition

abbrev expressionsReplayStmtRunWithOracleIfTrueOfConditionBody :=
  @Yul.ObserverOracle.ExpressionsReplay.Stmt.runWithOracle_if_true_of_condition_body

abbrev expressionsReplayStmtRunWithOracleSwitchNoneOfScrutinee :=
  @Yul.ObserverOracle.ExpressionsReplay.Stmt.runWithOracle_switch_none_of_scrutinee

abbrev expressionsReplayStmtRunWithOracleSwitchSomeOfScrutineeBody :=
  @Yul.ObserverOracle.ExpressionsReplay.Stmt.runWithOracle_switch_some_of_scrutinee_body

abbrev expressionsReplayStmtRunWithOracleForRegularOfInitLoop :=
  @Yul.ObserverOracle.ExpressionsReplay.Stmt.runWithOracle_for_regular_of_init_loop

abbrev expressionsReplayStmtRunForLoopWithOracleFalseOfCondition :=
  @Yul.ObserverOracle.ExpressionsReplay.Stmt.runForLoopWithOracle_false_of_condition

abbrev expressionsReplayStmtRunForLoopWithOracleTrueBrkOfBody :=
  @Yul.ObserverOracle.ExpressionsReplay.Stmt.runForLoopWithOracle_true_brk_of_body

abbrev expressionsReplayStmtRunForLoopWithOracleTrueContOfBodyPostLoop :=
  @Yul.ObserverOracle.ExpressionsReplay.Stmt.runForLoopWithOracle_true_cont_of_body_post_loop

abbrev expressionsReplayStmtRunForLoopWithOracleTrueRegularOfBodyPostLoop :=
  @Yul.ObserverOracle.ExpressionsReplay.Stmt.runForLoopWithOracle_true_regular_of_body_post_loop

abbrev expressionsReplayBlockRunWithOracleMono :=
  @Yul.ObserverOracle.ExpressionsReplay.Block.runWithOracle_mono

abbrev expressionsReplayStmtRunForLoopWithOracleMono :=
  @Yul.ObserverOracle.ExpressionsReplay.Stmt.runForLoopWithOracle_mono

abbrev expressionsReplayStmtRunWithOracleMono :=
  @Yul.ObserverOracle.ExpressionsReplay.Stmt.runWithOracle_mono

abbrev sourceReplayRun :=
  @Yul.ObserverOracle.SourceReplay.Program.run

abbrev sourceReplayEvalGasCons :=
  @Yul.ObserverOracle.SourceReplay.Expr.eval_gas_cons

abbrev sourceReplayEvalMsizeCons :=
  @Yul.ObserverOracle.SourceReplay.Expr.eval_msize_cons

abbrev sourceReplayExprEvalLength :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Expr.eval_length

abbrev sourceReplayExprSeqEvalLength :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.ExprSeq.eval_length

abbrev stackOpDupObserverNone :=
  @EvmCompiler.Yul.ObserverOracle.stackOp_dup?_observer_none

abbrev stackOpSwapObserverNone :=
  @EvmCompiler.Yul.ObserverOracle.stackOp_swap?_observer_none

abbrev stackOpSwapContinuingStep :=
  @EvmCompiler.Yul.ObserverOracle.stackOp_swap?_continuingStep

abbrev sourceReplayExprRunCompiledCodeWithOracleOfEvalSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Expr.runCompiledCodeWithOracle_of_eval_sourceOwned

abbrev sourceReplayExprSeqRunCompiledCodeWithOracleOfEvalSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Expr.runCompiledSeqCodeWithOracle_of_eval_sourceOwned

abbrev sourceReplayExprOracleFrameSafeCompileCodeOfEvalSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Expr.oracleFrameSafe_compileCode_of_eval_sourceOwned

abbrev sourceReplayExprOracleFrameSafeCompileSeqCodeOfEvalSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Expr.oracleFrameSafe_compileSeqCode_of_eval_sourceOwned

abbrev sourceReplayExprOracleStepPCCompileCodeOfEvalSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Expr.oracleStepPC_compileCode_of_eval_sourceOwned

abbrev sourceReplayExprOracleStepPCCompileSeqCodeOfEvalSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Expr.oracleStepPC_compileSeqCode_of_eval_sourceOwned

abbrev sourceReplayExprOracleSafeCodeExprOfCompileCodeEvalSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Expr.oracleSafe_codeExpr_of_compileCode_eval_sourceOwned

abbrev sourceReplayExprOracleSafeCodeStmtOfCompileCodeEvalSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Expr.oracleSafe_codeStmt_of_compileCode_eval_sourceOwned

abbrev sourceReplayExprOracleSafeCodeExprOfCompileSeqCodeEvalSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Expr.oracleSafe_codeExpr_of_compileSeqCode_eval_sourceOwned

abbrev sourceReplayExprOracleSafeCodeStmtOfCompileSeqCodeEvalSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Expr.oracleSafe_codeStmt_of_compileSeqCode_eval_sourceOwned

abbrev sourceReplayExprEvalOfEvalOne :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Expr.eval_of_evalOne

abbrev sourceReplayExprRunCompiledCodeWithOracleOfEvalOneSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Expr.runCompiledCodeWithOracle_of_evalOne_sourceOwned

abbrev sourceReplayExprRunCompiledConditionWithOracleOfEvalConditionSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Expr.runCompiledConditionWithOracle_of_evalCondition_sourceOwned

abbrev sourceReplayExprRunCompiledExpressionsConditionWithOracleOfEvalConditionSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Expr.runCompiledExpressionsConditionWithOracle_of_evalCondition_sourceOwned

abbrev sourceReplaySwitchCompileSelectNone :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Switch.compile_select_none

abbrev sourceReplaySwitchCompileSelectSome :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Switch.compile_select_some

abbrev sourceReplaySwitchCompileSelectedOpenFinish :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Switch.compile_selected_open_finish

abbrev sourceReplayStmtCompileExprWithOracleOfEvalSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.compileExprWithOracle_of_eval_sourceOwned

abbrev sourceReplayStmtCompileLetWithOracleOfEvalOneSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.compileLetWithOracle_of_evalOne_sourceOwned

abbrev sourceReplayStmtCompileAssignWithOracleOfEvalOneSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.compileAssignWithOracle_of_evalOne_sourceOwned

abbrev sourceReplayStmtOracleSafeExprBlockOfCompileCodeEvalSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.oracleSafe_exprBlock_of_compileCode_eval_sourceOwned

abbrev sourceReplayStmtOracleSafeExprsBlockOfCompileSeqCodeEvalSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.oracleSafe_exprsBlock_of_compileSeqCode_eval_sourceOwned

abbrev sourceReplayStmtOracleSafeLetBlockOfCompileCodeEvalOneSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.oracleSafe_letBlock_of_compileCode_evalOne_sourceOwned

abbrev sourceReplayStmtOracleSafeAssignBlockOfCompileCodeEvalOneSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.oracleSafe_assignBlock_of_compileCode_evalOne_sourceOwned

abbrev sourceReplayStmtOracleSafeBrkBlockOfCleanup :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.oracleSafe_brkBlock_of_cleanup

abbrev sourceReplayStmtOracleSafeContBlockOfCleanup :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.oracleSafe_contBlock_of_cleanup

abbrev sourceReplayStmtOracleSafeLeaveBlockOfCleanup :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.oracleSafe_leaveBlock_of_cleanup

abbrev sourceReplayStmtOracleSafeTerminalBlockOfRelSafe :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.oracleSafe_terminalBlock_of_relSafe

abbrev sourceReplayStmtOracleSafeTerminalArgsBlockOfCompileSeqCodeEvalSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.oracleSafe_terminalArgsBlock_of_compileSeqCode_eval_sourceOwned

abbrev sourceReplayStmtCompileIfFalseWithOracleOfEvalConditionSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.compileIfFalseWithOracle_of_evalCondition_sourceOwned

abbrev sourceReplayStmtCompileIfTrueWithOracleOfEvalConditionSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.compileIfTrueWithOracle_of_evalCondition_sourceOwned

abbrev sourceReplayStmtCompileSwitchNoneWithOracleOfEvalOneSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.compileSwitchNoneWithOracle_of_evalOne_sourceOwned

abbrev sourceReplayStmtCompileIfTrueAtomicPrefixWithOracleOfEvalConditionSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.compileIfTrueAtomicPrefixWithOracle_of_evalCondition_sourceOwned

abbrev sourceReplayStmtCompileSwitchSomeAtomicPrefixWithOracleOfEvalOneSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.compileSwitchSomeAtomicPrefixWithOracle_of_evalOne_sourceOwned

abbrev sourceReplayStmtRunForLoopFalseWithOracleOfEvalConditionSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.runForLoopFalseWithOracle_of_evalCondition_sourceOwned

abbrev sourceReplayStmtRunForLoopTrueRegularWithOracleOfEvalConditionBodyPostLoop :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.runForLoopTrueRegularWithOracle_of_evalCondition_body_post_loop

abbrev sourceReplayStmtRunForLoopTrueBrkWithOracleOfEvalConditionBody :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.runForLoopTrueBrkWithOracle_of_evalCondition_body

abbrev sourceReplayStmtRunForLoopTrueContWithOracleOfEvalConditionBodyPostLoop :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.runForLoopTrueContWithOracle_of_evalCondition_body_post_loop

abbrev sourceReplayStmtRunForLoopRegularWithOracleOfRunForLoop :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.runForLoopRegularWithOracle_of_runForLoop

abbrev sourceReplayStmtRunForRegularWithOracleCleanupToScope :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.runForRegularWithOracle_cleanupTo_scope

abbrev sourceReplayStmtCompileForRegularWithOracleOfRunForLoop :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.compileForRegularWithOracle_of_runForLoop

abbrev sourceReplayStmtCompileForRegularWithOracleAtomicSwitchInitOfRunForLoop :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.compileForRegularWithOracle_atomicSwitchInit_of_runForLoop

abbrev sourceReplayStmtCompileForRegularWithOracleAtomicSwitchBlocksOfRunForLoop :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.compileForRegularWithOracle_atomicSwitchBlocks_of_runForLoop

abbrev sourceReplayBlockCompileOpenConsForRegularAtomicSwitchBlocksWithOracleOfRunForLoop :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_forRegularAtomicSwitchBlocksWithOracle_of_runForLoop

abbrev sourceReplayBlockCompileOpenConsForRegularAtomicSwitchBlocksSlackWithOracleOfRunForLoop :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_forRegularAtomicSwitchBlocksSlackWithOracle_of_runForLoop

abbrev sourceReplayBlockCompileOpenConsForRegularAtomicSwitchBlocksRestSlackWithOracleOfRunForLoop :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_forRegularAtomicSwitchBlocksRestSlackWithOracle_of_runForLoop

abbrev sourceReplayBlockCompileOpenSingletonForRegularAtomicSwitchBlocksWithOracleOfRunForLoop :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_singleton_forRegularAtomicSwitchBlocksWithOracle_of_runForLoop

abbrev sourceReplayStmtCompileExprStmtListWithOracleOfEvalSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.compileExprStmtListWithOracle_of_eval_sourceOwned

abbrev sourceReplayStmtCompileLetStmtListWithOracleOfEvalOneSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.compileLetStmtListWithOracle_of_evalOne_sourceOwned

abbrev sourceReplayStmtCompileAssignStmtListWithOracleOfEvalOneSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.compileAssignStmtListWithOracle_of_evalOne_sourceOwned

abbrev sourceReplayStmtRunRegularScope :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.run_regular_scope

abbrev sourceReplayBlockRunOpenRegularScope :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.runOpen_regular_scope

abbrev sourceReplayBlockRunOpenRegularCleanupScopeRel :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.runOpen_regular_cleanupScopeRel

abbrev sourceReplayBlockCompileOpenNilWithOracle :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_nilWithOracle

abbrev sourceReplayBlockOracleSafeCompileOpenNil :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.oracleSafe_compileOpen_nil

abbrev sourceReplayBlockOracleSafeCompileOpenConsOfStmtBlock :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.oracleSafe_compileOpen_cons_of_stmtBlock

abbrev sourceReplayBlockCompileOpenConsRegularWithOracleOfRuns :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_regularWithOracle_of_runs

abbrev sourceReplayBlockCompileOpenConsRegularBlockWithOracleOfRuns :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_regularBlockWithOracle_of_runs

abbrev sourceReplayBlockCompileOpenConsRegularBlockWithOracleOfRunsTargetFuel :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_regularBlockWithOracle_of_runs_targetFuel

abbrev sourceReplayBlockCompileOpenConsExprWithOracleOfEvalSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_exprWithOracle_of_eval_sourceOwned

abbrev sourceReplayBlockCompileOpenConsExprBlockWithOracleOfEvalSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_exprBlockWithOracle_of_eval_sourceOwned

abbrev sourceReplayBlockCompileOpenConsExprBlockRestSlackWithOracleOfEvalSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_exprBlockRestSlackWithOracle_of_eval_sourceOwned

abbrev sourceReplayBlockCompileOpenConsLetWithOracleOfEvalOneSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_letWithOracle_of_evalOne_sourceOwned

abbrev sourceReplayBlockCompileOpenConsLetBlockWithOracleOfEvalOneSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_letBlockWithOracle_of_evalOne_sourceOwned

abbrev sourceReplayBlockCompileOpenConsLetBlockRestSlackWithOracleOfEvalOneSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_letBlockRestSlackWithOracle_of_evalOne_sourceOwned

abbrev sourceReplayBlockCompileOpenConsAssignWithOracleOfEvalOneSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_assignWithOracle_of_evalOne_sourceOwned

abbrev sourceReplayBlockCompileOpenConsAssignBlockWithOracleOfEvalOneSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_assignBlockWithOracle_of_evalOne_sourceOwned

abbrev sourceReplayBlockCompileOpenConsAssignBlockRestSlackWithOracleOfEvalOneSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_assignBlockRestSlackWithOracle_of_evalOne_sourceOwned

abbrev sourceReplayBlockAtomicPrefix :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.AtomicPrefix

abbrev sourceReplayBlockRunOpenAtomicPrefixModeRegular :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.runOpen_atomicPrefix_mode_regular

abbrev sourceReplayBlockRunScopedAtomicPrefixModeRegular :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.runScoped_atomicPrefix_mode_regular

abbrev sourceReplayBlockOracleSafeCompileOpenAtomicPrefixOfRun :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.oracleSafe_compileOpen_atomicPrefix_of_run

abbrev sourceReplayBlockCompileOpenAtomicPrefixWithOracle :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_atomicPrefixWithOracle

abbrev sourceReplayBlockCompileOpenAtomicPrefixBlockWithOracle :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_atomicPrefixBlockWithOracle

abbrev sourceReplayBlockCompileOpenAtomicPrefixBlockWithCleanupWithOracle :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_atomicPrefixBlockWithCleanupWithOracle

abbrev sourceReplayBlockCompileScopedAtomicPrefixBlockWithOracle :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileScoped_atomicPrefixBlockWithOracle

abbrev sourceReplayBlockCompileScopedAtomicPrefixWithOracle :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileScoped_atomicPrefixWithOracle

abbrev sourceReplayStmtCompileBlockStmtListWithOracleOfRunScopedAtomicPrefix :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.compileBlockStmtListWithOracle_of_runScoped_atomicPrefix

abbrev sourceReplayStmtOracleSafeBlockStmtOfRunScopedAtomicPrefix :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Stmt.oracleSafe_blockStmt_of_runScoped_atomicPrefix

abbrev sourceReplayBlockCompileOpenConsBlockWithOracleOfRunScopedAtomicPrefix :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_blockWithOracle_of_runScoped_atomicPrefix

abbrev sourceReplayBlockOracleSafeCompileOpenConsBlockOfRunScopedAtomicPrefix :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.oracleSafe_compileOpen_cons_block_of_runScoped_atomicPrefix

abbrev sourceReplayBlockCompileOpenConsIfFalseWithOracleOfEvalConditionSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_ifFalseWithOracle_of_evalCondition_sourceOwned

abbrev sourceReplayBlockCompileOpenConsIfFalseSlackWithOracleOfEvalConditionSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_ifFalseSlackWithOracle_of_evalCondition_sourceOwned

abbrev sourceReplayBlockCompileOpenConsIfFalseRestSlackWithOracleOfEvalConditionSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_ifFalseRestSlackWithOracle_of_evalCondition_sourceOwned

abbrev sourceReplayBlockCompileOpenConsIfTrueRegularWithOracleOfEvalConditionSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_ifTrueRegularWithOracle_of_evalCondition_sourceOwned

abbrev sourceReplayBlockCompileOpenConsIfTrueAtomicPrefixWithOracleOfEvalConditionSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_ifTrueAtomicPrefixWithOracle_of_evalCondition_sourceOwned

abbrev sourceReplayBlockCompileOpenConsIfTrueAtomicPrefixRestSlackWithOracleOfEvalConditionSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_ifTrueAtomicPrefixRestSlackWithOracle_of_evalCondition_sourceOwned

abbrev sourceReplayBlockCompileOpenConsSwitchNoneSlackWithOracleOfEvalOneSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_switchNoneSlackWithOracle_of_evalOne_sourceOwned

abbrev sourceReplayBlockCompileOpenConsSwitchNoneRestSlackWithOracleOfEvalOneSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_switchNoneRestSlackWithOracle_of_evalOne_sourceOwned

abbrev sourceReplayBlockCompileOpenConsSwitchSomeAtomicPrefixWithOracleOfEvalOneSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_switchSomeAtomicPrefixWithOracle_of_evalOne_sourceOwned

abbrev sourceReplayBlockCompileOpenConsSwitchSomeAtomicPrefixRestSlackWithOracleOfEvalOneSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_switchSomeAtomicPrefixRestSlackWithOracle_of_evalOne_sourceOwned

abbrev sourceReplayBlockCompileOpenConsSwitchAtomicPrefixWithOracleOfEvalOneSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_cons_switchAtomicPrefixWithOracle_of_evalOne_sourceOwned

abbrev sourceReplayBlockCompileOpenSingletonIfTrueAtomicPrefixWithOracleOfEvalConditionSourceOwned :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_singleton_ifTrueAtomicPrefixWithOracle_of_evalCondition_sourceOwned

abbrev sourceReplayBlockAtomicIfPrefix :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.AtomicIfPrefix

abbrev sourceReplayBlockCompileOpenAtomicIfPrefixBlockWithOracle :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_atomicIfPrefixBlockWithOracle

abbrev sourceReplayBlockAtomicSwitchCases :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.AtomicSwitchCases

abbrev sourceReplayBlockAtomicSwitchDefault :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.AtomicSwitchDefault

abbrev sourceReplayBlockAtomicPrefixOfSwitchSelect :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.atomicPrefix_of_switch_select

abbrev sourceReplayBlockAtomicSwitchPrefix :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.AtomicSwitchPrefix

abbrev sourceReplayBlockAtomicSwitchForPrefixSlack :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.AtomicSwitchForPrefixSlack

abbrev sourceReplayBlockAtomicSwitchForPrefixSlackPos :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.atomicSwitchForPrefixSlack_pos

abbrev sourceReplayBlockRunOpenAtomicSwitchPrefixModeRegular :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.runOpen_atomicSwitchPrefix_mode_regular

abbrev sourceReplayBlockRunOpenAtomicSwitchPrefixModeRegularOfBlock :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.runOpen_atomicSwitchPrefix_mode_regular_of_block

abbrev sourceReplayBlockRunScopedAtomicSwitchPrefixModeRegular :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.runScoped_atomicSwitchPrefix_mode_regular

abbrev sourceReplayBlockRunScopedAtomicSwitchPrefixModeRegularOfBlock :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.runScoped_atomicSwitchPrefix_mode_regular_of_block

abbrev sourceReplayBlockRunForLoopAtomicSwitchPrefixModeRegular :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.runForLoop_atomicSwitchPrefix_mode_regular

abbrev sourceReplayBlockRunOpenAtomicSwitchForPrefixSlackModeRegular :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.runOpen_atomicSwitchForPrefixSlack_mode_regular

abbrev sourceReplayBlockCompileOpenAtomicSwitchForPrefixSlackBlockWithOracleOfRun :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_atomicSwitchForPrefixSlackBlockWithOracle_of_run

abbrev sourceReplayBlockCompileOpenAtomicSwitchForPrefixSlackBlockWithOracle :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_atomicSwitchForPrefixSlackBlockWithOracle

abbrev sourceReplayBlockCompileOpenAtomicSwitchPrefixBlockWithOracle :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_atomicSwitchPrefixBlockWithOracle

abbrev sourceReplayBlockCompileOpenAtomicSwitchPrefixBlockWithCleanupWithOracle :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_atomicSwitchPrefixBlockWithCleanupWithOracle

abbrev sourceReplayBlockCompileScopedAtomicSwitchPrefixBlockRegularWithOracle :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileScoped_atomicSwitchPrefixBlockRegularWithOracle

abbrev sourceReplayBlockCompileScopedAtomicSwitchPrefixBlockRegularWithOracleOfBlock :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileScoped_atomicSwitchPrefixBlockRegularWithOracle_of_block

abbrev sourceReplayBlockAtomicBlockPrefix :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.AtomicBlockPrefix

abbrev sourceReplayBlockCompileOpenAtomicBlockPrefixWithOracle :=
  @EvmCompiler.Yul.ObserverOracle.SourceReplay.Block.compileOpen_atomicBlockPrefixWithOracle

abbrev exprObserverFree :=
  @Yul.ObserverOracle.ExprObserverFree

abbrev exprSeqObserverFree :=
  @Yul.ObserverOracle.ExprSeqObserverFree

abbrev blockObserverFree :=
  @Yul.ObserverOracle.BlockObserverFree

abbrev stmtObserverFree :=
  @Yul.ObserverOracle.StmtObserverFree

abbrev stmtListObserverFree :=
  @Yul.ObserverOracle.StmtListObserverFree

abbrev blockObserverFreeOfSelect :=
  @Yul.ObserverOracle.blockObserverFree_of_select

abbrev sourceReplayExprObserverFreeMatchesSource :=
  @Yul.ObserverOracle.SourceReplay.Expr.eval_observerFree_matches_source

abbrev sourceReplayExprSeqObserverFreeMatchesSource :=
  @Yul.ObserverOracle.SourceReplay.ExprSeq.eval_observerFree_matches_source

abbrev sourceReplayEvalOneObserverFreeMatchesSource :=
  @Yul.ObserverOracle.SourceReplay.Expr.evalOne_observerFree_matches_source

abbrev sourceReplayEvalConditionObserverFreeMatchesSource :=
  @Yul.ObserverOracle.SourceReplay.Expr.evalCondition_observerFree_matches_source

abbrev sourceReplayBlockOpenObserverFreeMatchesSource :=
  @Yul.ObserverOracle.SourceReplay.Block.runOpen_observerFree_matches_source

abbrev sourceReplayBlockScopedObserverFreeMatchesSource :=
  @Yul.ObserverOracle.SourceReplay.Block.runScoped_observerFree_matches_source

abbrev sourceReplayStmtForLoopObserverFreeMatchesSource :=
  @Yul.ObserverOracle.SourceReplay.Stmt.runForLoop_observerFree_matches_source

abbrev sourceReplayStmtObserverFreeMatchesSource :=
  @Yul.ObserverOracle.SourceReplay.Stmt.run_observerFree_matches_source

abbrev sourceReplayProgramRunStateObserverFreeMatchesSource :=
  @Yul.ObserverOracle.SourceReplay.Program.runState_observerFree_matches_source

abbrev sourceReplayProgramRunObserverFreeMatchesSource :=
  @Yul.ObserverOracle.SourceReplay.Program.run_observerFree_matches_source

end ImportedYulResourceObserverBoundary

namespace FunctionsOpenCALLBoundary

noncomputable section

/-!
CALL/CREATE request-site and response-preservation vocabulary used by the
checked imported-Yul boundary below. Lower Functions-to-compiled-open checked
target and soundness roots stay in `OpenLowering` instead of being re-exported
as public `LayerAudit` endpoints.
-/

abbrev openExternalCallKindCallSiteEqOfArgs :=
  @Yul.OpenExternal.CallKind.callSite_eq_of_args

abbrev openExternalCreateKindCreateSiteEqOfArgs :=
  @Yul.OpenExternal.CreateKind.createSite_eq_of_args

abbrev openExternalOpenCallRel :=
  @Yul.OpenExternal.OpenCallRel

abbrev openExternalOpenCallRelPreservesResponse :=
  @Yul.OpenExternal.OpenCallRel.preserves_response

abbrev openExternalOpenCreateRel :=
  @Yul.OpenExternal.OpenCreateRel

abbrev openExternalOpenCreateRelPreservesResponse :=
  @Yul.OpenExternal.OpenCreateRel.preserves_response

end
end FunctionsOpenCALLBoundary

namespace ImportedYulOpenCALLBoundary

noncomputable section

/-!
Checked imported-Yul open CALL/CREATE boundary.

The public audit surface here pins the source-facing open-trace contract,
the shared external-world readiness predicate, the checked current-bounds
wrapper, and the canonical final endpoints. Lower checked-target decomposition
facts stay inside their proof modules instead of being exported as public audit
roots.
-/

abbrev sourceOpenDispatcherTraceAccepted :=
  @Yul.Program.SourceOpenDispatcherTraceAccepted

abbrev sourceOpenTraceExternalResponsesAdmissible :=
  @Yul.Reference.SourceBridgeFacts.SourceOpenTraceExternalResponsesAdmissible

abbrev openXBoundaryFamilySharedResponseExternalWorldReadyFor :=
  Yul.Program.OpenXBoundaryFamilySharedResponseExternalWorldReadyFor

theorem checkedImportedYulCallCreateCurrentNoCallReturnDataCopyBoundsReady
    {program : Yul.Program} {functionProgram : Functions.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    (hChecked :
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesCALLFamilyFeaturesSourceStaticRegularOpenAssemblyInferredBoundStackSafe?
          program =
        some (functionProgram, asm, target)) :
    Yul.OpenGasAware.OpenXBlockTraceRelReady.CurrentNoCallReturnDataCopyBoundsReady
      asm target :=
  Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesCALLFamilyFeaturesSourceStaticRegularOpenAssemblyInferredBoundStackSafe?_currentNoCallReturnDataCopyBoundsReady
    hChecked

theorem checkedImportedYulCallCreateFinalObservation
    {cfg : Yul.Reference.StateRelConfig}
    {program : Yul.Program} {functionProgram : Functions.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : Yul.EVMState}
    {referenceResult : Yul.Reference.Result}
    {trace : Yul.OpenExternal.OpenTrace}
    {sourceResult : Except Yul.Reference.Exception Yul.Reference.State}
    (hInitialCodeImageRel :
      Yul.Program.RecursiveBridgeInitialCodeImageRel cfg program target shared
        initial)
    (hSourceRun :
      Yul.Program.RecursiveBridgeSourceRun program shared store sourceFuel
        referenceResult)
    (hChecked :
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesCALLFamilyFeaturesSourceStaticRegularOpenAssemblyInferredBoundStackSafe?
          program =
        some (functionProgram, asm, target))
    (hTraceAccepted :
      Yul.Program.SourceOpenDispatcherTraceAccepted cfg program shared
        sourceFuel trace sourceResult)
    (hExternalWorldReady :
      Yul.Program.OpenXBoundaryFamilySharedResponseExternalWorldReadyFor
        asm target)
    (minimumCompilerFuel : Nat) :
    ∃ compilerFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ ctxAfter : Functions.Source.Ctx,
    ∃ programOutcome : Functions.Source.Outcome,
    ∃ targetFuel : Nat,
    ∃ targetResult : Assembly.StepResult,
    ∃ evmFuel : Nat,
    ∃ gasBound : Nat,
      program.toObjects? =
        some { root := Objects.Object.mk "root" functionProgram [] [] } ∧
      minimumCompilerFuel ≤ compilerFuel ∧
      Yul.OpenExternal.OpenResultResolves
        (Yul.Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured functionProgram
          Functions.Source.Ctx.initial compilerFuel functionProgram.body
          (Functions.Source.Program.initialState
            (Yul.Program.canonicalEntryState initial).toSharedState))
        trace (.ok (sourceOutcome, ctxAfter)) ∧
      Yul.Reference.SourceBridgeFacts.SourceResultOutcomeRel cfg []
        (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel cfg)
        (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        sourceResult sourceOutcome ∧
      Yul.OpenExternal.OpenResultResolves
        (Yul.Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Program.runState
          Locals.Source.PrimitiveSemantics.structured compilerFuel functionProgram
          (Functions.Source.Program.initialState
            (Yul.Program.canonicalEntryState initial).toSharedState))
        trace (.ok programOutcome) ∧
      Yul.OpenAssembly.OpenBlockTraceResult asm target targetFuel
        (Yul.Program.canonicalEntryState initial) trace targetResult ∧
      Yul.Program.OpenXContractLivenessAndSafetyFinalObservation target
        (Yul.Program.canonicalEntryState initial) trace targetResult evmFuel
        gasBound ∧
      Functions.Source.WholeProgramOutcomeRel programOutcome targetResult ∧
      Yul.Program.SourceOpenTargetCommittedObservationRel cfg shared
        (Yul.Program.canonicalEntryState initial) sourceResult targetResult :=
  Yul.Program.RecursiveBridgeCALLFamilyRegularOpenAssemblyInferredBoundStackSafeReturnDataCopyBoundsCanonicalEntryTopAssumptions.openXContractLivenessAndSafetyFinalObservation
    { initialCodeImageRel := hInitialCodeImageRel
      sourceRun := hSourceRun
      checked := hChecked }
    hTraceAccepted hExternalWorldReady minimumCompilerFuel

theorem checkedImportedYulCallCreateAtGas
    {cfg : Yul.Reference.StateRelConfig}
    {program : Yul.Program} {functionProgram : Functions.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : Yul.EVMState}
    {referenceResult : Yul.Reference.Result}
    {trace : Yul.OpenExternal.OpenTrace}
    {sourceResult : Except Yul.Reference.Exception Yul.Reference.State}
    (hInitialCodeImageRel :
      Yul.Program.RecursiveBridgeInitialCodeImageRel cfg program target shared
        initial)
    (hSourceRun :
      Yul.Program.RecursiveBridgeSourceRun program shared store sourceFuel
        referenceResult)
    (hChecked :
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesCALLFamilyFeaturesSourceStaticRegularOpenAssemblyInferredBoundStackSafe?
          program =
        some (functionProgram, asm, target))
    (hTraceAccepted :
      Yul.Program.SourceOpenDispatcherTraceAccepted cfg program shared
        sourceFuel trace sourceResult)
    (hExternalWorldReady :
      Yul.Program.OpenXBoundaryFamilySharedResponseExternalWorldReadyFor
        asm target)
    (minimumCompilerFuel gas : Nat) :
    ∃ compilerFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ ctxAfter : Functions.Source.Ctx,
    ∃ programOutcome : Functions.Source.Outcome,
    ∃ targetFuel : Nat,
    ∃ targetResult : Assembly.StepResult,
    ∃ evmFuel : Nat,
    ∃ gasBound : Nat,
      program.toObjects? =
        some { root := Objects.Object.mk "root" functionProgram [] [] } ∧
      minimumCompilerFuel ≤ compilerFuel ∧
      Yul.OpenExternal.OpenResultResolves
        (Yul.Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured functionProgram
          Functions.Source.Ctx.initial compilerFuel functionProgram.body
          (Functions.Source.Program.initialState
            (Yul.Program.canonicalEntryState initial).toSharedState))
        trace (.ok (sourceOutcome, ctxAfter)) ∧
      Yul.Reference.SourceBridgeFacts.SourceResultOutcomeRel cfg []
        (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel cfg)
        (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        sourceResult sourceOutcome ∧
      Yul.OpenExternal.OpenResultResolves
        (Yul.Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Program.runState
          Locals.Source.PrimitiveSemantics.structured compilerFuel functionProgram
          (Functions.Source.Program.initialState
            (Yul.Program.canonicalEntryState initial).toSharedState))
        trace (.ok programOutcome) ∧
      Yul.OpenAssembly.OpenBlockTraceResult asm target targetFuel
        (Yul.Program.canonicalEntryState initial) trace targetResult ∧
      Yul.Program.OpenXContractLivenessAndSafetyFinalObservation target
        (Yul.Program.canonicalEntryState initial) trace targetResult evmFuel
        gasBound ∧
      (gasBound ≤ gas →
        gas < EvmYul.UInt256.size →
          Yul.OpenGasAware.OpenXReplayAt target
            (Yul.Program.canonicalEntryState initial) trace targetResult evmFuel
            gas) ∧
      (gas < EvmYul.UInt256.size →
        Yul.OpenGasAware.OpenXCommittedSafeAt target
          (Yul.Program.canonicalEntryState initial) targetResult evmFuel gas) ∧
      Functions.Source.WholeProgramOutcomeRel programOutcome targetResult ∧
      Yul.Program.SourceOpenTargetCommittedObservationRel cfg shared
        (Yul.Program.canonicalEntryState initial) sourceResult targetResult :=
  Yul.Program.RecursiveBridgeCALLFamilyRegularOpenAssemblyInferredBoundStackSafeReturnDataCopyBoundsCanonicalEntryTopAssumptions.openXContractLivenessAndSafetyAtGas
    { initialCodeImageRel := hInitialCodeImageRel
      sourceRun := hSourceRun
      checked := hChecked }
    hTraceAccepted hExternalWorldReady minimumCompilerFuel gas

theorem checkedImportedYulCallCreateOutcomeSafetyAtGas
    {cfg : Yul.Reference.StateRelConfig}
    {program : Yul.Program} {functionProgram : Functions.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : Yul.EVMState}
    {referenceResult : Yul.Reference.Result}
    {trace : Yul.OpenExternal.OpenTrace}
    {sourceResult : Except Yul.Reference.Exception Yul.Reference.State}
    (hInitialCodeImageRel :
      Yul.Program.RecursiveBridgeInitialCodeImageRel cfg program target shared
        initial)
    (hSourceRun :
      Yul.Program.RecursiveBridgeSourceRun program shared store sourceFuel
        referenceResult)
    (hChecked :
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesCALLFamilyFeaturesSourceStaticRegularOpenAssemblyInferredBoundStackSafe?
          program =
        some (functionProgram, asm, target))
    (hTraceAccepted :
      Yul.Program.SourceOpenDispatcherTraceAccepted cfg program shared
        sourceFuel trace sourceResult)
    (hExternalWorldReady :
      Yul.Program.OpenXBoundaryFamilySharedResponseExternalWorldReadyFor
        asm target)
    (minimumCompilerFuel gas : Nat) :
    ∃ compilerFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ ctxAfter : Functions.Source.Ctx,
    ∃ programOutcome : Functions.Source.Outcome,
    ∃ targetFuel : Nat,
    ∃ targetResult : Assembly.StepResult,
    ∃ evmFuel : Nat,
    ∃ gasBound : Nat,
      program.toObjects? =
        some { root := Objects.Object.mk "root" functionProgram [] [] } ∧
      minimumCompilerFuel ≤ compilerFuel ∧
      Yul.OpenExternal.OpenResultResolves
        (Yul.Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured functionProgram
          Functions.Source.Ctx.initial compilerFuel functionProgram.body
          (Functions.Source.Program.initialState
            (Yul.Program.canonicalEntryState initial).toSharedState))
        trace (.ok (sourceOutcome, ctxAfter)) ∧
      Yul.Reference.SourceBridgeFacts.SourceResultOutcomeRel cfg []
        (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel cfg)
        (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        sourceResult sourceOutcome ∧
      Yul.OpenExternal.OpenResultResolves
        (Yul.Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Program.runState
          Locals.Source.PrimitiveSemantics.structured compilerFuel functionProgram
          (Functions.Source.Program.initialState
            (Yul.Program.canonicalEntryState initial).toSharedState))
        trace (.ok programOutcome) ∧
      Yul.OpenAssembly.OpenBlockTraceResult asm target targetFuel
        (Yul.Program.canonicalEntryState initial) trace targetResult ∧
      Yul.Program.OpenXContractLivenessAndSafetyFinalObservation target
        (Yul.Program.canonicalEntryState initial) trace targetResult evmFuel
        gasBound ∧
      (gasBound ≤ gas →
        gas < EvmYul.UInt256.size →
          Yul.OpenGasAware.OpenXReplayAt target
            (Yul.Program.canonicalEntryState initial) trace targetResult evmFuel
            gas) ∧
      (gas < EvmYul.UInt256.size →
        ∃ outcome :
          Except Yul.OpenGasAware.EVMException Yul.OpenGasAware.EVMResult,
          Yul.OpenGasAware.OpenXOutcomeResult
            (Assembly.GasAware.validJumps target) evmFuel
            (Assembly.GasAware.installCodeAndGas target gas
              (Yul.Program.canonicalEntryState initial))
            outcome ∧
          Assembly.GasAware.XRunOutcomeSafelyMatches targetResult outcome) ∧
      Functions.Source.WholeProgramOutcomeRel programOutcome targetResult ∧
      Yul.Program.SourceOpenTargetCommittedObservationRel cfg shared
        (Yul.Program.canonicalEntryState initial) sourceResult targetResult :=
  Yul.Program.RecursiveBridgeCALLFamilyRegularOpenAssemblyInferredBoundStackSafeReturnDataCopyBoundsCanonicalEntryTopAssumptions.openXContractLivenessAndSafetyOutcomeSafetyAtGas
    { initialCodeImageRel := hInitialCodeImageRel
      sourceRun := hSourceRun
      checked := hChecked }
    hTraceAccepted hExternalWorldReady minimumCompilerFuel gas

theorem checkedImportedYulCallCreateResultOrFailureAtGas
    {cfg : Yul.Reference.StateRelConfig}
    {program : Yul.Program} {functionProgram : Functions.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {sourceFuel : Nat} {initial : Yul.EVMState}
    {referenceResult : Yul.Reference.Result}
    {trace : Yul.OpenExternal.OpenTrace}
    {sourceResult : Except Yul.Reference.Exception Yul.Reference.State}
    (hInitialCodeImageRel :
      Yul.Program.RecursiveBridgeInitialCodeImageRel cfg program target shared
        initial)
    (hSourceRun :
      Yul.Program.RecursiveBridgeSourceRun program shared store sourceFuel
        referenceResult)
    (hChecked :
      Yul.Program.compileCheckedAssemblyTargetBytecodeResourcesCALLFamilyFeaturesSourceStaticRegularOpenAssemblyInferredBoundStackSafe?
          program =
        some (functionProgram, asm, target))
    (hTraceAccepted :
      Yul.Program.SourceOpenDispatcherTraceAccepted cfg program shared
        sourceFuel trace sourceResult)
    (hExternalWorldReady :
      Yul.Program.OpenXBoundaryFamilySharedResponseExternalWorldReadyFor
        asm target)
    (minimumCompilerFuel gas : Nat) :
    ∃ compilerFuel : Nat,
    ∃ sourceOutcome : Objects.Source.Outcome,
    ∃ ctxAfter : Functions.Source.Ctx,
    ∃ programOutcome : Functions.Source.Outcome,
    ∃ targetFuel : Nat,
    ∃ targetResult : Assembly.StepResult,
    ∃ evmFuel : Nat,
    ∃ gasBound : Nat,
      program.toObjects? =
        some { root := Objects.Object.mk "root" functionProgram [] [] } ∧
      minimumCompilerFuel ≤ compilerFuel ∧
      Yul.OpenExternal.OpenResultResolves
        (Yul.Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Block.runOpen
          Locals.Source.PrimitiveSemantics.structured functionProgram
          Functions.Source.Ctx.initial compilerFuel functionProgram.body
          (Functions.Source.Program.initialState
            (Yul.Program.canonicalEntryState initial).toSharedState))
        trace (.ok (sourceOutcome, ctxAfter)) ∧
      Yul.Reference.SourceBridgeFacts.SourceResultOutcomeRel cfg []
        (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel cfg)
        (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel cfg)
        sourceResult sourceOutcome ∧
      Yul.OpenExternal.OpenResultResolves
        (Yul.Reference.SourceBridgeFacts.CompilerOpen.FunctionsOpen.Program.runState
          Locals.Source.PrimitiveSemantics.structured compilerFuel functionProgram
          (Functions.Source.Program.initialState
            (Yul.Program.canonicalEntryState initial).toSharedState))
        trace (.ok programOutcome) ∧
      Yul.OpenAssembly.OpenBlockTraceResult asm target targetFuel
        (Yul.Program.canonicalEntryState initial) trace targetResult ∧
      Yul.Program.OpenXContractLivenessAndSafetyFinalObservation target
        (Yul.Program.canonicalEntryState initial) trace targetResult evmFuel
        gasBound ∧
      (gasBound ≤ gas →
        gas < EvmYul.UInt256.size →
          Yul.OpenGasAware.OpenXReplayAt target
            (Yul.Program.canonicalEntryState initial) trace targetResult evmFuel
            gas) ∧
      (gas < EvmYul.UInt256.size →
        ((∃ result : EvmYul.EVM.ExecutionResult Yul.EVMState,
          Yul.OpenGasAware.OpenXOutcomeResult
            (Assembly.GasAware.validJumps target) evmFuel
            (Assembly.GasAware.installCodeAndGas target gas
              (Yul.Program.canonicalEntryState initial))
            (.ok result) ∧
          Assembly.GasAware.XResultCommittedObservation result =
            Assembly.GasAware.XTargetCommittedObservation targetResult) ∨
          (∃ outcome :
            Except Yul.OpenGasAware.EVMException Yul.OpenGasAware.EVMResult,
            Yul.OpenGasAware.OpenXOutcomeResult
              (Assembly.GasAware.validJumps target) evmFuel
              (Assembly.GasAware.installCodeAndGas target gas
                (Yul.Program.canonicalEntryState initial))
              outcome ∧
            Assembly.GasAware.XRunOutcomeFails outcome))) ∧
      Functions.Source.WholeProgramOutcomeRel programOutcome targetResult ∧
      Yul.Program.SourceOpenTargetCommittedObservationRel cfg shared
        (Yul.Program.canonicalEntryState initial) sourceResult targetResult :=
  Yul.Program.RecursiveBridgeCALLFamilyRegularOpenAssemblyInferredBoundStackSafeReturnDataCopyBoundsCanonicalEntryTopAssumptions.openXContractLivenessAndSafetyResultOrFailureAtGas
    { initialCodeImageRel := hInitialCodeImageRel
      sourceRun := hSourceRun
      checked := hChecked }
    hTraceAccepted hExternalWorldReady minimumCompilerFuel gas

end
end ImportedYulOpenCALLBoundary

namespace ImportedYulBoundary

private abbrev recursiveBridgeTopToGasAwareEVMUserCallResult :=
  @Yul.Program.compileStackGuardedReturnDataCopyBounds?_runResult_existsSourceRun_exprUserCallResultContracts_sufficientGas_X

private abbrev recursiveBridgeTopToGasAwareEVMUserCallResultNoOutOfGas :=
  @Yul.Program.compileStackGuardedReturnDataCopyBounds?_runResult_existsSourceRun_exprUserCallResultContracts_sufficientGas_no_out_of_gas_X

private abbrev recursiveBridgeTopToGasAwareEVMStackGuardedPlannedPreallocNoCallCreate :=
  @Yul.Program.compileStackGuardedReturnDataCopyBoundsPlannedPrealloc?_noCallCreate

private abbrev recursiveBridgeTopToGasAwareEVMStackGuardedPlannedPreallocReturnDataCopyBounds :=
  @Yul.Program.compileStackGuardedReturnDataCopyBoundsPlannedPrealloc?_blockPathReturnDataCopyBounds

private abbrev recursiveBridgeTopToGasAwareEVMStackGuardedNoOutOfFuel :=
  @Yul.Program.compileStackGuardedReturnDataCopyBoundsPlannedPrealloc?_runResult_existsSourceRun_exprNoOutOfFuelContracts_sufficientGas_X

namespace PublicSpineRegression

noncomputable section

/-!
These examples are public-spine tripwires. The explicit exact-live-layout roots
must still consume the live no-internal-CALL checked compile gate plus inferred
assembly stack-bound check, exact hidden-frame-word source check, and executable
max-live-layout-width source check. The short top roots are the stack-guarded
surface and must consume only the stack-guarded compile result plus the named
fallback scratch policy.
-/

example
    {cfg : Yul.Reference.StateRelConfig}
    {program : Yul.Program}
    (hExprNoSuccessfulOutOfFuel :
      Yul.Program.RecursiveBridgeExprNoOutOfFuelContracts cfg program) :
    Yul.Program.RecursiveBridgeSemanticCoreContracts cfg
      (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
        cfg)
      (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel
        cfg)
      Locals.Source.PrimitiveSemantics.structured program :=
  Yul.Program.RecursiveBridgeSemanticCoreContracts.structured_canonical_of_exprNoOutOfFuel
    hExprNoSuccessfulOutOfFuel

example
    {cfg : Yul.Reference.StateRelConfig}
    {program : Yul.Program}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    (hExprNoSuccessfulOutOfFuel :
      Yul.Program.RecursiveBridgeExprNoOutOfFuelContracts cfg program) :
    Yul.Program.RecursiveBridgeSemanticContracts cfg
      (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
        cfg)
      (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel
        cfg)
      Locals.Source.PrimitiveSemantics.structured
      (Yul.Program.RecursiveBridgeSemanticContracts.dispatcherOutcomeRel cfg
        (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalTerminalRel
          cfg)
        (Yul.Program.RecursiveBridgeTerminalObservationContracts.canonicalRevertRel
          cfg)
        program (EvmYul.Yul.State.Ok shared store))
      program shared store :=
  Yul.Program.RecursiveBridgeSemanticContracts.structured_canonical_of_exprNoOutOfFuel
    hExprNoSuccessfulOutOfFuel

example
    {cfg : Yul.Reference.StateRelConfig}
    {program : Yul.Program} :
    Yul.Program.RecursiveBridgeExprNoUserCallResultContracts cfg program :=
  Yul.Program.RecursiveBridgeExprNoUserCallResultContracts.derived

example
    {cfg : Yul.Reference.StateRelConfig}
    {program : Yul.Program}
    (hExprResultContracts :
      Yul.Program.RecursiveBridgeExprResultContracts cfg program) :
    Yul.Program.RecursiveBridgeExprNoOutOfFuelContracts cfg program :=
  Yul.Program.RecursiveBridgeExprNoOutOfFuelContracts.of_resultContracts
    hExprResultContracts

example
    {cfg : Yul.Reference.StateRelConfig}
    {program : Yul.Program}
    (hExprNoSuccessfulOutOfFuel :
      Yul.Program.RecursiveBridgeExprNoOutOfFuelContracts cfg program) :
    Yul.Program.RecursiveBridgeExprResultContracts cfg program :=
  hExprNoSuccessfulOutOfFuel.to_resultContracts

example
    {state state' : Yul.Fresh.State} {expr : Yul.AstExpr}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    (hLower : Yul.Expr.lower1? state expr = some (pre, lower, state'))
    (hPre :
      Yul.Reference.SourceBridgeFacts.GeneratedPrelude pre) :
    Yul.Reference.SourceBridgeFacts.ExprNoUserCalls expr :=
  Yul.Reference.SourceBridgeFacts.exprNoUserCalls_of_lower1?_generatedPrelude
    hLower hPre

example
    {state state' : Yul.Fresh.State} {expr : Yul.AstExpr}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    (hLower : Yul.Expr.lower1? state expr = some (pre, lower, state'))
    (hNoCall :
      Functions.LiveLayout.NoInternalCall.StmtList.Holds pre) :
    Yul.Reference.SourceBridgeFacts.ExprNoUserCalls expr :=
  Yul.Reference.SourceBridgeFacts.exprNoUserCalls_of_lower1?_noInternalCall
    hLower hNoCall

example
    {cfg : Yul.Reference.StateRelConfig} {layout : List Yul.Name}
    {contract : Yul.AstContract} {fuel : Nat}
    {state state' : Yul.Fresh.State} {expr : Yul.AstExpr}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    (hLower : Yul.Expr.lower1? state expr = some (pre, lower, state'))
    (hNoCall :
      Functions.LiveLayout.NoInternalCall.StmtList.Holds pre)
    (hSafe : Yul.Reference.Safe.expr expr)
    (hScoped : Yul.Reference.SourceBridgeFacts.SourceExprScoped layout expr)
    (hOk :
      Yul.Reference.SourceBridgeFacts.UserCallArity.ExprOk contract expr) :
    Yul.Reference.SourceBridgeFacts.ExprEvalResultOkAt cfg layout fuel expr
      (some contract) :=
  Yul.Reference.SourceBridgeFacts.exprEvalResultOkAt_of_lower1?_noInternalCall
    hLower hNoCall hSafe hScoped hOk

example
    {cfg : Yul.Reference.StateRelConfig} {layout : List Yul.Name}
    {contract : Yul.AstContract} {fuel : Nat} {expr : Yul.AstExpr}
    (hSafe : Yul.Reference.Safe.expr expr)
    (hScoped : Yul.Reference.SourceBridgeFacts.SourceExprScoped layout expr)
    (hOk :
      Yul.Reference.SourceBridgeFacts.UserCallArity.ExprOk contract expr)
    (hNoUser : Yul.Reference.SourceBridgeFacts.ExprNoUserCalls expr) :
    Yul.Reference.SourceBridgeFacts.ExprEvalResultOkAt cfg layout fuel expr
      (some contract) :=
  Yul.Reference.SourceBridgeFacts.exprEvalResultOkAt_of_noUserCalls
    hSafe hScoped hOk hNoUser

example
    {cfg : Yul.Reference.StateRelConfig} {layout : List Yul.Name}
    {contract : Yul.AstContract} {fuel : Nat}
    {cond : Yul.AstExpr} {body : List Yul.AstStmt}
    (hSafe : Yul.Reference.Safe.expr cond)
    (hScoped : Yul.Reference.SourceBridgeFacts.SourceExprScoped layout cond)
    (hOk :
      Yul.Reference.SourceBridgeFacts.UserCallArity.ExprOk contract cond)
    (hNoUser :
      Yul.Reference.SourceBridgeFacts.StmtNoUserCalls (.If cond body)) :
    Yul.Reference.SourceBridgeFacts.ExprEvalResultOkAt cfg layout fuel cond
      (some contract) :=
  Yul.Reference.SourceBridgeFacts.exprEvalResultOkAt_of_stmtNoUser_if
    hSafe hScoped hOk hNoUser

example
    {cfg : Yul.Reference.StateRelConfig} {layout : List Yul.Name}
    {contract : Yul.AstContract} {fuel : Nat}
    {cond : Yul.AstExpr} {post body : List Yul.AstStmt}
    (hSafe : Yul.Reference.Safe.expr cond)
    (hScoped : Yul.Reference.SourceBridgeFacts.SourceExprScoped layout cond)
    (hOk :
      Yul.Reference.SourceBridgeFacts.UserCallArity.ExprOk contract cond)
    (hNoUser :
      Yul.Reference.SourceBridgeFacts.StmtNoUserCalls (.For cond post body)) :
    Yul.Reference.SourceBridgeFacts.ExprEvalResultOkAt cfg layout fuel cond
      (some contract) :=
  Yul.Reference.SourceBridgeFacts.exprEvalResultOkAt_of_stmtNoUser_for
    hSafe hScoped hOk hNoUser

example
    {cfg : Yul.Reference.StateRelConfig} {layout : List Yul.Name}
    {contract : Yul.AstContract} {fuel : Nat}
    {scrutinee : Yul.AstExpr}
    {cases : List (Yul.Word × List Yul.AstStmt)}
    {defaultBody : List Yul.AstStmt}
    (hSafe : Yul.Reference.Safe.expr scrutinee)
    (hScoped :
      Yul.Reference.SourceBridgeFacts.SourceExprScoped layout scrutinee)
    (hOk :
      Yul.Reference.SourceBridgeFacts.UserCallArity.ExprOk contract scrutinee)
    (hNoUser :
      Yul.Reference.SourceBridgeFacts.StmtNoUserCalls
        (.Switch scrutinee cases defaultBody)) :
    Yul.Reference.SourceBridgeFacts.ExprEvalResultOkAt cfg layout fuel
      scrutinee (some contract) :=
  Yul.Reference.SourceBridgeFacts.exprEvalResultOkAt_of_stmtNoUser_switch
    hSafe hScoped hOk hNoUser

example
    {fuel : Nat} {state state' : Yul.Fresh.State}
    {stmt : Yul.AstStmt} {lower : List Functions.Stmt}
    (hLower :
      Yul.Stmt.toFunctionsListFuel? fuel state stmt = some (lower, state'))
    (hNoCall :
      Functions.LiveLayout.NoInternalCall.StmtList.Holds lower) :
    Yul.Reference.SourceBridgeFacts.StmtNoUserCalls stmt :=
  Yul.Reference.SourceBridgeFacts.stmtNoUserCalls_of_toFunctionsListFuel?_noInternalCall
    hLower hNoCall

example
    {fuel : Nat} {state state' : Yul.Fresh.State}
    {stmts : List Yul.AstStmt} {lower : Functions.Block}
    (hLower :
      Yul.Stmt.List.toBlockFuel? fuel state stmts = some (lower, state'))
    (hNoCall :
      Functions.LiveLayout.NoInternalCall.Block.Holds lower) :
    Yul.Reference.SourceBridgeFacts.StmtsNoUserCalls stmts :=
  Yul.Reference.SourceBridgeFacts.stmtsNoUserCalls_of_toBlockFuel?_noInternalCall
    hLower hNoCall

example
    {fuel : Nat} {state state' : Yul.Fresh.State}
    {cases : List (Yul.Word × List Yul.AstStmt)}
    {lower : List (Yul.Word × Functions.Block)}
    (hLower :
      Yul.Stmt.CaseList.toFunctionsFuel? fuel state cases =
        some (lower, state'))
    (hNoCall :
      Functions.LiveLayout.NoInternalCall.CaseList.Holds lower) :
    Yul.Reference.SourceBridgeFacts.CasesNoUserCalls cases :=
  Yul.Reference.SourceBridgeFacts.casesNoUserCalls_of_toFunctionsFuel?_noInternalCall
    hLower hNoCall

private abbrev recursiveBridgeNoUserStmtFrontierAdapter :=
  @EvmCompiler.Yul.Reference.SourceBridgeFacts.checkedStmtBlockLoweringSoundWhenFreshNamesAtExact_of_programAccepted_frontier_noUser_reserved_supported

private abbrev recursiveBridgeNoUserIfSeqFrontierAdapter :=
  @EvmCompiler.Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_frontier_if_recursive_noUser_reserved_supported

private abbrev recursiveBridgeNoUserForSeqFrontierAdapter :=
  @EvmCompiler.Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_frontier_for_recursive_noUser_reserved_supported

private abbrev recursiveBridgeNoUserSwitchSeqFrontierAdapter :=
  @EvmCompiler.Yul.Reference.SourceBridgeFacts.checkedSeqLoweringSoundWhenFreshNamesAtCompileFuelHiddenCtx_cons_frontier_switch_recursive_noUser_reserved_supported

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {cfg : Yul.Reference.StateRelConfig}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : Yul.EVMState}
    {referenceResult : Yul.Reference.Result}
    (hExprUserCallResultContracts :
      Yul.Program.RecursiveBridgeExprUserCallResultContracts cfg program)
    (hInitialCodeImageRel :
      Yul.Program.RecursiveBridgeInitialCodeImageRel cfg program target shared
        initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        Yul.Program.RecursiveBridgeSourceRun program shared store sourceFuel
          referenceResult)
    (hCheckedCompileTarget :
      Yul.Program.compileStackGuardedReturnDataCopyBounds?
          range program =
        some (asm, target))
    (hBoundary :
      Yul.Program.StackGuardedReturnDataCopyBoundsFallbackScratchReady range
        program initial)
    (hInitialPerm : initial.executionEnv.perm = true) :
  Yul.Program.StackGuardedSufficientGasConclusion cfg range program asm target
      shared store initial referenceResult :=
  recursiveBridgeTopToGasAwareEVMUserCallResult hSpec
    hExprUserCallResultContracts hInitialCodeImageRel hSourceFuelRun
    hCheckedCompileTarget hBoundary hInitialPerm

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {cfg : Yul.Reference.StateRelConfig}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {program : Yul.Program}
    {asm : Assembly.Program} {target : Assembly.TargetProgram}
    {shared : EvmYul.SharedState .Yul}
    {store : EvmYul.Yul.VarStore}
    {initial : Yul.EVMState}
    {referenceResult : Yul.Reference.Result}
    (hExprUserCallResultContracts :
      Yul.Program.RecursiveBridgeExprUserCallResultContracts cfg program)
    (hInitialCodeImageRel :
      Yul.Program.RecursiveBridgeInitialCodeImageRel cfg program target shared
        initial)
    (hSourceFuelRun :
      ∃ sourceFuel,
        Yul.Program.RecursiveBridgeSourceRun program shared store sourceFuel
          referenceResult)
    (hCheckedCompileTarget :
      Yul.Program.compileStackGuardedReturnDataCopyBounds?
          range program =
        some (asm, target))
    (hBoundary :
      Yul.Program.StackGuardedReturnDataCopyBoundsFallbackScratchReady range
        program initial)
    (hInitialPerm : initial.executionEnv.perm = true) :
  Yul.Program.StackGuardedNoOutOfGasConclusion cfg range program asm target
      shared store initial referenceResult :=
  recursiveBridgeTopToGasAwareEVMUserCallResultNoOutOfGas hSpec
    hExprUserCallResultContracts hInitialCodeImageRel hSourceFuelRun
    hCheckedCompileTarget hBoundary hInitialPerm

example
    {program : Yul.Program} {maxFrames : Nat}
    {hResource : Yul.Program.RecursiveBridgeSourceResourceBound program
      maxFrames}
    {active layout : List Yul.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source source' : Functions.Source.State}
    {baseState baseState' : Structured.RunState}
    {state : Yul.EVMState} {tokens : List Yul.Word}
    (hBase :
      Functions.CallDepth.SourceDirectBaseContext
        hResource.lowerObj.toFunctions active layout hiddenReturns source
        baseState)
    (hActive :
      Functions.CallDepth.Ranked.SourceCallDepth.ActiveStackWitness
        hResource.lowerObj.toFunctions maxFrames active)
    (hRel :
      Functions.SourceDirect.StateRel layout hiddenReturns source'
        baseState')
    (hFrameRel :
      Structured.Preservation.Frame.StateRel baseState' state tokens) :
    Yul.Program.RecursiveBridgeSourceDirectActiveResourcePoint hResource
      state :=
  Yul.Program.RecursiveBridgeSourceDirectActiveResourcePoint.of_base_withStateRel
    hBase hActive hRel hFrameRel

example
    {program : Yul.Program} {maxFrames : Nat}
    {hResource : Yul.Program.RecursiveBridgeSourceResourceBound program
      maxFrames}
    {active layout layout' returns : List Yul.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source source' : Functions.Source.State}
    {baseState target' : Structured.RunState}
    {state : Yul.EVMState} {tokens : List Yul.Word}
    (hBase :
      Functions.CallDepth.SourceDirectBaseContext
        hResource.lowerObj.toFunctions active layout hiddenReturns source
        baseState)
    (hActive :
      Functions.CallDepth.Ranked.SourceCallDepth.ActiveStackWitness
        hResource.lowerObj.toFunctions maxFrames active)
    (hLayout' : layout'.length ≤ 16)
    (hRel :
      Functions.SourceDirect.BlockScopedOutcomeRel returns layout'
        hiddenReturns
        (Functions.Source.Outcome.regular source')
        (Structured.Outcome.regular target'))
    (hFrameRel :
      Structured.Preservation.Frame.StateRel target' state tokens) :
    Yul.Program.RecursiveBridgeSourceDirectActiveResourcePoint hResource
      state :=
  Yul.Program.RecursiveBridgeSourceDirectActiveResourcePoint.of_regularBlockScopedOutcomeRel
    hBase hActive hLayout' hRel hFrameRel

example
    {program : Yul.Program} {maxFrames : Nat}
    {hResource : Yul.Program.RecursiveBridgeSourceResourceBound program
      maxFrames}
    {active layout returns : List Yul.Name} {retc : Nat}
    {hiddenReturns : List Structured.ReturnDest}
    {source source' : Functions.Source.State}
    {baseState target' : Structured.RunState}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {state : Yul.EVMState} {tokens : List Yul.Word}
    (hBase :
      Functions.CallDepth.SourceDirectBaseContext
        hResource.lowerObj.toFunctions active layout hiddenReturns source
        baseState)
    (hActive :
      Functions.CallDepth.Ranked.SourceCallDepth.ActiveStackWitness
        hResource.lowerObj.toFunctions maxFrames active)
    (hLayout' : targetCtx.layout.length ≤ 16)
    (hRel :
      Functions.SourceDirect.BlockOpenResultRel retc returns hiddenReturns
        (Functions.Source.Outcome.regular source', sourceCtx)
        (Structured.Outcome.regular target', targetCtx))
    (hFrameRel :
      Structured.Preservation.Frame.StateRel target' state tokens) :
    Yul.Program.RecursiveBridgeSourceDirectActiveResourcePoint hResource
      state :=
  Yul.Program.RecursiveBridgeSourceDirectActiveResourcePoint.of_regularBlockOpenResultRel
    hBase hActive hLayout' hRel hFrameRel

example
    {program : Yul.Program} {maxFrames : Nat}
    {hResource : Yul.Program.RecursiveBridgeSourceResourceBound program
      maxFrames}
    {callerLayout : List Yul.Name}
    {callerSource calleeSource : Functions.Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {state : Yul.EVMState} {tokens : List Yul.Word}
    {callee : Yul.Name} {calleeFn : Functions.FunDef} {retc : Nat}
    (hCaller :
      Functions.CallDepth.SourceDirectBaseContext
        hResource.lowerObj.toFunctions [] callerLayout [] callerSource
        callerTarget)
    (hRoot :
      callee ∈
        Functions.CallDepth.Program.mainInternalCalls
          hResource.lowerObj.toFunctions)
    (hCalleeFind :
      Functions.FunList.find? callee
          hResource.lowerObj.toFunctions.functions =
        some calleeFn)
    (hCalleeBound :
      Functions.SourceDirect.FrameBound.FunDef calleeFn)
    (hActive :
      Functions.CallDepth.Ranked.SourceCallDepth.ActiveStackWitness
        hResource.lowerObj.toFunctions maxFrames [callee])
    (hRel :
      Functions.SourceDirect.StateRel
        (Functions.SourceDirect.FunDef.targetBodyCtx calleeFn).layout
        [{ callerStack := callerTarget.evm.stack, retc := retc }]
        calleeSource calleeTarget)
    (hFrameRel :
      Structured.Preservation.Frame.StateRel calleeTarget state tokens) :
    Yul.Program.RecursiveBridgeSourceDirectActiveResourcePoint hResource
      state :=
  Yul.Program.RecursiveBridgeSourceDirectActiveResourcePoint.rootCallBodyTargetCtx
    hCaller hRoot hCalleeFind hCalleeBound hActive hRel hFrameRel

example
    {program : Yul.Program} {maxFrames : Nat}
    {hResource : Yul.Program.RecursiveBridgeSourceResourceBound program
      maxFrames}
    {active callerLayout : List Yul.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {callerSource calleeSource : Functions.Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {state : Yul.EVMState} {tokens : List Yul.Word}
    {caller callee : Yul.Name} {callerFn calleeFn : Functions.FunDef}
    {retc : Nat}
    (hCallerContext :
      Functions.CallDepth.SourceDirectBaseContext
        hResource.lowerObj.toFunctions active callerLayout hiddenReturns
        callerSource callerTarget)
    (hCaller : active.getLast? = some caller)
    (hCallerFind :
      Functions.FunList.find? caller
          hResource.lowerObj.toFunctions.functions =
        some callerFn)
    (hCall :
      callee ∈ Functions.CallDepth.FunDef.internalCalls callerFn)
    (hCalleeFind :
      Functions.FunList.find? callee
          hResource.lowerObj.toFunctions.functions =
        some calleeFn)
    (hCalleeBound :
      Functions.SourceDirect.FrameBound.FunDef calleeFn)
    (hActive :
      Functions.CallDepth.Ranked.SourceCallDepth.ActiveStackWitness
        hResource.lowerObj.toFunctions maxFrames (active ++ [callee]))
    (hRel :
      Functions.SourceDirect.StateRel
        (Functions.SourceDirect.FunDef.targetBodyCtx calleeFn).layout
        ({ callerStack := callerTarget.evm.stack, retc := retc } ::
          hiddenReturns)
        calleeSource calleeTarget)
    (hFrameRel :
      Structured.Preservation.Frame.StateRel calleeTarget state tokens) :
    Yul.Program.RecursiveBridgeSourceDirectActiveResourcePoint hResource
      state :=
  Yul.Program.RecursiveBridgeSourceDirectActiveResourcePoint.callBodyTargetCtx
    hCallerContext hCaller hCallerFind hCall hCalleeFind hCalleeBound hActive
    hRel hFrameRel

example
    {program : Yul.Program}
    {check : Yul.Program.RecursiveBridgeExecutableSCCRecurrenceCheckResult
      program}
    (hCheck :
      Yul.Program.recursiveBridgeExecutableSCCRecurrenceCheckResult?
          program =
        some check) :
    Functions.CallDepth.Ranked.SourceRecurrenceBound
      check.lowerObj.toFunctions check.maxFrames :=
  let _hChecked :=
      Yul.Program.recursiveBridgeExecutableSCCRecurrenceCheckResult?_eq_some
        hCheck
  check.sourceRecurrenceBound

example
    {program : Yul.Program}
    {check : Yul.Program.RecursiveBridgeExecutableSCCRecurrenceCheckResult
      program}
    (hCheck :
      Yul.Program.recursiveBridgeExecutableSCCRecurrenceCheckResult?
          program =
        some check)
    {frame : Functions.CallDepth.Ranked.GuardedZeroCalls.SourceCallFrame}
    {depth : Nat}
    (hRoot :
      Functions.CallDepth.Ranked.GuardedZeroCalls.GuardedSemanticRootFrame
        check.lowerObj.toFunctions frame)
    (hChain :
      Functions.CallDepth.Ranked.ConcreteCallChain
        (Functions.CallDepth.Ranked.GuardedZeroCalls.GuardedSemanticDirectCall
          check.lowerObj.toFunctions)
        frame depth) :
    depth + 1 ≤ check.maxFrames := by
  let _hChecked :=
    Yul.Program.recursiveBridgeExecutableSCCRecurrenceCheckResult?_eq_some
      hCheck
  exact check.guardedSemanticRootChain_frame_count_bound hRoot hChain

example
    {program : Yul.Program} {lowerObj : Objects.Program}
    (hLower : program.toObjects? = some lowerObj)
    (hAcyclic :
      Functions.CallDepth.Ranked.inferAcyclicRecurrenceDepth?
          lowerObj.toFunctions =
        none)
    (hSCC :
      Functions.CallDepth.Ranked.checkSCCRecurrence?
          lowerObj.toFunctions =
        none) :
    Yul.Program.recursiveBridgeExecutableSourceRecurrenceDepth? program =
      none :=
  Yul.Program.recursiveBridgeExecutableSourceRecurrenceDepth?_none_of_default_branches_none
    hLower hAcyclic hSCC

example
    {program : Yul.Program} {lowerObj : Objects.Program}
    (hLower : program.toObjects? = some lowerObj)
    (hAcyclic :
      Functions.CallDepth.Ranked.inferAcyclicRecurrenceDepth?
          lowerObj.toFunctions =
        none)
    (hSCC :
      Functions.CallDepth.Ranked.checkSCCRecurrence?
          lowerObj.toFunctions =
        none) :
    Yul.Program.recursiveBridgeSourceResourceDepth? program = none :=
  Yul.Program.recursiveBridgeSourceResourceDepth?_none_of_default_branches_none
    hLower hAcyclic hSCC

example
    {program : Yul.Program} {depth : Nat}
    (hDepth :
      Yul.Program.recursiveBridgeExecutableSourceRecurrenceDepth? program =
        some depth) :
    ∃ lowerObj,
      program.toObjects? = some lowerObj ∧
        ((∃ check :
            Functions.CallDepth.Ranked.CheckedProgramRecurrenceCheckResult
              lowerObj.toFunctions,
            check.depth = depth) ∨
          (Functions.CallDepth.Ranked.inferAcyclicRecurrenceDepth?
              lowerObj.toFunctions =
            none ∧
              ∃ check :
                Functions.CallDepth.Ranked.SCCRecurrenceCheckResult
                  lowerObj.toFunctions,
                Functions.CallDepth.Ranked.checkSCCRecurrence?
                    lowerObj.toFunctions =
                  some check ∧
                  check.maxFrames = depth)) :=
  Yul.Program.recursiveBridgeExecutableSourceRecurrenceDepth?_eq_some_cases
    hDepth

example
    {program : Yul.Program} {depth : Nat}
    (hDepth :
      Yul.Program.recursiveBridgeSourceResourceDepth? program = some depth) :
    ∃ lowerObj,
      program.toObjects? = some lowerObj ∧
        ((Functions.CallDepth.Ranked.inferAcyclicRecurrenceDepth?
              lowerObj.toFunctions =
            some depth ∧
            Functions.CallDepth.Ranked.sourceStackFitsEVM? depth = true ∧
            ∃ check :
              Functions.CallDepth.Ranked.CheckedProgramRecurrenceCheckResult
                lowerObj.toFunctions,
              check.depth = depth) ∨
          (((Functions.CallDepth.Ranked.inferAcyclicRecurrenceDepth?
                lowerObj.toFunctions =
              none) ∨
              ∃ acyclicDepth,
                Functions.CallDepth.Ranked.inferAcyclicRecurrenceDepth?
                    lowerObj.toFunctions =
                  some acyclicDepth ∧
                  Functions.CallDepth.Ranked.sourceStackFitsEVM?
                      acyclicDepth =
                    false) ∧
            ∃ check :
              Functions.CallDepth.Ranked.SCCRecurrenceCheckResult
                lowerObj.toFunctions,
              Functions.CallDepth.Ranked.checkSCCRecurrence?
                  lowerObj.toFunctions =
                some check ∧
                check.maxFrames = depth ∧
                  Functions.CallDepth.Ranked.sourceStackFitsEVM? depth =
                    true)) :=
  Yul.Program.recursiveBridgeSourceResourceDepth?_eq_some_cases hDepth

example
    {program : Functions.Program}
    {check :
      Functions.CallDepth.Program.StackFrameWordSumCheckResult program}
    (hCheck :
      Functions.CallDepth.Program.stackFrameWordSumCheck? program =
        some check) :
    Functions.CallDepth.Program.maxActiveFrameWords? program =
        some check.frameWords ∧
      16 + check.frameWords + 17 ≤ 1024 :=
  Functions.CallDepth.Program.stackFrameWordSumCheck?_eq_some hCheck

example
    {program : Functions.Program}
    {check :
      Functions.CallDepth.Program.StackFrameWordSumCheckResult program}
    {name : Functions.Name} {pathWords : Nat}
    (hRoot :
      name ∈ Functions.CallDepth.Program.mainInternalCalls program)
    (hPath :
      Functions.CallDepth.FunctionPathFrameWords program.functions name
        pathWords) :
    pathWords ≤ check.frameWords :=
  check.path_words_bound hRoot hPath

example
    {program : Functions.Program} {bound : Nat}
    (hBound :
      Functions.CallDepth.Program.maxActiveFrameWords? program = some bound)
    {name : Functions.Name} {pathWords : Nat}
    (hRoot :
      name ∈ Functions.CallDepth.Program.mainInternalCalls program)
    (hPath :
      Functions.CallDepth.FunctionPathFrameWords program.functions name
        pathWords) :
    pathWords ≤ bound :=
  Functions.CallDepth.Program.maxActiveFrameWords?_sound hBound hRoot hPath

example
    {functions : List Functions.FunDef}
    {root current : Functions.Name} {pathWords : Nat}
    (hPath :
      Functions.CallDepth.FunctionPathFrameWordsTo functions root current
        pathWords) :
    Functions.CallDepth.FunctionPathFrameWords functions root pathWords :=
  hPath.toFunctionPathFrameWords

example
    {program : Functions.Program}
    {check :
      Functions.CallDepth.Program.StackFrameWordSumCheckResult program}
    {active : List Functions.Name} {pathWords : Nat}
    (hPath :
      Functions.CallDepth.Program.ActiveCallFrameWords program active
        pathWords) :
    pathWords ≤ check.frameWords :=
  Functions.CallDepth.Program.ActiveCallFrameWords.words_le_check check hPath

example
    {program : Functions.Program}
    {check :
      Functions.CallDepth.Program.StackFrameWordSumCheckResult program}
    {active : List Functions.Name}
    {source : Structured.RunState}
    (hContext :
      Functions.CallDepth.ActiveHiddenFrameWordsContext program active
        source.returns)
    (hVisible : source.evm.stack.length ≤ 16) :
    Structured.Preservation.Frame.SourceStackHeadroom source :=
  Functions.CallDepth.ActiveHiddenFrameWordsContext.sourceStackHeadroom
    (check := check) hContext hVisible

example
    {program : Functions.Program}
    {check :
      Functions.CallDepth.Program.StackFrameWordSumCheckResult program}
    {active layout : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Structured.RunState}
    (hContext :
      Functions.CallDepth.ActiveHiddenFrameWordsContext program active
        hiddenReturns)
    (hLayout : layout.length ≤ 16)
    (hRel :
      Functions.SourceDirect.StateRel layout hiddenReturns source target) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  Functions.CallDepth.ActiveHiddenFrameWordsContext.sourceStackHeadroom_of_sourceDirectStateRel
    (check := check) hContext hLayout hRel

example
    {program : Functions.Program}
    {active : List Functions.Name} {callee : Functions.Name}
    {frame : Structured.ReturnDest}
    {hiddenReturns : List Structured.ReturnDest}
    (hContext :
      Functions.CallDepth.ActiveHiddenFrameWordsContext program
        (active ++ [callee]) (frame :: hiddenReturns)) :
    Functions.CallDepth.ActiveHiddenFrameWordsContext program active
      hiddenReturns :=
  Functions.CallDepth.ActiveHiddenFrameWordsContext.afterReturn hContext

example
    {program : Functions.Program}
    {check :
      Functions.CallDepth.Program.StackFrameWordSumCheckResult program}
    {active layout : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Structured.RunState}
    (hContext :
      Functions.CallDepth.SourceDirectWeightedFrameContext program active
        layout hiddenReturns source target) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  Functions.CallDepth.SourceDirectWeightedFrameContext.sourceStackHeadroom
    (check := check) hContext

example
    {program : Functions.Program}
    {active callerLayout : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {callerSource calleeSource : Functions.Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {caller callee : Functions.Name}
    {callerFn calleeFn : Functions.FunDef} {retc : Nat}
    (hCallerContext :
      Functions.CallDepth.SourceDirectWeightedFrameContext program active
        callerLayout hiddenReturns callerSource callerTarget)
    (hCaller : active.getLast? = some caller)
    (hCallerFind :
      Functions.FunList.find? caller program.functions = some callerFn)
    (hCall : callee ∈ Functions.CallDepth.FunDef.internalCalls callerFn)
    (hCalleeFind :
      Functions.FunList.find? callee program.functions = some calleeFn)
    (hCalleeBound : Functions.SourceDirect.FrameBound.FunDef calleeFn)
    (hArgCallerBound :
      calleeFn.params.length + callerTarget.evm.stack.length ≤ 16)
    (hRel :
      Functions.SourceDirect.StateRel
        (Functions.SourceDirect.FunDef.targetBodyCtx calleeFn).layout
        ({ callerStack := callerTarget.evm.stack, retc := retc } ::
          hiddenReturns)
        calleeSource calleeTarget) :
    Functions.CallDepth.SourceDirectWeightedFrameContext program
      (active ++ [callee])
      (Functions.SourceDirect.FunDef.targetBodyCtx calleeFn).layout
      ({ callerStack := callerTarget.evm.stack, retc := retc } ::
        hiddenReturns)
      calleeSource calleeTarget :=
  Functions.CallDepth.SourceDirectWeightedFrameContext.callBodyTargetCtxOfArgCallerBound
    hCallerContext hCaller hCallerFind hCall hCalleeFind hCalleeBound
    hArgCallerBound hRel

example
    {program : Functions.Program}
    {active : List Functions.Name} {callee : Functions.Name}
    {calleeLayout callerLayout : List Functions.Name}
    {calleeHidden callerHidden : List Structured.ReturnDest}
    {calleeSource callerSource : Functions.Source.State}
    {state returned callerTarget : Structured.RunState}
    {frame : Structured.ReturnDest} {stack : EvmYul.Stack Functions.Word}
    (hCalleeContext :
      Functions.CallDepth.SourceDirectWeightedFrameContext program
        (active ++ [callee]) calleeLayout calleeHidden calleeSource state)
    (hActive :
      Functions.CallDepth.Program.ActiveCallStack program active)
    (hPop : state.popReturn? = some (frame, returned))
    (hAttach :
      Structured.StackFrame.attachReturns? frame state.evm.stack =
        some stack)
    (hReturnFrameVisible :
      frame.retc + frame.callerStack.length ≤ 16)
    (hCallerTarget :
      callerTarget = returned.withEVM { state.evm with stack := stack })
    (hRel :
      Functions.SourceDirect.StateRel callerLayout callerHidden callerSource
        callerTarget) :
    Functions.CallDepth.SourceDirectWeightedFrameContext program active
      callerLayout callerHidden callerSource callerTarget :=
  Functions.CallDepth.SourceDirectWeightedFrameContext.afterAttachReturns?
    hCalleeContext hActive hPop hAttach hReturnFrameVisible hCallerTarget hRel

example
    {program : Functions.Program}
    {bound :
      Functions.CallDepth.SourceFrameWordSumResourceBound program}
    {active layout : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Structured.RunState}
    (hContext :
      Functions.CallDepth.SourceDirectWeightedFrameContext program active
        layout hiddenReturns source target) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  bound.sourceStackHeadroom_of_weightedContext hContext

example
    {program : Functions.Program}
    {active layout : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Structured.RunState}
    (hContext :
      Functions.CallDepth.SourceDirectWeightedFrameContext program active
        layout hiddenReturns source target) :
    ∃ activeWords,
      Functions.CallDepth.Program.ActiveCallFrameWords program active
        activeWords ∧
        Structured.Preservation.Frame.sourceStackWeight target ≤
          layout.length + activeWords :=
  hContext.sourceStackWeight_le_layout_plus_activeWords

example
    {program : Functions.Program}
    {check :
      Functions.CallDepth.Program.StackFrameWordSumCheckResult program}
    {active layout : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Structured.RunState}
    (hContext :
      Functions.CallDepth.SourceDirectWeightedFrameContext program active
        layout hiddenReturns source target) :
    Structured.Preservation.Frame.sourceStackWeight target ≤
      16 + check.frameWords :=
  hContext.sourceStackWeight_le_checked_frameWords

example
    {program : Functions.Program}
    {bound :
      Functions.CallDepth.SourceFrameWordSumResourceBound program}
    (hBound :
      Functions.CallDepth.Program.sourceFrameWordSumResourceBound? program =
        some bound) :
    Functions.CallDepth.Program.stackFrameWordSumCheck? program =
      some bound.check :=
  Functions.CallDepth.Program.sourceFrameWordSumResourceBound?_eq_some
    hBound

example
    {program : Functions.Program}
    {bound :
      Functions.CallDepth.SourceFrameWordSumResourceBound program}
    (hBound :
      Functions.CallDepth.Program.sourceFrameWordSumResourceBound? program =
        some bound) :
    Functions.CallDepth.Program.maxActiveFrameWords? program =
        some bound.check.frameWords ∧
      16 + bound.check.frameWords + 17 ≤ 1024 :=
  Functions.CallDepth.Program.sourceFrameWordSumResourceBound?_sound hBound

example
    {program : Yul.Program}
    {hResource :
      Yul.Program.RecursiveBridgeSourceFrameWordSumResourceBound program}
    {active layout : List Yul.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Structured.RunState}
    (context :
      Functions.CallDepth.SourceDirectWeightedFrameContext
        hResource.lowerObj.toFunctions active layout hiddenReturns source
        target) :
    Structured.Preservation.Frame.SourceStackHeadroom target :=
  Yul.Program.RecursiveBridgeSourceFrameWordSumResourceBound.sourceStackHeadroom_of_weightedContext
    hResource context

example
    {program : Yul.Program}
    {hResource :
      Yul.Program.RecursiveBridgeSourceFrameWordSumResourceBound program}
    {state : Yul.EVMState}
    (hPoint :
      Yul.Program.RecursiveBridgeSourceDirectFrameWordSumPoint hResource
        state) :
    ∃ baseState tokens,
      Structured.Preservation.Frame.StateRel baseState state tokens ∧
        Structured.Preservation.Frame.SourceStackHeadroom baseState :=
  Yul.Program.RecursiveBridgeSourceDirectFrameWordSumPoint.point_sourceStackHeadroom
    hPoint

example
    {program : Yul.Program}
    {hResource :
      Yul.Program.RecursiveBridgeSourceFrameWordSumResourceBound program}
    {active callerLayout : List Yul.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {callerSource calleeSource : Functions.Source.State}
    {callerTarget calleeTarget : Structured.RunState}
    {state : Yul.EVMState} {tokens : List Yul.Word}
    {caller callee : Yul.Name} {callerFn calleeFn : Functions.FunDef}
    {retc : Nat}
    (hCallerContext :
      Functions.CallDepth.SourceDirectWeightedFrameContext
        hResource.lowerObj.toFunctions active callerLayout hiddenReturns
        callerSource callerTarget)
    (hCaller : active.getLast? = some caller)
    (hCallerFind :
      Functions.FunList.find? caller
          hResource.lowerObj.toFunctions.functions =
        some callerFn)
    (hCall :
      callee ∈ Functions.CallDepth.FunDef.internalCalls callerFn)
    (hCalleeFind :
      Functions.FunList.find? callee
          hResource.lowerObj.toFunctions.functions =
        some calleeFn)
    (hCalleeBound :
      Functions.SourceDirect.FrameBound.FunDef calleeFn)
    (hArgCallerBound :
      calleeFn.params.length + callerTarget.evm.stack.length ≤ 16)
    (hRel :
      Functions.SourceDirect.StateRel
        (Functions.SourceDirect.FunDef.targetBodyCtx calleeFn).layout
        ({ callerStack := callerTarget.evm.stack, retc := retc } ::
          hiddenReturns)
        calleeSource calleeTarget)
    (hFrameRel :
      Structured.Preservation.Frame.StateRel calleeTarget state tokens) :
    Yul.Program.RecursiveBridgeSourceDirectFrameWordSumPoint hResource state :=
  Yul.Program.RecursiveBridgeSourceDirectFrameWordSumPoint.callBodyTargetCtxOfArgCallerBound
    hCallerContext hCaller hCallerFind hCall hCalleeFind hCalleeBound
    hArgCallerBound hRel hFrameRel

end

end PublicSpineRegression

namespace LiveLayoutRegression

example {layout live : List Functions.Name}
    (hCheck : Functions.LiveLayout.Layout.entryWindowOk? layout live = true)
    {name : Functions.Name} (hName : name ∈ live) :
    ∃ idx,
      (Functions.LiveLayout.Layout.trimDeadPrefix layout live)[idx]? =
          some name ∧
        idx + 1 ≤ 16 :=
  Functions.LiveLayout.Layout.entryWindowOk?_sound hCheck hName

example {layout live : List Functions.Name} :
    Functions.LiveLayout.Layout.entryWindowOk? layout live = true ↔
      ∀ {name : Functions.Name}, name ∈ live →
        ∃ idx,
          Functions.LiveLayout.Layout.index? name
              (Functions.LiveLayout.Layout.trimDeadPrefix layout live) =
            some idx ∧
          idx + 1 ≤ 16 :=
  Functions.LiveLayout.Layout.entryWindowOk?_iff_index

example :
    Functions.LiveLayout.Layout.promoteName?
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15",
        "x"] "x" =
      some
        (["x", "d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
          "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15"],
          16) := by
  native_decide

example :
    Functions.LiveLayout.Layout.promoteName?
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15",
        "d16", "x"] "x" = none := by
  native_decide

example {protectedDepth : Nat} {layout : List Functions.Name}
    {reqs : List Functions.LiveLayout.Prepare.NameReq}
    {promoteStmt : Locals.Stmt} {promoted : List Functions.Name}
    (hPromote :
      Functions.LiveLayout.Prepare.promoteBlockedAboveSuffix?
          protectedDepth layout reqs =
        some (promoteStmt, promoted)) :
    ∃ name idx,
      promoteStmt = .promoteName name ∧
        Functions.LiveLayout.Layout.promoteName? layout name =
          some (promoted, idx) ∧
        idx < layout.length - protectedDepth :=
  Functions.LiveLayout.Prepare.promoteBlockedAboveSuffix?_eq_some hPromote

example :
    Functions.LiveLayout.Prepare.promoteBlockedAboveSuffix? 0
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15",
        "x"] [(1, "x")] =
      some
        (.promoteName "x",
          ["x", "d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
            "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15"]) := by
  rfl

example :
    Functions.LiveLayout.Prepare.promoteBlockedAboveSuffix? 1
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15",
        "x"] [(1, "x")] = none := by
  rfl

example :
    Functions.LiveLayout.Prepare.forStmtAboveSuffix? 0 []
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15",
        "x"] ["x"]
      (.expr (.prim .pop (Locals.ExprSeq.cons (.var "x") .nil))) =
      some
        ([Locals.Stmt.promoteName "x"],
          ["x", "d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
            "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15"]) := by
  rfl

example :
    Functions.LiveLayout.Prepare.forStmtAboveSuffix? 1 []
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15",
        "x"] ["x"]
      (.expr (.prim .pop (Locals.ExprSeq.cons (.var "x") .nil))) = none := by
  rfl

set_option maxRecDepth 20000 in
example :
    Functions.LiveLayout.Checked.StmtList.check? [] {}
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "d14", "dead",
        "x"]
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "d14"]
      [(.expr (.prim .pop (Locals.ExprSeq.cons (.var "x") .nil)))] =
      some
        ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
          "d8", "d9", "d10", "d11", "d12", "d13", "d14", "dead"] := by
  rfl

set_option maxRecDepth 20000 in
example :
    ∃ lower,
      Functions.LiveLayout.Lower.StmtList.toLocals? [] {}
        ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
          "d8", "d9", "d10", "d11", "d12", "d13", "d14", "dead",
          "x"]
        ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
          "d8", "d9", "d10", "d11", "d12", "d13", "d14"]
        [(.expr (.prim .pop (Locals.ExprSeq.cons (.var "x") .nil)))] =
        some
          (lower,
            ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
              "d8", "d9", "d10", "d11", "d12", "d13", "d14", "dead"]) := by
  refine ⟨_, rfl⟩

set_option maxRecDepth 50000 in
example :
    (Functions.LiveLayout.Prepare.forStmtAboveSuffix? 0 []
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "dead", "y",
        "x"]
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "x", "y"]
      (.expr (.prim .pop (Locals.ExprSeq.cons
        (.prim .add (Locals.ExprSeq.cons (.var "x")
          (Locals.ExprSeq.cons (.var "y") .nil))) .nil)))).map
        (fun pair => pair.1.length) = some 2 := by
  native_decide

set_option maxRecDepth 50000 in
example :
    Functions.LiveLayout.Checked.StmtList.check? [] {}
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "dead", "y",
        "x"]
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13"]
      [(.expr (.prim .pop (Locals.ExprSeq.cons
        (.prim .add (Locals.ExprSeq.cons (.var "x")
          (Locals.ExprSeq.cons (.var "y") .nil))) .nil)))] =
      some ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "dead"] := by
  native_decide

set_option maxRecDepth 50000 in
example :
    (Functions.LiveLayout.Lower.StmtList.toLocals? [] {}
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "dead", "y",
        "x"]
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13"]
      [(.expr (.prim .pop (Locals.ExprSeq.cons
        (.prim .add (Locals.ExprSeq.cons (.var "x")
          (Locals.ExprSeq.cons (.var "y") .nil))) .nil)))]).isSome =
      true := by
  native_decide

set_option maxRecDepth 20000 in
example :
    Functions.LiveLayout.Checked.StmtList.check? [] {}
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15",
        "x"]
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7",
        "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15"]
      [(.expr (.prim .pop (Locals.ExprSeq.cons (.var "x") .nil)))] =
      none := by
  rfl

example {protectedDepth fuel : Nat} {returns live layout : List Functions.Name}
    {stmt : Functions.Stmt} {reqs : List Functions.LiveLayout.Prepare.NameReq}
    {prep : List Locals.Stmt} {finalLayout : List Functions.Name}
    (hLoop :
      Functions.LiveLayout.Prepare.loopAboveSuffix protectedDepth returns live
          stmt reqs fuel layout =
        some (prep, finalLayout)) :
    Functions.LiveLayout.Prepare.checked? returns live finalLayout stmt =
      true :=
  Functions.LiveLayout.Prepare.loopAboveSuffix_checked hLoop

example {protectedDepth fuel : Nat} {returns live layout : List Functions.Name}
    {stmt : Functions.Stmt} {reqs : List Functions.LiveLayout.Prepare.NameReq}
    {prep : List Locals.Stmt} {finalLayout : List Functions.Name}
    (hLoop :
      Functions.LiveLayout.Prepare.loopAboveSuffix protectedDepth returns live
          stmt reqs fuel layout =
        some (prep, finalLayout)) :
    Functions.LiveLayout.TargetLayout.StmtList.regularOutLayout layout prep =
      finalLayout :=
  Functions.LiveLayout.TargetLayout.Prepare.loopAboveSuffix_regularOutLayout
    hLoop

example {protectedDepth : Nat} {returns live layout : List Functions.Name}
    {stmt : Functions.Stmt}
    {prep : List Locals.Stmt} {finalLayout : List Functions.Name}
    (hPrepare :
      Functions.LiveLayout.Prepare.forStmtAboveSuffix? protectedDepth returns
          layout live stmt =
        some (prep, finalLayout)) :
    Functions.LiveLayout.Layout.entryWindowOk? finalLayout live = true ∧
      Functions.LiveLayout.StmtAccess.accessible? returns finalLayout stmt =
        true :=
  Functions.LiveLayout.Prepare.forStmtAboveSuffix?_checked hPrepare

example {protectedDepth : Nat} {returns live layout : List Functions.Name}
    {stmt : Functions.Stmt}
    {prep : List Locals.Stmt} {finalLayout : List Functions.Name}
    (hPrepare :
      Functions.LiveLayout.Prepare.forStmtAboveSuffix? protectedDepth returns
          layout live stmt =
        some (prep, finalLayout)) :
    Functions.LiveLayout.TargetLayout.StmtList.regularOutLayout layout prep =
      finalLayout :=
  Functions.LiveLayout.TargetLayout.Prepare.forStmtAboveSuffix?_regularOutLayout
    hPrepare

example {retc protectedDepth idx : Nat}
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {promoted : List Functions.Name} {name : Functions.Name}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
        target)
    (hPromote :
      Functions.LiveLayout.Layout.promoteName? target.layout name =
        some (promoted, idx))
    (hIdx : idx < target.layout.length - protectedDepth)
    (hBreakDepth :
      ∀ {depth : Nat}, target.breakDepth? = some depth →
        depth ≤ protectedDepth)
    (hContinueDepth :
      ∀ {depth : Nat}, target.continueDepth? = some depth →
        depth ≤ protectedDepth) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
      (target.withLayout promoted) :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel.promoteName_of_idx_lt_protectedDepth
    hRel hPromote hIdx hBreakDepth hContinueDepth

example {retc protectedDepth : Nat}
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {returns live : List Functions.Name} {stmt : Functions.Stmt}
    {prep : List Locals.Stmt} {finalLayout : List Functions.Name}
    (hPrepare :
      Functions.LiveLayout.Prepare.forStmtAboveSuffix? protectedDepth returns
          target.layout live stmt =
        some (prep, finalLayout))
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
        target)
    (hBreakDepth :
      ∀ {depth : Nat}, target.breakDepth? = some depth →
        depth ≤ protectedDepth)
    (hContinueDepth :
      ∀ {depth : Nat}, target.continueDepth? = some depth →
        depth ≤ protectedDepth) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
      (target.withLayout finalLayout) :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel.forStmtAboveSuffix_of_depth_bounds
    hPrepare hRel hBreakDepth hContinueDepth

example {retc targetDepth : Nat}
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {live : Functions.LiveLayout.Ctx}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
        target)
    (hControl :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source)
    (hNoDup : target.layout.Nodup)
    (hTargetDepth : target.breakDepth? = some targetDepth) :
    targetDepth ≤ live.protectedDepth :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel.breakDepth_le_protectedDepth
    hRel hControl hNoDup hTargetDepth

example {retc targetDepth : Nat}
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {live : Functions.LiveLayout.Ctx}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
        target)
    (hControl :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source)
    (hNoDup : target.layout.Nodup)
    (hTargetDepth : target.continueDepth? = some targetDepth) :
    targetDepth ≤ live.protectedDepth :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel.continueDepth_le_protectedDepth
    hRel hControl hNoDup hTargetDepth

example {retc : Nat}
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {liveCtx : Functions.LiveLayout.Ctx}
    {returns live : List Functions.Name} {stmt : Functions.Stmt}
    {prep : List Locals.Stmt} {finalLayout : List Functions.Name}
    (hPrepare :
      Functions.LiveLayout.Prepare.forStmtAboveSuffix?
          liveCtx.protectedDepth returns target.layout live stmt =
        some (prep, finalLayout))
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
        target)
    (hControl :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel liveCtx source)
    (hNoDup : target.layout.Nodup) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
      (target.withLayout finalLayout) :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel.forStmtAboveSuffix_of_liveControl
    hPrepare hRel hControl hNoDup

example {layout₁ layout₂ : List Locals.Name}
    {source : Locals.Source.State}
    {target₁ target₂ : Structured.RunState}
    (hRel₁ :
      Locals.SourceLowering.StateRel layout₁ source target₁)
    (hRel₂ :
      Locals.SourceLowering.StateRel layout₂ source target₂) :
    target₁.evm.toSharedState = target₂.evm.toSharedState :=
  Locals.SourceLowering.StateRel.target_shared_eq_of_same_source hRel₁ hRel₂

example :
    ¬ Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved
      ({ (default : EvmYul.MachineState) with activeWords := ⟨0⟩ })
      (⟨0⟩ : Locals.Word) := by
  change ¬ EvmYul.UInt256.ofNat (EvmYul.MachineState.M 0 0 32) =
    (⟨0⟩ : EvmYul.UInt256)
  native_decide

example :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved
      ({ (default : EvmYul.MachineState) with activeWords := ⟨1⟩ })
      (⟨0⟩ : Locals.Word) := by
  change EvmYul.UInt256.ofNat (EvmYul.MachineState.M 1 0 32) =
    (⟨1⟩ : EvmYul.UInt256)
  native_decide

example :
    ¬ Locals.SourceLowering.StateRel.SpillScratch.ScratchWordAllocated
      ({ (default : EvmYul.MachineState) with activeWords := ⟨1⟩ })
      (⟨0⟩ : Locals.Word) := by
  change ¬ 0 + 32 ≤ (default : EvmYul.MachineState).memory.size
  native_decide

example {machine : EvmYul.MachineState} {offset : Locals.Word}
    (hWithin :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordWithinActiveNat
        machine offset) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved
      machine offset :=
  Locals.SourceLowering.StateRel.SpillScratch.scratchWordReserved_of_withinActiveNat
    hWithin

example {machine : EvmYul.MachineState} {offset : Locals.Word}
    (hAllocated :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordAllocated
        machine offset)
    (hWithin :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordWithinActiveNat
        machine offset)
    (hNoOverflow :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchActiveBytesNoOverflow
        machine) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReadable
      machine offset :=
  Locals.SourceLowering.StateRel.SpillScratch.scratchWordReadable_of_allocated_withinActiveNat
    hAllocated hWithin hNoOverflow

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec) :
    ffi.ByteArray.zeroes 0 = ByteArray.empty :=
  Locals.SourceLowering.StateRel.SpillScratch.zeroPadding_zero_eq_empty hSpec

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (n : USize) :
    (ffi.ByteArray.zeroes n).size = n.toNat :=
  Locals.SourceLowering.StateRel.SpillScratch.zeroPadding_size hSpec n

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (n : USize) :
    (ffi.ByteArray.zeroes n).data.toList = List.replicate n.toNat 0 :=
  Locals.SourceLowering.StateRel.SpillScratch.zeroPadding_data_toList
    hSpec n

example :
    Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec ↔
      Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingToListSpec :=
  Locals.SourceLowering.StateRel.SpillScratch.zeroPadding_iff_toList

example
    (hSpec :
      Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingToListSpec) :
    Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec :=
  Locals.SourceLowering.StateRel.SpillScratch.zeroPadding_of_toList hSpec

example (xs : List UInt8) :
    (List.toByteArray xs).data.toList = xs :=
  Locals.SourceLowering.StateRel.SpillScratch.list_toByteArray_data_toList
    xs

example (bytes : ByteArray) :
    bytes.toList = bytes.data.toList :=
  Locals.SourceLowering.StateRel.SpillScratch.byteArray_toList_eq_data_toList
    bytes

example {n : Nat} (hLen : n ≤ 32) :
    ({ toBitVec := 32 - (n : BitVec System.Platform.numBits) } : USize).toNat +
        n = 32 :=
  Locals.SourceLowering.StateRel.SpillScratch.usize_wordPadding_toNat_add hLen

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec) :
    Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec :=
  Locals.SourceLowering.StateRel.SpillScratch.wordByteEncoding_of_zeroPadding
    hSpec

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec) :
    Locals.SourceLowering.StateRel.SpillScratch.WordByteRoundTripSpec :=
  Locals.SourceLowering.StateRel.SpillScratch.wordByteRoundTrip_of_zeroPadding
    hSpec

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec) :
    Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingModelSpec :=
  Locals.SourceLowering.StateRel.SpillScratch.wordByteEncodingModel_of_zeroPadding
    hSpec

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {memory : ByteArray} {offset : Nat}
    (hAllocated : offset + 32 ≤ memory.size) :
    memory.readWithPadding offset 32 =
      { data := memory.data.extract offset (offset + 32) } :=
  Locals.SourceLowering.StateRel.SpillScratch.byteArray_readWithPadding32_allocated
    hSpec hAllocated

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {dest source restore : ByteArray} {offset : Nat}
    (hSource : source.size = 32)
    (hRestore : restore.size = 32)
    (hDest : offset + 32 ≤ dest.size)
    (hRestoreBytes :
      restore.data = dest.data.extract offset (offset + 32)) :
    restore.write 0 (source.write 0 dest offset 32) offset 32 = dest :=
  Locals.SourceLowering.StateRel.SpillScratch.byteArray_write32_restore_exact
    hSpec hSource hRestore hDest hRestoreBytes

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hEncoding :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingModelSpec)
    {machine : EvmYul.MachineState} {offset : Locals.Word}
    (hAllocated :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordAllocated
        machine offset)
    (hReadable :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReadable
        machine offset) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchWordBytesCanonical
      machine offset :=
  Locals.SourceLowering.StateRel.SpillScratch.scratchWordBytesCanonical_of_readable
    hSpec hEncoding hAllocated hReadable

example {machine : EvmYul.MachineState} {base count slot : Nat}
    (hAllocated :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionAllocatedNat
        machine base count)
    (hWithin :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionWithinActiveNat
        machine base count)
    (hNoOverflow :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchActiveBytesNoOverflow
        machine)
    (hSlot : slot < count) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchWordAllocated machine
      (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionWord
        base slot) :=
  Locals.SourceLowering.StateRel.SpillScratch.scratchWordAllocated_of_regionNat
    hAllocated hWithin hNoOverflow hSlot

example {machine : EvmYul.MachineState} {base count : Nat}
    (hCheck :
      Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?
        machine base count = true) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
      machine base count :=
  Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?_sound
    hCheck

example :
    Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?
      ({ (default : EvmYul.MachineState) with activeWords := ⟨0⟩ }) 0 1 =
        false := by
  native_decide

example :
    Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?
      ({ (default : EvmYul.MachineState) with activeWords := ⟨1⟩ }) 0 1 =
        false := by
  native_decide

example :
    Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?
      ({ (default : EvmYul.MachineState) with
          activeWords := ⟨1⟩
          memory := List.toByteArray (List.replicate 32 (0 : UInt8)) })
      0 1 = true := by
  native_decide

example {machine : EvmYul.MachineState} {base count slot : Nat}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        machine base count)
    (hSlot : slot < count) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved machine
      (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionWord
        base slot) :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady.scratchWordReserved
    hReady hSlot

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {offset len : Nat}
    (hEnd : offset + len ≤ range.base) :
    range.disjointBytes offset len :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.disjointBytes_of_before
    hEnd

example {a lenA b lenB : Nat}
    (hCheck :
      Locals.SourceLowering.StateRel.SpillScratch.ByteDisjoint.check
        a lenA b lenB = true) :
    Locals.SourceLowering.StateRel.SpillScratch.ByteDisjoint
      a lenA b lenB :=
  Locals.SourceLowering.StateRel.SpillScratch.ByteDisjoint.check_sound
    hCheck

example :
    Locals.SourceLowering.StateRel.SpillScratch.ByteDisjoint.check
      0 32 64 32 = true := by
  native_decide

example :
    Locals.SourceLowering.StateRel.SpillScratch.ByteDisjoint.check
      16 32 0 32 = false := by
  native_decide

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {offset len : Nat}
    (hCheck : range.disjointBytes? offset len = true) :
    range.disjointBytes offset len :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.disjointBytes?_sound
    hCheck

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {offset len : Nat}
    (hDisjoint : range.disjointBytes offset len) :
    range.disjointBytes? offset len = true :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.disjointBytes?_complete
    hDisjoint

example {op : Structured.BasicOp}
    (hCheck :
      Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.basicOp?
        op = true) :
    ¬
      Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.BasicOpMemoryTouching
        op :=
  Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.basicOp?_sound
    hCheck

example {kind : Assembly.HaltKind}
    (hCheck :
      Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.haltKind?
        kind = true) :
    ¬
      Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.HaltKindMemoryTouching
        kind :=
  Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.haltKind?_sound
    hCheck

example :
    Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.basicOp?
      Structured.BasicOp.add = true := by
  native_decide

example :
    Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.basicOp?
      Structured.BasicOp.mload = false := by
  native_decide

example :
    Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.haltKind?
      Assembly.HaltKind.return = false := by
  native_decide

example :
    Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.program?
      { procs := []
        body :=
          { stmts :=
              [Locals.Stmt.expr
                (Locals.Expr.prim Structured.BasicOp.mload
                  (Locals.ExprSeq.cons
                    (Locals.Expr.lit (EvmYul.UInt256.ofNat 0))
                    Locals.ExprSeq.nil))] } } =
      false := by
  native_decide

example {program : Locals.Program}
    (hCheck :
      Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.program?
        program = true) :
    Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.ProgramSafe
      program :=
  Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.program?_sound
    hCheck

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    (hCheck :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.checked?
        range sourceScope stackLayout layout = true) :
    Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed
      range sourceScope stackLayout layout :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.checked?_sound
    hCheck

example
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {name : Locals.Name}
    {location :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation}
    (hNoDup :
      List.Nodup
        (Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.names
          layout))
    (hBinding : (name, location) ∈ layout) :
    Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.lookup?
      name layout = some location :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.lookup?_complete
    hNoDup hBinding

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {slot : Nat}
    (hSlot :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.firstFreeScratchSlot?
        range layout = some slot) :
    slot < range.words ∧
      slot ∉
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.scratchSlots
          layout :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.firstFreeScratchSlot?_sound
    hSlot

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.evictTopStack

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.evictTopStackLayout

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.evictTopStackLayout?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.names_evictTopStackLayout

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.StoreDefined.evictTopStackLayout

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.evictTopStackLayout?_sound

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.evictTopStackLayout?_slot

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.evictTopStackLayout?_names

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.evictTopStackLayout?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel.evictTopStack_mstore

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {offset : Nat} {name : Locals.Name} {slot : Nat}
    (hLayout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed
        range sourceScope stackLayout layout)
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
          slot) ∈ layout) :
    Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.readCode?
      range offset name layout =
        some
          (Locals.SourceLowering.StateRel.SpillScratch.spillLoadCode
            (range.word slot)) :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.readCode?_scratch_of_binding
    hLayout hBinding

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {offset : Nat} {name : Locals.Name} {depth : Nat}
    {op : Structured.BasicOp}
    (hLayout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed
        range sourceScope stackLayout layout)
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.stack
          depth) ∈ layout)
    (hDup : Locals.StackOp.dup? (offset + depth + 1) = some op) :
    Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.readCode?
      range offset name layout =
        some [Structured.BasicInstr.op op] :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.readCode?_stack_of_binding
    hLayout hBinding hDup

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {offset : Nat}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {value : Locals.Word} :
    Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileOneCode?
      range offset layout (Locals.Expr.lit value) =
        some [Structured.BasicInstr.push value] :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileOneCode?_lit

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {offset : Nat} {name : Locals.Name} {slot : Nat}
    (hLayout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed
        range sourceScope stackLayout layout)
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
          slot) ∈ layout) :
    Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileOneCode?
      range offset layout (Locals.Expr.var name) =
        some
          (Locals.SourceLowering.StateRel.SpillScratch.spillLoadCode
            (range.word slot)) :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileOneCode?_scratch_var_of_binding
    hLayout hBinding

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {offset : Nat} {name : Locals.Name} {depth : Nat}
    {op : Structured.BasicOp}
    (hLayout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed
        range sourceScope stackLayout layout)
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.stack
          depth) ∈ layout)
    (hDup : Locals.StackOp.dup? (offset + depth + 1) = some op) :
    Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileOneCode?
      range offset layout (Locals.Expr.var name) =
        some [Structured.BasicInstr.op op] :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileOneCode?_stack_var_of_binding
    hLayout hBinding hDup

example
    {program : Locals.Program} {target : EvmYul.MachineState}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    (hCheck :
      Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.check?
        program target range sourceScope stackLayout layout = true) :
    Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.Sound
      program target range sourceScope stackLayout layout :=
  Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.check?_sound
    hCheck

example
    {program : Locals.Program} {target : EvmYul.MachineState}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    (hCheck :
      Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.check?
        program target range sourceScope stackLayout layout = true) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
      target range.base range.words :=
  Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.check?_scratchReady
    hCheck

example
    {target : EvmYul.MachineState}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    (hCheck :
      Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.scratchCheck?
        target range sourceScope stackLayout layout = true) :
    Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.ScratchSound
      target range sourceScope stackLayout layout :=
  Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.scratchCheck?_sound
    hCheck

example
    {program : Locals.Program} {target : EvmYul.MachineState}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    (hCheck :
      Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.check?
        program target range sourceScope stackLayout layout = true) :
    Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.scratchCheck?
      target range sourceScope stackLayout layout = true :=
  Locals.SourceLowering.StateRel.SpillScratch.PrivateScratchBoundary.check?_scratchCheck
    hCheck

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel.of_privateScratchBoundary_empty

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel.of_scratchBoundary_empty

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    (hLayout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed
        range sourceScope stackLayout layout)
    {name : Locals.Name} {slot : Nat}
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
          slot) ∈ layout) :
    slot < range.words :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed.scratch_binding
    hLayout hBinding

example :
    Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.checked?
      { base := 0, words := 1 }
      ["x", "y"]
      ["x"]
      [("x",
          Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.stack
            0),
        ("y",
          Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
            0)] =
      true := by
  native_decide

example :
    Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.checked?
      { base := 0, words := 2 }
      ["x", "y"]
      []
      [("x",
          Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
            0),
        ("y",
          Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
            0)] =
      false := by
  native_decide

example :
    Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.checked?
      { base := 0, words := 1 }
      ["x"]
      []
      [("x",
          Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
            1)] =
      false := by
  native_decide

example :
    Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.checked?
      { base := 0, words := 1 }
      ["x"]
      ["y"]
      [("x",
          Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.stack
            0)] =
      false := by
  native_decide

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {store : Locals.Source.Store} {machine : EvmYul.MachineState}
    {stack : EvmYul.Stack Locals.Word}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    (hValues :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
        range store machine stack layout)
    {name : Locals.Name} {depth : Nat}
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.stack
          depth) ∈ layout) :
    stack[depth]? = store name :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel.stack_binding
    hValues hBinding

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {store : Locals.Source.Store} {machine : EvmYul.MachineState}
    {stack : EvmYul.Stack Locals.Word}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    (hValues :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
        range store machine stack layout)
    {name : Locals.Name} {slot : Nat}
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
          slot) ∈ layout) :
    ∃ value, store name = some value ∧
      (machine.mload (range.word slot)).1 = value :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel.scratch_binding
    hValues hBinding

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {store : Locals.Source.Store} {machine : EvmYul.MachineState}
    {stack : EvmYul.Stack Locals.Word}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    (hLayout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed
        range sourceScope stackLayout layout)
    (hValues :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
        range store machine stack layout)
    {name : Locals.Name} {slot : Nat}
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
          slot) ∈ layout) :
    slot < range.words ∧
      ∃ value, store name = some value ∧
        (machine.mload (range.word slot)).1 = value :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel.scratch_binding_of_wellFormed
    hLayout hValues hBinding

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    (hLayout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed
        range sourceScope stackLayout layout)
    {left right : Locals.Name} {slot : Nat}
    (hLeft :
      (left,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
          slot) ∈ layout)
    (hRight :
      (right,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
          slot) ∈ layout) :
    left = right :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed.scratch_binding_name_eq
    hLayout hLeft hRight

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {store : Locals.Source.Store} {machine : EvmYul.MachineState}
    {stack : EvmYul.Stack Locals.Word}
    {writeSlot : Nat} {value : Locals.Word}
    (hLayout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed
        range sourceScope stackLayout layout)
    (hValues :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
        range store machine stack layout)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        machine range.base range.words)
    (hWriteSlot : writeSlot < range.words)
    (hStoreMatches :
      ∀ {name : Locals.Name},
        (name,
          Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
            writeSlot) ∈ layout →
          store name = some value) :
    Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
      range store
      ((machine.mstore (range.word writeSlot) value).mload
        (range.word writeSlot)).2 stack layout :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel.mload_after_mstore_target_scratch_slot_preserve
    hSpec hWordBytes hLayout hValues hReady hWriteSlot hStoreMatches

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {store : Locals.Source.Store} {machine : EvmYul.MachineState}
    {stack : EvmYul.Stack Locals.Word}
    {name : Locals.Name} {writeSlot : Nat} {value : Locals.Word}
    (hLayout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed
        range sourceScope stackLayout layout)
    (hValues :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
        range store machine stack layout)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        machine range.base range.words)
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
          writeSlot) ∈ layout) :
    Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
      range (Locals.Source.Store.insert store name value)
      (machine.mstore (range.word writeSlot) value) stack layout :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel.mstore_target_scratch_slot_assign
    hSpec hWordBytes hLayout hValues hReady hBinding

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.SharedState .EVM}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SharedStateEqOutsideScratch
        range source target) :
    Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
      range source.toMachineState target.toMachineState :=
  Locals.SourceLowering.StateRel.SpillScratch.SharedStateEqOutsideScratch.memory
    hRel

example :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratchExceptGas

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratchExceptGas.of_exact

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SharedStateEqOutsideScratchExceptGas

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SharedStateEqOutsideScratch.exceptGas

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SharedStateEqOutsideScratch.exceptGas_of_eraseControl

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target) :
    Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
      range
      ((source.setReturnData ByteArray.empty).setHReturn ByteArray.empty)
      ((target.setReturnData ByteArray.empty).setHReturn ByteArray.empty) :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.setReturnData_setHReturn
    hRel ByteArray.empty ByteArray.empty

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target) :
    Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
      range (source.setHReturn ByteArray.empty)
      (target.setHReturn ByteArray.empty) :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.setHReturn
    hRel ByteArray.empty

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.SharedState .EVM}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SharedStateEqOutsideScratch
        range source target) :
    Locals.SourceLowering.StateRel.SpillScratch.SharedStateEqOutsideScratch
      range
      ({ source with
        toMachineState :=
          (source.toMachineState.setReturnData ByteArray.empty).setHReturn
            ByteArray.empty } : EvmYul.SharedState .EVM)
      ({ target with
        toMachineState :=
          (target.toMachineState.setReturnData ByteArray.empty).setHReturn
            ByteArray.empty } : EvmYul.SharedState .EVM) :=
  Locals.SourceLowering.StateRel.SpillScratch.SharedStateEqOutsideScratch.setReturnData_setHReturn
    hRel ByteArray.empty ByteArray.empty

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {state₁ state₂ : Locals.EVMState} {recipient : Locals.Word}
    {tail₁ tail₂ : EvmYul.Stack Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SharedStateEqOutsideScratch
        range state₁.toSharedState state₂.toSharedState) :
    Locals.SourceLowering.StateRel.SpillScratch.SharedStateEqOutsideScratch
      range
      (Locals.SourceLowering.PrimitiveSemantics.selfdestructTerminalState
          state₁ recipient tail₁).toSharedState
      (Locals.SourceLowering.PrimitiveSemantics.selfdestructTerminalState
          state₂ recipient tail₂).toSharedState :=
  Locals.SourceLowering.PrimitiveSemantics.selfdestructTerminalState_toSharedState_outsideScratch
    state₁ state₂ recipient tail₁ tail₂ hRel

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {kind : Assembly.HaltKind}
    {sourceShared sourceShared' targetShared : EvmYul.SharedState .EVM}
    {values : List Locals.Word} {evm : Locals.EVMState}
    {baseStack : EvmYul.Stack Locals.Word}
    (hNoMem :
      ¬ Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.HaltKindMemoryTouching
          kind)
    (hEval :
      Locals.Source.PrimitiveSemantics.structured.terminal kind
          sourceShared values =
        .ok sourceShared')
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SharedStateEqOutsideScratch
        range sourceShared targetShared)
    (hShared : evm.toSharedState = targetShared)
    (hStack : evm.stack = values.reverse ++ baseStack) :
    ∃ evm',
      Structured.Terminal.step kind evm = .ok evm' ∧
        Locals.SourceLowering.StateRel.SpillScratch.SharedStateEqOutsideScratch
          range sourceShared' evm'.toSharedState :=
  Locals.SourceLowering.PrimitiveSemantics.structured_terminal_step_exists_outsideScratch
    hNoMem hEval hRel hShared hStack

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.SharedState .EVM}
    {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SharedStateEqOutsideScratch
        range source target)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        target.toMachineState range.base range.words)
    (hSlot : slot < range.words) :
    Locals.SourceLowering.StateRel.SpillScratch.SharedStateEqOutsideScratch
      range source
      ({ target with
        toMachineState := target.toMachineState.mstore
          (range.word slot) value } : EvmYul.SharedState .EVM) :=
  Locals.SourceLowering.StateRel.SpillScratch.SharedStateEqOutsideScratch.mstore_target_scratch_slot
    hSpec hWordBytes hRel hReady hSlot

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source : Locals.Source.State} {target : Locals.EVMState}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout source target) :
    Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
      range source.vars target.toMachineState target.stack layout :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel.valueRel
    hRel

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source : Locals.Source.State} {target : Locals.EVMState}
    {name : Locals.Name} {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout source target)
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
          slot) ∈ layout) :
    Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
      range sourceScope stackLayout layout
      (source.withVars (Locals.Source.Store.insert source.vars name value))
      ({ target with
        toMachineState := target.toMachineState.mstore
          (range.word slot) value } : Locals.EVMState) :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel.mstore_scratch_assign
    hSpec hWordBytes hRel hBinding

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source : Locals.Source.State} {target : Locals.EVMState}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout source target) :
    Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
      range sourceScope stackLayout layout source [] target :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.of_spillStateRel
    hRel

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source : Locals.Source.State} {target : Locals.EVMState}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source [] target) :
    Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
      range sourceScope stackLayout layout source target :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.to_spillStateRel_nil
    hRel

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source : Locals.Source.State} {target : Locals.EVMState}
    {stackPrefix : List Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source stackPrefix target) :
    ∃ baseStack : EvmYul.Stack Locals.Word,
      target.stack = stackPrefix ++ baseStack ∧
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
          range source.vars target.toMachineState baseStack layout :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.valueRel_base
    hRel

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {offset len : Nat}
    (hStart : range.endExclusive ≤ offset) :
    range.disjointBytes offset len :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.disjointBytes_of_after
    hStart

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {offset len slot : Nat}
    (hDisjoint : range.disjointBytes offset len)
    (hSlot : slot < range.words) :
    Locals.SourceLowering.StateRel.SpillScratch.ByteDisjoint offset len
      (range.slot slot) 32 :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.byteDisjoint_slot_of_disjointBytes
    hDisjoint hSlot

example {machine : EvmYul.MachineState}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.ready?
        machine range = true) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
      machine range.base range.words :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.ready?_sound
    hReady

example {machine : EvmYul.MachineState}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {offset len slot : Nat}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        machine range.base range.words)
    (hDisjoint : range.disjointBytes offset len)
    (hSlot : slot < range.words) :
    Locals.SourceLowering.StateRel.SpillScratch.ByteDisjoint offset len
      (range.word slot).toNat 32 :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.byteDisjoint_word_slot_of_disjointBytes
    hReady hDisjoint hSlot

example {machine : EvmYul.MachineState}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {left right : Nat}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        machine range.base range.words)
    (hLeft : left < range.words)
    (hRight : right < range.words)
    (hNe : left ≠ right) :
    Locals.SourceLowering.StateRel.SpillScratch.ByteDisjoint
      (range.word left).toNat 32 (range.word right).toNat 32 :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.byteDisjoint_word_slots_of_ne
    hReady hLeft hRight hNe

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {machine : EvmYul.MachineState} :
    Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch
      range machine machine :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch.refl
    range machine

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch
        range source target) :
    Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch
      range target source :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch.symm
    hRel

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch
        range source target) :
    target.msize = source.msize :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch.msize_eq
    hRel

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState} {offset : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch
        range source target)
    (hDisjoint : range.disjointBytes offset.toNat 32) :
    target.lookupMemory offset = source.lookupMemory offset :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch.lookupMemory_eq_of_disjoint
    hRel hDisjoint

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState} {offset : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch
        range source target)
    (hDisjoint : range.disjointBytes offset.toNat 32) :
    (target.mload offset).1 = (source.mload offset).1 ∧
      Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch
        range (source.mload offset).2 (target.mload offset).2 :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch.mload_of_disjoint
    hRel hDisjoint

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {machine : EvmYul.MachineState} :
    Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
      range machine machine :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.refl
    range machine

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target) :
    Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
      range target source :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.symm
    hRel

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target) :
    Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch
      range source target :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.toMemoryEqOutsideScratch
    hRel

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState} {offset : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target)
    (hDisjoint : range.disjointBytes offset.toNat 32) :
    (target.mload offset).1 = (source.mload offset).1 ∧
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range (source.mload offset).2 (target.mload offset).2 :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.mload_of_disjoint
    hRel hDisjoint

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState} {offset len : Nat}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target)
    (hDisjoint : range.disjointBytes offset len) :
    target.memory.readWithoutPadding offset len =
      source.memory.readWithoutPadding offset len :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.readWithoutPadding_eq_of_disjoint
    hRel hDisjoint

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState} {offset len : Nat}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target)
    (hDisjoint : range.disjointBytes offset len) :
    target.memory.readWithPadding offset len =
      source.memory.readWithPadding offset len :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.readWithPadding_eq_of_disjoint
    hRel hDisjoint

example {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : ByteArray} {offset len : Nat}
    (hSize : target.size = source.size)
    (hByteEq :
      ∀ idx (_hDisjoint : range.disjointBytes idx 1)
        (hTarget : idx < target.size)
        (hSource : idx < source.size),
          target[idx]'hTarget = source[idx]'hSource)
    (hDisjoint : range.disjointBytes offset len) :
    target.readWithPadding offset len =
      source.readWithPadding offset len :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.byteArray_readWithPadding_eq_of_disjoint_byte_eq
    hSize hByteEq hDisjoint

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {target source bytes : ByteArray} {writeOffset idx : Nat}
    (hBytes : bytes.size = 32)
    (hTargetAlloc : writeOffset + 32 ≤ target.size)
    (hSourceAlloc : writeOffset + 32 ≤ source.size)
    (hByteEq :
      ∀ (hTarget : idx < target.size)
        (hSource : idx < source.size),
          target[idx]'hTarget = source[idx]'hSource)
    (hTargetIdx : idx < (bytes.write 0 target writeOffset 32).size)
    (hSourceIdx : idx < (bytes.write 0 source writeOffset 32).size) :
    (bytes.write 0 target writeOffset 32)[idx]'hTargetIdx =
      (bytes.write 0 source writeOffset 32)[idx]'hSourceIdx :=
  Locals.SourceLowering.StateRel.SpillScratch.byteArray_write32_byte_eq_noExpansion
    hSpec hBytes hTargetAlloc hSourceAlloc hByteEq hTargetIdx hSourceIdx

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState}
    {offset value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target)
    (hTargetAllocated : offset.toNat + 32 ≤ target.memory.size) :
    Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
      range (source.mstore offset value) (target.mstore offset value) :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.mstore_pair_noExpansion
    hSpec hWordBytes hRel hTargetAllocated

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {dest source : ByteArray} {offset : Nat}
    (hSource : source.size = 32)
    (hPadNoOverflow : offset - dest.size < USize.size) :
    (source.write 0 dest offset 32).size =
      max dest.size (offset + 32) :=
  Locals.SourceLowering.StateRel.SpillScratch.byteArray_write32_size_general
    hSpec hSource hPadNoOverflow

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {dest source : ByteArray} {offset : Nat}
    (hSource : source.size = 32)
    (hPadNoOverflow : offset - dest.size < USize.size)
    (hExpanding : ¬ offset + 32 ≤ dest.size) :
    source.write 0 dest offset 32 =
      { data :=
          (dest.data ++
            (ffi.ByteArray.zeroes
              (OfNat.ofNat (offset - dest.size))).data).extract 0 offset ++
            source.data } :=
  Locals.SourceLowering.StateRel.SpillScratch.byteArray_write32_expanding_exact
    hSpec hSource hPadNoOverflow hExpanding

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {target source bytes : ByteArray} {writeOffset idx : Nat}
    (hBytes : bytes.size = 32)
    (hSize : target.size = source.size)
    (hPadNoOverflow : writeOffset - target.size < USize.size)
    (hByteEq :
      ∀ (hTarget : idx < target.size)
        (hSource : idx < source.size),
          target[idx]'hTarget = source[idx]'hSource)
    (hTargetIdx : idx < (bytes.write 0 target writeOffset 32).size)
    (hSourceIdx : idx < (bytes.write 0 source writeOffset 32).size) :
    (bytes.write 0 target writeOffset 32)[idx]'hTargetIdx =
      (bytes.write 0 source writeOffset 32)[idx]'hSourceIdx :=
  Locals.SourceLowering.StateRel.SpillScratch.byteArray_write32_byte_eq_boundedExpansion
    hSpec hBytes hSize hPadNoOverflow hByteEq hTargetIdx hSourceIdx

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState}
    {offset value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target)
    (hTargetPadNoOverflow :
      offset.toNat - target.memory.size < USize.size) :
    Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
      range (source.mstore offset value) (target.mstore offset value) :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.mstore_pair_boundedExpansion
    hSpec hWordBytes hRel hTargetPadNoOverflow

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {dest source : ByteArray}
    {writeOffset readOffset len : Nat}
    (hSource : source.size = 32)
    (hDest : writeOffset + 32 ≤ dest.size)
    (hDisjoint :
      Locals.SourceLowering.StateRel.SpillScratch.ByteDisjoint
        readOffset len writeOffset 32) :
    (source.write 0 dest writeOffset 32).readWithoutPadding
        readOffset len =
      dest.readWithoutPadding readOffset len :=
  Locals.SourceLowering.StateRel.SpillScratch.byteArray_readWithoutPadding_write32_eq_of_byteDisjoint
    hSpec hSource hDest hDisjoint

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {dest source : ByteArray}
    {writeOffset readOffset len : Nat}
    (hSource : source.size = 32)
    (hDest : writeOffset + 32 ≤ dest.size)
    (hDisjoint :
      Locals.SourceLowering.StateRel.SpillScratch.ByteDisjoint
        readOffset len writeOffset 32) :
    (source.write 0 dest writeOffset 32).readWithPadding
        readOffset len =
      dest.readWithPadding readOffset len :=
  Locals.SourceLowering.StateRel.SpillScratch.byteArray_readWithPadding_write32_eq_of_byteDisjoint
    hSpec hSource hDest hDisjoint

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {dest source : ByteArray}
    {writeOffset idx : Nat}
    (hSource : source.size = 32)
    (hDest : writeOffset + 32 ≤ dest.size)
    (hDisjoint :
      Locals.SourceLowering.StateRel.SpillScratch.ByteDisjoint
        idx 1 writeOffset 32)
    (hWrittenIdx : idx < (source.write 0 dest writeOffset 32).size)
    (hDestIdx : idx < dest.size) :
    (source.write 0 dest writeOffset 32)[idx]'hWrittenIdx =
      dest[idx]'hDestIdx :=
  Locals.SourceLowering.StateRel.SpillScratch.byteArray_write32_getElem_eq_of_byteDisjoint
    hSpec hSource hDest hDisjoint hWrittenIdx hDestIdx

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (value : Locals.Word) :
    EvmYul.fromByteArrayBigEndian value.toByteArray = value.toNat :=
  Locals.SourceLowering.StateRel.SpillScratch.word_fromByteArrayBigEndian_toByteArray
    hSpec value

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    {dest source : ByteArray} {offset : Nat}
    (hSource : source.size = 32)
    (hDest : offset + 32 ≤ dest.size) :
    (source.write 0 dest offset 32).readWithPadding offset 32 =
      source :=
  Locals.SourceLowering.StateRel.SpillScratch.byteArray_readWithPadding32_write32_same
    hSpec hSource hDest

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState}
    {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch
        range source target)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        target range.base range.words)
    (hSlot : slot < range.words) :
    Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch
      range source (target.mstore (range.word slot) value) :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch.mstore_target_scratch_slot
    hSpec hWordBytes hRel hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState}
    {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch
        range source target)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.ready?
        target range = true)
    (hSlot : slot < range.words) :
    Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch
      range source (target.mstore (range.word slot) value) :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryEqOutsideScratch.mstore_target_scratch_slot_of_ready?
    hSpec hWordBytes hRel hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState}
    {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        target range.base range.words)
    (hSlot : slot < range.words) :
    Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
      range source (target.mstore (range.word slot) value) :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.mstore_target_scratch_slot
    hSpec hWordBytes hRel hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState}
    {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.ready?
        target range = true)
    (hSlot : slot < range.words) :
    Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
      range source (target.mstore (range.word slot) value) :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.mstore_target_scratch_slot_of_ready?
    hSpec hWordBytes hRel hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState}
    {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        target range.base range.words)
    (hSlot : slot < range.words) :
    ((target.mstore (range.word slot) value).mload
        (range.word slot)).1 =
      value ∧
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source
          ((target.mstore (range.word slot) value).mload
            (range.word slot)).2 :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.mload_after_mstore_target_scratch_slot
    hSpec hWordBytes hRel hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source target : EvmYul.MachineState}
    {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.ready?
        target range = true)
    (hSlot : slot < range.words) :
    ((target.mstore (range.word slot) value).mload
        (range.word slot)).1 =
      value ∧
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source
          ((target.mstore (range.word slot) value).mload
            (range.word slot)).2 :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.mload_after_mstore_target_scratch_slot_of_ready?
    hSpec hWordBytes hRel hReady hSlot

example {state : Locals.EVMState} {offset value : Locals.Word} :
    ∃ final,
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillReloadCode
            offset value) state =
        .ok final ∧
      final.stack =
        ((state.toMachineState.mstore offset value).mload offset).1 ::
          state.stack ∧
      final.toMachineState =
        ((state.toMachineState.mstore offset value).mload offset).2 :=
  Locals.SourceLowering.StateRel.SpillScratch.run_spillReloadCode
    state offset value

example {state : Locals.EVMState} {baseStack : EvmYul.Stack Locals.Word}
    {offset value : Locals.Word} :
    ∃ final,
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillTopReloadCode
            offset) { state with stack := value :: baseStack } =
        .ok final ∧
      final.stack =
        ((state.toMachineState.mstore offset value).mload offset).1 ::
          baseStack ∧
      final.toMachineState =
        ((state.toMachineState.mstore offset value).mload offset).2 :=
  Locals.SourceLowering.StateRel.SpillScratch.run_spillTopReloadCode
    state baseStack offset value

example {state : Locals.EVMState} {baseStack : EvmYul.Stack Locals.Word}
    {offset value : Locals.Word} :
    ∃ final,
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillStoreTopCode
            offset) { state with stack := value :: baseStack } =
        .ok final ∧
      final.stack = baseStack ∧
      final.toMachineState =
        state.toMachineState.mstore offset value :=
  Locals.SourceLowering.StateRel.SpillScratch.run_spillStoreTopCode
    state baseStack offset value

example {state : Locals.EVMState} {baseStack : EvmYul.Stack Locals.Word}
    {offset value : Locals.Word} :
    ∃ final,
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillStoreTopCode
            offset) { state with stack := value :: baseStack } =
        .ok final ∧
      final.stack = baseStack ∧
      final.toMachineState =
        state.toMachineState.mstore offset value ∧
      final.toSharedState =
        ({ state with
          toMachineState := state.toMachineState.mstore offset value } :
          Locals.EVMState).toSharedState :=
  Locals.SourceLowering.StateRel.SpillScratch.run_spillStoreTopCode_shared
    state baseStack offset value

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source : EvmYul.MachineState} {target : Locals.EVMState}
    {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target.toMachineState)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        target.toMachineState range.base range.words)
    (hSlot : slot < range.words) :
    ∃ final,
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillReloadCode
            (range.word slot) value) target =
        .ok final ∧
      final.stack = value :: target.stack ∧
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source final.toMachineState :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.run_spillReloadCode_target_scratch_slot
    hSpec hWordBytes hRel hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source : EvmYul.MachineState} {target : Locals.EVMState}
    {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target.toMachineState)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.ready?
        target.toMachineState range = true)
    (hSlot : slot < range.words) :
    ∃ final,
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillReloadCode
            (range.word slot) value) target =
        .ok final ∧
      final.stack = value :: target.stack ∧
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source final.toMachineState :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.run_spillReloadCode_target_scratch_slot_of_ready?
    hSpec hWordBytes hRel hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source : EvmYul.MachineState} {target : Locals.EVMState}
    {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target.toMachineState)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        target.toMachineState range.base range.words)
    (hSlot : slot < range.words) :
    ∃ final,
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillTopReloadCode
            (range.word slot))
          { target with stack := value :: target.stack } =
        .ok final ∧
      final.stack = value :: target.stack ∧
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source final.toMachineState :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.run_spillTopReloadCode_target_scratch_slot
    hSpec hWordBytes hRel hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source : EvmYul.MachineState} {target : Locals.EVMState}
    {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target.toMachineState)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.ready?
        target.toMachineState range = true)
    (hSlot : slot < range.words) :
    ∃ final,
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillTopReloadCode
            (range.word slot))
          { target with stack := value :: target.stack } =
        .ok final ∧
      final.stack = value :: target.stack ∧
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source final.toMachineState :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.run_spillTopReloadCode_target_scratch_slot_of_ready?
    hSpec hWordBytes hRel hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source : EvmYul.MachineState} {target : Locals.EVMState}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {store : Locals.Source.Store}
    {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target.toMachineState)
    (hLayout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed
        range sourceScope stackLayout layout)
    (hValues :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
        range store target.toMachineState target.stack layout)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        target.toMachineState range.base range.words)
    (hSlot : slot < range.words)
    (hStoreMatches :
      ∀ {name : Locals.Name},
        (name,
          Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
            slot) ∈ layout →
          store name = some value) :
    ∃ final,
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillTopReloadCode
            (range.word slot))
          { target with stack := value :: target.stack } =
        .ok final ∧
      final.stack = value :: target.stack ∧
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source final.toMachineState ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
        range store final.toMachineState target.stack layout :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.run_spillTopReloadCode_target_scratch_slot_valueRel
    hSpec hWordBytes hRel hLayout hValues hReady hSlot hStoreMatches

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source : EvmYul.MachineState} {target : Locals.EVMState}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {store : Locals.Source.Store}
    {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target.toMachineState)
    (hLayout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed
        range sourceScope stackLayout layout)
    (hValues :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
        range store target.toMachineState target.stack layout)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.ready?
        target.toMachineState range = true)
    (hSlot : slot < range.words)
    (hStoreMatches :
      ∀ {name : Locals.Name},
        (name,
          Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
            slot) ∈ layout →
          store name = some value) :
    ∃ final,
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillTopReloadCode
            (range.word slot))
          { target with stack := value :: target.stack } =
        .ok final ∧
      final.stack = value :: target.stack ∧
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source final.toMachineState ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
        range store final.toMachineState target.stack layout :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.run_spillTopReloadCode_target_scratch_slot_valueRel_of_ready?
    hSpec hWordBytes hRel hLayout hValues hReady hSlot hStoreMatches

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source : EvmYul.MachineState} {target : Locals.EVMState}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {store : Locals.Source.Store}
    {name : Locals.Name} {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target.toMachineState)
    (hLayout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed
        range sourceScope stackLayout layout)
    (hValues :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
        range store target.toMachineState target.stack layout)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        target.toMachineState range.base range.words)
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
          slot) ∈ layout) :
    ∃ final,
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillStoreTopCode
            (range.word slot))
          { target with stack := value :: target.stack } =
        .ok final ∧
      final.stack = target.stack ∧
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source final.toMachineState ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
        range (Locals.Source.Store.insert store name value)
        final.toMachineState target.stack layout :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.run_spillStoreTopCode_target_scratch_binding_assign
    hSpec hWordBytes hRel hLayout hValues hReady hBinding

example {state : Locals.EVMState} {offset : Locals.Word} :
    ∃ final,
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillLoadCode
            offset) state =
        .ok final ∧
      final.stack =
        (state.toMachineState.mload offset).1 :: state.stack ∧
      final.toMachineState =
        (state.toMachineState.mload offset).2 :=
  Locals.SourceLowering.StateRel.SpillScratch.run_spillLoadCode
    state offset

example {state : Locals.EVMState} {offset : Locals.Word} :
    ∃ final,
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillLoadCode
            offset) state =
        .ok final ∧
      final.stack =
        (state.toMachineState.mload offset).1 :: state.stack ∧
      final.toMachineState =
        (state.toMachineState.mload offset).2 ∧
      final.toSharedState =
        ({ state with
          toMachineState := (state.toMachineState.mload offset).2 } :
          Locals.EVMState).toSharedState :=
  Locals.SourceLowering.StateRel.SpillScratch.run_spillLoadCode_shared
    state offset

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source : Locals.Source.State} {target : Locals.EVMState}
    {stackPrefix : List Locals.Word}
    {name : Locals.Name} {slot : Nat}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source stackPrefix target)
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
          slot) ∈ layout) :
    ∃ value final,
      source.vars name = some value ∧
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillLoadCode
            (range.word slot)) target =
        .ok final ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source
        (value :: stackPrefix) final :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.run_spillLoadCode_scratch_binding
    hRel hBinding

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source : Locals.Source.State} {target : Locals.EVMState}
    {name : Locals.Name} {slot : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source [value] target)
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
          slot) ∈ layout) :
    ∃ final,
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillStoreTopCode
            (range.word slot)) target =
        .ok final ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout
        (source.withVars
          (Locals.Source.Store.insert source.vars name value))
        final :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.run_spillStoreTopCode_scratch_assign
    hSpec hWordBytes hRel hBinding

example
    {prim : Locals.Source.PrimitiveSemantics}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source : Locals.Source.State} {target : Locals.EVMState}
    {stackPrefix : List Locals.Word}
    {name : Locals.Name} {slot : Nat}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source stackPrefix target)
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
          slot) ∈ layout) :
    ∃ value code final,
      Locals.Source.Expr.eval prim (Locals.Expr.var name) source =
        .ok (source, [value]) ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.readCode?
        range stackPrefix.length name layout = some code ∧
      Structured.Code.run code target = .ok final ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source
        (value :: stackPrefix) final :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.readCode_scratch_var_bridge
    hRel hBinding

example
    {prim : Locals.Source.PrimitiveSemantics}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source : Locals.Source.State} {target : Locals.EVMState}
    {stackPrefix : List Locals.Word}
    {name : Locals.Name} {depth : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source stackPrefix target)
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.stack
          depth) ∈ layout)
    (hStore : source.vars name = some value)
    (hBound : stackPrefix.length + depth + 1 ≤ 16) :
    ∃ code final,
      Locals.Source.Expr.eval prim (Locals.Expr.var name) source =
        .ok (source, [value]) ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.readCode?
        range stackPrefix.length name layout = some code ∧
      Structured.Code.run code target = .ok final ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source
        (value :: stackPrefix) final :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.readCode_stack_var_bridge
    hRel hBinding hStore hBound

example
    {prim : Locals.Source.PrimitiveSemantics}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source : Locals.Source.State} {target : Locals.EVMState}
    {stackPrefix : List Locals.Word} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source stackPrefix target) :
    ∃ code final,
      Locals.Source.Expr.eval prim (Locals.Expr.lit value) source =
        .ok (source, [value]) ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileOneCode?
        range stackPrefix.length layout (Locals.Expr.lit value) =
          some code ∧
      Structured.Code.run code target = .ok final ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source
        (value :: stackPrefix) final :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.compileOneCode_lit_bridge
    hRel

example
    {prim : Locals.Source.PrimitiveSemantics}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source : Locals.Source.State} {target : Locals.EVMState}
    {stackPrefix : List Locals.Word}
    {name : Locals.Name} {slot : Nat}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source stackPrefix target)
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
          slot) ∈ layout) :
    ∃ value code final,
      Locals.Source.Expr.eval prim (Locals.Expr.var name) source =
        .ok (source, [value]) ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileOneCode?
        range stackPrefix.length layout (Locals.Expr.var name) = some code ∧
      Structured.Code.run code target = .ok final ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source
        (value :: stackPrefix) final :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.compileOneCode_scratch_var_bridge
    hRel hBinding

example
    {prim : Locals.Source.PrimitiveSemantics}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source : Locals.Source.State} {target : Locals.EVMState}
    {stackPrefix : List Locals.Word}
    {name : Locals.Name} {depth : Nat} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source stackPrefix target)
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.stack
          depth) ∈ layout)
    (hStore : source.vars name = some value)
    (hBound : stackPrefix.length + depth + 1 ≤ 16) :
    ∃ code final,
      Locals.Source.Expr.eval prim (Locals.Expr.var name) source =
        .ok (source, [value]) ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileOneCode?
        range stackPrefix.length layout (Locals.Expr.var name) = some code ∧
      Structured.Code.run code target = .ok final ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source
        (value :: stackPrefix) final :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.compileOneCode_stack_var_bridge
    hRel hBinding hStore hBound

example {n : Nat} {op : Structured.BasicOp}
    (hDup : Locals.StackOp.dup? n = some op) :
    1 ≤ n ∧ n ≤ 16 :=
  Locals.SourceLowering.StateRel.SpillScratch.stackOp_dup?_some_bound hDup

example {n : Nat} {op : Structured.BasicOp}
    (hSwap : Locals.StackOp.swap? n = some op) :
    1 ≤ n ∧ n ≤ 16 :=
  Locals.SourceLowering.StateRel.SpillScratch.stackOp_swap?_some_bound hSwap

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {offset : Nat}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout} :
    Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileSeqCode?
      range offset layout Locals.ExprSeq.nil = some [] :=
  rfl

example
    {prim : Locals.Source.PrimitiveSemantics}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source source' : Locals.Source.State} {target : Locals.EVMState}
    {stackPrefix : List Locals.Word} {offset results : Nat}
    {expr : Locals.Expr results} {values : List Locals.Word}
    {code : Structured.Code}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source stackPrefix target)
    (hPrefixLen : stackPrefix.length = offset)
    (hCompile :
      Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileOneCode?
        range offset layout expr = some code)
    (hEval :
      Locals.Source.Expr.eval prim expr source = .ok (source', values)) :
    ∃ final,
      Structured.Code.run code target = .ok final ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source'
        (values.reverse ++ stackPrefix) final :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.compileOneCode_bridge
    hRel hPrefixLen hCompile hEval

example
    {prim : Locals.Source.PrimitiveSemantics}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {offset : Nat}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {results : Nat} {expr : Locals.Expr results}
    {source source' : Locals.Source.State}
    {values : List Locals.Word} {code : Structured.Code}
    (hCompile :
      Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileOneCode?
        range offset layout expr = some code)
    (hEval :
      Locals.Source.Expr.eval prim expr source = .ok (source', values)) :
    values.length = results :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.compileOneCode_eval_length
    hCompile hEval

example
    {prim : Locals.Source.PrimitiveSemantics}
    {results : Nat} {exprs : Locals.ExprSeq results}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source source' : Locals.Source.State} {target : Locals.EVMState}
    {stackPrefix : List Locals.Word} {offset : Nat}
    {values : List Locals.Word} {code : Structured.Code}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source stackPrefix target)
    (hPrefixLen : stackPrefix.length = offset)
    (hCompile :
      Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileSeqCode?
        range offset layout exprs = some code)
    (hEval :
      Locals.Source.Expr.ExprSeq.eval prim exprs source =
        .ok (source', values)) :
    ∃ final,
      Structured.Code.run code target = .ok final ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source'
        (values.reverse ++ stackPrefix) final :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.compileSeqCode_bridge
    hRel hPrefixLen hCompile hEval

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {offset : Nat}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {value : Locals.Word} :
    Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileCode?
      range offset layout (Locals.Expr.lit value) =
        some [Structured.BasicInstr.push value] :=
  rfl

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {offset : Nat}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout} :
    Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileSeqFullCode?
      range offset layout Locals.ExprSeq.nil = some [] :=
  rfl

example
    {prim : Locals.Source.PrimitiveSemantics}
    (hPrim :
      Locals.SourceLowering.StateRel.SpillScratch.PrimitiveScratchSound
        prim)
    {results : Nat} {expr : Locals.Expr results}
    {source source' : Locals.Source.State}
    {values : List Locals.Word}
    (hSafe :
      Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.ExprSafe
        expr)
    (hEval :
      Locals.Source.Expr.eval prim expr source = .ok (source', values)) :
    values.length = results :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.eval_length_of_exprSafe
    hPrim hSafe hEval

example :
    Locals.SourceLowering.StateRel.SpillScratch.PrimitiveScratchSound
      Locals.Source.PrimitiveSemantics.structured :=
  Locals.SourceLowering.PrimitiveSemantics.structuredScratchSound

example
    {prim : Locals.Source.PrimitiveSemantics}
    (hPrim :
      Locals.SourceLowering.StateRel.SpillScratch.PrimitiveScratchSound
        prim)
    {results : Nat} {expr : Locals.Expr results}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source source' : Locals.Source.State} {target : Locals.EVMState}
    {stackPrefix : List Locals.Word} {offset : Nat}
    {values : List Locals.Word} {code : Structured.Code}
    (hSafe :
      Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.ExprSafe
        expr)
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source stackPrefix target)
    (hPrefixLen : stackPrefix.length = offset)
    (hCompile :
      Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileCode?
        range offset layout expr = some code)
    (hEval :
      Locals.Source.Expr.eval prim expr source = .ok (source', values)) :
    ∃ final,
      Structured.Code.run code target = .ok final ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source'
        (values.reverse ++ stackPrefix) final :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.compileCode_bridge
    hPrim hSafe hRel hPrefixLen hCompile hEval

example
    {prim : Locals.Source.PrimitiveSemantics}
    (hPrim :
      Locals.SourceLowering.StateRel.SpillScratch.PrimitiveScratchSound
        prim)
    {results : Nat} {exprs : Locals.ExprSeq results}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source source' : Locals.Source.State} {target : Locals.EVMState}
    {stackPrefix : List Locals.Word} {offset : Nat}
    {values : List Locals.Word} {code : Structured.Code}
    (hSafe :
      Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.ExprSeqSafe
        exprs)
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source stackPrefix target)
    (hPrefixLen : stackPrefix.length = offset)
    (hCompile :
      Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileSeqFullCode?
        range offset layout exprs = some code)
    (hEval :
      Locals.Source.Expr.ExprSeq.eval prim exprs source =
        .ok (source', values)) :
    ∃ final,
      Structured.Code.run code target = .ok final ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source'
        (values.reverse ++ stackPrefix) final :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.compileSeqFullCode_bridge
    hPrim hSafe hRel hPrefixLen hCompile hEval

example
    {results : Nat} {expr : Locals.Expr results}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source source' : Locals.Source.State} {target : Locals.EVMState}
    {stackPrefix : List Locals.Word} {offset : Nat}
    {values : List Locals.Word} {code : Structured.Code}
    (hSafe :
      Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.ExprSafe
        expr)
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source stackPrefix target)
    (hPrefixLen : stackPrefix.length = offset)
    (hCompile :
      Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileCode?
        range offset layout expr = some code)
    (hEval :
      Locals.Source.Expr.eval Locals.Source.PrimitiveSemantics.structured
          expr source =
        .ok (source', values)) :
    ∃ final,
      Structured.Code.run code target = .ok final ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source'
        (values.reverse ++ stackPrefix) final :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.compileCode_bridge_structured
    hSafe hRel hPrefixLen hCompile hEval

example
    {results : Nat} {exprs : Locals.ExprSeq results}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source source' : Locals.Source.State} {target : Locals.EVMState}
    {stackPrefix : List Locals.Word} {offset : Nat}
    {values : List Locals.Word} {code : Structured.Code}
    (hSafe :
      Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.ExprSeqSafe
        exprs)
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source stackPrefix target)
    (hPrefixLen : stackPrefix.length = offset)
    (hCompile :
      Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileSeqFullCode?
        range offset layout exprs = some code)
    (hEval :
      Locals.Source.Expr.ExprSeq.eval
          Locals.Source.PrimitiveSemantics.structured exprs source =
        .ok (source', values)) :
    ∃ final,
      Structured.Code.run code target = .ok final ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source'
        (values.reverse ++ stackPrefix) final :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.compileSeqFullCode_bridge_structured
    hSafe hRel hPrefixLen hCompile hEval

example
    {expr : Locals.Expr 0}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source source' : Locals.Source.State} {target : Locals.EVMState}
    {values : List Locals.Word} {code : Structured.Code}
    (hSafe :
      Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.ExprSafe
        expr)
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout source target)
    (hCompile :
      Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileCode?
        range 0 layout expr = some code)
    (hEval :
      Locals.Source.Expr.eval Locals.Source.PrimitiveSemantics.structured
          expr source =
        .ok (source', values)) :
    ∃ final,
      Structured.Code.run code target = .ok final ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout source' final :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.compileCode_zero_spillStateRel_structured
    hSafe hRel hCompile hEval

example
    {expr : Locals.Expr 0}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source source' : Locals.Source.State} {target : Locals.EVMState}
    {values : List Locals.Word} {code : Structured.Code}
    (hSafe :
      Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.ExprSafe
        expr)
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout source target)
    (hCompile :
      Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileCode?
        range 0 layout expr = some code)
    (hEval :
      Locals.Source.Expr.eval Locals.Source.PrimitiveSemantics.structured
          expr source =
        .ok (source', values)) :
    ∃ result,
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
          (Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.Code
            code) target =
        .ok result ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
        range sourceScope stackLayout layout
        (Locals.Source.Outcome.regular source') result :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.compileCode_zero_spillOutcomeRel_structured
    hSafe hRel hCompile hEval

example
    (pre : Structured.Code)
    (tail : Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode)
    (target : Locals.EVMState) :
    Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
        (Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.prependCode
          pre tail) target =
      (do
        let afterPrefix ← Structured.Code.run pre target
        Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run tail
          afterPrefix) :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run_prependCode
    pre tail target

example
    (head tail :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode)
    (target : Locals.EVMState) :
    Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
        (Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.seq
          head tail) target =
      (do
        let headResult ←
          Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
            head target
        Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.continueWith
          tail headResult) :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run_seq
    head tail target

example
    {head tail :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode}
    {target targetMid : Locals.EVMState}
    {result :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtResult}
    (hHeadRun :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
        head target =
          .ok
            (Locals.SourceLowering.StateRel.SpillScratch.SpillStmtResult.regular
              targetMid))
    (hTailRun :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
        tail targetMid =
          .ok result) :
    Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
        (Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.seq
          head tail) target =
      .ok result :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run_seq_regular
    hHeadRun hTailRun

example
    {head tail :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode}
    {target targetHalt : Locals.EVMState}
    {kind : Assembly.HaltKind}
    (hHeadRun :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
        head target =
          .ok
            (Locals.SourceLowering.StateRel.SpillScratch.SpillStmtResult.halt
              kind targetHalt)) :
    Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
        (Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.seq
          head tail) target =
      .ok
        (Locals.SourceLowering.StateRel.SpillScratch.SpillStmtResult.halt
          kind targetHalt) :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run_seq_halt
    hHeadRun

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source : Locals.Source.State}
    {result :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtResult}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
        range sourceScope stackLayout layout
        (Locals.Source.Outcome.regular source) result) :
    ∃ target,
      result =
          Locals.SourceLowering.StateRel.SpillScratch.SpillStmtResult.regular
            target ∧
        Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
          range sourceScope stackLayout layout source target :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel.regular_inv
    hRel

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {kind : Assembly.HaltKind}
    {source : Locals.Source.State}
    {result :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtResult}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
        range sourceScope stackLayout layout
        (Locals.Source.Outcome.halt kind source) result) :
    ∃ target,
      result =
          Locals.SourceLowering.StateRel.SpillScratch.SpillStmtResult.halt
            kind target ∧
        Locals.SourceLowering.StateRel.SpillScratch.SpillHaltRel
          range source target :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel.halt_inv
    hRel

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout sourceScope' stackLayout' : List Locals.Name}
    {layout layout' :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {kind : Assembly.HaltKind}
    {source : Locals.Source.State}
    {result :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtResult}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
        range sourceScope stackLayout layout
        (Locals.Source.Outcome.halt kind source) result) :
    Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
      range sourceScope' stackLayout' layout'
      (Locals.Source.Outcome.halt kind source) result :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel.halt_layout_irrelevant
    hRel

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {headSourceScope headStackLayout tailSourceScope tailStackLayout :
      List Locals.Name}
    {headLayout tailLayout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {head tail :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode}
    {target : Locals.EVMState}
    {sourceMid : Locals.Source.State}
    {sourceTail : Locals.Source.Outcome}
    {headResult :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtResult}
    (hHeadRun :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
        head target =
        .ok headResult)
    (hHeadRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
        range headSourceScope headStackLayout headLayout
        (Locals.Source.Outcome.regular sourceMid) headResult)
    (hTail :
      ∀ targetMid,
        Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
          range headSourceScope headStackLayout headLayout
          sourceMid targetMid →
        ∃ tailResult,
          Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
            tail targetMid =
            .ok tailResult ∧
          Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
            range tailSourceScope tailStackLayout tailLayout
            sourceTail tailResult) :
    ∃ result,
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
        (Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.seq
          head tail) target =
        .ok result ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
        range tailSourceScope tailStackLayout tailLayout
        sourceTail result :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel.seq_regular_preserves
    hHeadRun hHeadRel hTail

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {headSourceScope headStackLayout tailSourceScope tailStackLayout :
      List Locals.Name}
    {headLayout tailLayout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {head tail :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode}
    {target : Locals.EVMState}
    {kind : Assembly.HaltKind}
    {sourceHalt : Locals.Source.State}
    {headResult :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtResult}
    (hHeadRun :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
        head target =
        .ok headResult)
    (hHeadRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
        range headSourceScope headStackLayout headLayout
        (Locals.Source.Outcome.halt kind sourceHalt) headResult) :
    ∃ result,
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
        (Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.seq
          head tail) target =
        .ok result ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
        range tailSourceScope tailStackLayout tailLayout
        (Locals.Source.Outcome.halt kind sourceHalt) result :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel.seq_halt_preserves
    hHeadRun hHeadRel

example :
    Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.skip =
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.Code [] :=
  rfl

example
    (target : Locals.EVMState) :
    Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
        Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.skip
        target =
      .ok
        (Locals.SourceLowering.StateRel.SpillScratch.SpillStmtResult.regular
          target) :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run_skip
    target

example
    (target : Locals.EVMState) :
    Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
        (Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.seqList
          []) target =
      .ok
        (Locals.SourceLowering.StateRel.SpillScratch.SpillStmtResult.regular
          target) :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run_seqList_nil
    target

example
    (head : Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode)
    (tail : List
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode)
    (target : Locals.EVMState) :
    Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
        (Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.seqList
          (head :: tail)) target =
      (do
        let headResult ←
          Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
            head target
        Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.continueWith
          (Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.seqList
            tail) headResult) :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run_seqList_cons
    head tail target

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.toExpressionsBlock

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.toExpressionsOutcome

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run_toExpressionsBlock_exists

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source : Locals.Source.State}
    {target : Locals.EVMState}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout source target) :
    ∃ result,
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
        Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.skip
        target =
        .ok result ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
        range sourceScope stackLayout layout
        (Locals.Source.Outcome.regular source) result :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel.skip_preserves
    hRel

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source : Locals.Source.State}
    {target : Locals.EVMState}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout source target) :
    ∃ result,
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
        (Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.seqList
          []) target =
        .ok result ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
        range sourceScope stackLayout layout
        (Locals.Source.Outcome.regular source) result :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel.seqList_nil_preserves
    hRel

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {headSourceScope headStackLayout tailSourceScope tailStackLayout :
      List Locals.Name}
    {headLayout tailLayout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {head : Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode}
    {tail : List
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode}
    {target : Locals.EVMState}
    {sourceMid : Locals.Source.State}
    {sourceTail : Locals.Source.Outcome}
    {headResult :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtResult}
    (hHeadRun :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
        head target =
        .ok headResult)
    (hHeadRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
        range headSourceScope headStackLayout headLayout
        (Locals.Source.Outcome.regular sourceMid) headResult)
    (hTail :
      ∀ targetMid,
        Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
          range headSourceScope headStackLayout headLayout
          sourceMid targetMid →
        ∃ tailResult,
          Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
            (Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.seqList
              tail) targetMid =
            .ok tailResult ∧
          Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
            range tailSourceScope tailStackLayout tailLayout
            sourceTail tailResult) :
    ∃ result,
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
        (Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.seqList
          (head :: tail)) target =
        .ok result ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
        range tailSourceScope tailStackLayout tailLayout
        sourceTail result :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel.seqList_cons_regular_preserves
    hHeadRun hHeadRel hTail

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {headSourceScope headStackLayout tailSourceScope tailStackLayout :
      List Locals.Name}
    {headLayout tailLayout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {head : Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode}
    {tail : List
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode}
    {target : Locals.EVMState}
    {kind : Assembly.HaltKind}
    {sourceHalt : Locals.Source.State}
    {headResult :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtResult}
    (hHeadRun :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
        head target =
        .ok headResult)
    (hHeadRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
        range headSourceScope headStackLayout headLayout
        (Locals.Source.Outcome.halt kind sourceHalt) headResult) :
    ∃ result,
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
        (Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.seqList
          (head :: tail)) target =
        .ok result ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
        range tailSourceScope tailStackLayout tailLayout
        (Locals.Source.Outcome.halt kind sourceHalt) result :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel.seqList_cons_halt_preserves
    hHeadRun hHeadRel

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {name : Locals.Name}
    (hLayout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed
        range sourceScope stackLayout layout)
    (hFresh : name ∉ sourceScope) :
    Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed
      range (name :: sourceScope) (name :: stackLayout)
      (Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.pushStackLayout
        name layout) :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed.pushStack
    hLayout hFresh

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {name : Locals.Name} {slot : Nat}
    (hLayout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed
        range sourceScope stackLayout layout)
    (hFresh : name ∉ sourceScope)
    (hSlot : slot < range.words)
    (hSlotFresh :
      slot ∉
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.scratchSlots
          layout) :
    Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed
      range (name :: sourceScope) stackLayout
      (Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.pushScratchLayout
        name slot layout) :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed.pushScratch
    hLayout hFresh hSlot hSlotFresh

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source : Locals.Source.State} {target : Locals.EVMState}
    {name : Locals.Name} {value : Locals.Word}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel
        range sourceScope stackLayout layout source [value] target)
    (hFresh : name ∉ sourceScope) :
    Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
      range (name :: sourceScope) (name :: stackLayout)
      (Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.pushStackLayout
        name layout)
      (source.insert name value) target :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.to_spillStateRel_cons_insert_stack
    hRel hFresh

example
    {expr : Locals.Expr 1}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source sourceAfterValue : Locals.Source.State}
    {target : Locals.EVMState}
    {name : Locals.Name} {value : Locals.Word} {code : Structured.Code}
    (hSafe :
      Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.ExprSafe
        expr)
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout source target)
    (hFresh : name ∉ sourceScope)
    (hCompile :
      Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileCode?
        range 0 layout expr = some code)
    (hEval :
      Locals.Source.Expr.eval Locals.Source.PrimitiveSemantics.structured
          expr source =
        .ok (sourceAfterValue, [value])) :
    ∃ final,
      Structured.Code.run code target = .ok final ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range (name :: sourceScope) (name :: stackLayout)
        (Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.pushStackLayout
          name layout)
        (sourceAfterValue.insert name value) final :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.compileCode_one_letStack_spillStateRel_structured
    hSafe hRel hFresh hCompile hEval

example
    {expr : Locals.Expr 1}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source sourceAfterValue : Locals.Source.State}
    {target : Locals.EVMState}
    {name : Locals.Name} {value : Locals.Word} {code : Structured.Code}
    (hSafe :
      Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.ExprSafe
        expr)
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout source target)
    (hFresh : name ∉ sourceScope)
    (hCompile :
      Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileCode?
        range 0 layout expr = some code)
    (hEval :
      Locals.Source.Expr.eval Locals.Source.PrimitiveSemantics.structured
          expr source =
        .ok (sourceAfterValue, [value])) :
    ∃ result,
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
          (Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.Code
            code) target =
        .ok result ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
        range (name :: sourceScope) (name :: stackLayout)
        (Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.pushStackLayout
          name layout)
        (Locals.Source.Outcome.regular
          (sourceAfterValue.insert name value)) result :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.compileCode_one_letStack_spillOutcomeRel_structured
    hSafe hRel hFresh hCompile hEval

example
    (hSpec :
      Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {expr : Locals.Expr 1}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source sourceAfterValue : Locals.Source.State}
    {target : Locals.EVMState}
    {name : Locals.Name} {slot : Nat} {value : Locals.Word}
    {code : Structured.Code}
    (hSafe :
      Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.ExprSafe
        expr)
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout source target)
    (hFresh : name ∉ sourceScope)
    (hSlot : slot < range.words)
    (hSlotFresh :
      slot ∉
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.scratchSlots
          layout)
    (hCompile :
      Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileCode?
        range 0 layout expr = some code)
    (hEval :
      Locals.Source.Expr.eval Locals.Source.PrimitiveSemantics.structured
          expr source =
        .ok (sourceAfterValue, [value])) :
    ∃ final,
      Structured.Code.run
          (code ++
            Locals.SourceLowering.StateRel.SpillScratch.spillStoreTopCode
              (range.word slot)) target =
        .ok final ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range (name :: sourceScope) stackLayout
        (Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.pushScratchLayout
          name slot layout)
        (sourceAfterValue.insert name value) final :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.compileCode_one_letScratch_spillStateRel_structured
    hSpec hWordBytes hSafe hRel hFresh hSlot hSlotFresh hCompile hEval

example
    (hSpec :
      Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {expr : Locals.Expr 1}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source sourceAfterValue : Locals.Source.State}
    {target : Locals.EVMState}
    {name : Locals.Name} {slot : Nat} {value : Locals.Word}
    {code : Structured.Code}
    (hSafe :
      Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.ExprSafe
        expr)
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout source target)
    (hFresh : name ∉ sourceScope)
    (hSlot : slot < range.words)
    (hSlotFresh :
      slot ∉
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.scratchSlots
          layout)
    (hCompile :
      Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileCode?
        range 0 layout expr = some code)
    (hEval :
      Locals.Source.Expr.eval Locals.Source.PrimitiveSemantics.structured
          expr source =
        .ok (sourceAfterValue, [value])) :
    ∃ result,
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
          (Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.Code
            (code ++
              Locals.SourceLowering.StateRel.SpillScratch.spillStoreTopCode
                (range.word slot))) target =
        .ok result ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
        range (name :: sourceScope) stackLayout
        (Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.pushScratchLayout
          name slot layout)
        (Locals.Source.Outcome.regular
          (sourceAfterValue.insert name value)) result :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.compileCode_one_letScratch_spillOutcomeRel_structured
    hSpec hWordBytes hSafe hRel hFresh hSlot hSlotFresh hCompile hEval

example
    (hSpec :
      Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {expr : Locals.Expr 1}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source sourceAfterValue : Locals.Source.State}
    {target : Locals.EVMState}
    {name : Locals.Name} {slot : Nat} {value : Locals.Word}
    {code : Structured.Code}
    (hSafe :
      Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.ExprSafe
        expr)
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout source target)
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
          slot) ∈ layout)
    (hCompile :
      Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileCode?
        range 0 layout expr = some code)
    (hEval :
      Locals.Source.Expr.eval Locals.Source.PrimitiveSemantics.structured
          expr source =
        .ok (sourceAfterValue, [value])) :
    ∃ final,
      Structured.Code.run
          (code ++
            Locals.SourceLowering.StateRel.SpillScratch.spillStoreTopCode
              (range.word slot)) target =
        .ok final ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout
        (sourceAfterValue.withVars
          (Locals.Source.Store.insert sourceAfterValue.vars name value))
        final :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.compileCode_one_assignScratch_spillStateRel_structured
    hSpec hWordBytes hSafe hRel hBinding hCompile hEval

example
    (hSpec :
      Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {expr : Locals.Expr 1}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source sourceAfterValue : Locals.Source.State}
    {target : Locals.EVMState}
    {name : Locals.Name} {slot : Nat} {value : Locals.Word}
    {code : Structured.Code}
    (hSafe :
      Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.ExprSafe
        expr)
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout source target)
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
          slot) ∈ layout)
    (hCompile :
      Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileCode?
        range 0 layout expr = some code)
    (hEval :
      Locals.Source.Expr.eval Locals.Source.PrimitiveSemantics.structured
          expr source =
        .ok (sourceAfterValue, [value])) :
    ∃ result,
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
          (Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.Code
            (code ++
              Locals.SourceLowering.StateRel.SpillScratch.spillStoreTopCode
                (range.word slot))) target =
        .ok result ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
        range sourceScope stackLayout layout
        (Locals.Source.Outcome.regular
          (sourceAfterValue.withVars
            (Locals.Source.Store.insert sourceAfterValue.vars name value)))
        result :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.compileCode_one_assignScratch_spillOutcomeRel_structured
    hSpec hWordBytes hSafe hRel hBinding hCompile hEval

example
    {expr : Locals.Expr 1}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source sourceAfterValue : Locals.Source.State}
    {target : Locals.EVMState}
    {name : Locals.Name} {depth : Nat} {value : Locals.Word}
    {swapOp : Structured.BasicOp} {code : Structured.Code}
    (hSafe :
      Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.ExprSafe
        expr)
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout source target)
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.stack
          depth) ∈ layout)
    (hContains :
      sourceAfterValue.vars.contains name = true)
    (hBound : depth + 1 ≤ 16)
    (hSwap : Locals.StackOp.swap? (depth + 1) = some swapOp)
    (hCompile :
      Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileCode?
        range 0 layout expr = some code)
    (hEval :
      Locals.Source.Expr.eval Locals.Source.PrimitiveSemantics.structured
          expr source =
        .ok (sourceAfterValue, [value])) :
    ∃ final,
      Structured.Code.run
          (code ++
            [Structured.BasicInstr.op swapOp,
              Structured.BasicInstr.op .pop]) target =
        .ok final ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout
        (sourceAfterValue.withVars
          (Locals.Source.Store.insert sourceAfterValue.vars name value))
        final :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.compileCode_one_assignStack_spillStateRel_structured
    hSafe hRel hBinding hContains hBound hSwap hCompile hEval

example
    {expr : Locals.Expr 1}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source sourceAfterValue : Locals.Source.State}
    {target : Locals.EVMState}
    {name : Locals.Name} {depth : Nat} {value : Locals.Word}
    {swapOp : Structured.BasicOp} {code : Structured.Code}
    (hSafe :
      Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.ExprSafe
        expr)
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout source target)
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.stack
          depth) ∈ layout)
    (hContains :
      sourceAfterValue.vars.contains name = true)
    (hBound : depth + 1 ≤ 16)
    (hSwap : Locals.StackOp.swap? (depth + 1) = some swapOp)
    (hCompile :
      Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileCode?
        range 0 layout expr = some code)
    (hEval :
      Locals.Source.Expr.eval Locals.Source.PrimitiveSemantics.structured
          expr source =
        .ok (sourceAfterValue, [value])) :
    ∃ result,
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
          (Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.Code
            (code ++
              [Structured.BasicInstr.op swapOp,
                Structured.BasicInstr.op .pop])) target =
        .ok result ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
        range sourceScope stackLayout layout
        (Locals.Source.Outcome.regular
          (sourceAfterValue.withVars
            (Locals.Source.Store.insert sourceAfterValue.vars name value)))
        result :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.compileCode_one_assignStack_spillOutcomeRel_structured
    hSafe hRel hBinding hContains hBound hSwap hCompile hEval

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source : EvmYul.MachineState} {target : Locals.EVMState}
    {slot : Nat}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target.toMachineState)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        target.toMachineState range.base range.words)
    (hSlot : slot < range.words) :
    ∃ final,
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillLoadCode
            (range.word slot)) target =
        .ok final ∧
      final.stack =
        (target.toMachineState.mload (range.word slot)).1 ::
          target.stack ∧
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source final.toMachineState :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.run_spillLoadCode_target_scratch_slot
    hRel hReady hSlot

example
    {kind : Assembly.HaltKind}
    {args : Locals.ExprSeq kind.argCount}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source sourceAfterArgs : Locals.Source.State}
    {target : Locals.EVMState}
    {values : List Locals.Word}
    {shared' : EvmYul.SharedState .EVM}
    {code : Structured.Code}
    (hNoMem :
      ¬ Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.HaltKindMemoryTouching
          kind)
    (hSafe :
      Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.ExprSeqSafe
        args)
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout source target)
    (hCompile :
      Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileSeqFullCode?
          range 0 layout args =
        some code)
    (hEvalArgs :
      Locals.Source.Expr.ExprSeq.eval
          Locals.Source.PrimitiveSemantics.structured args source =
        .ok (sourceAfterArgs, values))
    (hTerminal :
      Locals.Source.PrimitiveSemantics.structured.terminal kind
          sourceAfterArgs.shared values =
        .ok shared') :
    ∃ targetAfterArgs final,
      Structured.Code.run code target = .ok targetAfterArgs ∧
      Structured.Terminal.step kind targetAfterArgs = .ok final ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillHaltRel
        range (sourceAfterArgs.withShared shared') final :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.compileSeqFullCode_terminalArgs_spillHaltRel_structured
    hNoMem hSafe hRel hCompile hEvalArgs hTerminal

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source : Locals.Source.State}
    {target : Locals.EVMState}
    {kind : Assembly.HaltKind}
    {shared' : EvmYul.SharedState .EVM}
    (hNoMem :
      ¬ Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.HaltKindMemoryTouching
          kind)
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout source target)
    (hTerminal :
      Locals.Source.PrimitiveSemantics.structured.terminal kind
          source.shared [] =
        .ok shared') :
    ∃ result,
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
          (Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.Terminal
            [] kind) target =
        .ok result ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
        range sourceScope stackLayout layout
        (Locals.Source.Outcome.halt kind
          (source.withShared shared')) result :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.terminal_spillOutcomeRel_structured
    hNoMem hRel hTerminal

example
    {kind : Assembly.HaltKind}
    {args : Locals.ExprSeq kind.argCount}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {source sourceAfterArgs : Locals.Source.State}
    {target : Locals.EVMState}
    {values : List Locals.Word}
    {shared' : EvmYul.SharedState .EVM}
    {code : Structured.Code}
    (hNoMem :
      ¬ Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.HaltKindMemoryTouching
          kind)
    (hSafe :
      Locals.SourceLowering.StateRel.SpillScratch.SourceNoMemoryTouch.ExprSeqSafe
        args)
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout source target)
    (hCompile :
      Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileSeqFullCode?
          range 0 layout args =
        some code)
    (hEvalArgs :
      Locals.Source.Expr.ExprSeq.eval
          Locals.Source.PrimitiveSemantics.structured args source =
        .ok (sourceAfterArgs, values))
    (hTerminal :
      Locals.Source.PrimitiveSemantics.structured.terminal kind
          sourceAfterArgs.shared values =
        .ok shared') :
    ∃ result,
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
          (Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.Terminal
            code kind) target =
        .ok result ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
        range sourceScope stackLayout layout
        (Locals.Source.Outcome.halt kind
          (sourceAfterArgs.withShared shared')) result :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillStackPrefixRel.compileSeqFullCode_terminalArgs_spillOutcomeRel_structured
    hNoMem hSafe hRel hCompile hEvalArgs hTerminal

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {expr : Locals.Expr 0}
    {plan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan}
    {source source' : Locals.Source.State}
    {target : Locals.EVMState}
    {values : List Locals.Word}
    (hPlan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan.compileExpr0?
          range sourceScope stackLayout layout expr =
        some plan)
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout source target)
    (hEval :
      Locals.Source.Expr.eval Locals.Source.PrimitiveSemantics.structured
          expr source =
        .ok (source', values)) :
    ∃ result,
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
          plan.code target =
        .ok result ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
        range plan.sourceScope plan.stackLayout plan.layout
        (Locals.Source.Outcome.regular source') result :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan.compileExpr0?_sound
    hPlan hRel hEval

example
    (hSpec :
      Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {name : Locals.Name} {expr : Locals.Expr 1}
    {plan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan}
    {source sourceAfterValue : Locals.Source.State}
    {target : Locals.EVMState} {value : Locals.Word}
    (hPlan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan.compileLet?
          range sourceScope stackLayout layout name expr =
        some plan)
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout source target)
    (hFresh : name ∉ sourceScope)
    (hEval :
      Locals.Source.Expr.eval Locals.Source.PrimitiveSemantics.structured
          expr source =
        .ok (sourceAfterValue, [value])) :
    ∃ result,
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
          plan.code target =
        .ok result ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
        range plan.sourceScope plan.stackLayout plan.layout
        (Locals.Source.Outcome.regular
          (sourceAfterValue.insert name value)) result :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan.compileLet?_sound
    hSpec hWordBytes hPlan hRel hFresh hEval

example
    (hSpec :
      Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {name : Locals.Name} {expr : Locals.Expr 1}
    {plan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan}
    {source sourceAfterValue : Locals.Source.State}
    {target : Locals.EVMState} {value : Locals.Word}
    (hPlan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan.compileAssign?
          range sourceScope stackLayout layout name expr =
        some plan)
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout source target)
    (hContains : sourceAfterValue.vars.contains name = true)
    (hEval :
      Locals.Source.Expr.eval Locals.Source.PrimitiveSemantics.structured
          expr source =
        .ok (sourceAfterValue, [value])) :
    ∃ result,
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
          plan.code target =
        .ok result ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
        range plan.sourceScope plan.stackLayout plan.layout
        (Locals.Source.Outcome.regular
          (sourceAfterValue.withVars
            (Locals.Source.Store.insert sourceAfterValue.vars name value)))
        result :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan.compileAssign?_sound
    hSpec hWordBytes hPlan hRel hContains hEval

example
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {kind : Assembly.HaltKind}
    {plan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source : Locals.Source.State} {target : Locals.EVMState}
    {shared' : EvmYul.SharedState .EVM}
    (hPlan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan.compileTerminal?
          sourceScope stackLayout layout kind =
        some plan)
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout source target)
    (hTerminal :
      Locals.Source.PrimitiveSemantics.structured.terminal kind
          source.shared [] =
        .ok shared') :
    ∃ result,
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
          plan.code target =
        .ok result ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
        range plan.sourceScope plan.stackLayout plan.layout
        (Locals.Source.Outcome.halt kind
          (source.withShared shared')) result :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan.compileTerminal?_sound
    hPlan hRel hTerminal

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {kind : Assembly.HaltKind}
    {args : Locals.ExprSeq kind.argCount}
    {plan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan}
    {source sourceAfterArgs : Locals.Source.State}
    {target : Locals.EVMState}
    {values : List Locals.Word}
    {shared' : EvmYul.SharedState .EVM}
    (hPlan :
      Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan.compileTerminalArgs?
          range sourceScope stackLayout layout kind args =
        some plan)
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.SpillStateRel
        range sourceScope stackLayout layout source target)
    (hEvalArgs :
      Locals.Source.Expr.ExprSeq.eval
          Locals.Source.PrimitiveSemantics.structured args source =
        .ok (sourceAfterArgs, values))
    (hTerminal :
      Locals.Source.PrimitiveSemantics.structured.terminal kind
          sourceAfterArgs.shared values =
        .ok shared') :
    ∃ result,
      Locals.SourceLowering.StateRel.SpillScratch.SpillStmtCode.run
          plan.code target =
        .ok result ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillOutcomeRel
        range plan.sourceScope plan.stackLayout plan.layout
        (Locals.Source.Outcome.halt kind
          (sourceAfterArgs.withShared shared')) result :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan.compileTerminalArgs?_sound
    hPlan hRel hEvalArgs hTerminal

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan.compileExpr0?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan.compileExpr0?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan.compileLet?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan.compileLet?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan.compileAssign?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan.compileAssign?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan.compileTerminal?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan.compileTerminal?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan.compileTerminalArgs?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan.compileTerminalArgs?_wellFormed

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan.Fresh

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan.compile?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan.compile?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileCode?_noCallCreate

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillExpr.compileSeqFullCode?_noCallCreate

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillAtomPlan.compile?_noCallCreate

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtom?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtList?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpen?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.spillAllStack?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithSpill?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithAdaptiveSpill?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithConservativeSpill?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithSpill?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithSpill?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithConservativeSpill?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithConservativeSpill?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithAdaptiveSpill?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithAdaptiveSpill?

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtom?_atom

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtom?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithSpill?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithAdaptiveSpill?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithConservativeSpill?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithAdaptiveSpill?_of_compileFreshAtom?

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithConservativeSpill?_of_compileFreshAtom?

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithConservativeSpill?_fallback

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithConservativeSpill?_fallback_some

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithAdaptiveSpill?_isSome_of_compileFreshAtomWithSpill?

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithConservativeSpill?_isSome_of_compileFreshAtomWithSpill?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtom?_swap17Regression_rejects

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithConservativeSpill?_swap17Regression_accepts

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressions?_deepLocalsRegression_rejects

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithConservativeSpillExpressions?_deepLocalsRegression_accepts

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram_noCallCreate

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtom?_noCallCreate

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.spillAllStack?_noCallCreate

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithSpill?_noCallCreate

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithConservativeSpill?_noCallCreate

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithConservativeSpill?_noCallCreate

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithConservativeSpill?_noCallCreate

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithConservativeSpillExpressions?_noCallCreate

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithConservativeSpillChecked?_noCallCreate

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtom?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtom?_regular_storeDefined_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtom?_regular_storeDefined_of_source_run_emptyStack

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.run_spillStoreTopCode_evictTopStackLayout?_of_topValue

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.run_spillStoreTopCode_evictTopStackLayout?_of_storeDefined

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.spillAllStack?_sound

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.spillAllStack?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithSpill?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithConservativeSpill?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithAdaptiveSpill?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithSpill?_regular_storeDefined_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithConservativeSpill?_regular_storeDefined_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileFreshAtomWithAdaptiveSpill?_regular_storeDefined_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtList?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpen?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithSpill?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithSpill?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithConservativeSpill?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithConservativeSpill?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithAdaptiveSpill?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithAdaptiveSpill?_wellFormed

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithAdaptiveSpill?_of_compileStmtList?

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithConservativeSpill?_of_compileStmtList?

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithAdaptiveSpill?_of_compileBlockOpen?

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithConservativeSpill?_of_compileBlockOpen?

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithConservativeSpillExpressions?_of_compileBlockOpen?

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.toExpressionsProgram

example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithConservativeSpillExpressions?

noncomputable example :=
  Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithConservativeSpillChecked?

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithConservativeSpillChecked?_eq_some

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtList?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpen?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithSpill?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithSpill?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithConservativeSpill?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithConservativeSpill?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithConservativeSpill?_expressionsBlock_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithConservativeSpill?_expressionsBlock_sound_of_privateScratchBoundary

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithConservativeSpill?_expressionsBlock_sound_of_initialState_privateScratchBoundary

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithConservativeSpill?_expressionsProgram_run_of_initialState_privateScratchBoundary

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithConservativeSpillChecked?_assembly_sound_of_initialState_privateScratchBoundary

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileProgramBodyWithConservativeSpillChecked?_assembly_sound_of_initialState_privateScratchBoundary_endPc

noncomputable example :=
  Locals.Source.Program.compileCheckedWithConservativeSpill?

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_eq_some

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_components

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_of_checked

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_noCallCreate

example :=
  Locals.Source.Program.ConservativeSpillOpenOutcomeRel

example :=
  @Locals.Source.Program.ConservativeSpillOpenOutcomeRel.regular_inv

example :=
  @Locals.Source.Program.ConservativeSpillOpenOutcomeRel.halt_inv

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_openBlock_preserves

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_openBlock_preserves_endPc

example :=
  Locals.Source.Program.scopedProgramOutcome

example :=
  Locals.Source.Program.ConservativeSpillProgramOutcomeRel

example :=
  Locals.Source.Program.ConservativeSpillObservableOutcomeRel

example :=
  @Locals.Source.Program.ConservativeSpillProgramOutcomeRel.regular_inv

example :=
  @Locals.Source.Program.ConservativeSpillProgramOutcomeRel.halt_inv

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_preserves

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_preserves_endPc

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_regular_result

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_halt_result

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_regular_sharedState

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_regular_observations

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_halt_sharedState

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_halt_observations

example :=
  @Locals.Source.Program.compileCheckedWithConservativeSpill?_observations

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileStmtListWithAdaptiveSpill?_sound_of_source_run

example :=
  @Locals.SourceLowering.StateRel.SpillScratch.SpillPlan.compileBlockOpenWithAdaptiveSpill?_sound_of_source_run

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source : EvmYul.MachineState} {target : Locals.EVMState}
    {slot : Nat}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target.toMachineState)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.ready?
        target.toMachineState range = true)
    (hSlot : slot < range.words) :
    ∃ final,
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillLoadCode
            (range.word slot)) target =
        .ok final ∧
      final.stack =
        (target.toMachineState.mload (range.word slot)).1 ::
          target.stack ∧
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source final.toMachineState :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.run_spillLoadCode_target_scratch_slot_of_ready?
    hRel hReady hSlot

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source : EvmYul.MachineState} {target : Locals.EVMState}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {store : Locals.Source.Store}
    {name : Locals.Name} {slot : Nat}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target.toMachineState)
    (hLayout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed
        range sourceScope stackLayout layout)
    (hValues :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
        range store target.toMachineState target.stack layout)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        target.toMachineState range.base range.words)
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
          slot) ∈ layout) :
    ∃ value final,
      store name = some value ∧
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillLoadCode
            (range.word slot)) target =
        .ok final ∧
      final.stack = value :: target.stack ∧
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source final.toMachineState ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
        range store final.toMachineState target.stack layout :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.run_spillLoadCode_target_scratch_binding_valueRel
    hRel hLayout hValues hReady hBinding

example
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {source : EvmYul.MachineState} {target : Locals.EVMState}
    {sourceScope stackLayout : List Locals.Name}
    {layout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.Layout}
    {store : Locals.Source.Store}
    {name : Locals.Name} {slot : Nat}
    (hRel :
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source target.toMachineState)
    (hLayout :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.WellFormed
        range sourceScope stackLayout layout)
    (hValues :
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
        range store target.toMachineState target.stack layout)
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRange.ready?
        target.toMachineState range = true)
    (hBinding :
      (name,
        Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.LocalLocation.scratch
          slot) ∈ layout) :
    ∃ value final,
      store name = some value ∧
      Structured.Code.run
          (Locals.SourceLowering.StateRel.SpillScratch.spillLoadCode
            (range.word slot)) target =
        .ok final ∧
      final.stack = value :: target.stack ∧
      Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch
        range source final.toMachineState ∧
      Locals.SourceLowering.StateRel.SpillScratch.SpillLayout.ValueRel
        range store final.toMachineState target.stack layout :=
  Locals.SourceLowering.StateRel.SpillScratch.MemoryByteEqOutsideScratch.run_spillLoadCode_target_scratch_binding_valueRel_of_ready?
    hRel hLayout hValues hReady hBinding

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {machine : EvmYul.MachineState} {offset value : Locals.Word}
    (hAllocated :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordAllocated
        machine offset)
    (hReadableAfter :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReadable
        (machine.mstore offset value) offset) :
    (machine.mstore offset value).lookupMemory offset = value :=
  Locals.SourceLowering.StateRel.SpillScratch.lookupMemory_mstore_same_of_allocated_readable
    hSpec hWordBytes hAllocated hReadableAfter

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {machine : EvmYul.MachineState}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {slot : Nat} {value : Locals.Word}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        machine range.base range.words)
    (hSlot : slot < range.words) :
    (machine.mstore (range.word slot) value).lookupMemory
        (range.word slot) =
      value :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady.lookupMemory_mstore_range_slot_same
    hSpec hWordBytes hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {machine : EvmYul.MachineState}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {slot : Nat} {value : Locals.Word}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        machine range.base range.words)
    (hSlot : slot < range.words) :
    ((machine.mstore (range.word slot) value).mload
        (range.word slot)).1 =
      value :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady.mload_mstore_range_slot_value
    hSpec hWordBytes hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hWordBytes :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingSpec)
    {machine : EvmYul.MachineState}
    {range : Locals.SourceLowering.StateRel.SpillScratch.ScratchRange}
    {writeSlot readSlot : Nat} {value : Locals.Word}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        machine range.base range.words)
    (hWriteSlot : writeSlot < range.words)
    (hReadSlot : readSlot < range.words)
    (hNe : readSlot ≠ writeSlot) :
    ((machine.mstore (range.word writeSlot) value).mload
        (range.word readSlot)).1 =
      (machine.mload (range.word readSlot)).1 :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady.mload_mstore_range_other_slot_value
    hSpec hWordBytes hReady hWriteSlot hReadSlot hNe

example {machine : EvmYul.MachineState} {base count left right : Nat}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        machine base count)
    (hLeft : left < count)
    (hRight : right < count)
    (hLt : left < right) :
    (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionWord
        base left).toNat + 32 ≤
      (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionWord
        base right).toNat :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady.scratchWordSlotEndLeSlotStart
    hReady hLeft hRight hLt

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hEncoding :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingModelSpec)
    {state : Locals.EVMState} {base count slot : Nat}
    {value : Locals.Word}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        state.toMachineState base count)
    (hSlot : slot < count) :
    ({ state with
        toMachineState :=
          (state.toMachineState.mstore
              (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionWord
                base slot) value).mstore
            (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionWord
              base slot)
            (state.toMachineState.mload
              (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionWord
                base slot)).1 } :
      Locals.EVMState).toSharedState = state.toSharedState :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady.slot_mstore_restore_loaded_evm_shared_eq
    hSpec hEncoding hReady hSlot

example
    {machine : EvmYul.MachineState} {base count slot : Nat}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        machine base count)
    (hSlot : slot < count) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
      (machine.mload
        (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionWord
          base slot)).2
      base count :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady.mload_slot
    hReady hSlot

example
    {machine : EvmYul.MachineState} {base count slot : Nat}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?
        machine base count = true)
    (hSlot : slot < count) :
    Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?
      (machine.mload
        (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionWord
          base slot)).2
      base count = true :=
  Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?_mload_slot
    hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hEncoding :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingModelSpec)
    {machine : EvmYul.MachineState} {base count slot : Nat}
    {value : Locals.Word}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
        machine base count)
    (hSlot : slot < count) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady
      (machine.mstore
        (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionWord
          base slot) value)
      base count :=
  Locals.SourceLowering.StateRel.SpillScratch.ScratchRegionReady.mstore_slot
    hSpec hEncoding.size hReady hSlot

example
    (hSpec : Locals.SourceLowering.StateRel.SpillScratch.ZeroPaddingSpec)
    (hEncoding :
      Locals.SourceLowering.StateRel.SpillScratch.WordByteEncodingModelSpec)
    {machine : EvmYul.MachineState} {base count slot : Nat}
    {value : Locals.Word}
    (hReady :
      Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?
        machine base count = true)
    (hSlot : slot < count) :
    Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?
      (machine.mstore
        (Locals.SourceLowering.StateRel.SpillScratch.scratchRegionWord
          base slot) value)
      base count = true :=
  Locals.SourceLowering.StateRel.SpillScratch.scratchRegionReady?_mstore_slot
    hSpec hEncoding.size hReady hSlot

example {machine : EvmYul.MachineState} {offset value : Locals.Word}
    (hScratch :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved machine
        offset) :
    (machine.mstore offset value).activeWords = machine.activeWords :=
  Locals.SourceLowering.StateRel.SpillScratch.mstore_activeWords hScratch

example {machine : EvmYul.MachineState} {offset : Locals.Word} :
    (machine.mload offset).2.activeWords = machine.activeWords ↔
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved machine
        offset :=
  Locals.SourceLowering.StateRel.SpillScratch.mload_activeWords_eq_iff_reserved

example {machine : EvmYul.MachineState} {offset value : Locals.Word} :
    (machine.mstore offset value).activeWords = machine.activeWords ↔
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved machine
        offset :=
  Locals.SourceLowering.StateRel.SpillScratch.mstore_activeWords_eq_iff_reserved

example {machine : EvmYul.MachineState} {offset value : Locals.Word}
    (hScratch :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved machine
        offset) :
    Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved
      (machine.mstore offset value) offset :=
  Locals.SourceLowering.StateRel.SpillScratch.mstore_scratch_reserved hScratch

example {machine : EvmYul.MachineState} {offset : Locals.Word}
    (hScratch :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved machine
        offset) :
    (machine.mload offset).2 = machine :=
  Locals.SourceLowering.StateRel.SpillScratch.mload_machine_eq hScratch

example {state : Locals.EVMState} {offset : Locals.Word}
    (hScratch :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved
        state.toMachineState offset) :
    ({ state with
        toMachineState := (state.toMachineState.mload offset).2 } :
      Locals.EVMState).toSharedState = state.toSharedState :=
  Locals.SourceLowering.StateRel.SpillScratch.mload_evm_shared_eq hScratch

example {state : Locals.EVMState} {offset : Locals.Word}
    {stack : EvmYul.Stack Locals.Word}
    (hScratch :
      Locals.SourceLowering.StateRel.SpillScratch.ScratchWordReserved
        state.toMachineState offset) :
    (({ state with
        toMachineState := (state.toMachineState.mload offset).2 } :
      Locals.EVMState).replaceStackAndIncrPC stack).toSharedState =
      state.toSharedState :=
  Locals.SourceLowering.StateRel.SpillScratch.mload_replaceStackAndIncrPC_shared_eq
    hScratch

example :
    Functions.LiveLayout.Layout.allAccessible? 0
      (List.replicate 17 "dead" ++ ["x"]) ["x"] = false := by
  native_decide

example :
    Functions.LiveLayout.Layout.entryWindowOk?
      (List.replicate 17 "dead" ++ ["x"]) ["x"] = true := by
  native_decide

example {layout live : List Functions.Name}
    (hCheck : Functions.LiveLayout.Layout.entryWindowOk? layout live = true) :
    Functions.LiveLayout.NameSet.allIn?
      (Functions.LiveLayout.Layout.trimDeadPrefix layout live) live = true :=
  Functions.LiveLayout.Layout.entryWindowOk?_allIn_trimDeadPrefix hCheck

example {ctx : Functions.LiveLayout.Ctx} {after : List Functions.Name}
    {body : Functions.Block} {name : Functions.Name}
    (hMem :
      name ∈ Functions.LiveLayout.Block.liveBefore ctx after body) :
    name ∈
      Functions.LiveLayout.Stmt.liveBefore ctx after
        (Functions.Stmt.block body) :=
  Functions.LiveLayout.LiveBefore.block_body_subset_stmt hMem

example {ctx : Functions.LiveLayout.Ctx} {after : List Functions.Name}
    {cond : Functions.Expr 1} {body : Functions.Block}
    {name : Functions.Name}
    (hMem :
      name ∈ Functions.LiveLayout.Block.liveBefore ctx after body) :
    name ∈
      Functions.LiveLayout.Stmt.liveBefore ctx after
        (Functions.Stmt.if_ cond body) :=
  Functions.LiveLayout.LiveBefore.if_body_subset_stmt hMem

example {ctx : Functions.LiveLayout.Ctx} {after : List Functions.Name}
    {switchExpr : Functions.Expr 1} {scrutinee : EvmYul.UInt256}
    {cases : List (EvmYul.UInt256 × Functions.Block)}
    {defaultBody : Option Functions.Block} {body : Functions.Block}
    {name : Functions.Name}
    (hSelect :
      Functions.Switch.select scrutinee cases defaultBody = some body)
    (hMem :
      name ∈ Functions.LiveLayout.Block.liveBefore ctx after body) :
    name ∈
      Functions.LiveLayout.Stmt.liveBefore ctx after
        (Functions.Stmt.switch switchExpr cases defaultBody) :=
  Functions.LiveLayout.LiveBefore.switch_selected_body_subset_stmt
    hSelect hMem

example {ctx : Functions.LiveLayout.Ctx} {after : List Functions.Name}
    {declared name : Functions.Name} {value : Functions.Expr 1}
    (hAfter : name ∈ after)
    (hNe : name ≠ declared) :
    name ∈
      Functions.LiveLayout.Stmt.liveBefore ctx after
        (Functions.Stmt.let_ declared value) :=
  Functions.LiveLayout.LiveBefore.let_after_of_ne hAfter hNe

example {ctx : Functions.LiveLayout.Ctx} {after env : List Functions.Name}
    {declared name : Functions.Name} {value : Functions.Expr 1}
    (hScoped :
      Functions.Scope.Stmt.Scoped env (Functions.Stmt.let_ declared value))
    (hScope : name ∈ env)
    (hAfter : name ∈ after) :
    name ∈
      Functions.LiveLayout.Stmt.liveBefore ctx after
        (Functions.Stmt.let_ declared value) :=
  Functions.LiveLayout.LiveBefore.let_after_of_scoped_scope hScoped hScope
    hAfter

example {results : Nat} {layout : List Functions.Name}
    {expr : Functions.Expr results}
    (hCheck : Functions.LiveLayout.ExprAccess.expr? 0 layout expr = true) :
    Locals.SourceLowering.Expr.Accessible layout 0 expr :=
  Functions.LiveLayout.ExprAccess.expr?_sound hCheck

example {layout names : List Functions.Name}
    (hCheck : Functions.LiveLayout.NamesAccess.names? 0 layout names = true)
    {idx : Nat} {name : Functions.Name}
    (hGet : names[idx]? = some name) :
    ∃ layoutIdx,
      layout[layoutIdx]? = some name ∧ idx + layoutIdx + 1 ≤ 16 :=
  by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Functions.LiveLayout.NamesAccess.names?_get?_sound hCheck hGet

example {layout names : List Functions.Name}
    (hAccess :
      Functions.LiveLayout.NamesAccess.Accessible layout 0 names) :
    Functions.SourceDirect.ReturnValuesRel.Accessible layout 0 names :=
  Functions.LiveLayout.NamesAccess.to_returnValuesAccessible hAccess

example {layout names : List Functions.Name}
    (hAccess :
      Functions.LiveLayout.NamesAccess.Accessible layout 0 names) :
    names.length ≤ 16 :=
  Functions.LiveLayout.NamesAccess.length_le_16_of_accessible_zero hAccess

example {returns layout : List Functions.Name} {stmt : Functions.Stmt}
    (hCheck :
      Functions.LiveLayout.StmtAccess.accessible? returns layout stmt =
        true) :
    Functions.LiveLayout.StmtAccess.Accessible returns layout stmt :=
  Functions.LiveLayout.StmtAccess.accessible?_sound hCheck

example {returns : List Functions.Name} {ctx : Functions.LiveLayout.Ctx}
    {layout after : List Functions.Name} {block : Functions.Block}
    {outLayout : List Functions.Name}
    (hCheck :
      Functions.LiveLayout.Checked.Block.check? returns ctx layout after block =
        some outLayout) :
    Functions.LiveLayout.Checked.Block.Sound returns ctx layout after block
      outLayout :=
  Functions.LiveLayout.Checked.Block.check?_sound hCheck

example {fn : Functions.FunDef}
    (hCheck : Functions.LiveLayout.Checked.FunDef.check? fn = true) :
    ∃ layout,
      Functions.LiveLayout.Checked.Block.Sound fn.returns
        { returns := fn.returns }
        (fn.returns.reverse ++ fn.params.reverse) fn.returns fn.body layout ∧
        Functions.LiveLayout.NamesAccess.Accessible layout 0 fn.returns :=
  Functions.LiveLayout.Checked.FunDef.check?_sound hCheck

example {fn : Functions.FunDef} {proc : Locals.Proc}
    (hLower :
      Functions.LiveLayout.Lower.FunDef.toLocalsProc? fn = some proc) :
    ∃ lowerBody layout,
      Functions.LiveLayout.Lower.Block.toLocals? fn.returns
          { returns := fn.returns }
          (fn.returns.reverse ++ fn.params.reverse) fn.returns fn.body =
        some (lowerBody, layout) ∧
      Functions.LiveLayout.NamesAccess.Accessible layout 0 fn.returns ∧
      proc =
        { name := fn.name
          argc := fn.params.length
          retc := fn.returns.length
          entryLayout := fn.params.reverse
          body :=
            { stmts :=
                Functions.Lower.initReturns fn.returns ++
                  (lowerBody.stmts ++
                    Functions.Lower.pushReturns fn.returns) } } :=
  Functions.LiveLayout.Lower.FunDef.toLocalsProc?_components hLower

example {returns : List Functions.Name} {ctx : Functions.LiveLayout.Ctx}
    {layout after : List Functions.Name} {block : Functions.Block}
    {lowerBlock : Locals.Block} {outLayout : List Functions.Name}
    (hLower :
      Functions.LiveLayout.Lower.Block.toLocals? returns ctx layout after
        block =
        some (lowerBlock, outLayout)) :
    Functions.LiveLayout.TargetLayout.StmtList.regularOutLayout layout
        lowerBlock.stmts =
      outLayout :=
  Functions.LiveLayout.TargetLayout.Lower.block_toLocals?_layout hLower

example {program : Locals.Program}
    {ctx runCtx : Locals.Ctx} {fuel : Nat} {stmt : Locals.Stmt}
    {state final : Locals.RunState}
    (hRun :
      Locals.Direct.Stmt.run program ctx fuel stmt state =
        .ok (Structured.Outcome.regular final, runCtx)) :
    runCtx.layout =
      Functions.LiveLayout.TargetLayout.Stmt.regularOutLayout ctx.layout
        stmt :=
  Functions.LiveLayout.TargetLayout.Stmt.run_regular_layout hRun

example {program : Locals.Program}
    {ctx runCtx : Locals.Ctx} {fuel : Nat} {stmt : Locals.Stmt}
    {state final : Locals.RunState}
    (hRun :
      Locals.Direct.Stmt.run program ctx fuel stmt state =
        .ok (Structured.Outcome.regular final, runCtx)) :
    runCtx =
      ctx.withLayout
        (Functions.LiveLayout.TargetLayout.Stmt.regularOutLayout ctx.layout
          stmt) :=
  Functions.LiveLayout.TargetLayout.Stmt.run_regular_ctx hRun

example {program : Locals.Program}
    {ctx runCtx : Locals.Ctx} {fuel : Nat} {block : Locals.Block}
    {state final : Locals.RunState}
    (hRun :
      Locals.Direct.Block.runOpen program ctx fuel block state =
        .ok (Structured.Outcome.regular final, runCtx)) :
    runCtx.layout =
      Functions.LiveLayout.TargetLayout.StmtList.regularOutLayout
        ctx.layout block.stmts :=
  Functions.LiveLayout.TargetLayout.StmtList.block_runOpen_regular_layout
    hRun

example {program : Locals.Program}
    {ctx runCtx : Locals.Ctx} {fuel : Nat} {block : Locals.Block}
    {state final : Locals.RunState}
    (hRun :
      Locals.Direct.Block.runOpen program ctx fuel block state =
        .ok (Structured.Outcome.regular final, runCtx)) :
    runCtx =
      ctx.withLayout
        (Functions.LiveLayout.TargetLayout.StmtList.regularOutLayout
          ctx.layout block.stmts) :=
  Functions.LiveLayout.TargetLayout.StmtList.block_runOpen_regular_ctx
    hRun

example {returns : List Functions.Name} {ctx : Functions.LiveLayout.Ctx}
    {layout after : List Functions.Name} {block : Functions.Block}
    {lowerBlock : Locals.Block} {outLayout : List Functions.Name}
    {program : Locals.Program} {targetCtx runCtx : Locals.Ctx}
    {fuel : Nat} {state final : Locals.RunState}
    (hLower :
      Functions.LiveLayout.Lower.Block.toLocals? returns ctx layout after
        block =
        some (lowerBlock, outLayout))
    (hCtxLayout : targetCtx.layout = layout)
    (hRun :
      Locals.Direct.Block.runOpen program targetCtx fuel lowerBlock state =
        .ok (Structured.Outcome.regular final, runCtx)) :
    runCtx.layout = outLayout :=
  Functions.LiveLayout.TargetLayout.Lower.block_runOpen_regular_layout_of_lower
    hLower hCtxLayout hRun

example {returns : List Functions.Name} {ctx : Functions.LiveLayout.Ctx}
    {layout after : List Functions.Name} {block : Functions.Block}
    {lowerBlock : Locals.Block} {outLayout : List Functions.Name}
    {program : Locals.Program} {targetCtx runCtx : Locals.Ctx}
    {fuel : Nat} {state final : Locals.RunState}
    (hLower :
      Functions.LiveLayout.Lower.Block.toLocals? returns ctx layout after
        block =
        some (lowerBlock, outLayout))
    (hCtxLayout : targetCtx.layout = layout)
    (hRun :
      Locals.Direct.Block.runOpen program targetCtx fuel lowerBlock state =
        .ok (Structured.Outcome.regular final, runCtx)) :
    runCtx = targetCtx.withLayout outLayout :=
  Functions.LiveLayout.TargetLayout.Lower.block_runOpen_regular_ctx_of_lower
    hLower hCtxLayout hRun

example {returns : List Functions.Name} {ctx : Functions.LiveLayout.Ctx}
    {layout after outLayout : List Functions.Name} {block : Functions.Block}
    {lowerBlock : Locals.Block}
    {sourceResult : Functions.Source.Outcome × Functions.Source.Ctx}
    {program : Locals.Program} {targetCtx : Locals.Ctx}
    {fuel : Nat} {state : Locals.RunState}
    {targetResult : Locals.Outcome × Locals.Ctx}
    (hLower :
      Functions.LiveLayout.Lower.Block.toLocals? returns ctx layout after
        block =
        some (lowerBlock, outLayout))
    (hCtxLayout : targetCtx.layout = layout)
    (hRun :
      Locals.Direct.Block.runOpen program targetCtx fuel lowerBlock state =
        .ok targetResult) :
    Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenTargetRegularOutputLayoutRel
      outLayout sourceResult targetResult :=
  Functions.LiveLayout.SourceTarget.block_target_regular_output_layout_of_lower_run
    hLower hCtxLayout hRun

example {outLayout returns : List Functions.Name}
    {sourceResult : Functions.Source.Outcome × Functions.Source.Ctx}
    {targetState : Locals.RunState} {targetCtx : Locals.Ctx}
    (hLayout :
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenTargetRegularOutputLayoutRel
        outLayout sourceResult
        (Structured.Outcome.regular targetState, targetCtx))
    (hAccess :
      Functions.LiveLayout.NamesAccess.Accessible outLayout 0 returns) :
    Functions.LiveLayout.NamesAccess.Accessible targetCtx.layout 0 returns :=
  Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenTargetRegularOutputLayoutRel.namesAccessible_of_regular
    hLayout hAccess

example {outLayout returns : List Functions.Name}
    {sourceResult : Functions.Source.Outcome × Functions.Source.Ctx}
    {targetState : Locals.RunState} {targetCtx : Locals.Ctx}
    (hLayout :
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenTargetRegularOutputLayoutRel
        outLayout sourceResult
        (Structured.Outcome.regular targetState, targetCtx))
    (hAccess :
      Functions.LiveLayout.NamesAccess.Accessible outLayout 0 returns) :
    Functions.SourceDirect.ReturnValuesRel.Accessible targetCtx.layout 0
      returns :=
  Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenTargetRegularOutputLayoutRel.returnValuesAccessible_of_regular
    hLayout hAccess

example {returns : List Functions.Name} {ctx : Functions.LiveLayout.Ctx}
    {layout after outLayout baseLayout : List Functions.Name}
    {block : Functions.Block} {lowerBlock : Locals.Block}
    {retc : Nat} {hiddenReturns : List Structured.ReturnDest}
    {sourceResult : Functions.Source.Outcome × Functions.Source.Ctx}
    {program : Locals.Program} {targetCtx : Locals.Ctx}
    {target : Locals.RunState}
    (hLower :
      Functions.LiveLayout.Lower.Block.toLocals? returns ctx layout after
        block =
        some (lowerBlock, outLayout))
    (hCtxLayout : targetCtx.layout = layout)
    (hResult :
      ∃ targetFuel targetResult,
        Locals.Direct.Block.runOpen program targetCtx targetFuel lowerBlock
            target =
          .ok targetResult ∧
        Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenResultRel retc
          returns hiddenReturns sourceResult targetResult ∧
        Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRegularLayoutRelTo
          baseLayout sourceResult targetResult) :
    ∃ targetFuel targetResult,
      Locals.Direct.Block.runOpen program targetCtx targetFuel lowerBlock
          target =
        .ok targetResult ∧
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenResultRel retc
        returns hiddenReturns sourceResult targetResult ∧
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRegularLayoutRelTo
        baseLayout sourceResult targetResult ∧
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenTargetRegularOutputLayoutRel
        outLayout sourceResult targetResult :=
  Functions.LiveLayout.SourceTarget.block_target_result_with_output_layout_of_lower
    hLower hCtxLayout hResult

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {ctx : Functions.LiveLayout.Ctx}
    {after outLayout baseLayout : List Functions.Name}
    {retc fuel : Nat} {sourceCtx : Functions.Source.Ctx}
    {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {block : Functions.Block} {lowerBlock : Locals.Block}
    {source : Functions.Source.State} {target : Locals.RunState}
    {sourceResult : Functions.Source.Outcome × Functions.Source.Ctx}
    (hLower :
      Functions.LiveLayout.Lower.Block.toLocals? returns ctx targetCtx.layout
        after block =
        some (lowerBlock, outLayout))
    (hSourceRun :
      Functions.Source.Block.runOpen prim sourceProgram sourceCtx (fuel + 1)
          block source =
        .ok sourceResult)
    (hNilLayout :
      block.stmts = [] →
        Functions.SourceDirect.CleanupLayoutRel
          (Functions.LiveLayout.Layout.trimDeadPrefix targetCtx.layout after)
          baseLayout)
    (hStateRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hCtxRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hHead :
      ∀ {stmt rest restLive stmtLive liveLayout prep preparedLayout lowerStmt
          nextLayout lowerRest},
        restLive = Functions.LiveLayout.StmtList.liveBefore ctx after rest →
        stmtLive = Functions.LiveLayout.Stmt.liveBefore ctx restLive stmt →
        liveLayout =
          Functions.LiveLayout.Layout.trimDeadPrefix targetCtx.layout
            stmtLive →
        Functions.LiveLayout.Prepare.forStmtAboveSuffix? ctx.protectedDepth
          returns liveLayout stmtLive stmt =
          some (prep, preparedLayout) →
        Functions.LiveLayout.Layout.entryWindowOk? preparedLayout stmtLive =
          true →
        Functions.LiveLayout.StmtAccess.accessible? returns preparedLayout
          stmt = true →
        Functions.LiveLayout.Lower.Stmt.toLocals? returns ctx preparedLayout
          restLive stmt =
          some (lowerStmt, nextLayout) →
        Functions.LiveLayout.Lower.StmtList.toLocals? returns ctx nextLayout
          after rest =
          some (lowerRest, outLayout) →
        ∀ {cleaned},
          Functions.SourceDirect.StateRel preparedLayout hiddenReturns source
            cleaned →
          Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
            sourceProgram targetProgram returns retc fuel sourceCtx
            (targetCtx.withLayout preparedLayout)
            hiddenReturns stmt { stmts := lowerStmt } source cleaned)
    (hTail :
      ∀ {stmt rest restLive stmtLive liveLayout prep preparedLayout lowerStmt
          nextLayout lowerRest},
        restLive = Functions.LiveLayout.StmtList.liveBefore ctx after rest →
        stmtLive = Functions.LiveLayout.Stmt.liveBefore ctx restLive stmt →
        liveLayout =
          Functions.LiveLayout.Layout.trimDeadPrefix targetCtx.layout
            stmtLive →
        Functions.LiveLayout.Prepare.forStmtAboveSuffix? ctx.protectedDepth
          returns liveLayout stmtLive stmt =
          some (prep, preparedLayout) →
        Functions.LiveLayout.Layout.entryWindowOk? preparedLayout stmtLive =
          true →
        Functions.LiveLayout.StmtAccess.accessible? returns preparedLayout
          stmt = true →
        Functions.LiveLayout.Lower.Stmt.toLocals? returns ctx preparedLayout
          restLive stmt =
          some (lowerStmt, nextLayout) →
        Functions.LiveLayout.Lower.StmtList.toLocals? returns ctx nextLayout
          after rest =
          some (lowerRest, outLayout) →
        ∀ {sourceAfter : Functions.Source.State}
          {targetAfter : Locals.RunState}
          {sourceCtxAfter : Functions.Source.Ctx}
          {targetCtxAfter : Locals.Ctx},
          Functions.SourceDirect.StateRel targetCtxAfter.layout hiddenReturns
            sourceAfter targetAfter →
          Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc
            sourceCtxAfter targetCtxAfter →
          Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayoutTo
            prim sourceProgram targetProgram returns retc fuel sourceCtxAfter
            targetCtxAfter baseLayout hiddenReturns { stmts := rest }
            { stmts := lowerRest } sourceAfter targetAfter) :
    ∃ targetFuel targetResult,
      Locals.Direct.Block.runOpen targetProgram targetCtx targetFuel lowerBlock
          target =
        .ok targetResult ∧
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenResultRel retc
        returns hiddenReturns sourceResult targetResult ∧
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRegularLayoutRelTo
        baseLayout sourceResult targetResult ∧
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenTargetRegularOutputLayoutRel
        outLayout sourceResult targetResult :=
  Functions.LiveLayout.SourceTarget.block_target_result_of_source_run_lower_with_layout_to_output_layout
    hLower hSourceRun hNilLayout hStateRel hCtxRel hHead hTail

example {ctx : Locals.Ctx} {targetDepth : Nat}
    {source : Locals.Source.State} {target cleaned : Locals.RunState}
    (hRun :
      Locals.Direct.Ctx.runCleanupTo ctx targetDepth target = .ok cleaned)
    (hRel : Locals.SourceLowering.StateRel ctx.layout source target) :
    Locals.SourceLowering.StateRel
        (ctx.layout.drop (ctx.layout.length - targetDepth)) source cleaned ∧
      cleaned.returns = target.returns :=
  Functions.LiveLayout.Drop.cleanupTo_stateRel_drop hRun hRel

example {ctx : Locals.Ctx} {live : List Functions.Name}
    {source : Locals.Source.State} {target cleaned : Locals.RunState}
    (hRun :
      Locals.Direct.Ctx.runCleanupTo ctx
          (Functions.LiveLayout.Layout.trimDeadPrefix ctx.layout live).length
          target =
        .ok cleaned)
    (hRel : Locals.SourceLowering.StateRel ctx.layout source target) :
    Locals.SourceLowering.StateRel
        (Functions.LiveLayout.Layout.trimDeadPrefix ctx.layout live) source
        cleaned ∧
      cleaned.returns = target.returns :=
  Functions.LiveLayout.Drop.cleanupTo_trimDeadPrefix_stateRel hRun hRel

example :
    let deadNames : List Functions.Name :=
      ["d0", "d1", "d2", "d3", "d4", "d5", "d6", "d7", "d8",
        "d9", "d10", "d11", "d12", "d13", "d14", "d15", "d16"]
    Functions.LiveLayout.Checked.Program.check?
      { functions := []
        body :=
          { stmts :=
              [.let_ "x" Functions.LiveLayout.Examples.lit0] ++
                (deadNames.map fun name =>
                  Functions.Stmt.let_ name
                    Functions.LiveLayout.Examples.lit0) ++
                [Functions.LiveLayout.Examples.popVar "x"] } } = true := by
  native_decide

example :
    (Functions.LiveLayout.Lower.Program.toExpressions?
      Functions.LiveLayout.Examples.manyDeadProgram).isSome = true := by
  native_decide

example :
    (Functions.LiveLayout.Lower.Program.toExpressionsNoInternalCall?
      Functions.LiveLayout.Examples.manyDeadProgram).isSome = true := by
  native_decide

example {program : Functions.Program} {lower : Locals.Program}
    (hLower :
      Functions.LiveLayout.Lower.Program.toLocals? program = some lower) :
    Functions.LiveLayout.Checked.Program.check? program = true :=
  Functions.LiveLayout.Lower.Program.toLocals?_checked hLower

example {program : Functions.Program} {lower : Locals.Program}
    (hLower :
      Functions.LiveLayout.Lower.Program.toLocals? program = some lower) :
    ∃ lowerProcs lowerBody bodyLayout,
      Functions.LiveLayout.Lower.FunList.toLocalsProcs? program.functions =
          some lowerProcs ∧
        Functions.LiveLayout.Lower.Block.toLocals? [] {} [] [] program.body =
          some (lowerBody, bodyLayout) ∧
        lower = { procs := lowerProcs, body := lowerBody } :=
  Functions.LiveLayout.Lower.Program.toLocals?_components hLower

example {program : Functions.Program} {lower : Locals.Program}
    (hLower :
      Functions.LiveLayout.Lower.Program.toLocalsNoInternalCall? program =
        some lower) :
    Functions.LiveLayout.NoInternalCall.Program.Holds program ∧
      Functions.LiveLayout.Checked.Program.check? program = true :=
  Functions.LiveLayout.Lower.Program.toLocalsNoInternalCall?_checked hLower

example {program : Functions.Program} {lower : Locals.Program}
    (hLower :
      Functions.LiveLayout.Lower.Program.toLocalsNoInternalCall? program =
        some lower) :
    Functions.LiveLayout.NoInternalCall.Program.Holds program ∧
      ∃ lowerProcs lowerBody bodyLayout,
        Functions.LiveLayout.Lower.FunList.toLocalsProcs?
            program.functions =
          some lowerProcs ∧
          Functions.LiveLayout.Lower.Block.toLocals? [] {} [] []
              program.body =
            some (lowerBody, bodyLayout) ∧
          lower = { procs := lowerProcs, body := lowerBody } :=
  Functions.LiveLayout.Lower.Program.toLocalsNoInternalCall?_components hLower

example {program : Functions.Program} {asm : Assembly.TargetProgram}
    (hCompile :
      Functions.LiveLayout.Lower.Program.compile? program = some asm) :
    Functions.LiveLayout.Checked.Program.check? program = true :=
  Functions.LiveLayout.Lower.Program.compile?_checked hCompile

example {program : Functions.Program} {asm : Assembly.TargetProgram}
    (hCompile :
      Functions.LiveLayout.Lower.Program.compileNoInternalCall? program =
        some asm) :
    Functions.LiveLayout.NoInternalCall.Program.Holds program ∧
      Functions.LiveLayout.Checked.Program.check? program = true :=
  Functions.LiveLayout.Lower.Program.compileNoInternalCall?_checked hCompile

example {program : Functions.Program} {asm : Assembly.Program}
    (hCompile :
      Functions.Source.Program.compileLiveNoInternalCallChecked? program =
        some asm) :
    ∃ lower : Expressions.Program,
      Functions.LiveLayout.Lower.Program.toExpressionsNoInternalCall?
          program =
        some lower ∧
        Structured.Preservation.ProcedurePreservation.compileChecked?
          lower.toStructured = some asm :=
  Functions.Source.Program.compileLiveNoInternalCallChecked?_eq_some hCompile

example {program : Functions.Program} {asm : Assembly.Program}
    (hCompile :
      Functions.Source.Program.compileLiveNoInternalCallChecked? program =
        some asm) :
    Functions.LiveLayout.NoInternalCall.Program.Holds program ∧
      Functions.LiveLayout.Checked.Program.check? program = true :=
  Functions.Source.Program.compileLiveNoInternalCallChecked?_liveGate hCompile

example {program : Functions.Program} {asm : Assembly.Program}
    (hNoCallCreate : program.usesCallCreate = false)
    (hCompile :
      Functions.Source.Program.compileLiveNoInternalCallChecked? program =
        some asm) :
    Assembly.Program.usesCallCreate asm = false :=
  Functions.Source.Program.compileLiveNoInternalCallChecked?_noCallCreate
    hNoCallCreate hCompile

example {program : Objects.Program} {asm : Assembly.Program}
    (hCompile :
      Objects.Source.Program.compileLiveNoInternalCallChecked? program =
        some asm) :
    Functions.Source.Program.compileLiveNoInternalCallChecked?
        program.toFunctions =
      some asm := by
  simpa [Objects.Source.Program.compileLiveNoInternalCallChecked?]
    using hCompile

example {program : Objects.Program} {asm : Assembly.Program}
    (hNoCallCreate : program.toFunctions.usesCallCreate = false)
    (hCompile :
      Objects.Source.Program.compileLiveNoInternalCallChecked? program =
        some asm) :
    Assembly.Program.usesCallCreate asm = false :=
  Objects.Source.Program.compileLiveNoInternalCallChecked?_noCallCreate
    hNoCallCreate hCompile

example {maxWords : Nat} {program : Functions.Program}
    {range : Functions.CallAwareSpill.ScratchRange}
    {plan : Functions.CallAwareSpill.Plan}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    (hNoCallCreate : program.usesCallCreate = false)
    (hCompile :
      Functions.CallAwareSpill.compileCheckedPlannedPreallocWithSwitchFallback?
          maxWords program =
        some (range, plan, exprProgram, asm)) :
    Assembly.Program.usesCallCreate asm = false :=
  Functions.CallAwareSpill.compileCheckedPlannedPreallocWithSwitchFallback?_noCallCreate
    hNoCallCreate hCompile

example {maxWords : Nat} {program : Objects.Program}
    {range : Functions.CallAwareSpill.ScratchRange}
    {plan : Functions.CallAwareSpill.Plan}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    (hCompile :
      Objects.Source.Program.compileCheckedWithCallAwareSpillWithSwitchPlannedPrealloc?
          maxWords program =
        some (range, plan, exprProgram, asm)) :
    Functions.CallAwareSpill.compileCheckedPlannedPreallocWithSwitchFallback?
        maxWords program.toFunctions =
      some (range, plan, exprProgram, asm) :=
  Objects.Source.Program.compileCheckedWithCallAwareSpillWithSwitchPlannedPrealloc?_eq_some
    hCompile

example {maxWords : Nat} {program : Objects.Program}
    {range : Functions.CallAwareSpill.ScratchRange}
    {plan : Functions.CallAwareSpill.Plan}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    (hCompile :
      Objects.Source.Program.compileCheckedWithCallAwareSpillWithSwitchPlannedPrealloc?
          maxWords program =
        some (range, plan, exprProgram, asm)) :
    program.toFunctions.SourceAccepted :=
  Objects.Source.Program.compileCheckedWithCallAwareSpillWithSwitchPlannedPrealloc?_sourceAccepted
    hCompile

example {maxWords : Nat} {program : Objects.Program}
    {range : Functions.CallAwareSpill.ScratchRange}
    {plan : Functions.CallAwareSpill.Plan}
    {exprProgram : Expressions.Program} {asm : Assembly.Program}
    (hNoCallCreate : program.toFunctions.usesCallCreate = false)
    (hCompile :
      Objects.Source.Program.compileCheckedWithCallAwareSpillWithSwitchPlannedPrealloc?
          maxWords program =
        some (range, plan, exprProgram, asm)) :
    Assembly.Program.usesCallCreate asm = false :=
  Objects.Source.Program.compileCheckedWithCallAwareSpillWithSwitchPlannedPrealloc?_noCallCreate
    hNoCallCreate hCompile

example {program : Yul.Program} {asm : Assembly.Program}
    {functionProgram : Functions.Program}
    (hCompile :
      Yul.Program.compileLiveNoInternalCallChecked? program = some asm)
    (hToObjects :
      program.toObjects? =
        some { root := Objects.Object.mk "root" functionProgram [] [] }) :
    Functions.LiveLayout.NoInternalCall.Program.Holds functionProgram ∧
      Functions.LiveLayout.Checked.Program.check? functionProgram = true :=
  Yul.Program.compileLiveNoInternalCallChecked?_loweredFunctionProgram_liveGate
    hCompile hToObjects

example {layout live : List Functions.Name} {name : Functions.Name}
    (hMem :
      name ∈ Functions.LiveLayout.Layout.trimDeadPrefix layout live) :
    name ∈ layout :=
  Functions.LiveLayout.Layout.mem_trimDeadPrefix hMem

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx}
    (hRel : Functions.SourceDirect.CtxRel retc source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc source target :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxRel.of_ctxRel hRel

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx}
    (hRel : Functions.SourceDirect.CtxRel retc source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
      target :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel.of_ctxRel hRel

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
        target) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc
      source.withoutLoopControl target.withoutLoopControl :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel.withoutLoopControl
    hRel

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} (names : List Functions.Name)
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
        target) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc
      { source with scope := names ++ source.scope }
      (target.withLayout (names ++ target.layout)) :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel.withScopePrepend
    names hRel

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {layout : List Functions.Name}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
        target)
    (hSubset :
      ∀ {name : Functions.Name}, name ∈ layout → name ∈ source.scope)
    (hCleanupLayout :
      Functions.SourceDirect.CleanupLayoutRel layout target.layout) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
      (target.withLayout layout) :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel.withLayout_of_source_subset_cleanupLayoutRel
    hRel hSubset hCleanupLayout

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
        target) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc
      (source.withLoopControl source.scope source.scope)
      (target.withLoopControl target.layout.length) :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel.withLoopControl_self
    hRel

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {live : Functions.LiveLayout.Ctx}
    {keepLive : List Functions.Name}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
        target)
    (hControl :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source)
    (hBreakLiveSubset :
      ∀ {name : Functions.Name}, name ∈ live.breakLive → name ∈ keepLive)
    (hContinueLiveSubset :
      ∀ {name : Functions.Name},
        name ∈ live.continueLive → name ∈ keepLive) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
      (target.withLayout
        (Functions.LiveLayout.Layout.trimDeadPrefix target.layout keepLive)) :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel.trimDeadPrefix_of_handler_live_subset
    hRel hControl hBreakLiveSubset hContinueLiveSubset

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {sourceOutcome : Functions.Source.Outcome}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
        target) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel retc
      source target sourceOutcome :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel.of_cleanupRel
    hRel

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {sourceOutcome : Functions.Source.Outcome}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel retc
        source target sourceOutcome) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc source target :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel.ctxRel hRel

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {sourceOutcome : Functions.Source.Outcome}
    {breakScope : List Functions.Name} {targetDepth : Nat}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel retc
        source target sourceOutcome)
    (hMode : sourceOutcome.mode = .brk)
    (hBreak : source.breakScope? = some breakScope)
    (hTargetDepth : target.breakDepth? = some targetDepth) :
    Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel target.layout
      targetDepth breakScope :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel.breakCleanup
    hRel hMode hBreak hTargetDepth

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {sourceOutcome : Functions.Source.Outcome}
    {continueScope : List Functions.Name} {targetDepth : Nat}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel retc
        source target sourceOutcome)
    (hMode : sourceOutcome.mode = .cont)
    (hContinue : source.continueScope? = some continueScope)
    (hTargetDepth : target.continueDepth? = some targetDepth) :
    Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel target.layout
      targetDepth continueScope :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel.continueCleanup
    hRel hMode hContinue hTargetDepth

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {live : Functions.LiveLayout.Ctx}
    {keepLive : List Functions.Name}
    {sourceOutcome : Functions.Source.Outcome}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxCleanupRel retc source
        target)
    (hControl :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source)
    (hBreakLiveSubset :
      sourceOutcome.mode = .brk →
        ∀ {name : Functions.Name},
          name ∈ live.breakLive → name ∈ keepLive)
    (hContinueLiveSubset :
      sourceOutcome.mode = .cont →
        ∀ {name : Functions.Name},
          name ∈ live.continueLive → name ∈ keepLive) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel retc
      source
      (target.withLayout
        (Functions.LiveLayout.Layout.trimDeadPrefix target.layout keepLive))
      sourceOutcome :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel.trimDeadPrefix_of_mode_live_subset
    hRel hControl hBreakLiveSubset hContinueLiveSubset

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {live : Functions.LiveLayout.Ctx}
    {keepLive : List Functions.Name}
    {outerOutcome sourceOutcome : Functions.Source.Outcome}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel retc
        source target outerOutcome)
    (hControl :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source)
    (hBreakMode :
      sourceOutcome.mode = .brk → outerOutcome.mode = .brk)
    (hContinueMode :
      sourceOutcome.mode = .cont → outerOutcome.mode = .cont)
    (hBreakLiveSubset :
      sourceOutcome.mode = .brk →
        ∀ {name : Functions.Name},
          name ∈ live.breakLive → name ∈ keepLive)
    (hContinueLiveSubset :
      sourceOutcome.mode = .cont →
        ∀ {name : Functions.Name},
          name ∈ live.continueLive → name ∈ keepLive) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel retc
      source
      (target.withLayout
        (Functions.LiveLayout.Layout.trimDeadPrefix target.layout keepLive))
      sourceOutcome :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel.trimDeadPrefix_of_outer_mode_live_subset
    hRel hControl hBreakMode hContinueMode hBreakLiveSubset
    hContinueLiveSubset

example {retc protectedDepth : Nat}
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {returns live : List Functions.Name} {stmt : Functions.Stmt}
    {prep : List Locals.Stmt} {finalLayout : List Functions.Name}
    {sourceOutcome : Functions.Source.Outcome}
    (hPrepare :
      Functions.LiveLayout.Prepare.forStmtAboveSuffix? protectedDepth returns
          target.layout live stmt =
        some (prep, finalLayout))
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel retc
        source target sourceOutcome)
    (hBreakDepth :
      sourceOutcome.mode = .brk →
        ∀ {depth : Nat}, target.breakDepth? = some depth →
          depth ≤ protectedDepth)
    (hContinueDepth :
      sourceOutcome.mode = .cont →
        ∀ {depth : Nat}, target.continueDepth? = some depth →
          depth ≤ protectedDepth) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel retc
      source (target.withLayout finalLayout) sourceOutcome :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel.forStmtAboveSuffix_of_mode_depth_bounds
    hPrepare hRel hBreakDepth hContinueDepth

example {retc targetDepth : Nat}
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {live : Functions.LiveLayout.Ctx}
    {sourceOutcome : Functions.Source.Outcome}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel retc
        source target sourceOutcome)
    (hMode : sourceOutcome.mode = .brk)
    (hControl :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source)
    (hNoDup : target.layout.Nodup)
    (hTargetDepth : target.breakDepth? = some targetDepth) :
    targetDepth ≤ live.protectedDepth :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel.breakDepth_le_protectedDepth
    hRel hMode hControl hNoDup hTargetDepth

example {retc targetDepth : Nat}
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    {live : Functions.LiveLayout.Ctx}
    {sourceOutcome : Functions.Source.Outcome}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel retc
        source target sourceOutcome)
    (hMode : sourceOutcome.mode = .cont)
    (hControl :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source)
    (hNoDup : target.layout.Nodup)
    (hTargetDepth : target.continueDepth? = some targetDepth) :
    targetDepth ≤ live.protectedDepth :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel.continueDepth_le_protectedDepth
    hRel hMode hControl hNoDup hTargetDepth

example {live : Functions.LiveLayout.Ctx} :
    Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel live
      Functions.Source.Ctx.initial :=
  Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel.initial

example {live : Functions.LiveLayout.Ctx} {source : Functions.Source.Ctx}
    {breakLive continueLive breakScope continueScope :
      List Functions.Name}
    (hBreak :
      Functions.SourceDirect.SameScope breakLive breakScope)
    (hContinue :
      Functions.SourceDirect.SameScope continueLive continueScope)
    (hBreakScope :
      ∀ name, name ∈ breakScope → name ∈ source.scope)
    (hContinueScope :
      ∀ name, name ∈ continueScope → name ∈ source.scope) :
    Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel
      (live.withLoop breakLive continueLive)
      (source.withLoopControl breakScope continueScope) :=
  Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel.withLoop_sameScope
    hBreak hContinue hBreakScope hContinueScope

example {live : Functions.LiveLayout.Ctx} {source : Functions.Source.Ctx}
    {breakLive continueLive : List Functions.Name}
    (hBreak :
      Functions.SourceDirect.SameScope breakLive source.scope)
    (hContinue :
      Functions.SourceDirect.SameScope continueLive source.scope) :
    Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel
      (live.withLoop breakLive continueLive)
      (source.withLoopControl source.scope source.scope) :=
  Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel.withLoop_self
    hBreak hContinue

example {live : Functions.LiveLayout.Ctx} {source : Functions.Source.Ctx} :
    Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel live
      source.withoutLoopControl :=
  Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel.withoutLoopControl

example {live : Functions.LiveLayout.Ctx} {source : Functions.Source.Ctx}
    (names : List Functions.Name)
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel live
        source) :
    Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel live
      { source with scope := names ++ source.scope } :=
  Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel.withScopePrepend
    names hRel

example {prim : Functions.Source.PrimitiveSemantics}
    {program : Functions.Program} {live : Functions.LiveLayout.Ctx}
    {source sourceOut : Functions.Source.Ctx} {fuel : Nat}
    {stmt : Functions.Stmt} {state sourceAfter : Functions.Source.State}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel live
        source)
    (hRun :
      Functions.Source.Stmt.run prim program source fuel stmt state =
        .ok (Functions.Source.Outcome.regular sourceAfter, sourceOut)) :
    Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel live
      sourceOut :=
  Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel.stmt_regular
    hRel hRun

example {prim : Functions.Source.PrimitiveSemantics}
    {program : Functions.Program} {live : Functions.LiveLayout.Ctx}
    {source sourceOut : Functions.Source.Ctx} {fuel : Nat}
    {block : Functions.Block} {state sourceAfter : Functions.Source.State}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel live
        source)
    (hRun :
      Functions.Source.Block.runOpen prim program source fuel block state =
        .ok (Functions.Source.Outcome.regular sourceAfter, sourceOut)) :
    Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel live
      sourceOut :=
  Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel.block_regular
    hRel hRun

example {live : Functions.LiveLayout.Ctx} {source : Functions.Source.Ctx}
    {after : List Functions.Name} {declared : Functions.Name}
    {value : Functions.Expr 1} {breakScope : List Functions.Name}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel live
        source)
    (hBreak : source.breakScope? = some breakScope)
    (hScoped :
      Functions.Scope.Stmt.Scoped source.scope
        (Functions.Stmt.let_ declared value))
    (hAfter :
      ∀ {name : Functions.Name}, name ∈ live.breakLive → name ∈ after) :
    ∀ {name : Functions.Name}, name ∈ live.breakLive →
      name ∈
        Functions.LiveLayout.Stmt.liveBefore live after
          (Functions.Stmt.let_ declared value) :=
  Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel.breakLive_subset_let_liveBefore_of_scoped
    hRel hBreak hScoped hAfter

example {live : Functions.LiveLayout.Ctx} {source : Functions.Source.Ctx}
    {after : List Functions.Name} {declared : Functions.Name}
    {value : Functions.Expr 1} {continueScope : List Functions.Name}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel live
        source)
    (hContinue : source.continueScope? = some continueScope)
    (hScoped :
      Functions.Scope.Stmt.Scoped source.scope
        (Functions.Stmt.let_ declared value))
    (hAfter :
      ∀ {name : Functions.Name}, name ∈ live.continueLive → name ∈ after) :
    ∀ {name : Functions.Name}, name ∈ live.continueLive →
      name ∈
        Functions.LiveLayout.Stmt.liveBefore live after
          (Functions.Stmt.let_ declared value) :=
  Functions.LiveLayout.SourceDirectBridge.LiveHandlerScopeRel.continueLive_subset_let_liveBefore_of_scoped
    hRel hContinue hScoped hAfter

example {env : List Functions.Name} {value : EvmYul.UInt256}
    {cases : List (EvmYul.UInt256 × Functions.Block)}
    {defaultBody : Option Functions.Block} {body : Functions.Block}
    (hCases : Functions.Scope.CaseList.Scoped env cases)
    (hDefault : Functions.Scope.Default.Scoped env defaultBody)
    (hSelect :
      Functions.Source.Switch.select value cases defaultBody = some body) :
    Functions.Scope.Block.Scoped env body :=
  Functions.LiveLayout.SourceScoped.blockScoped_of_source_select_some
    hCases hDefault hSelect

example {env : List Functions.Name} {value : EvmYul.UInt256}
    {scrutinee : Functions.Expr 1}
    {cases : List (EvmYul.UInt256 × Functions.Block)}
    {defaultBody : Option Functions.Block} {body : Functions.Block}
    (hScoped :
      Functions.Scope.Stmt.Scoped env
        (Functions.Stmt.switch scrutinee cases defaultBody))
    (hSelect :
      Functions.Source.Switch.select value cases defaultBody = some body) :
    Functions.Scope.Block.Scoped env body :=
  Functions.LiveLayout.SourceScoped.blockScoped_of_switch_select_some
    hScoped hSelect

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {live : List Functions.Name}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc source
      (target.withLayout
        (Functions.LiveLayout.Layout.trimDeadPrefix target.layout live)) :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxRel.cleanupTo_trimDeadPrefix
    hRel

example {layout scope : List Functions.Name}
    (hRel : Functions.SourceDirect.CleanupScopeRel layout scope) :
    Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel layout
      scope.length scope :=
  Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel.of_cleanupScope
    hRel

example {layout scope : List Functions.Name} {depth : Nat}
    {name : Functions.Name}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel layout depth
        scope) :
    Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel
      (name :: layout) depth scope :=
  Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel.cons hRel

example {layout scope added : List Functions.Name} {depth : Nat}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel layout depth
        scope) :
    Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel
      (added ++ layout) depth scope :=
  Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel.prepend added
    hRel

example {layout base scope : List Functions.Name} {depth : Nat}
    (hLayout :
      Functions.SourceDirect.CleanupLayoutRel layout base)
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel base depth
        scope) :
    Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel layout depth
      scope :=
  Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel.of_cleanupLayoutRel
    hLayout hRel

example {layout promoted scope : List Functions.Name} {depth idx : Nat}
    {name : Functions.Name}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel layout depth
        scope)
    (hPromote :
      Functions.LiveLayout.Layout.promoteName? layout name =
        some (promoted, idx))
    (hIdx : idx < layout.length - depth) :
    Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel promoted depth
      scope :=
  Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel.promoteName_of_idx_lt_suffix
    hRel hPromote hIdx

example {layout live scope : List Functions.Name} {depth : Nat}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel layout depth
        scope)
    (hKeep :
      ∀ {name : Functions.Name},
        name ∈ layout.drop (layout.length - depth) → name ∈ live) :
    Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel
      (Functions.LiveLayout.Layout.trimDeadPrefix layout live) depth scope :=
  Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel.trimDeadPrefix_of_keep
    hRel hKeep

example {layout scope : List Functions.Name}
    (hSubset : ∀ {name : Functions.Name}, name ∈ layout → name ∈ scope) :
    Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel layout
      layout.length scope :=
  Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel.full_layout
    hSubset

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {scope : List Functions.Name} {depth : Nat}
    (hRel : Functions.SourceDirect.CtxRel retc source target)
    (hBreak : source.breakScope? = some scope)
    (hTargetDepth : target.breakDepth? = some depth) :
    Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel target.layout
      depth scope :=
  Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel.break_of_ctxRel
    hRel hBreak hTargetDepth

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {scope : List Functions.Name} {depth : Nat}
    (hRel : Functions.SourceDirect.CtxRel retc source target)
    (hContinue : source.continueScope? = some scope)
    (hTargetDepth : target.continueDepth? = some depth) :
    Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel target.layout
      depth scope :=
  Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel.continue_of_ctxRel
    hRel hContinue hTargetDepth

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {scope : List Functions.Name}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc source target)
    (hBreak : source.breakScope? = some scope) :
    ∃ depth, target.breakDepth? = some depth :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxRel.breakDepth_some
    hRel hBreak

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {scope : List Functions.Name}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc source target)
    (hContinue : source.continueScope? = some scope) :
    ∃ depth, target.continueDepth? = some depth :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxRel.continueDepth_some
    hRel hContinue

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc
      (source.withLoopControl source.scope source.scope)
      (target.withLoopControl target.layout.length) :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxRel.withLoopControl_self
    hRel

example {layout live scope : List Functions.Name}
    (hNoDup : layout.Nodup)
    (hCleanup :
      Functions.SourceDirect.CleanupScopeRel layout scope)
    (hSame :
      Functions.SourceDirect.SameScope live scope) :
    Functions.SourceDirect.CleanupScopeRel
      (Functions.LiveLayout.Layout.trimDeadPrefix layout live) scope :=
  Functions.LiveLayout.Layout.cleanupScope_trimDeadPrefix_of_sameScope
    hNoDup hCleanup hSame

example {live : Functions.LiveLayout.Ctx} {source : Functions.Source.Ctx}
    {breakLive continueLive breakScope continueScope :
      List Functions.Name}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source)
    (hBreak :
      Functions.SourceDirect.SameScope breakLive breakScope)
    (hContinue :
      Functions.SourceDirect.SameScope continueLive continueScope) :
    Functions.LiveLayout.SourceDirectBridge.LiveControlRel
      (live.withLoop breakLive continueLive)
      (source.withLoopControl breakScope continueScope) :=
  Functions.LiveLayout.SourceDirectBridge.LiveControlRel.withLoop
    hRel hBreak hContinue

example {live : Functions.LiveLayout.Ctx} {source : Functions.Source.Ctx}
    {layout breakScope : List Functions.Name} {depth : Nat}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source)
    (hBreak : source.breakScope? = some breakScope)
    (hCleanup :
      Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel layout depth
        breakScope) :
    Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel
      (Functions.LiveLayout.Layout.trimDeadPrefix layout live.breakLive) depth
      breakScope :=
  Functions.LiveLayout.SourceDirectBridge.LiveControlRel.breakCleanup_trimDeadPrefix
    hRel hBreak hCleanup

example {live : Functions.LiveLayout.Ctx} {source : Functions.Source.Ctx}
    {layout continueScope : List Functions.Name} {depth : Nat}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source)
    (hContinue : source.continueScope? = some continueScope)
    (hCleanup :
      Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel layout depth
        continueScope) :
    Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel
      (Functions.LiveLayout.Layout.trimDeadPrefix layout live.continueLive)
      depth continueScope :=
  Functions.LiveLayout.SourceDirectBridge.LiveControlRel.continueCleanup_trimDeadPrefix
    hRel hContinue hCleanup

example {live : Functions.LiveLayout.Ctx} {source : Functions.Source.Ctx}
    {returns leaveScope : List Functions.Name}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source)
    (hReturns : live.returns = returns)
    (hLeave : source.leaveScope? = some leaveScope) :
    ∀ name, name ∈ returns → name ∈ leaveScope :=
  Functions.LiveLayout.SourceDirectBridge.LiveControlRel.returnScope_of_returns_eq
    hRel hReturns hLeave

example (fn : Functions.FunDef) :
    Functions.LiveLayout.SourceDirectBridge.LiveControlRel
      { returns := fn.returns }
      (Functions.SourceDirect.FunDef.sourceBodyCtx fn) :=
  Functions.LiveLayout.SourceDirectBridge.FunDef.liveControlRel_bodyCtx fn

example {live : Functions.LiveLayout.Ctx} {source : Functions.Source.Ctx}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source) :
    Functions.LiveLayout.SourceDirectBridge.LiveControlRel live
      source.withoutLoopControl :=
  Functions.LiveLayout.SourceDirectBridge.LiveControlRel.withoutLoopControl
    hRel

example {prim : Functions.Source.PrimitiveSemantics}
    {program : Functions.Program} {live : Functions.LiveLayout.Ctx}
    {source sourceOut : Functions.Source.Ctx} {fuel : Nat}
    {stmt : Functions.Stmt} {state sourceAfter : Functions.Source.State}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source)
    (hRun :
      Functions.Source.Stmt.run prim program source fuel stmt state =
        .ok (Functions.Source.Outcome.regular sourceAfter, sourceOut)) :
    Functions.LiveLayout.SourceDirectBridge.LiveControlRel live sourceOut :=
  Functions.LiveLayout.SourceDirectBridge.LiveControlRel.stmt_regular
    hRel hRun

example {prim : Functions.Source.PrimitiveSemantics}
    {program : Functions.Program} {live : Functions.LiveLayout.Ctx}
    {source sourceOut : Functions.Source.Ctx} {fuel : Nat}
    {block : Functions.Block} {state sourceAfter : Functions.Source.State}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveControlRel live source)
    (hRun :
      Functions.Source.Block.runOpen prim program source fuel block state =
        .ok (Functions.Source.Outcome.regular sourceAfter, sourceOut)) :
    Functions.LiveLayout.SourceDirectBridge.LiveControlRel live sourceOut :=
  Functions.LiveLayout.SourceDirectBridge.LiveControlRel.block_regular
    hRel hRun

example (fn : Functions.FunDef) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxRel fn.returns.length
      (Functions.SourceDirect.FunDef.sourceBodyCtx fn)
      (Functions.SourceDirect.FunDef.targetBodyCtx fn) :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxRel.bodyCtx fn

example (fn : Functions.FunDef) :
    ∀ {breakScope targetDepth},
      (Functions.SourceDirect.FunDef.sourceBodyCtx fn).breakScope? =
        some breakScope →
      (Functions.SourceDirect.FunDef.targetBodyCtx fn).breakDepth? =
        some targetDepth →
        Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel
          (Functions.SourceDirect.FunDef.targetBodyCtx fn).layout targetDepth
          breakScope :=
  Functions.LiveLayout.SourceDirectBridge.FunDef.bodyCtx_breakCleanupScope fn

example (fn : Functions.FunDef) :
    ∀ {continueScope targetDepth},
      (Functions.SourceDirect.FunDef.sourceBodyCtx fn).continueScope? =
        some continueScope →
      (Functions.SourceDirect.FunDef.targetBodyCtx fn).continueDepth? =
        some targetDepth →
        Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel
          (Functions.SourceDirect.FunDef.targetBodyCtx fn).layout targetDepth
          continueScope :=
  Functions.LiveLayout.SourceDirectBridge.FunDef.bodyCtx_continueCleanupScope fn

example {retc : Nat} {returns : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {sourceResult : Functions.Source.Outcome × Functions.Source.Ctx}
    {targetResult : Locals.Outcome × Locals.Ctx}
    (hRel :
      Functions.SourceDirect.StmtRunResultRel retc returns hiddenReturns
        sourceResult targetResult) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunResultRel retc returns
      hiddenReturns sourceResult targetResult :=
  Functions.LiveLayout.SourceDirectBridge.LiveStmtRunResultRel.of_sourceDirect
    hRel

example {retc : Nat} {returns : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {sourceOutcome : Functions.Source.Outcome}
    {targetOutcome : Locals.Outcome}
    {sourceCtx stmtSourceCtx : Functions.Source.Ctx}
    {targetCtx : Locals.Ctx}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveStmtRunResultRel retc returns
        hiddenReturns (sourceOutcome, stmtSourceCtx)
        (targetOutcome, targetCtx))
    (hSourceCtx : stmtSourceCtx = sourceCtx)
    (hNonregular : sourceOutcome.mode ≠ .regular) :
    Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenResultRel retc returns
      hiddenReturns (sourceOutcome, sourceCtx) (targetOutcome, targetCtx) :=
  Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenResultRel.of_stmt_nonregular
    hRel hSourceCtx hNonregular

example {retc : Nat} {returns : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {sourceResult : Functions.Source.Outcome × Functions.Source.Ctx}
    {targetResult : Locals.Outcome × Locals.Ctx}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenResultRel retc
        returns hiddenReturns sourceResult targetResult) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceResult.2
      targetResult.2 :=
  Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenResultRel.ctxRel hRel

example {retc : Nat} {returns : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {sourceResult : Functions.Source.Outcome × Functions.Source.Ctx}
    {targetResult : Locals.Outcome × Locals.Ctx}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenResultRel retc
        returns hiddenReturns sourceResult targetResult)
    (hNotBreak : sourceResult.1.mode ≠ .brk)
    (hNotContinue : sourceResult.1.mode ≠ .cont) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxOutcomeCleanupRel retc
      sourceResult.2 targetResult.2 sourceResult.1 :=
  Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenResultRel.outcomeCleanup_of_not_break_continue
    hRel hNotBreak hNotContinue

example : True := by
  have _ :=
    @Functions.LiveLayout.SourceDirectBridge.LiveLoopStmtRunResultRel.to_liveStmtRunResultRel
  trivial

example : True := by
  have _ :=
    @Functions.LiveLayout.SourceDirectBridge.LiveLoopStmtRunResultRel.to_stmtOutcomeRel_of_target_layout
  trivial

example : True := by
  have _ :=
    @Functions.LiveLayout.SourceDirectBridge.LiveLoopBlockOpenResultRel.to_liveBlockOpenResultRel
  trivial

example : True := by
  have _ :=
    @Functions.LiveLayout.SourceDirectBridge.LiveLoopBlockOpenResultRel.of_liveLoopStmtRunResultRel
  trivial

example {ctx : Locals.Ctx} {live : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target cleaned : Locals.RunState}
    (hRun :
      Locals.Direct.Ctx.runCleanupTo ctx
          (Functions.LiveLayout.Layout.trimDeadPrefix ctx.layout live).length
          target =
        .ok cleaned)
    (hRel :
      Functions.SourceDirect.StateRel ctx.layout hiddenReturns source target) :
    Functions.SourceDirect.StateRel
      (Functions.LiveLayout.Layout.trimDeadPrefix ctx.layout live)
      hiddenReturns source cleaned :=
  Functions.LiveLayout.SourceDirectBridge.stateRel_cleanupTo_trimDeadPrefix
    hRun hRel

example {program : Locals.Program}
    {ctx midCtx : Locals.Ctx} {fuel : Nat} {stmt : Locals.Stmt}
    {state mid : Locals.RunState}
    (hRun :
      Locals.Direct.Stmt.run program ctx fuel stmt state =
        .ok (Structured.Outcome.regular mid, midCtx)) :
    ∃ blockFuel,
      Locals.Direct.Block.runOpen program ctx blockFuel { stmts := [stmt] }
        state =
        .ok (Structured.Outcome.regular mid, midCtx) :=
  Functions.LiveLayout.Target.runOpen_singleton_regular_exists hRun

example {program : Locals.Program}
    {ctx runCtx : Locals.Ctx} {live : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {tail : List Locals.Stmt} {outcome : Locals.Outcome}
    (hRel :
      Functions.SourceDirect.StateRel ctx.layout hiddenReturns source target)
    (hTail :
      ∀ {cleaned},
        Functions.SourceDirect.StateRel
          (Functions.LiveLayout.Layout.trimDeadPrefix ctx.layout live)
          hiddenReturns source cleaned →
        ∃ tailFuel,
          Locals.Direct.Block.runOpen program
            (ctx.withLayout
              (Functions.LiveLayout.Layout.trimDeadPrefix ctx.layout live))
            tailFuel { stmts := tail } cleaned =
            .ok (outcome, runCtx)) :
    ∃ blockFuel,
      Locals.Direct.Block.runOpen program ctx blockFuel
        { stmts :=
            Functions.LiveLayout.Lower.cleanupToLive ctx.layout live :: tail }
        target =
        .ok (outcome, runCtx) :=
  Functions.LiveLayout.Target.cleanupToLive_prefix_runOpen_exists hRel hTail

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx sourceCtxAfter : Functions.Source.Ctx}
    {targetCtx targetCtxAfter : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {targetStmtBlock targetRestBlock : Locals.Block}
    {source sourceAfter : Functions.Source.State}
    {target targetAfter : Locals.RunState}
    {stmtTargetFuel : Nat}
    (hSourceStmt :
      Functions.Source.Stmt.run prim sourceProgram sourceCtx fuel stmt source =
        .ok (Functions.Source.Outcome.regular sourceAfter, sourceCtxAfter))
    (hTargetStmt :
      Locals.Direct.Block.runOpen targetProgram targetCtx stmtTargetFuel
        targetStmtBlock target =
        .ok (Structured.Outcome.regular targetAfter, targetCtxAfter))
    (hRest :
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridge prim
        sourceProgram targetProgram returns retc fuel sourceCtxAfter
        targetCtxAfter hiddenReturns { stmts := rest } targetRestBlock
        sourceAfter targetAfter) :
    Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridge prim
      sourceProgram targetProgram returns retc (fuel + 1) sourceCtx targetCtx
      hiddenReturns { stmts := stmt :: rest }
      { stmts := targetStmtBlock.stmts ++ targetRestBlock.stmts } source
      target :=
  Functions.LiveLayout.SourceTarget.blockOpen_cons_regular_runBridge_of_parts
    hSourceStmt hTargetStmt hRest

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx stmtSourceCtx : Functions.Source.Ctx}
    {targetCtx targetRunCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {targetStmtBlock : Locals.Block} {targetTail : List Locals.Stmt}
    {source : Functions.Source.State} {target : Locals.RunState}
    {sourceOutcome : Functions.Source.Outcome}
    {targetOutcome : Locals.Outcome}
    {stmtTargetFuel : Nat}
    (hSourceStmt :
      Functions.Source.Stmt.run prim sourceProgram sourceCtx fuel stmt source =
        .ok (sourceOutcome, stmtSourceCtx))
    (hSourceCtx : stmtSourceCtx = sourceCtx)
    (hNonregular : sourceOutcome.mode ≠ .regular)
    (hTargetStmt :
      Locals.Direct.Block.runOpen targetProgram targetCtx stmtTargetFuel
        targetStmtBlock target =
        .ok (targetOutcome, targetRunCtx))
    (hStmtRel :
      Functions.LiveLayout.SourceDirectBridge.LiveStmtRunResultRel retc returns
        hiddenReturns (sourceOutcome, stmtSourceCtx)
        (targetOutcome, targetRunCtx)) :
    Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridge prim
      sourceProgram targetProgram returns retc (fuel + 1) sourceCtx targetCtx
      hiddenReturns { stmts := stmt :: rest }
      { stmts := targetStmtBlock.stmts ++ targetTail } source target :=
  Functions.LiveLayout.SourceTarget.blockOpen_cons_nonregular_runBridge_of_parts
    hSourceStmt hSourceCtx hNonregular hTargetStmt hStmtRel

example {returns : List Functions.Name} {ctx : Functions.LiveLayout.Ctx}
    {layout after : List Functions.Name}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {lowerStmts : List Locals.Stmt} {outLayout : List Functions.Name}
    (hLower :
      Functions.LiveLayout.Lower.StmtList.toLocals? returns ctx layout after
        (stmt :: rest) = some (lowerStmts, outLayout)) :
    ∃ restLive stmtLive liveLayout,
      ∃ (prep : List Locals.Stmt),
      ∃ preparedLayout lowerStmt nextLayout lowerRest,
      restLive =
          Functions.LiveLayout.StmtList.liveBefore ctx after rest ∧
        stmtLive =
          Functions.LiveLayout.Stmt.liveBefore ctx restLive stmt ∧
        liveLayout =
          Functions.LiveLayout.Layout.trimDeadPrefix layout stmtLive ∧
        Functions.LiveLayout.Prepare.forStmtAboveSuffix? ctx.protectedDepth
          returns liveLayout stmtLive stmt =
          some (prep, preparedLayout) ∧
        Functions.LiveLayout.Layout.entryWindowOk? preparedLayout stmtLive =
          true ∧
        Functions.LiveLayout.StmtAccess.accessible? returns
          preparedLayout stmt = true ∧
        Functions.LiveLayout.Lower.Stmt.toLocals? returns ctx
          preparedLayout restLive stmt =
            some (lowerStmt, nextLayout) ∧
        Functions.LiveLayout.Lower.StmtList.toLocals? returns ctx nextLayout
          after rest =
            some (lowerRest, outLayout) ∧
        lowerStmts =
          Functions.LiveLayout.Lower.cleanupToLive layout stmtLive ::
            (prep ++ (lowerStmt ++ lowerRest)) :=
  Functions.LiveLayout.Lower.StmtList.toLocals?_cons_components hLower

example {returns : List Functions.Name} {ctx : Functions.LiveLayout.Ctx}
    {layout after : List Functions.Name}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {lowerStmts : List Locals.Stmt} {outLayout : List Functions.Name}
    (hLower :
      Functions.LiveLayout.Lower.StmtList.toLocals? returns ctx layout after
        (stmt :: rest) = some (lowerStmts, outLayout)) :
    ∃ restLive stmtLive liveLayout,
      ∃ (prep : List Locals.Stmt),
      ∃ (preparedLayout : List Functions.Name),
      restLive =
          Functions.LiveLayout.StmtList.liveBefore ctx after rest ∧
        stmtLive =
          Functions.LiveLayout.Stmt.liveBefore ctx restLive stmt ∧
        liveLayout =
          Functions.LiveLayout.Layout.trimDeadPrefix layout stmtLive ∧
        Functions.LiveLayout.Prepare.forStmtAboveSuffix? ctx.protectedDepth
          returns liveLayout stmtLive stmt =
            some (prep, preparedLayout) ∧
        Functions.LiveLayout.Layout.entryWindowOk? preparedLayout stmtLive =
          true :=
  by
    rcases Functions.LiveLayout.Lower.StmtList.toLocals?_cons_components
        hLower with
      ⟨restLive, stmtLive, liveLayout, prep, preparedLayout, lowerStmt,
        nextLayout, lowerRest, hRestLive, hStmtLive, hLiveLayout, hPrepare,
        hEntry, _hAccess, _hLowerStmt, _hLowerRest, _hLowerStmts⟩
    exact ⟨restLive, stmtLive, liveLayout, prep, preparedLayout, hRestLive,
      hStmtLive, hLiveLayout, hPrepare, hEntry⟩

example {returns : List Functions.Name} {ctx : Functions.LiveLayout.Ctx}
    {layout after : List Functions.Name}
    {init post body : Functions.Block} {cond : Functions.Expr 1}
    {lowerStmt : List Locals.Stmt} {outLayout : List Functions.Name}
    (hLower :
      Functions.LiveLayout.Lower.Stmt.toLocals? returns ctx layout after
        (.for_ init cond post body) = some (lowerStmt, outLayout)) :
    let loopMentioned :=
      Functions.LiveLayout.NameSet.unions
        [Functions.LiveLayout.Reads.expr cond,
          Functions.LiveLayout.Reads.block post,
          Functions.LiveLayout.Reads.block body, after]
    let postLive := Functions.LiveLayout.Block.liveBefore ctx loopMentioned post
    let bodyCtx := ctx.withLoop after postLive
    let bodyLive :=
      Functions.LiveLayout.Block.liveBefore bodyCtx postLive body
    let loopLive :=
      Functions.LiveLayout.NameSet.unions
        [Functions.LiveLayout.Reads.expr cond, after, postLive, bodyLive]
    let initAfter := Functions.LiveLayout.NameSet.union loopLive layout
    ∃ lowerInit loopLayout lowerPost postLayout lowerBody bodyLayout,
      Functions.LiveLayout.Lower.Block.toLocals? returns
          (ctx.withProtectedLayout layout) layout initAfter init =
        some (lowerInit, loopLayout) ∧
      Functions.LiveLayout.ExprAccess.expr? 0 loopLayout cond = true ∧
      let postAfter :=
        Functions.LiveLayout.Checked.scopedAfter loopLayout loopMentioned
      let bodyAfter :=
        Functions.LiveLayout.Checked.scopedAfter loopLayout postLive
      let postCtx := ctx.withProtectedLayout loopLayout
      let bodyCheckCtx :=
        (ctx.withLoop
          (Functions.LiveLayout.Checked.scopedAfter loopLayout after)
          bodyAfter).withProtectedLayout loopLayout
      Functions.LiveLayout.Lower.Block.toLocals? returns postCtx loopLayout
          postAfter post =
        some (lowerPost, postLayout) ∧
      Functions.LiveLayout.Lower.Block.toLocals? returns bodyCheckCtx
          loopLayout bodyAfter body =
        some (lowerBody, bodyLayout) ∧
      lowerStmt =
        [Locals.Stmt.for_ lowerInit cond lowerPost lowerBody] ∧
      outLayout = layout :=
  Functions.LiveLayout.Lower.ForLowering.components_of_toLocals? hLower

example {retc : Nat} {returns : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {targetOutcome : Locals.Outcome}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveStmtRunResultRel retc returns
        hiddenReturns
        (Functions.Source.Outcome.regular source, sourceCtx)
        (targetOutcome, targetCtx)) :
    ∃ target,
      targetOutcome = Structured.Outcome.regular target ∧
        Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
          target ∧
        Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
          targetCtx :=
  Functions.LiveLayout.SourceDirectBridge.LiveStmtRunResultRel.source_regular_target_regular
    hRel

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} {name : Functions.Name}
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc
      { source with scope := name :: source.scope }
      (target.withLayout (name :: target.layout)) :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxRel.withScopeCons hRel

example {retc : Nat} {source : Functions.Source.Ctx}
    {target : Locals.Ctx} (names : List Functions.Name)
    (hRel :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc
      { source with scope := names ++ source.scope }
      (target.withLayout (names ++ target.layout)) :=
  Functions.LiveLayout.SourceDirectBridge.LiveCtxRel.withScopePrepend names
    hRel

example {program : Locals.Program} {ctx : Locals.Ctx}
    {fuel : Nat} {name : Functions.Name} {expr : Locals.Expr 1}
    {state targetAfter : Locals.RunState}
    (hRun :
      Locals.Direct.Stmt.run program ctx fuel (.assign name expr) state =
        .ok (Structured.Outcome.regular targetAfter, ctx)) :
    targetAfter.returns = state.returns :=
  Functions.LiveLayout.SourceTarget.Target.assign_returns hRun

example {prim : Functions.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source sourceAfterExpr : Functions.Source.State}
    {target : Locals.RunState}
    {expr : Locals.Expr 0} {values : List EvmYul.UInt256}
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hNoDup : targetCtx.layout.Nodup)
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hAccess :
      Locals.SourceLowering.Expr.Accessible targetCtx.layout 0 expr)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hEval :
      Functions.Source.Expr.eval prim expr source =
        .ok (sourceAfterExpr, values)) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns (.expr expr) { stmts := [Locals.Stmt.expr expr] }
      source target :=
  Functions.LiveLayout.SourceTarget.expr_liveStmtRunBridge hPrim hCtx hNoDup
    hOwned hAccess hRel hEval

example {prim : Functions.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source sourceAfterValue : Functions.Source.State}
    {target : Locals.RunState}
    {name : Functions.Name} {value : EvmYul.UInt256}
    {expr : Locals.Expr 1}
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hNoDup : targetCtx.layout.Nodup)
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hAccess :
      Locals.SourceLowering.Expr.Accessible targetCtx.layout 0 expr)
    (hFresh : name ∉ sourceCtx.scope)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hEvalOne :
      Functions.Source.Expr.evalOne prim expr source =
        .ok (sourceAfterValue, value)) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns (.let_ name expr)
      { stmts := [Locals.Stmt.let_ name expr] } source target :=
  Functions.LiveLayout.SourceTarget.let_liveStmtRunBridge hPrim hCtx hNoDup
    hOwned hAccess hFresh hRel hEvalOne

example {prim : Functions.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source sourceAfterValue : Functions.Source.State}
    {target : Locals.RunState}
    {name : Functions.Name} {idx : Nat} {value : EvmYul.UInt256}
    {expr : Locals.Expr 1}
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hNoDup : targetCtx.layout.Nodup)
    (hName : targetCtx.layout[idx]? = some name)
    (hBound : idx + 1 ≤ 16)
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hAccess :
      Locals.SourceLowering.Expr.Accessible targetCtx.layout 0 expr)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hEvalOne :
      Functions.Source.Expr.evalOne prim expr source =
        .ok (sourceAfterValue, value)) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns (.assign name expr)
      { stmts := [Locals.Stmt.assign name expr] } source target :=
  Functions.LiveLayout.SourceTarget.assign_liveStmtRunBridge hPrim hCtx
    hNoDup hName hBound hOwned hAccess hRel hEvalOne

example {prim : Functions.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {liveCtx : Functions.LiveLayout.Ctx}
    {after : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source sourceAfterExpr : Functions.Source.State}
    {target : Locals.RunState}
    {expr : Locals.Expr 0} {values : List EvmYul.UInt256}
    {lowerStmt : List Locals.Stmt} {nextLayout : List Functions.Name}
    (hLower :
      Functions.LiveLayout.Lower.Stmt.toLocals? returns liveCtx
          targetCtx.layout after (.expr expr) =
        some (lowerStmt, nextLayout))
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hNoDup : targetCtx.layout.Nodup)
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hAccess :
      Locals.SourceLowering.Expr.Accessible targetCtx.layout 0 expr)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hEval :
      Functions.Source.Expr.eval prim expr source =
        .ok (sourceAfterExpr, values)) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns (.expr expr) { stmts := lowerStmt } source target :=
  Functions.LiveLayout.SourceTarget.expr_liveStmtRunBridge_of_lower hPrim
    hLower hCtx hNoDup hOwned hAccess hRel hEval

example {prim : Functions.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {liveCtx : Functions.LiveLayout.Ctx}
    {after : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source sourceAfterValue : Functions.Source.State}
    {target : Locals.RunState}
    {name : Functions.Name} {value : EvmYul.UInt256}
    {expr : Locals.Expr 1}
    {lowerStmt : List Locals.Stmt} {nextLayout : List Functions.Name}
    (hLower :
      Functions.LiveLayout.Lower.Stmt.toLocals? returns liveCtx
          targetCtx.layout after (.let_ name expr) =
        some (lowerStmt, nextLayout))
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hNoDup : targetCtx.layout.Nodup)
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hAccess :
      Locals.SourceLowering.Expr.Accessible targetCtx.layout 0 expr)
    (hFresh : name ∉ sourceCtx.scope)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hEvalOne :
      Functions.Source.Expr.evalOne prim expr source =
        .ok (sourceAfterValue, value)) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns (.let_ name expr) { stmts := lowerStmt } source target :=
  Functions.LiveLayout.SourceTarget.let_liveStmtRunBridge_of_lower hPrim
    hLower hCtx hNoDup hOwned hAccess hFresh hRel hEvalOne

example {prim : Functions.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {liveCtx : Functions.LiveLayout.Ctx}
    {after : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source sourceAfterValue : Functions.Source.State}
    {target : Locals.RunState}
    {name : Functions.Name} {value : EvmYul.UInt256}
    {expr : Locals.Expr 1}
    {lowerStmt : List Locals.Stmt} {nextLayout : List Functions.Name}
    (hLower :
      Functions.LiveLayout.Lower.Stmt.toLocals? returns liveCtx
          targetCtx.layout after (.assign name expr) =
        some (lowerStmt, nextLayout))
    (hAccessCheck :
      Functions.LiveLayout.StmtAccess.accessible? returns targetCtx.layout
          (.assign name expr) =
        true)
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hNoDup : targetCtx.layout.Nodup)
    (hOwned : Locals.Source.Expr.SourceOwned expr)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hEvalOne :
      Functions.Source.Expr.evalOne prim expr source =
        .ok (sourceAfterValue, value)) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns (.assign name expr) { stmts := lowerStmt } source target :=
  Functions.LiveLayout.SourceTarget.assign_liveStmtRunBridge_of_lower hPrim
    hLower hAccessCheck hCtx hNoDup hOwned hRel hEvalOne

example {program : Locals.Program} {ctx : Locals.Ctx}
    {fuel : Nat} {stmt : Locals.Stmt}
    {state : Locals.RunState} {outcome : Locals.Outcome}
    (hRun :
      Locals.Direct.Stmt.run program ctx fuel stmt state = .ok (outcome, ctx))
    (hNonregular : outcome.mode ≠ .regular) :
    ∃ blockFuel,
      Locals.Direct.Block.runOpen program ctx blockFuel { stmts := [stmt] }
        state =
        .ok (outcome, ctx) :=
  Functions.LiveLayout.Target.runOpen_singleton_nonregular_exists hRun
    hNonregular

example {prim : Functions.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {kind : Assembly.HaltKind}
    {sharedAfter : EvmYul.SharedState .EVM}
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hTerminal : prim.terminal kind source.shared [] = .ok sharedAfter) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns (.terminal kind)
      { stmts := [Locals.Stmt.terminal kind] } source target :=
  Functions.LiveLayout.SourceTarget.terminal_liveStmtRunBridge hPrim hCtx hRel
    hTerminal

example {prim : Functions.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {liveCtx : Functions.LiveLayout.Ctx}
    {after : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {kind : Assembly.HaltKind}
    {sharedAfter : EvmYul.SharedState .EVM}
    {lowerStmt : List Locals.Stmt} {nextLayout : List Functions.Name}
    (hLower :
      Functions.LiveLayout.Lower.Stmt.toLocals? returns liveCtx
          targetCtx.layout after (.terminal kind) =
        some (lowerStmt, nextLayout))
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hTerminal : prim.terminal kind source.shared [] = .ok sharedAfter) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns (.terminal kind) { stmts := lowerStmt } source target :=
  Functions.LiveLayout.SourceTarget.terminal_liveStmtRunBridge_of_lower hPrim
    hLower hCtx hRel hTerminal

example {prim : Functions.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {liveCtx : Functions.LiveLayout.Ctx}
    {after : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source sourceAfterArgs : Functions.Source.State}
    {target : Locals.RunState}
    {kind : Assembly.HaltKind} {args : Locals.ExprSeq kind.argCount}
    {values : List EvmYul.UInt256}
    {sharedAfter : EvmYul.SharedState .EVM}
    {lowerStmt : List Locals.Stmt} {nextLayout : List Functions.Name}
    (hLower :
      Functions.LiveLayout.Lower.Stmt.toLocals? returns liveCtx
          targetCtx.layout after (.terminalArgs kind args) =
        some (lowerStmt, nextLayout))
    (hAccessCheck :
      Functions.LiveLayout.StmtAccess.accessible? returns targetCtx.layout
          (.terminalArgs kind args) =
        true)
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hNoDup : targetCtx.layout.Nodup)
    (hOwned : Locals.Source.ExprSeq.SourceOwned args)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hEvalArgs :
      Locals.Source.Expr.ExprSeq.eval prim args source =
        .ok (sourceAfterArgs, values))
    (hTerminal :
      prim.terminal kind sourceAfterArgs.shared values = .ok sharedAfter) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns (.terminalArgs kind args) { stmts := lowerStmt } source
      target :=
  Functions.LiveLayout.SourceTarget.terminalArgs_liveStmtRunBridge_of_lower
    hPrim hLower hAccessCheck hCtx hNoDup hOwned hRel hEvalArgs hTerminal

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {breakScope : List Functions.Name}
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hBreak : sourceCtx.breakScope? = some breakScope)
    (hCleanupScope :
      ∀ {targetDepth},
        targetCtx.breakDepth? = some targetDepth →
          Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel
            targetCtx.layout targetDepth breakScope)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns .brk { stmts := [Locals.Stmt.brk] } source target :=
  Functions.LiveLayout.SourceTarget.brk_liveStmtRunBridge
    hCtx hBreak hCleanupScope hRel

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {liveCtx : Functions.LiveLayout.Ctx}
    {after : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {breakScope : List Functions.Name}
    {lowerStmt : List Locals.Stmt} {nextLayout : List Functions.Name}
    (hLower :
      Functions.LiveLayout.Lower.Stmt.toLocals? returns liveCtx
          targetCtx.layout after .brk =
        some (lowerStmt, nextLayout))
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hBreak : sourceCtx.breakScope? = some breakScope)
    (hCleanupScope :
      ∀ {targetDepth},
        targetCtx.breakDepth? = some targetDepth →
          Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel
            targetCtx.layout targetDepth breakScope)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns .brk { stmts := lowerStmt } source target :=
  Functions.LiveLayout.SourceTarget.brk_liveStmtRunBridge_of_lower
    hLower hCtx hBreak hCleanupScope hRel

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {continueScope : List Functions.Name}
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hContinue : sourceCtx.continueScope? = some continueScope)
    (hCleanupScope :
      ∀ {targetDepth},
        targetCtx.continueDepth? = some targetDepth →
          Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel
            targetCtx.layout targetDepth continueScope)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns .cont { stmts := [Locals.Stmt.cont] } source target :=
  Functions.LiveLayout.SourceTarget.cont_liveStmtRunBridge
    hCtx hContinue hCleanupScope hRel

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {liveCtx : Functions.LiveLayout.Ctx}
    {after : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {continueScope : List Functions.Name}
    {lowerStmt : List Locals.Stmt} {nextLayout : List Functions.Name}
    (hLower :
      Functions.LiveLayout.Lower.Stmt.toLocals? returns liveCtx
          targetCtx.layout after .cont =
        some (lowerStmt, nextLayout))
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hContinue : sourceCtx.continueScope? = some continueScope)
    (hCleanupScope :
      ∀ {targetDepth},
        targetCtx.continueDepth? = some targetDepth →
          Functions.LiveLayout.SourceDirectBridge.LiveCleanupScopeRel
            targetCtx.layout targetDepth continueScope)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns .cont { stmts := lowerStmt } source target :=
  Functions.LiveLayout.SourceTarget.cont_liveStmtRunBridge_of_lower
    hLower hCtx hContinue hCleanupScope hRel

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {leaveScope : List Functions.Name}
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hLeave : sourceCtx.leaveScope? = some leaveScope)
    (hReturnScope :
      ∀ name, name ∈ returns → name ∈ leaveScope)
    (hNoDup : targetCtx.layout.Nodup)
    (hReturnsLen : returns.length = retc)
    (hHiddenReturns : hiddenReturns ≠ [])
    (hAccess :
      Functions.LiveLayout.NamesAccess.Accessible targetCtx.layout 0 returns)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns .leave
      { stmts :=
          Functions.Lower.pushReturns returns ++ [Locals.Stmt.leave] }
      source target :=
  Functions.LiveLayout.SourceTarget.leave_liveStmtRunBridge
    hCtx hLeave hReturnScope hNoDup hReturnsLen hHiddenReturns hAccess hRel

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {leaveScope : List Functions.Name}
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hLeave : sourceCtx.leaveScope? = some leaveScope)
    (hReturnScope :
      ∀ name, name ∈ returns → name ∈ leaveScope)
    (hNoDup : targetCtx.layout.Nodup)
    (hReturnsLen : returns.length = retc)
    (hLeaveFrame :
      Functions.SourceDirect.LeaveFrameAvailable sourceCtx hiddenReturns)
    (hAccess :
      Functions.LiveLayout.NamesAccess.Accessible targetCtx.layout 0 returns)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns .leave
      { stmts :=
          Functions.Lower.pushReturns returns ++ [Locals.Stmt.leave] }
      source target :=
  Functions.LiveLayout.SourceTarget.leave_liveStmtRunBridge_of_leaveFrame
    hCtx hLeave hReturnScope hNoDup hReturnsLen hLeaveFrame hAccess hRel

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {liveCtx : Functions.LiveLayout.Ctx}
    {after : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {leaveScope : List Functions.Name}
    {lowerStmt : List Locals.Stmt} {nextLayout : List Functions.Name}
    (hLower :
      Functions.LiveLayout.Lower.Stmt.toLocals? returns liveCtx
          targetCtx.layout after .leave =
        some (lowerStmt, nextLayout))
    (hAccessCheck :
      Functions.LiveLayout.StmtAccess.accessible? returns targetCtx.layout
          .leave =
        true)
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hLeave : sourceCtx.leaveScope? = some leaveScope)
    (hReturnScope :
      ∀ name, name ∈ returns → name ∈ leaveScope)
    (hNoDup : targetCtx.layout.Nodup)
    (hReturnsLen : returns.length = retc)
    (hHiddenReturns : hiddenReturns ≠ [])
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns .leave { stmts := lowerStmt } source target :=
  Functions.LiveLayout.SourceTarget.leave_liveStmtRunBridge_of_lower
    hLower hAccessCheck hCtx hLeave hReturnScope hNoDup hReturnsLen
    hHiddenReturns hRel

example {ctx : Locals.Ctx}
    {outer scope : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State}
    {target cleaned : Locals.RunState}
    (hRel :
      Functions.SourceDirect.StateRel ctx.layout hiddenReturns source target)
    (hLayout :
      Functions.SourceDirect.CleanupLayoutRel ctx.layout outer)
    (hSubset : ∀ {name : Functions.Name}, name ∈ outer → name ∈ scope)
    (hRun :
      Locals.Direct.Ctx.runCleanupTo ctx outer.length target =
        .ok cleaned) :
    Functions.SourceDirect.StateRel outer hiddenReturns
      (Locals.Source.State.restrictTo scope source) cleaned :=
  Functions.LiveLayout.SourceDirectBridge.stateRel_cleanupTo_layout_subset
    hRel hLayout hSubset hRun

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {body : Functions.Block} {lowerBody : Locals.Block}
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hBody :
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridge prim
        sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
        hiddenReturns body lowerBody source target)
    (hRegularLayout :
      ∀ {sourceInner : Functions.Source.State}
        {sourceCtxOut : Functions.Source.Ctx}
        {targetInner : Locals.RunState} {targetCtxOut : Locals.Ctx}
        {bodyTargetFuel : Nat},
        Functions.Source.Block.runOpen prim sourceProgram sourceCtx fuel body
            source =
          .ok (Functions.Source.Outcome.regular sourceInner, sourceCtxOut) →
        Locals.Direct.Block.runOpen targetProgram targetCtx bodyTargetFuel
            lowerBody target =
          .ok (Structured.Outcome.regular targetInner, targetCtxOut) →
        Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenResultRel retc
          returns hiddenReturns
          (Functions.Source.Outcome.regular sourceInner, sourceCtxOut)
          (Structured.Outcome.regular targetInner, targetCtxOut) →
        Functions.SourceDirect.CleanupLayoutRel targetCtxOut.layout
          targetCtx.layout) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns (.block body) { stmts := [Locals.Stmt.block lowerBody] }
      source target :=
  Functions.LiveLayout.block_liveStmtRunBridge_of_open_bridge
    hCtx hBody hRegularLayout

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {body : Functions.Block} {lowerBody : Locals.Block}
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hBody :
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayout
        prim sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
        hiddenReturns body lowerBody source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns (.block body) { stmts := [Locals.Stmt.block lowerBody] }
      source target :=
  Functions.LiveLayout.block_liveStmtRunBridge_of_open_bridge_with_layout
    hCtx hBody

example : True := by
  have _ :=
    @Functions.LiveLayout.blockScoped_from_open_bridge_with_layout
  have _ :=
    @Functions.LiveLayout.blockScoped_from_open_target_result_with_layout
  trivial

example : True := by
  have _ :=
    @Functions.LiveLayout.blockScoped_from_loop_open_bridge_with_layout
  trivial

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {liveCtx : Functions.LiveLayout.Ctx}
    {after nextLayout : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {body : Functions.Block} {lowerStmt : List Locals.Stmt}
    (hLower :
      Functions.LiveLayout.Lower.Stmt.toLocals? returns liveCtx
        targetCtx.layout after (.block body) =
        some (lowerStmt, nextLayout))
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hBody :
      ∀ {lowerBody bodyLayout},
        Functions.LiveLayout.Lower.Block.toLocals? returns
          (liveCtx.withProtectedLayout targetCtx.layout) targetCtx.layout
          (Functions.LiveLayout.Checked.scopedAfter targetCtx.layout after)
          body =
          some (lowerBody, bodyLayout) →
        Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayout
          prim sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
          hiddenReturns body lowerBody source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns (.block body) { stmts := lowerStmt } source target :=
  Functions.LiveLayout.block_liveStmtRunBridge_of_lower hLower hCtx hBody

example {prim : Functions.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {liveCtx : Functions.LiveLayout.Ctx}
    {after nextLayout : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source sourceAfterCond : Functions.Source.State}
    {target : Locals.RunState}
    {cond : Functions.Expr 1} {body : Functions.Block}
    {lowerStmt : List Locals.Stmt} {value : EvmYul.UInt256}
    (hLower :
      Functions.LiveLayout.Lower.Stmt.toLocals? returns liveCtx
        targetCtx.layout after (.if_ cond body) =
        some (lowerStmt, nextLayout))
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hNoDup : targetCtx.layout.Nodup)
    (hOwned : Locals.Source.Expr.SourceOwned cond)
    (hAccess :
      Locals.SourceLowering.Expr.Accessible targetCtx.layout 0 cond)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hEvalOne :
      Functions.Source.Expr.evalOne prim cond source =
        .ok (sourceAfterCond, value))
    (hBody :
      ∀ {lowerBody bodyLayout targetAfterCond},
        Functions.LiveLayout.Lower.Block.toLocals? returns
          (liveCtx.withProtectedLayout targetCtx.layout) targetCtx.layout
          (Functions.LiveLayout.Checked.scopedAfter targetCtx.layout after)
          body =
          some (lowerBody, bodyLayout) →
        Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns
          sourceAfterCond targetAfterCond →
        Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayout
          prim sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
          hiddenReturns body lowerBody sourceAfterCond targetAfterCond) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc (fuel + 1) sourceCtx targetCtx
      hiddenReturns (.if_ cond body) { stmts := lowerStmt } source target :=
  Functions.LiveLayout.if_liveStmtRunBridge_of_lower hPrim hLower hCtx hNoDup
    hOwned hAccess hRel hEvalOne hBody

example {prim : Functions.Source.PrimitiveSemantics}
    (hPrim : Locals.SourceLowering.PrimitiveSound prim)
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {liveCtx : Functions.LiveLayout.Ctx}
    {after nextLayout : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source sourceAfterScrutinee : Functions.Source.State}
    {target : Locals.RunState}
    {scrutinee : Functions.Expr 1}
    {cases : List (EvmYul.UInt256 × Functions.Block)}
    {defaultBody : Option Functions.Block}
    {lowerStmt : List Locals.Stmt} {value : EvmYul.UInt256}
    (hLower :
      Functions.LiveLayout.Lower.Stmt.toLocals? returns liveCtx
        targetCtx.layout after (.switch scrutinee cases defaultBody) =
        some (lowerStmt, nextLayout))
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hNoDup : targetCtx.layout.Nodup)
    (hOwned : Locals.Source.Expr.SourceOwned scrutinee)
    (hAccess :
      Locals.SourceLowering.Expr.Accessible targetCtx.layout 0 scrutinee)
    (hRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hEvalOne :
      Functions.Source.Expr.evalOne prim scrutinee source =
        .ok (sourceAfterScrutinee, value))
    (hBody :
      ∀ {value body lowerBody bodyLayout targetAfterPop},
        Functions.Source.Switch.select value cases defaultBody = some body →
        Functions.LiveLayout.Lower.Block.toLocals? returns
          (liveCtx.withProtectedLayout targetCtx.layout) targetCtx.layout
          (Functions.LiveLayout.Checked.scopedAfter targetCtx.layout after)
          body =
          some (lowerBody, bodyLayout) →
        Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns
          sourceAfterScrutinee targetAfterPop →
        Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayout
          prim sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
          hiddenReturns body lowerBody sourceAfterScrutinee targetAfterPop) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc (fuel + 1) sourceCtx targetCtx
      hiddenReturns (.switch scrutinee cases defaultBody) { stmts := lowerStmt }
      source target :=
  Functions.LiveLayout.switch_liveStmtRunBridge_of_lower hPrim hLower hCtx
    hNoDup hOwned hAccess hRel hEvalOne hBody

example : True := by
  have _ :=
    @Functions.LiveLayout.SourceDirectBridge.stateRel_restrictTo_layout_subset
  trivial

example : True := by
  have _ := @Functions.LiveLayout.runForLoop_condition_bridge_live
  trivial

example : True := by
  have _ := @Functions.LiveLayout.runForLoop_false_from_eval_live
  trivial

example : True := by
  have _ := @Functions.LiveLayout.runForLoop_from_exact_source_run_live
  trivial

example : True := by
  have _ :=
    @Functions.LiveLayout.runForLoop_from_exact_source_run_live_with_block_bridges
  trivial

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name}
    {retc sourceFuel initTargetFuel loopTargetFuel : Nat}
    {sourceCtx sourceInitCtx : Functions.Source.Ctx}
    {targetCtx targetInitCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source sourceAfterInit sourceLoop : Functions.Source.State}
    {target targetAfterInit targetLoop : Locals.RunState}
    {init post body : Functions.Block} {cond : Functions.Expr 1}
    {lowerInit lowerPost lowerBody : Locals.Block}
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hSourceInit :
      Functions.Source.Block.runOpen prim sourceProgram
          sourceCtx.withoutLoopControl sourceFuel init source =
        .ok (Functions.Source.Outcome.regular sourceAfterInit, sourceInitCtx))
    (hTargetInit :
      Locals.Direct.Block.runOpen targetProgram targetCtx.withoutLoopControl
          initTargetFuel lowerInit target =
        .ok (Structured.Outcome.regular targetAfterInit, targetInitCtx))
    (hLoop :
      Functions.Source.Stmt.runForLoop prim sourceProgram sourceInitCtx cond
          sourceInitCtx.withoutLoopControl post
          (sourceInitCtx.withLoopControl sourceInitCtx.scope
            sourceInitCtx.scope)
          body sourceFuel sourceAfterInit =
        .ok (Functions.Source.Outcome.regular sourceLoop))
    (hTargetLoop :
      Locals.Direct.Stmt.runForLoop targetProgram targetInitCtx cond
          targetInitCtx.withoutLoopControl lowerPost
          (targetInitCtx.withLoopControl targetInitCtx.layout.length)
          lowerBody loopTargetFuel targetAfterInit =
        .ok (Structured.Outcome.regular targetLoop))
    (hLoopRel :
      Functions.SourceDirect.StateRel targetInitCtx.layout hiddenReturns
        sourceLoop targetLoop)
    (hLayout :
      Functions.SourceDirect.CleanupLayoutRel targetInitCtx.layout
        targetCtx.layout) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc (sourceFuel + 1) sourceCtx
      targetCtx hiddenReturns (.for_ init cond post body)
      { stmts := [Locals.Stmt.for_ lowerInit cond lowerPost lowerBody] }
      source target :=
  Functions.LiveLayout.for_regular_liveStmtRunBridge_from_init_loop_regular
    hCtx hSourceInit hTargetInit hLoop hTargetLoop hLoopRel hLayout

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name}
    {retc sourceFuel initTargetFuel : Nat}
    {sourceCtx sourceInitCtx : Functions.Source.Ctx}
    {targetCtx targetInitCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {init post body : Functions.Block} {cond : Functions.Expr 1}
    {lowerInit lowerPost lowerBody : Locals.Block}
    {sourceInit : Functions.Source.Outcome} {targetInit : Locals.Outcome}
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hSourceInit :
      Functions.Source.Block.runOpen prim sourceProgram
          sourceCtx.withoutLoopControl sourceFuel init source =
        .ok (sourceInit, sourceInitCtx))
    (hTargetInit :
      Locals.Direct.Block.runOpen targetProgram targetCtx.withoutLoopControl
          initTargetFuel lowerInit target =
        .ok (targetInit, targetInitCtx))
    (hInitRel :
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenResultRel retc
        returns hiddenReturns (sourceInit, sourceInitCtx)
        (targetInit, targetInitCtx))
    (hPass :
      sourceInit.mode = .leave ∨
        ∃ kind, sourceInit.mode = .halt kind) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc (sourceFuel + 1) sourceCtx
      targetCtx hiddenReturns (.for_ init cond post body)
      { stmts := [Locals.Stmt.for_ lowerInit cond lowerPost lowerBody] }
      source target :=
  Functions.LiveLayout.for_leave_or_halt_liveStmtRunBridge_from_init_open
    hCtx hSourceInit hTargetInit hInitRel hPass

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name}
    {retc sourceFuel initTargetFuel loopTargetFuel : Nat}
    {sourceCtx sourceInitCtx : Functions.Source.Ctx}
    {targetCtx targetInitCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source sourceAfterInit : Functions.Source.State}
    {target targetAfterInit : Locals.RunState}
    {init post body : Functions.Block} {cond : Functions.Expr 1}
    {lowerInit lowerPost lowerBody : Locals.Block}
    {sourceLoop : Functions.Source.Outcome} {targetLoop : Locals.Outcome}
    (hCtx :
      Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtx
        targetCtx)
    (hSourceInit :
      Functions.Source.Block.runOpen prim sourceProgram
          sourceCtx.withoutLoopControl sourceFuel init source =
        .ok (Functions.Source.Outcome.regular sourceAfterInit, sourceInitCtx))
    (hTargetInit :
      Locals.Direct.Block.runOpen targetProgram targetCtx.withoutLoopControl
          initTargetFuel lowerInit target =
        .ok (Structured.Outcome.regular targetAfterInit, targetInitCtx))
    (hLoop :
      Functions.Source.Stmt.runForLoop prim sourceProgram sourceInitCtx cond
          sourceInitCtx.withoutLoopControl post
          (sourceInitCtx.withLoopControl sourceInitCtx.scope
            sourceInitCtx.scope)
          body sourceFuel sourceAfterInit =
        .ok sourceLoop)
    (hTargetLoop :
      Locals.Direct.Stmt.runForLoop targetProgram targetInitCtx cond
          targetInitCtx.withoutLoopControl lowerPost
          (targetInitCtx.withLoopControl targetInitCtx.layout.length)
          lowerBody loopTargetFuel targetAfterInit =
        .ok targetLoop)
    (hOutcomeRel :
      ∃ outcomeLayout,
        Functions.SourceDirect.StmtOutcomeRel returns outcomeLayout
          hiddenReturns sourceLoop targetLoop)
    (hPass :
      sourceLoop.mode = .leave ∨
        ∃ kind, sourceLoop.mode = .halt kind) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc (sourceFuel + 1) sourceCtx
      targetCtx hiddenReturns (.for_ init cond post body)
      { stmts := [Locals.Stmt.for_ lowerInit cond lowerPost lowerBody] }
      source target :=
  Functions.LiveLayout.for_leave_or_halt_liveStmtRunBridge_from_init_loop
    hCtx hSourceInit hTargetInit hLoop hTargetLoop hOutcomeRel hPass

example : True := by
  have _ :=
    @Functions.LiveLayout.for_liveStmtRunBridge_from_exact_source_run_of_lower
  trivial

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {body : Functions.Block} {lowerBody : Locals.Block}
    (hBody :
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayout
        prim sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
        hiddenReturns body lowerBody source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns body lowerBody source target :=
  Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayout.to_open
    hBody

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {stmt : Functions.Stmt} {targetBlock : Locals.Block}
    (hStmt :
      Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridgeWithLayout prim
        sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
        hiddenReturns stmt targetBlock source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns stmt targetBlock source target :=
  Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridgeWithLayout.to_stmt
    hStmt

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns baseLayout : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {body : Functions.Block} {lowerBody : Locals.Block}
    (hBody :
      Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayoutTo
        prim sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
        baseLayout hiddenReturns body lowerBody source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns body lowerBody source target :=
  Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayoutTo.to_open
    hBody

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns baseLayout : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {stmt : Functions.Stmt} {targetBlock : Locals.Block}
    (hStmt :
      Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridgeWithLayoutTo prim
        sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
        baseLayout hiddenReturns stmt targetBlock source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns stmt targetBlock source target :=
  Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridgeWithLayoutTo.to_stmt
    hStmt

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns loopLayout : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {body : Functions.Block} {lowerBody : Locals.Block}
    (hBody :
      Functions.LiveLayout.SourceDirectBridge.LiveLoopBlockOpenRunBridgeWithLayout
        prim sourceProgram targetProgram returns loopLayout retc fuel sourceCtx
        targetCtx hiddenReturns body lowerBody source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayout prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns body lowerBody source target :=
  Functions.LiveLayout.SourceDirectBridge.LiveLoopBlockOpenRunBridgeWithLayout.to_open_with_layout
    hBody

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns loopLayout : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {stmt : Functions.Stmt} {targetBlock : Locals.Block}
    (hStmt :
      Functions.LiveLayout.SourceDirectBridge.LiveLoopStmtRunBridgeWithLayout prim
        sourceProgram targetProgram returns loopLayout retc fuel sourceCtx
        targetCtx hiddenReturns stmt targetBlock source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridgeWithLayout prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      hiddenReturns stmt targetBlock source target :=
  Functions.LiveLayout.SourceDirectBridge.LiveLoopStmtRunBridgeWithLayout.to_stmt_with_layout
    hStmt

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns loopLayout baseLayout : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {body : Functions.Block} {lowerBody : Locals.Block}
    (hBody :
      Functions.LiveLayout.SourceDirectBridge.LiveLoopBlockOpenRunBridgeWithLayoutTo
        prim sourceProgram targetProgram returns loopLayout retc fuel sourceCtx
        targetCtx baseLayout hiddenReturns body lowerBody source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayoutTo
      prim sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      baseLayout hiddenReturns body lowerBody source target :=
  Functions.LiveLayout.SourceDirectBridge.LiveLoopBlockOpenRunBridgeWithLayoutTo.to_open_with_layout
    hBody

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns loopLayout baseLayout : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    {stmt : Functions.Stmt} {targetBlock : Locals.Block}
    (hStmt :
      Functions.LiveLayout.SourceDirectBridge.LiveLoopStmtRunBridgeWithLayoutTo
        prim sourceProgram targetProgram returns loopLayout retc fuel sourceCtx
        targetCtx baseLayout hiddenReturns stmt targetBlock source target) :
    Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridgeWithLayoutTo prim
      sourceProgram targetProgram returns retc fuel sourceCtx targetCtx
      baseLayout hiddenReturns stmt targetBlock source target :=
  Functions.LiveLayout.SourceDirectBridge.LiveLoopStmtRunBridgeWithLayoutTo.to_stmt_with_layout
    hStmt

example : True := by
  have _ :=
    @Functions.LiveLayout.SourceDirectBridge.LiveLoopStmtRunBridgeWithLayoutTo.target_result_of_source
  trivial

example : True := by
  have _ :=
    @Functions.LiveLayout.SourceDirectBridge.LiveLoopBlockOpenRunBridgeWithLayoutTo.target_result_of_source
  trivial

/- The broad live-layout helper catalogue stays inside its proof modules; this public audit keeps only the concrete regression examples below. -/

example {targets : List Functions.Name} {functionName : Functions.Name}
    {args : List (Functions.Expr 1)} :
    Functions.LiveLayout.NoInternalCall.Stmt.check?
        (.call targets functionName args) = false := by
  rfl

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {fuel : Nat}
    {sourceCtx stmtSourceCtx : Functions.Source.Ctx}
    {stmt : Functions.Stmt} {source : Functions.Source.State}
    {sourceOutcome : Functions.Source.Outcome}
    (hSourceStmt :
      Functions.Source.Stmt.run prim sourceProgram sourceCtx fuel stmt
          source =
        .ok (sourceOutcome, stmtSourceCtx))
    (hNonregular : sourceOutcome.mode ≠ .regular) :
    stmtSourceCtx = sourceCtx :=
  Functions.Source.Stmt.run_nonregular_ctx hSourceStmt hNonregular

example {program : Locals.Program} {protectedDepth : Nat}
    {returns live : List Functions.Name} {stmt : Functions.Stmt}
    {ctx : Locals.Ctx} {prep : List Locals.Stmt}
    {finalLayout : List Functions.Name}
    {hiddenReturns : List Structured.ReturnDest}
    {source : Functions.Source.State} {target : Locals.RunState}
    (hPrepare :
      Functions.LiveLayout.Prepare.forStmtAboveSuffix? protectedDepth returns
          ctx.layout live stmt =
        some (prep, finalLayout))
    (hRel :
      Functions.SourceDirect.StateRel ctx.layout hiddenReturns source target) :
    ∃ prepared prepareFuel,
      Locals.Direct.Block.runOpen program ctx prepareFuel { stmts := prep }
          target =
        .ok (Structured.Outcome.regular prepared,
          ctx.withLayout finalLayout) ∧
      Functions.SourceDirect.StateRel finalLayout hiddenReturns source
        prepared :=
  Functions.LiveLayout.Target.prepareForStmtAboveSuffix_runOpen_exists
    hPrepare hRel

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {protectedDepth retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {stmtLive liveLayout preparedLayout : List Functions.Name}
    {prep lowerStmt lowerRest : List Locals.Stmt}
    {source : Functions.Source.State} {target : Locals.RunState}
    (hLiveLayout :
      liveLayout =
        Functions.LiveLayout.Layout.trimDeadPrefix targetCtx.layout stmtLive)
    (hPrepare :
      Functions.LiveLayout.Prepare.forStmtAboveSuffix? protectedDepth returns
        liveLayout stmtLive stmt =
        some (prep, preparedLayout))
    (hStateRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hHead :
      ∀ {cleaned},
        Functions.SourceDirect.StateRel preparedLayout hiddenReturns source
          cleaned →
        Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
          sourceProgram targetProgram returns retc fuel sourceCtx
          (targetCtx.withLayout preparedLayout)
          hiddenReturns stmt { stmts := lowerStmt } source cleaned)
    (hTail :
      ∀ {sourceAfter : Functions.Source.State} {targetAfter : Locals.RunState}
        {sourceCtxAfter : Functions.Source.Ctx} {targetCtxAfter : Locals.Ctx},
        Functions.SourceDirect.StateRel targetCtxAfter.layout hiddenReturns
          sourceAfter targetAfter →
        Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtxAfter
          targetCtxAfter →
        Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridge prim
          sourceProgram targetProgram returns retc fuel sourceCtxAfter
          targetCtxAfter hiddenReturns { stmts := rest }
          { stmts := lowerRest } sourceAfter targetAfter) :
    Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridge prim
      sourceProgram targetProgram returns retc (fuel + 1) sourceCtx targetCtx
      hiddenReturns { stmts := stmt :: rest }
      { stmts :=
          Functions.LiveLayout.Lower.cleanupToLive targetCtx.layout stmtLive ::
            (prep ++ (lowerStmt ++ lowerRest)) } source target :=
  Functions.LiveLayout.SourceTarget.stmtList_cons_runBridge_of_lower_components
    hLiveLayout hPrepare hStateRel hHead hTail

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns : List Functions.Name} {retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {stmtLive : List Functions.Name}
    {lowerStmt lowerRest : List Locals.Stmt}
    {source : Functions.Source.State} {target : Locals.RunState}
    (hStateRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hEntryLayout :
      Functions.SourceDirect.CleanupLayoutRel
        (Functions.LiveLayout.Layout.trimDeadPrefix targetCtx.layout stmtLive)
        targetCtx.layout)
    (hHead :
      ∀ {cleaned},
        Functions.SourceDirect.StateRel
          (Functions.LiveLayout.Layout.trimDeadPrefix targetCtx.layout
            stmtLive)
          hiddenReturns source cleaned →
        Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridgeWithLayout prim
          sourceProgram targetProgram returns retc fuel sourceCtx
          (targetCtx.withLayout
            (Functions.LiveLayout.Layout.trimDeadPrefix targetCtx.layout
              stmtLive))
          hiddenReturns stmt { stmts := lowerStmt } source cleaned)
    (hTail :
      ∀ {sourceAfter : Functions.Source.State} {targetAfter : Locals.RunState}
        {sourceCtxAfter : Functions.Source.Ctx} {targetCtxAfter : Locals.Ctx},
        Functions.SourceDirect.StateRel targetCtxAfter.layout hiddenReturns
          sourceAfter targetAfter →
        Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtxAfter
          targetCtxAfter →
        Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayout
          prim sourceProgram targetProgram returns retc fuel sourceCtxAfter
          targetCtxAfter hiddenReturns { stmts := rest }
          { stmts := lowerRest } sourceAfter targetAfter) :
    Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayout
      prim sourceProgram targetProgram returns retc (fuel + 1) sourceCtx
      targetCtx hiddenReturns { stmts := stmt :: rest }
      { stmts :=
          Functions.LiveLayout.Lower.cleanupToLive targetCtx.layout stmtLive ::
            lowerStmt ++ lowerRest } source target :=
  Functions.LiveLayout.SourceTarget.stmtList_cons_runBridge_of_lower_components_with_layout
    hStateRel hEntryLayout hHead hTail

example {prim : Functions.Source.PrimitiveSemantics}
    {sourceProgram : Functions.Program} {targetProgram : Locals.Program}
    {returns baseLayout : List Functions.Name} {protectedDepth retc fuel : Nat}
    {sourceCtx : Functions.Source.Ctx} {targetCtx : Locals.Ctx}
    {hiddenReturns : List Structured.ReturnDest}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {stmtLive liveLayout preparedLayout : List Functions.Name}
    {prep lowerStmt lowerRest : List Locals.Stmt}
    {source : Functions.Source.State} {target : Locals.RunState}
    (hLiveLayout :
      liveLayout =
        Functions.LiveLayout.Layout.trimDeadPrefix targetCtx.layout stmtLive)
    (hPrepare :
      Functions.LiveLayout.Prepare.forStmtAboveSuffix? protectedDepth returns
        liveLayout stmtLive stmt =
        some (prep, preparedLayout))
    (hStateRel :
      Functions.SourceDirect.StateRel targetCtx.layout hiddenReturns source
        target)
    (hHead :
      ∀ {cleaned},
        Functions.SourceDirect.StateRel preparedLayout hiddenReturns source
          cleaned →
        Functions.LiveLayout.SourceDirectBridge.LiveStmtRunBridge prim
          sourceProgram targetProgram returns retc fuel sourceCtx
          (targetCtx.withLayout preparedLayout)
          hiddenReturns stmt { stmts := lowerStmt } source cleaned)
    (hTail :
      ∀ {sourceAfter : Functions.Source.State} {targetAfter : Locals.RunState}
        {sourceCtxAfter : Functions.Source.Ctx} {targetCtxAfter : Locals.Ctx},
        Functions.SourceDirect.StateRel targetCtxAfter.layout hiddenReturns
          sourceAfter targetAfter →
        Functions.LiveLayout.SourceDirectBridge.LiveCtxRel retc sourceCtxAfter
          targetCtxAfter →
        Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayoutTo
          prim sourceProgram targetProgram returns retc fuel sourceCtxAfter
          targetCtxAfter baseLayout hiddenReturns { stmts := rest }
          { stmts := lowerRest } sourceAfter targetAfter) :
    Functions.LiveLayout.SourceDirectBridge.LiveBlockOpenRunBridgeWithLayoutTo
      prim sourceProgram targetProgram returns retc (fuel + 1) sourceCtx
      targetCtx baseLayout hiddenReturns { stmts := stmt :: rest }
      { stmts :=
          Functions.LiveLayout.Lower.cleanupToLive targetCtx.layout stmtLive ::
            (prep ++ (lowerStmt ++ lowerRest)) } source target :=
  Functions.LiveLayout.SourceTarget.stmtList_cons_runBridge_of_lower_components_with_layout_to
    hLiveLayout hPrepare hStateRel hHead hTail

example :
    Functions.LiveLayout.FunDef.entryLive
      { name := "f"
        params := ["x"]
        returns := []
        body :=
          { stmts :=
              [ .let_ "dead" (.lit (EvmYul.UInt256.ofNat 0))
              , .expr (.prim .pop
                  (Locals.ExprSeq.cons (.var "x") .nil)) ] } } =
      ["x"] := by
  native_decide

example :
    Functions.LiveLayout.Layout.promoteName?
      ["v0", "v1", "v2", "v3", "v4", "v5", "v6", "v7", "v8",
        "v9", "v10", "v11", "v12", "v13", "v14", "v15", "v16",
        "deep"]
      "deep" = none := by
  native_decide

example :
    Functions.LiveLayout.Layout.promoteNameUnbounded?
      ["v0", "v1", "v2", "v3", "v4", "v5", "v6", "v7", "v8",
        "v9", "v10", "v11", "v12", "v13", "v14", "v15", "v16",
        "deep"]
      "deep" =
        some
          (["deep", "v0", "v1", "v2", "v3", "v4", "v5", "v6",
              "v7", "v8", "v9", "v10", "v11", "v12", "v13", "v14",
              "v15", "v16"],
            17) := by
  native_decide

example :
    (Locals.Ctx.promoteNameStackOnly?
      { Locals.Ctx.initial with
        layout :=
          ["v0", "v1", "v2", "v3", "v4", "v5", "v6", "v7", "v8",
            "v9", "v10", "v11", "v12", "v13", "v14", "v15", "v16",
            "deep"] }
      "deep").isNone = true := by
  native_decide

end LiveLayoutRegression

end ImportedYulBoundary
end LayerAudit
end EvmCompiler
