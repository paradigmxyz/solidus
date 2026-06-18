import EvmCompiler.Functions.AllocationInteractionCleanupResource
import EvmCompiler.Functions.AllocationInteractionLeave
import EvmCompiler.Functions.AllocationInteractionPrimitiveResource
import EvmCompiler.Functions.AllocationInteractionResource

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionLeaveResource

open AllocationInteractionRelation
open AllocationInteractionFrame
open AllocationInteractionResource
open AllocationInteractionCleanup

/-- Return-value emission and preserving cleanup retain activation resources. -/
theorem leave_of_lower_compile
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth : Nat} {config : Config}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Expressions.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns functionScope live : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Plan} {sourceFuel targetExtra frameBase : Nat}
    {mode : ActivationMode}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : SourceState} {target : TargetState}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hSourceScope : sourceCtx.leaveScope? = some functionScope)
    (hReturnsLive : ∀ name, name ∈ returns → name ∈ live)
    (hReturnsScope : ∀ name, name ∈ returns → name ∈ functionScope)
    (hTargetDepth : localsCtx.leaveDepth? = some 0)
    (hRetc : localsCtx.leaveRetc = returns.length)
    (hReturnFrame : target.returns ≠ [])
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState .leave =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan live frameBase mode source target)
    (hReady : AllocatorReady config allocatorDepth target) :
    Simulation.Interaction.Rel
      (OpenResultRel config allocatorDepth mode target)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel .leave source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (targetExtra + 4) { stmts := compiledStmts } target) := by
  obtain ⟨values, hLookup⟩ :=
    lookupMany_of_liveDefined hInvariant.defined hReturnsLive
  have hSafe :=
    AllocationInteractionLeave.ReturnValues.safe contract
      hInvariant.defined hReturnsLive
  have hScoped :=
    AllocationInteractionCleanup.ReturnValues.returnExprsScoped hReturnsLive
  obtain
      ⟨loweredReturns, returnCode, cleanup,
        hLowerReturns, hLowerSeq, hReturnCode, hCleanup,
        rfl, rfl, rfl, rfl⟩ :=
    AllocationInteractionCleanup.LeaveLeaf.compiler_shape
      hTargetDepth hRetc hLower hCompile
  have hReturnRel :=
    AllocationInteractionExpressionResource.forwardExprSeq
      (AllocationInteractionPrimitiveResource.canonicalPrimitiveForward
        contract)
      hConfig hSafe hInvariant.compiler hScoped hLowerSeq hReturnCode
      hInvariant.state hReady
  have hReturnEval := AllocationInteractionLeave.ReturnValues.openEval hLookup
  rw [hReturnEval] at hReturnRel
  obtain ⟨targetDone, hReturnRun, hReturnDone⟩ :=
    Simulation.Interaction.Rel.done_left hReturnRel
  cases hReturnDone with
  | @ok sourceResult targetAfterReturns hReturnResult =>
      obtain
          ⟨targetFinal, hCleanupRun, _hFinalStack,
            _hCleanupShared, hCleanupReturns, hCleanupEffect⟩ :=
        AllocationInteractionCleanupResource.Preserving.forward_zero_allocator
          (values := values.reverse) (baseStack := target.evm.stack)
          hCleanup
          (by simpa [List.length_reverse] using
            hReturnResult.1.valuesLength)
          (by simpa using hInvariant.stackLength)
          hReturnResult.1.stack hReturnResult.2.ready
      have hAfterReturns :
          targetAfterReturns.returns = target.returns := by
        have hAll :=
          Structured.InteractionSemantics.Code.openRun_returns
            returnCode target
        rw [hReturnRun] at hAll
        cases hAll with
        | done hDone => exact hDone
      have hFinalFrame : targetFinal.returns ≠ [] := by
        rw [hCleanupReturns, hAfterReturns]
        exact hReturnFrame
      have hSource :
          Functions.InteractionSemantics.Stmt.openRun
              sourceProgram sourceCtx sourceFuel .leave source =
            .done
              (.ok
                (Functions.Source.Effectful.Outcome.leave
                  (source.restrictTo functionScope), sourceCtx)) := by
        unfold Functions.InteractionSemantics.Stmt.openRun
          Functions.Source.Canonical.Stmt.run
        simp only [Functions.Source.Effectful.Control.Stmt.run]
        rw [hSourceScope]
        simp [Functions.InteractionSemantics.stateModel,
          Locals.InteractionSemantics.stateModel,
          Locals.Source.Effectful.Ordinary.stateModel,
          Locals.Source.Effectful.StateModel.restrictTo,
          Simulation.Interaction.pure]
        rfl
      have hTarget :
          Expressions.InteractionSemantics.Block.openRun
              targetProgram (targetExtra + 4)
              { stmts := [.code returnCode, .code cleanup, .leave] }
              target =
            .done
              (.ok (Structured.EffectSemantics.Outcome.leave targetFinal)) := by
        unfold Expressions.InteractionSemantics.Block.openRun
        simp only [Expressions.EffectSemantics.Control.Block.run,
          Expressions.EffectSemantics.Control.Stmt.run]
        unfold Structured.InteractionSemantics.Code.openRun at hReturnRun
        rw [hReturnRun]
        change
          Expressions.InteractionSemantics.Block.openRun
              targetProgram (targetExtra + 3)
              { stmts := [.code cleanup, .leave] } targetAfterReturns =
            .done
              (.ok (Structured.EffectSemantics.Outcome.leave targetFinal))
        exact
          Locals.InteractionPreservation.Stmt.TargetBlock.openRun_code_leave
            targetProgram targetExtra cleanup targetAfterReturns targetFinal
              hCleanupRun hFinalFrame
      rw [hSource, hTarget]
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact OutcomeEffect.of_activation
        (ActivationEffect.of_allocatorEffect
          (hReturnResult.2.trans hCleanupEffect))

end AllocationInteractionLeaveResource
end Functions
end EvmCompiler
