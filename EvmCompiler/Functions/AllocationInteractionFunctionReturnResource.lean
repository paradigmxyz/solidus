import EvmCompiler.Functions.AllocationInteractionCleanupResource
import EvmCompiler.Functions.AllocationInteractionExpressionResource
import EvmCompiler.Functions.AllocationInteractionLeave
import EvmCompiler.Functions.AllocationInteractionPrimitiveResource

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionFunctionReturnResource

open AllocationInteractionFrame
open AllocationInteractionRelation

/--
Execute the regular-return epilogue selected by the function compiler. The
result exposes only source return values, shared state, and the activation
effect needed by the adjacent call owner.
-/
theorem forward_regular
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth : Nat} {config : Config}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Plan} {live returns : List Locals.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {lowered : Locals.ExprSeq returns.length}
    {returnCode cleanup : Structured.Code}
    {source : SourceState} {target : TargetState}
    {values : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan live frameBase mode source target)
    (hReturnsLive : ∀ name, name ∈ returns → name ∈ live)
    (hLookup :
      Functions.Source.Store.lookupMany returns source.vars = some values)
    (hLower :
      AllocationLowering.lowerReturnExprs lowerCtx lowerState returns =
        some lowered)
    (hCompile :
      Locals.ExprSeq.compileCode localsCtx 0 lowered = some returnCode)
    (hCleanup :
      localsCtx.cleanupToPreserving? returns.length 0 = some cleanup)
    (hReady : AllocatorReady config allocatorDepth target) :
    ∃ afterValues final,
      Structured.InteractionSemantics.Code.openRun returnCode target =
          .done (.ok afterValues) ∧
        Structured.InteractionSemantics.Code.openRun cleanup afterValues =
          .done (.ok final) ∧
        Structured.InteractionSemantics.Code.openRun
            (returnCode ++ cleanup) target =
          .done (.ok final) ∧
        LeaveStateRel contract returns source final ∧
        final.returns = target.returns ∧
        ActivationEffect config allocatorDepth mode target final := by
  have hSafe :=
    AllocationInteractionLeave.ReturnValues.safe contract
      hInvariant.defined hReturnsLive
  have hScoped :=
    AllocationInteractionCleanup.ReturnValues.returnExprsScoped hReturnsLive
  have hLowerSeq :=
    AllocationInteractionCleanup.ReturnValues.lowerExprSeq hLower
  have hReturnRel :=
    AllocationInteractionExpressionResource.forwardExprSeq
      (AllocationInteractionPrimitiveResource.canonicalPrimitiveForward
        contract)
      hConfig hSafe hInvariant.compiler hScoped hLowerSeq hCompile
      hInvariant.state hReady
  have hReturnEval :=
    AllocationInteractionLeave.ReturnValues.openEval hLookup
  rw [hReturnEval] at hReturnRel
  obtain ⟨targetDone, hReturnRun, hReturnDone⟩ :=
    Simulation.Interaction.Rel.done_left hReturnRel
  cases hReturnDone with
  | @ok sourceResult afterValues hReturnResult =>
      obtain
          ⟨final, hCleanupRun, hFinalStack, hCleanupShared,
            hCleanupReturns, hCleanupEffect⟩ :=
        AllocationInteractionCleanupResource.Preserving.forward_zero_allocator
          (values := values.reverse) (baseStack := target.evm.stack)
          hCleanup
          (by simpa [List.length_reverse] using
            hReturnResult.1.valuesLength)
          (by simpa using hInvariant.stackLength)
          hReturnResult.1.stack hReturnResult.2.ready
      have hAfterReturns :
          afterValues.returns = target.returns := by
        have hAll :=
          Structured.InteractionSemantics.Code.openRun_returns
            returnCode target
        rw [hReturnRun] at hAll
        cases hAll with
        | done hDone => exact hDone
      have hCombined :
          Structured.InteractionSemantics.Code.openRun
              (returnCode ++ cleanup) target =
            .done (.ok final) := by
        rw [Structured.InteractionSemantics.Code.openRun_append, hReturnRun]
        exact hCleanupRun
      have hLeave : LeaveStateRel contract returns source final := by
        refine
          { shared := ?_
            activeNoWrap := ?_
            values := ⟨values, hLookup, hFinalStack⟩ }
        · rw [hCleanupShared]
          cases hReturnResult.1.state with
          | stack _ _ hState => exact hState.shared
          | scratch hState => exact hState.base.shared
        · rw [hCleanupShared]
          cases hReturnResult.1.state with
          | stack _ hNoWrap _ => exact hNoWrap
          | scratch hState => exact hState.activeNoWrap
      refine ⟨afterValues, final, hReturnRun, hCleanupRun, hCombined,
        hLeave, ?_, ?_⟩
      · exact hCleanupReturns.trans hAfterReturns
      · exact ActivationEffect.of_allocatorEffect
          (hReturnResult.2.trans hCleanupEffect)

end AllocationInteractionFunctionReturnResource
end Functions
end EvmCompiler
