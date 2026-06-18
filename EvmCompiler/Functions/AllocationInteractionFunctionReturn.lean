import EvmCompiler.Functions.AllocationInteractionCleanup
import EvmCompiler.Functions.AllocationInteractionExpressionRecursive
import EvmCompiler.Functions.AllocationInteractionLeave

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionFunctionReturn

open AllocationInteractionRelation

/-- Execute the semantic part of the ordinary compiler's regular function
return epilogue.  Scratch-resource preservation is an independent strengthening
owned by `AllocationInteractionFunctionReturnResource`. -/
theorem forward_regular
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Plan} {live returns : List Locals.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {lowered : Locals.ExprSeq returns.length}
    {returnCode cleanup : Structured.Code}
    {source : SourceState} {target : TargetState}
    {values : List Word}
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan live frameBase mode source target)
    (hReturnsLive : forall name, name ∈ returns -> name ∈ live)
    (hLookup :
      Functions.Source.Store.lookupMany returns source.vars = some values)
    (hLower :
      AllocationLowering.lowerReturnExprs lowerCtx lowerState returns =
        some lowered)
    (hCompile :
      Locals.ExprSeq.compileCode localsCtx 0 lowered = some returnCode)
    (hCleanup :
      localsCtx.cleanupToPreserving? returns.length 0 = some cleanup) :
    ∃ afterValues final,
      Structured.InteractionSemantics.Code.openRun returnCode target =
          .done (.ok afterValues) ∧
        Structured.InteractionSemantics.Code.openRun cleanup afterValues =
          .done (.ok final) ∧
        Structured.InteractionSemantics.Code.openRun
            (returnCode ++ cleanup) target =
          .done (.ok final) ∧
        LeaveStateRel contract returns source final ∧
        final.returns = target.returns := by
  have hSafe :=
    AllocationInteractionLeave.ReturnValues.safe contract
      hInvariant.defined hReturnsLive
  have hScoped :=
    AllocationInteractionCleanup.ReturnValues.returnExprsScoped hReturnsLive
  have hLowerSeq :=
    AllocationInteractionCleanup.ReturnValues.lowerExprSeq hLower
  have hReturnRel :=
    AllocationInteractionExpressionRecursive.forwardExprSeq
      hSafe hInvariant.compiler hScoped hLowerSeq hCompile hInvariant.state
  have hReturnEval :=
    AllocationInteractionLeave.ReturnValues.openEval hLookup
  rw [hReturnEval] at hReturnRel
  obtain ⟨targetDone, hReturnRun, hReturnDone⟩ :=
    Simulation.Interaction.Rel.done_left hReturnRel
  cases hReturnDone with
  | @ok sourceResult afterValues hReturnResult =>
      obtain
          ⟨final, hCleanupRun, hFinalStack, hCleanupShared,
            hCleanupReturns⟩ :=
        AllocationInteractionCleanup.Preserving.forward_zero
          (values := values.reverse) (baseStack := target.evm.stack)
          hCleanup
          (by simpa [List.length_reverse] using
            hReturnResult.valuesLength)
          (by simpa using hInvariant.stackLength)
          hReturnResult.stack
      have hAfterReturns : afterValues.returns = target.returns := by
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
          cases hReturnResult.state with
          | stack _ _ hState => exact hState.shared
          | scratch hState => exact hState.base.shared
        · rw [hCleanupShared]
          cases hReturnResult.state with
          | stack _ hNoWrap _ => exact hNoWrap
          | scratch hState => exact hState.activeNoWrap
      exact
        ⟨afterValues, final, hReturnRun, hCleanupRun, hCombined,
          hLeave, hCleanupReturns.trans hAfterReturns⟩

end AllocationInteractionFunctionReturn
end Functions
end EvmCompiler
