import EvmCompiler.Functions.AllocationInteractionCallTargets
import EvmCompiler.Functions.AllocationInteractionFrame
import EvmCompiler.Functions.AllocationInteractionFramePreservation

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionCallReturnResource

open AllocationInteractionCall
open AllocationInteractionFrame
open AllocationInteractionFrameExecution
open AllocationInteractionFramePreservation
open AllocationInteractionRelation

/--
Restore a suspended caller from a completed callee return and execute the
ordinary compiler's returned-value assignment code.
-/
theorem resume_and_writeback
    {contract : MemoryContract.Contract}
    {globalFrameWords callerDepth readyDepth : Nat}
    {config : Config}
    {callerLowerCtx : AllocationLowering.Ctx}
    {callerLowerState : AllocationLowering.State}
    {callerLocalsCtx : Locals.Ctx}
    {callerPlan : Plan} {callerLive : List Locals.Name}
    {callerFrameBase : Nat} {callerMode : ActivationMode}
    {sourceAfterArgs sourceReturned : SourceState}
    {callerTargetBase callFinal : TargetState}
    {returnValues : List Word} {targets : List Locals.Name}
    {returnStore : Locals.Source.Store} {stores : Structured.Code}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hCallerRel :
      ActivationStateRel contract callerPlan callerLive 0 callerFrameBase
        callerMode sourceAfterArgs callerTargetBase)
    (hCallerOwned :
      ActivationOwned config callerDepth callerFrameBase callerMode)
    (hCallerDepth : callerDepth ≤ readyDepth)
    (hBudget : Budget config callerDepth)
    (hMachine :
      Compiler.MemoryRelation.MachineRel contract
        sourceReturned.shared.toMachineState callFinal.evm.toMachineState)
    (hWorld :
      sourceReturned.shared.toState = callFinal.evm.toSharedState.toState)
    (hCallStack :
      callFinal.evm.stack = returnValues.reverse ++ callerTargetBase.evm.stack)
    (hCallEffect :
      BoundedEffect config readyDepth (callerDepth + 1)
        callerTargetBase callFinal)
    (hCallerContext :
      AllocationContext.ActivationExprContext callerLowerCtx callerLowerState
        callerLocalsCtx callerPlan callerLive callerMode)
    (hCallerWF : callerPlan.WellFormed)
    (hTargetsLive : ∀ target, target ∈ targets → target ∈ callerLive)
    (hTargetsNodup : targets.Nodup)
    (hAssign :
      Functions.Source.Store.assignMany targets returnValues
          sourceAfterArgs.vars =
        some returnStore)
    (hStores :
      AllocationLowering.lowerCallTargetsCode?
          callerLowerCtx callerLowerState targets.reverse targets.length =
        some stores) :
    ∃ targetFinal,
      Structured.InteractionSemantics.Code.openRun stores callFinal =
          .done (.ok targetFinal) ∧
        ActivationStateRel contract callerPlan callerLive 0 callerFrameBase
          callerMode
          { shared := sourceReturned.shared, vars := returnStore }
          targetFinal ∧
        targetFinal.evm.stack.length = callerTargetBase.evm.stack.length ∧
        BoundedEffect config readyDepth
          (CallTargets.protectedBound callerDepth callerMode)
          callerTargetBase targetFinal := by
  let callerReturned : SourceState :=
    { shared := sourceReturned.shared, vars := sourceAfterArgs.vars }
  have hProtected :
      ProtectedPrefix config callerDepth callerTargetBase callFinal :=
    hCallEffect.prefixStable (by omega) hBudget
  have hResumed :
      ActivationStateRel contract callerPlan callerLive
        returnValues.reverse.length callerFrameBase callerMode
        callerReturned callFinal := by
    apply resume_after_call hCallerRel hCallerOwned
    · rfl
    · exact hMachine
    · exact hWorld
    · exact hCallStack
    · exact hCallEffect.ready.activeNoWrap
    · exact hProtected
  have hAssignReverse :
      Functions.Source.Store.assignMany targets.reverse returnValues.reverse
          callerReturned.vars =
        some returnStore := by
    change
      Functions.Source.Store.assignMany targets.reverse returnValues.reverse
          sourceAfterArgs.vars =
        some returnStore
    exact Functions.Source.Store.assignMany_reverse_of_run
      hAssign hTargetsNodup
  have hStores' :
      AllocationLowering.lowerCallTargetsCode?
          callerLowerCtx callerLowerState targets.reverse
            returnValues.reverse.length =
        some stores := by
    simpa [Functions.Source.Store.assignMany_length hAssign] using hStores
  obtain ⟨targetFinal, hStoresRun, hFinalRel, hFinalStack, hWriteEffect⟩ :=
    CallTargets.forward_bounded hConfig hCallerContext hCallerWF
      (fun target hTarget => hTargetsLive target (by simpa using hTarget))
      hAssignReverse hStores' hResumed hCallStack hCallerOwned hCallerDepth
      hCallEffect.ready
  have hBound :
      CallTargets.protectedBound callerDepth callerMode ≤ callerDepth + 1 := by
    cases callerMode <;> simp [CallTargets.protectedBound]
  have hBeforeWrite := BoundedEffect.weaken hBound hCallEffect
  have hEffect := hBeforeWrite.trans hWriteEffect
  refine ⟨targetFinal, hStoresRun, ?_, hFinalStack, hEffect⟩
  simpa [callerReturned, Locals.Source.State.withVars] using hFinalRel

/-- Package a completed call that did not acquire a nested scratch frame. -/
theorem complete_without_release
    {config : Config} {allocatorDepth frameBase : Nat}
    {mode : ActivationMode} {before after : TargetState}
    (hEffect :
      BoundedEffect config allocatorDepth
        (CallTargets.protectedBound allocatorDepth mode) before after) :
    ActivationEffect config allocatorDepth mode before after := by
  apply ActivationEffect.of_boundedEffect
  simpa [CallTargets.protectedBound] using hEffect

/-- Release one nested scratch frame and restore the caller resource mode. -/
theorem complete_with_release
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase : Nat}
    {config : Config} {plan : Plan} {live : List Locals.Name}
    {mode : ActivationMode} {source : SourceState}
    {before afterWrite : TargetState}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hBudget : Budget config allocatorDepth)
    (hOwned : ActivationOwned config allocatorDepth frameBase mode)
    (hRel :
      ActivationStateRel contract plan live 0 frameBase mode source afterWrite)
    (hEffect :
      BoundedEffect config (allocatorDepth + 1)
        (CallTargets.protectedBound allocatorDepth mode) before afterWrite) :
    let final := scratchFrameReleaseTarget config allocatorDepth afterWrite
    Structured.InteractionSemantics.Code.openRun
        (AllocationSupport.scratchFrameReleaseCode config) afterWrite =
      .done (.ok final) ∧
      ActivationStateRel contract plan live 0 frameBase mode source final ∧
      ActivationEffect config allocatorDepth mode before final := by
  dsimp only
  obtain ⟨hRelease, hFinalRel⟩ :=
    scratchFrameRelease_activation_correct hConfig hBudget hEffect.ready
      hOwned hRel
  have hBound :
      CallTargets.protectedBound allocatorDepth mode ≤ allocatorDepth + 1 := by
    cases mode <;> simp [CallTargets.protectedBound]
  have hReleaseBounded := BoundedEffect.weaken hBound hRelease.effect
  have hCombined := hEffect.trans hReleaseBounded
  refine ⟨hRelease.execution, hFinalRel, ?_⟩
  exact ActivationEffect.of_boundedEffect
    (by simpa [CallTargets.protectedBound] using hCombined)

end AllocationInteractionCallReturnResource
end Functions
end EvmCompiler
