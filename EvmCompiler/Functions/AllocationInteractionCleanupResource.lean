import EvmCompiler.Functions.AllocationInteractionCleanup
import EvmCompiler.Functions.AllocationInteractionFrame

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionCleanupResource

open AllocationInteractionRelation
open AllocationInteractionFrame
open AllocationInteractionCleanup

namespace Plain

/-- Exact lexical cleanup changes only stack/control metadata. -/
theorem forward_allocator
    {contract : MemoryContract.Contract}
    {config : Config} {allocatorDepth : Nat}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Plan}
    {live : List Locals.Name} {targetDepth frameBase : Nat}
    {mode : ActivationMode}
    {source : SourceState} {target : TargetState}
    {cleanup : Structured.Code}
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan live frameBase mode source target)
    (hCleanup : localsCtx.cleanupTo? targetDepth = some cleanup)
    (hReady : AllocatorReady config allocatorDepth target) :
    ∃ targetFinal,
      Structured.InteractionSemantics.Code.openRun cleanup target =
          .done (.ok targetFinal) ∧
        AllocatorEffect config allocatorDepth target targetFinal := by
  obtain ⟨_hTargetDepth, hCleanupCode⟩ :=
    AllocationInteractionCleanup.Plain.cleanupTo?_shape hCleanup
  have hPopBound :
      localsCtx.layout.length - targetDepth ≤ target.evm.stack.length := by
    rw [hInvariant.stackLength]
    exact Nat.sub_le _ _
  obtain ⟨targetFinal, hRun, _hFinalStack, hShared, _hReturns⟩ :=
    Locals.InteractionPreservation.Code.openRun_replicate_pop
      (localsCtx.layout.length - targetDepth) hPopBound
  refine ⟨targetFinal, ?_, ?_⟩
  · simpa [hCleanupCode] using hRun
  · exact AllocatorEffect.of_machine_eq hReady
      (congrArg EvmYul.SharedState.toMachineState hShared)

end Plain

namespace Preserving

/-- Cleanup that preserves returned values changes only stack metadata. -/
theorem forward_zero_allocator
    {config : Config} {allocatorDepth : Nat}
    {ctx : Locals.Ctx} {preserve : Nat}
    {cleanup : Structured.Code}
    {values baseStack : List Assembly.Word}
    {target : Structured.RunState}
    (hCleanup : ctx.cleanupToPreserving? preserve 0 = some cleanup)
    (hValuesLength : values.length = preserve)
    (hBaseLength : baseStack.length = ctx.layout.length)
    (hStack : target.evm.stack = values ++ baseStack)
    (hReady : AllocatorReady config allocatorDepth target) :
    ∃ final,
      Structured.InteractionSemantics.Code.openRun cleanup target =
          .done (.ok final) ∧
        final.evm.stack = values ∧
        final.returns = target.returns ∧
        AllocatorEffect config allocatorDepth target final := by
  obtain ⟨final, hRun, hFinalStack, hShared, hReturns⟩ :=
    AllocationInteractionCleanup.Preserving.forward_zero
      hCleanup hValuesLength hBaseLength hStack
  refine ⟨final, hRun, hFinalStack, hReturns, ?_⟩
  exact AllocatorEffect.of_machine_eq hReady
    (congrArg EvmYul.SharedState.toMachineState hShared)

end Preserving

end AllocationInteractionCleanupResource
end Functions
end EvmCompiler
