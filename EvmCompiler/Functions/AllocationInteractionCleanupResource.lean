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

end AllocationInteractionCleanupResource
end Functions
end EvmCompiler
