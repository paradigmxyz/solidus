import EvmCompiler.Functions.AllocationInteractionCall
import EvmCompiler.Functions.AllocationInteractionFramePreservation

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionCall

open AllocationInteractionRelation
open AllocationInteractionFrame

namespace CalleeEntry

/--
Argument evaluation after frame acquisition establishes the canonical
scratch-backed callee entry relation. Frame growth is transported separately
from expression preservation, keeping allocator resources orthogonal to the
source semantics.
-/
theorem scratch_of_arguments
    {contract : MemoryContract.Contract}
    {globalFrameWords depth : Nat} {config : Config}
    {callerPlan calleePlan : Locals.Allocation.Plan}
    {callerLive : List Locals.Name} {callerFrameBase : Nat}
    {callerMode : ActivationMode}
    {pending : List (Locals.Name × Nat)}
    {sourceAfterArgs : SourceState}
    {targetAfterAcquire targetAfterArgs : TargetState}
    {args : List Word} {initialStore : Locals.Source.Store}
    {callerStack : EvmYul.Stack Word} {retc : Nat}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hBudget : Budget config depth)
    (hArgs :
      ActivationExprResultRel contract callerPlan callerLive 1
        callerFrameBase args.length callerMode sourceAfterArgs
        targetAfterAcquire targetAfterArgs args)
    (hAcquireStack :
      targetAfterAcquire.evm.stack =
        EvmYul.UInt256.ofNat (baseAt config depth) :: callerStack)
    (hFrameActive :
      baseAt config depth + bytes config ≤
        targetAfterAcquire.evm.activeWords.toNat *
          MemoryContract.wordBytes)
    (hFrameAllocated :
      baseAt config depth + bytes config ≤
        targetAfterAcquire.evm.toMachineState.memory.size)
    (hGrowth : TargetGrowth targetAfterAcquire targetAfterArgs)
    (hLookup :
      Functions.Source.Store.lookupMany
          (pending.map Prod.fst) initialStore =
        some args) :
    ActivationCalleeEntryRel contract calleePlan [] pending
      (baseAt config depth) (.scratch 0 config.frameWords)
      (Functions.InteractionSemantics.stateModel.withSource sourceAfterArgs
        { shared := sourceAfterArgs.shared, vars := initialStore })
      (structuredState targetAfterArgs
        (args.reverse ++ [EvmYul.UInt256.ofNat (baseAt config depth)])
        callerStack retc) := by
  have hArgsLength : args.length = pending.length := by
    simpa using Functions.Source.Store.lookupMany_length hLookup
  have hFinalActive :
      baseAt config depth + bytes config ≤
        targetAfterArgs.evm.activeWords.toNat * MemoryContract.wordBytes :=
    hFrameActive.trans
      (Nat.mul_le_mul_right MemoryContract.wordBytes hGrowth.active)
  have hFinalAllocated :
      baseAt config depth + bytes config ≤
        targetAfterArgs.evm.toMachineState.memory.size :=
    hFrameAllocated.trans hGrowth.memory
  have hFrameNoWrap :=
    noWrap_of_budget_of_scratchFrameConfig? hConfig hBudget
  have hFrameHost :=
    hostAddressable_of_budget_of_scratchFrameConfig? hConfig hBudget
  obtain ⟨reservation, hReservation, hReserved⟩ :=
    reserved_of_budget_of_scratchFrameConfig? hConfig hBudget
  have hBase := hArgs.state.state
  apply ActivationCalleeEntryRel.scratch_empty
      (values := args)
      (suffix := [EvmYul.UInt256.ofNat (baseAt config depth)])
  · simpa [structuredState, Functions.InteractionSemantics.stateModel,
      Locals.InteractionSemantics.stateModel,
      Locals.Source.Effectful.Ordinary.stateModel,
      Structured.RunState.withEVM, Structured.RunState.pushReturn] using
        hBase.machine
  · simpa [structuredState, Functions.InteractionSemantics.stateModel,
      Locals.InteractionSemantics.stateModel,
      Locals.Source.Effectful.Ordinary.stateModel,
      Structured.RunState.withEVM, Structured.RunState.pushReturn] using
        hBase.world
  · rw [← hArgsLength]
    simp [structuredState, Structured.RunState.withEVM,
      Structured.RunState.pushReturn]
  · simpa [bytes] using hFinalActive
  · simpa [bytes] using hFinalAllocated
  · simpa [bytes] using hFrameNoWrap
  · simpa [bytes] using hFrameHost
  · simpa [structuredState, Structured.RunState.withEVM,
      Structured.RunState.pushReturn] using hArgs.state.activeNoWrap
  · exact ⟨reservation, hReservation, hReserved⟩
  · simpa [Functions.InteractionSemantics.stateModel,
      Locals.InteractionSemantics.stateModel,
      Locals.Source.Effectful.Ordinary.stateModel] using hLookup
  · simp [structuredState, Structured.RunState.withEVM,
      Structured.RunState.pushReturn]

end CalleeEntry

end AllocationInteractionCall
end Functions
end EvmCompiler
