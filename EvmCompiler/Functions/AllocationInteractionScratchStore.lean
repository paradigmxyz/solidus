import EvmCompiler.Functions.AllocationInteractionRelation
import EvmCompiler.Functions.AllocationSupport
import EvmCompiler.Locals.InteractionPreservation

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionScratchStore

open AllocationInteractionRelation

/--
The compiler-generated frame-address sequence stores the current top value in
one reserved scratch slot and extends the live allocation relation.
-/
theorem assignTop
    {contract : MemoryContract.Contract} {plan : Plan}
    {beforeLive afterLive : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords slot : Nat}
    {source : SourceState} {target : TargetState}
    {name : Locals.Name} {value : Word} {rest : List Word}
    {op : Structured.BasicOp}
    {reservation : MemoryContract.ScratchReservation}
    (hRel :
      ScratchStateRel contract plan beforeLive (stackOffset + 1) frameBase
        frameDepth frameWords source target)
    (hStack : target.evm.stack = value :: rest)
    (hWF : plan.WellFormed)
    (hAfter :
      ∀ other, other ∈ afterLive →
        other = name ∨ other ∈ beforeLive)
    (hStackOrder :
      currentStackOrder plan afterLive =
        currentStackOrder plan beforeLive)
    (hLocation : plan.location? name = some (.scratch slot))
    (hAssignedBound : slot < frameWords)
    (hReservation : contract.scratch? = some reservation)
    (hRegion :
      reservation.containsRegion (scratchAddress frameBase slot) 1)
    (hOp :
      Locals.StackOp.dup? (stackOffset + frameDepth + 2) = some op) :
    ∃ targetFinal,
      Structured.InteractionSemantics.Code.openRun
          [ .op op,
            .push (AllocationSupport.slotOffset slot),
            .op .add,
            .op .mstore ] target =
        .done (.ok targetFinal) ∧
      ScratchStateRel contract plan afterLive stackOffset frameBase
        frameDepth frameWords (source.insert name value) targetFinal ∧
      targetFinal.evm.stack = rest := by
  let frameWord := EvmYul.UInt256.ofNat frameBase
  let offsetWord := AllocationSupport.slotOffset slot
  let address := EvmYul.UInt256.add offsetWord frameWord
  let afterDup := StateRel.pushTarget frameWord target
  let afterPush := StateRel.pushTargetBy 33 offsetWord afterDup
  let afterAdd := StateRel.contractTargetBy 1 address (value :: rest) afterPush
  let targetFinal := StateRel.mstoreTarget address value rest afterAdd
  have hAddress :
      address = EvmYul.UInt256.ofNat (scratchAddress frameBase slot) := by
    change
      EvmYul.UInt256.ofNat (32 * slot) +
          EvmYul.UInt256.ofNat frameBase =
        EvmYul.UInt256.ofNat
          (frameBase + MemoryContract.wordBytes * slot)
    rw [Assembly.UInt256_ofNat_add]
    simp [MemoryContract.wordBytes, Nat.add_comm]
  have hAfterDupRel :
      ScratchStateRel contract plan beforeLive (stackOffset + 2) frameBase
        frameDepth frameWords source afterDup :=
    by
      simpa [afterDup, StateRel.pushTarget] using
        hRel.push_target_by 1 frameWord
  have hAfterPushRel :
      ScratchStateRel contract plan beforeLive (stackOffset + 3) frameBase
        frameDepth frameWords source afterPush :=
    hAfterDupRel.push_target_by 33 offsetWord
  have hAfterPushStack :
      afterPush.evm.stack = offsetWord :: frameWord :: value :: rest := by
    simp [afterPush, afterDup, StateRel.pushTarget, StateRel.pushTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, hStack]
  have hAfterAddRel :
      ScratchStateRel contract plan beforeLive (stackOffset + 2) frameBase
        frameDepth frameWords source afterAdd :=
    hAfterPushRel.contract_target_by
      (value := address) hAfterPushStack 1
  have hAfterAddStack :
      afterAdd.evm.stack = address :: value :: rest := by
    rfl
  have hAfterAddStack' :
      afterAdd.evm.stack =
        EvmYul.UInt256.ofNat (scratchAddress frameBase slot) ::
          value :: rest := by
    simpa [hAddress] using hAfterAddStack
  have hFinalRel :
      ScratchStateRel contract plan afterLive stackOffset frameBase
        frameDepth frameWords (source.insert name value) targetFinal := by
    simpa [targetFinal, hAddress] using
      (hAfterAddRel.assign_scratch_live hWF hAfter hStackOrder
        hLocation hAssignedBound hReservation hRegion hAfterAddStack')
  have hFramePointer :
      target.evm.stack[stackOffset + frameDepth + 1]? = some frameWord := by
    simpa [frameWord,
      show stackOffset + 1 + frameDepth =
        stackOffset + frameDepth + 1 by omega] using hRel.framePointer
  have hDupRun :
      Structured.InteractionSemantics.Code.openRun [.op op] target =
        .done (.ok afterDup) := by
    simpa [afterDup, StateRel.pushTarget, StateRel.pushTargetBy] using
      (Locals.InteractionPreservation.Code.openRun_dup
        (by simpa [Nat.add_assoc] using hOp) hFramePointer)
  have hPushRun :
      Structured.InteractionSemantics.Code.openRun [.push offsetWord]
          afterDup =
        .done (.ok afterPush) := by
    simpa [afterPush, StateRel.pushTargetBy] using
      Locals.InteractionPreservation.Code.openRun_push offsetWord afterDup
  have hAddRun :
      Structured.InteractionSemantics.Code.openRun [.op .add] afterPush =
        .done (.ok afterAdd) := by
    simpa [afterAdd, StateRel.contractTargetBy] using
      Locals.InteractionPreservation.Code.openRun_add hAfterPushStack
  have hStoreRun :
      Structured.InteractionSemantics.Code.openRun [.op .mstore] afterAdd =
        .done (.ok targetFinal) := by
    simpa [targetFinal, StateRel.mstoreTarget] using
      Locals.InteractionPreservation.Code.openRun_mstore hAfterAddStack
  refine ⟨targetFinal, ?_, hFinalRel, ?_⟩
  · calc
      Structured.InteractionSemantics.Code.openRun
          [.op op, .push offsetWord, .op .add, .op .mstore] target =
        Simulation.Interaction.bind
          (Structured.InteractionSemantics.Code.openRun [.op op] target)
          (Structured.InteractionSemantics.Code.openRun
            [.push offsetWord, .op .add, .op .mstore]) := by
              rw [← Structured.InteractionSemantics.Code.openRun_append]
              rfl
      _ =
        Structured.InteractionSemantics.Code.openRun
          [.push offsetWord, .op .add, .op .mstore] afterDup := by
            rw [hDupRun]
            rfl
      _ =
        Simulation.Interaction.bind
          (Structured.InteractionSemantics.Code.openRun
            [.push offsetWord] afterDup)
          (Structured.InteractionSemantics.Code.openRun
            [.op .add, .op .mstore]) := by
              rw [← Structured.InteractionSemantics.Code.openRun_append]
              rfl
      _ =
        Structured.InteractionSemantics.Code.openRun
          [.op .add, .op .mstore] afterPush := by
            rw [hPushRun]
            rfl
      _ =
        Simulation.Interaction.bind
          (Structured.InteractionSemantics.Code.openRun [.op .add] afterPush)
          (Structured.InteractionSemantics.Code.openRun [.op .mstore]) := by
              rw [← Structured.InteractionSemantics.Code.openRun_append]
              rfl
      _ = Structured.InteractionSemantics.Code.openRun
          [.op .mstore] afterAdd := by
            rw [hAddRun]
            rfl
      _ = .done (.ok targetFinal) := hStoreRun
  · simp [targetFinal, afterAdd, afterPush, afterDup, hAddress,
      StateRel.mstoreTarget, StateRel.pushTarget, StateRel.pushTargetBy,
      StateRel.contractTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]

end AllocationInteractionScratchStore
end Functions
end EvmCompiler
