import EvmCompiler.Functions.AllocationInteractionCallArgumentResources
import EvmCompiler.Functions.AllocationInteractionOrdinaryPrimitive

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionPrimitiveResource

open AllocationInteractionRelation
open AllocationInteractionFrame
open AllocationInteractionExpressionResource

namespace TargetEffect

theorem to_allocatorEffect
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth : Nat} {config : Config}
    {sourceFinal : EvmYul.SharedState .EVM}
    {before after : TargetState}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hReady : AllocatorReady config allocatorDepth before)
    (hEffect :
      AllocationInteractionOrdinaryPrimitive.TargetEffect contract
        sourceFinal before.evm.toSharedState after.evm.toSharedState) :
    AllocatorEffect config allocatorDepth before after := by
  obtain
    ⟨reservation, hReservation, hAllocator, hFirst, hLimit,
      _hWords, _hWF, _hHost, _hPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  have hCellRegion :
      reservation.containsRegion config.allocatorCell 1 := by
    rw [hAllocator]
    unfold MemoryContract.ScratchReservation.containsRegion
      MemoryContract.ScratchReservation.allocatorCell
      MemoryContract.ScratchReservation.endExclusive
      MemoryContract.ScratchReservation.bytes
    simp only [MemoryContract.wordBytes]
    constructor
    · exact Nat.le_refl _
    · omega
  have hCellLookup :
      after.evm.toMachineState.lookupMemory
          (EvmYul.UInt256.ofNat config.allocatorCell) =
        before.evm.toMachineState.lookupMemory
          (EvmYul.UInt256.ofNat config.allocatorCell) :=
    hEffect.scratchStable reservation hReservation config.allocatorCell
      hCellRegion hReady.cellAllocated hReady.cellActive
  have hFinalReady : AllocatorReady config allocatorDepth after :=
    hReady.of_lookup_growth hCellLookup hEffect.activeMono
      hEffect.memoryMono hEffect.activeNoWrap
  refine
    { ready := hFinalReady
      growth := ⟨hEffect.activeMono, hEffect.memoryMono⟩
      prefixStable := ?_ }
  intro protectedDepth _hDepth hBudget
  refine
    { growth := ⟨hEffect.activeMono, hEffect.memoryMono⟩
      lookup := ?_ }
  intro address hStart hEnd hReadMemory hReadActive
  have hReservationBase : reservation.base ≤ address := by
    rw [hFirst] at hStart
    unfold MemoryContract.ScratchReservation.frameBase at hStart
    omega
  have hReservationEnd :
      address + MemoryContract.wordBytes ≤ reservation.endExclusive := by
    rw [← hLimit]
    exact hEnd.trans
      ((Nat.le_add_right (baseAt config protectedDepth) (bytes config)).trans
        hBudget)
  exact hEffect.scratchStable reservation hReservation address
    ⟨hReservationBase, by simpa using hReservationEnd⟩
    hReadMemory hReadActive

end TargetEffect

theorem allocatorEffect_of_finishExternalCall
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth : Nat} {config : Config}
    {before after : TargetState} {returnData : ByteArray}
    {inputOffset inputSize outputOffset outputSize : Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hReady : AllocatorReady config allocatorDepth before)
    (hInput :
      Simulation.MemorySafety.WindowSafe contract
        inputOffset.toNat inputSize.toNat)
    (hOutput :
      Simulation.MemorySafety.WindowSafe contract
        outputOffset.toNat outputSize.toNat)
    (hMachine :
      after.evm.toMachineState =
        before.evm.toMachineState.finishExternalCall returnData
          inputOffset inputSize outputOffset outputSize) :
    AllocatorEffect config allocatorDepth before after := by
  obtain
    ⟨reservation, hReservation, hAllocator, hFirst, hLimit,
      _hWords, _hWF, _hHost, _hPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  have hGrowth :=
    Simulation.MemorySafety.finishExternalCall_growth
      before.evm.toMachineState hReady.activeNoWrap returnData
      inputOffset inputSize outputOffset outputSize hInput hOutput
  have hLookup :
      ∀ {query : Nat},
        reservation.containsRegion query 1 →
        query + MemoryContract.wordBytes ≤
          before.evm.toMachineState.memory.size →
        query + MemoryContract.wordBytes ≤
          before.evm.activeWords.toNat * MemoryContract.wordBytes →
        after.evm.toMachineState.lookupMemory
            (EvmYul.UInt256.ofNat query) =
          before.evm.toMachineState.lookupMemory
            (EvmYul.UInt256.ofNat query) := by
    intro query hReserved hReadMemory hReadActive
    simpa [hMachine] using
      (Simulation.MemorySafety.lookupMemory_finishExternalCall_of_reserved
        before.evm.toMachineState hReady.activeNoWrap returnData
        inputOffset inputSize outputOffset outputSize hInput hOutput query
        hReservation hReserved hReadMemory hReadActive)
  have hCellRegion :
      reservation.containsRegion config.allocatorCell 1 := by
    rw [hAllocator]
    unfold MemoryContract.ScratchReservation.containsRegion
      MemoryContract.ScratchReservation.allocatorCell
      MemoryContract.ScratchReservation.endExclusive
      MemoryContract.ScratchReservation.bytes
    simp only [MemoryContract.wordBytes]
    constructor
    · exact Nat.le_refl _
    · omega
  have hActive :
      before.evm.activeWords.toNat ≤ after.evm.activeWords.toNat := by
    simpa [hMachine] using hGrowth.active
  have hMemory :
      before.evm.toMachineState.memory.size ≤
        after.evm.toMachineState.memory.size := by
    simpa [hMachine] using hGrowth.memory
  have hNoWrap :
      after.evm.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
    simpa [hMachine] using hGrowth.activeNoWrap
  have hFinalReady : AllocatorReady config allocatorDepth after :=
    hReady.of_lookup_growth
      (hLookup hCellRegion hReady.cellAllocated hReady.cellActive)
      hActive hMemory hNoWrap
  refine
    { ready := hFinalReady
      growth := ⟨hActive, hMemory⟩
      prefixStable := ?_ }
  intro protectedDepth _hDepth hBudget
  refine
    { growth := ⟨hActive, hMemory⟩
      lookup := ?_ }
  intro address hStart hEnd hReadMemory hReadActive
  have hReservationBase : reservation.base ≤ address := by
    rw [hFirst] at hStart
    unfold MemoryContract.ScratchReservation.frameBase at hStart
    omega
  have hReservationEnd :
      address + MemoryContract.wordBytes ≤ reservation.endExclusive := by
    rw [← hLimit]
    exact hEnd.trans
      ((Nat.le_add_right (baseAt config protectedDepth) (bytes config)).trans
        hBudget)
  exact hLookup
    ⟨hReservationBase, by simpa using hReservationEnd⟩
    hReadMemory hReadActive

namespace ClosedSpec

/-- Closed ordinary primitive specs preserve allocator resources universally. -/
theorem resourceForward
    {contract : MemoryContract.Contract} {op : Structured.BasicOp}
    (spec : AllocationInteractionOrdinaryPrimitive.ClosedSpec contract op) :
    PrimitiveForward contract op where
  preserve := by
    intro globalFrameWords allocatorDepth config plan live stackOffset
      frameBase mode source initialTarget target values hConfig hLength hRel
      hStack hSafe hReady
    obtain ⟨step, hSourceStep⟩ := spec.sourceStep
    obtain ⟨sourceSharedFinal, outputs, hSourceEval⟩ :=
      spec.evalExists hLength
    have hPrimitiveStep :=
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?_toPrimOp
        hSourceStep
    have hExternal :=
      Assembly.InteractionSemantics.PrimOp.externalKind_none_of_continuingStep
        hPrimitiveStep
    have hOpenSafe :
        Simulation.MemorySafety.OpenPrimitiveMemorySafe
          contract op source.shared.toMachineState values := by
      simpa [AllocationInteractionPrimitive.PrimitiveSafe, hExternal] using
        hSafe
    obtain ⟨targetSharedFinal, hTargetEval, hEffect⟩ :=
      spec.simulate hLength hRel.shared hOpenSafe hRel.activeNoWrap hSourceEval
    obtain ⟨sourceEVMFinal, hSourceBasicStep, hSourceShared, hSourceStack⟩ :=
      Locals.Source.PrimitiveSemantics.structured_eval_step_exists
        (evm := Locals.InteractionSemantics.Primitive.isolated source values)
        (baseStack := []) hSourceEval rfl (by
          simp [Locals.InteractionSemantics.Primitive.isolated])
    obtain ⟨targetEVMFinal, hTargetBasicStep, hTargetShared, hTargetStack⟩ :=
      Locals.Source.PrimitiveSemantics.structured_eval_step_exists
        hTargetEval rfl hStack
    have hSourceStepRun :
        step.run (Locals.InteractionSemantics.Primitive.isolated source values) =
          .ok sourceEVMFinal := by
      rw [← Locals.Source.PrimitiveSemantics.sourceContinuingStep_basicOpStep
        hSourceStep]
      exact hSourceBasicStep
    have hTargetStepRun : step.run target.evm = .ok targetEVMFinal := by
      rw [← Locals.Source.PrimitiveSemantics.sourceContinuingStep_basicOpStep
        hSourceStep]
      exact hTargetBasicStep
    let sourceFinal := source.withShared sourceSharedFinal
    let targetFinal := target.withEVM targetEVMFinal
    have hSourceOpen :
        Locals.InteractionSemantics.Primitive.openEval op source values =
          .done (.ok (sourceFinal, outputs)) := by
      rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
        hLength spec.supportsOpen hSourceStep spec.notGas spec.notMsize]
      rw [hSourceStepRun]
      simp [Simulation.Interaction.map, Simulation.Interaction.pure,
        Locals.InteractionSemantics.Primitive.finish,
        sourceFinal, hSourceShared, hSourceStack]
    have hTargetOpen :
        Structured.InteractionSemantics.BasicInstr.openStep (.op op) target =
          .done (.ok targetFinal) := by
      unfold Structured.InteractionSemantics.BasicInstr.openStep
        Structured.InteractionSemantics.BasicInstr.openStepEVM
      change
        Simulation.Interaction.map target.withEVM
            (Assembly.InteractionSemantics.PrimOp.openStep
              op.toPrimOp target.evm) =
          .done (.ok targetFinal)
      rw [Assembly.InteractionSemantics.PrimOp.openStep_of_continuingStep
        hPrimitiveStep spec.notGas spec.notMsize]
      rw [hTargetStepRun]
      simp [Simulation.Interaction.map, Simulation.Interaction.pure,
        targetFinal]
    have hSharedEVM :
        SharedRel contract sourceSharedFinal targetEVMFinal.toSharedState := by
      rw [hTargetShared]
      exact hEffect.shared
    have hOldRel :
        ActivationStateRel contract plan live
          (stackOffset + values.reverse.length) frameBase mode source target := by
      simpa [List.length_reverse, hLength] using hRel
    have hScratchStable :
        ∀ name slot,
          name ∈ live →
          plan.location? name = some (.scratch slot) →
          targetFinal.evm.toMachineState.lookupMemory
              (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) =
            target.evm.toMachineState.lookupMemory
              (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) := by
      intro name slot hLive hLocation
      cases hOldRel with
      | stack liveStackOnly _activeNoWrap _state =>
          exact False.elim (liveStackOnly name slot hLive hLocation)
      | scratch state =>
          obtain ⟨reservation, hReservation, _hFrame⟩ := state.frameReserved
          change
            targetEVMFinal.toMachineState.lookupMemory
                (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) =
              target.evm.toMachineState.lookupMemory
                (EvmYul.UInt256.ofNat (scratchAddress frameBase slot))
          rw [hTargetShared]
          exact hEffect.scratchStable reservation hReservation
            (scratchAddress frameBase slot)
            (state.scratchAddress_reserved hLive hLocation hReservation)
            (state.scratchAddress_end_le_memory hLive hLocation)
            (state.scratchAddress_end_le_active hLive hLocation)
    have hMemoryMono :
        target.evm.toMachineState.memory.size ≤
          targetFinal.evm.toMachineState.memory.size := by
      change
        target.evm.toMachineState.memory.size ≤
          targetEVMFinal.toMachineState.memory.size
      rw [hTargetShared]
      exact hEffect.memoryMono
    have hActiveMono :
        target.evm.activeWords.toNat ≤ targetFinal.evm.activeWords.toNat := by
      change target.evm.activeWords.toNat ≤ targetEVMFinal.activeWords.toNat
      rw [hTargetShared]
      exact hEffect.activeMono
    have hFinalNoWrap :
        targetFinal.evm.activeWords.toNat * MemoryContract.wordBytes <
          EvmYul.UInt256.size := by
      change
        targetEVMFinal.activeWords.toNat * MemoryContract.wordBytes <
          EvmYul.UInt256.size
      rw [hTargetShared]
      exact hEffect.activeNoWrap
    have hRebased :=
      hOldRel.rebase_prefix
        (sourceFinal := sourceFinal) (targetFinal := targetFinal)
        (oldPrefix := values.reverse) (newPrefix := outputs.reverse)
        (baseStack := initialTarget.evm.stack)
        (by simpa [sourceFinal, targetFinal] using hSharedEVM)
        hStack (by simpa [targetFinal] using hTargetStack)
        hScratchStable (by rfl) hMemoryMono hActiveMono hFinalNoWrap
    have hOutputsLength :
        outputs.length = Expressions.Structured.BasicOp.outputs op :=
      Locals.Source.PrimitiveSemantics.structured_eval_length hSourceEval
    have hFinalState :
        ActivationStateRel contract plan live
          (stackOffset + Expressions.Structured.BasicOp.outputs op)
          frameBase mode sourceFinal targetFinal := by
      simpa [List.length_reverse, hOutputsLength] using hRebased
    have hAllocatorEffect :
        AllocatorEffect config allocatorDepth target targetFinal := by
      apply TargetEffect.to_allocatorEffect hConfig hReady
      simpa [targetFinal, hTargetShared] using hEffect
    rw [hSourceOpen, hTargetOpen]
    apply Simulation.Interaction.Rel.done
    apply Simulation.Interaction.ExceptRel.ok
    exact
      ⟨⟨hFinalState, hOutputsLength,
          by simpa [targetFinal] using hTargetStack⟩,
        hAllocatorEffect⟩

end ClosedSpec

namespace FallibleClosedSpec

/-- Fallible closed primitives preserve resources on success and exact errors. -/
theorem resourceForward
    {contract : MemoryContract.Contract} {op : Structured.BasicOp}
    (spec :
      AllocationInteractionOrdinaryPrimitive.FallibleClosedSpec contract op) :
    PrimitiveForward contract op where
  preserve := by
    intro globalFrameWords allocatorDepth config plan live stackOffset
      frameBase mode source initialTarget target values hConfig hLength hRel
      hStack hSafe hReady
    obtain ⟨step, hSourceStep⟩ := spec.sourceStep
    have hPrimitiveStep :=
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?_toPrimOp
        hSourceStep
    have hExternal :=
      Assembly.InteractionSemantics.PrimOp.externalKind_none_of_continuingStep
        hPrimitiveStep
    have hOpenSafe :
        Simulation.MemorySafety.OpenPrimitiveMemorySafe
          contract op source.shared.toMachineState values := by
      simpa [AllocationInteractionPrimitive.PrimitiveSafe, hExternal] using
        hSafe
    cases hSourceEval :
        Locals.Source.PrimitiveSemantics.structured.eval
          op source.shared values with
    | error error =>
        have hSourceStepRun :
            step.run
                (Locals.InteractionSemantics.Primitive.isolated source values) =
              .error error := by
          simpa [Locals.InteractionSemantics.Primitive.isolated,
            Assembly.PrimStep.isoState] using
            (Locals.Source.PrimitiveSemantics.structured_eval_error_run
              hLength hSourceStep hSourceEval)
        have hTargetStepRun : step.run target.evm = .error error :=
          spec.errorSuffix hLength hSourceStep hRel.shared hStack hSourceEval
        have hSourceOpen :
            Locals.InteractionSemantics.Primitive.openEval op source values =
              .done (.error error) := by
          rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
            hLength spec.supportsOpen hSourceStep spec.notGas spec.notMsize]
          rw [hSourceStepRun]
          simp [Simulation.Interaction.map]
        have hTargetOpen :
            Structured.InteractionSemantics.BasicInstr.openStep (.op op)
                target =
              .done (.error error) := by
          unfold Structured.InteractionSemantics.BasicInstr.openStep
            Structured.InteractionSemantics.BasicInstr.openStepEVM
          change
            Simulation.Interaction.map target.withEVM
                (Assembly.InteractionSemantics.PrimOp.openStep
                  op.toPrimOp target.evm) =
              .done (.error error)
          rw [Assembly.InteractionSemantics.PrimOp.openStep_of_continuingStep
            hPrimitiveStep spec.notGas spec.notMsize]
          rw [hTargetStepRun]
          simp [Simulation.Interaction.map]
        rw [hSourceOpen, hTargetOpen]
        exact Simulation.Interaction.Rel.done
          (Simulation.Interaction.ExceptRel.error rfl)
    | ok result =>
        rcases result with ⟨sourceSharedFinal, outputs⟩
        obtain ⟨targetSharedFinal, hTargetEval, hEffect⟩ :=
          spec.simulateSuccess hLength hRel.shared hOpenSafe hRel.activeNoWrap
            hSourceEval
        obtain
            ⟨sourceEVMFinal, hSourceBasicStep, hSourceShared, hSourceStack⟩ :=
          Locals.Source.PrimitiveSemantics.structured_eval_step_exists
            (evm := Locals.InteractionSemantics.Primitive.isolated source values)
            (baseStack := []) hSourceEval rfl (by
              simp [Locals.InteractionSemantics.Primitive.isolated])
        obtain
            ⟨targetEVMFinal, hTargetBasicStep, hTargetShared, hTargetStack⟩ :=
          Locals.Source.PrimitiveSemantics.structured_eval_step_exists
            hTargetEval rfl hStack
        have hSourceStepRun :
            step.run
                (Locals.InteractionSemantics.Primitive.isolated source values) =
              .ok sourceEVMFinal := by
          rw [← Locals.Source.PrimitiveSemantics.sourceContinuingStep_basicOpStep
            hSourceStep]
          exact hSourceBasicStep
        have hTargetStepRun : step.run target.evm = .ok targetEVMFinal := by
          rw [← Locals.Source.PrimitiveSemantics.sourceContinuingStep_basicOpStep
            hSourceStep]
          exact hTargetBasicStep
        let sourceFinal := source.withShared sourceSharedFinal
        let targetFinal := target.withEVM targetEVMFinal
        have hSourceOpen :
            Locals.InteractionSemantics.Primitive.openEval op source values =
              .done (.ok (sourceFinal, outputs)) := by
          rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
            hLength spec.supportsOpen hSourceStep spec.notGas spec.notMsize]
          rw [hSourceStepRun]
          simp [Simulation.Interaction.map, Simulation.Interaction.pure,
            Locals.InteractionSemantics.Primitive.finish,
            sourceFinal, hSourceShared, hSourceStack]
        have hTargetOpen :
            Structured.InteractionSemantics.BasicInstr.openStep (.op op)
                target =
              .done (.ok targetFinal) := by
          unfold Structured.InteractionSemantics.BasicInstr.openStep
            Structured.InteractionSemantics.BasicInstr.openStepEVM
          change
            Simulation.Interaction.map target.withEVM
                (Assembly.InteractionSemantics.PrimOp.openStep
                  op.toPrimOp target.evm) =
              .done (.ok targetFinal)
          rw [Assembly.InteractionSemantics.PrimOp.openStep_of_continuingStep
            hPrimitiveStep spec.notGas spec.notMsize]
          rw [hTargetStepRun]
          simp [Simulation.Interaction.map, Simulation.Interaction.pure,
            targetFinal]
        have hSharedEVM :
            SharedRel contract sourceSharedFinal targetEVMFinal.toSharedState := by
          rw [hTargetShared]
          exact hEffect.shared
        have hOldRel :
            ActivationStateRel contract plan live
              (stackOffset + values.reverse.length) frameBase mode source
              target := by
          simpa [List.length_reverse, hLength] using hRel
        have hScratchStable :
            ∀ name slot,
              name ∈ live →
              plan.location? name = some (.scratch slot) →
              targetFinal.evm.toMachineState.lookupMemory
                  (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) =
                target.evm.toMachineState.lookupMemory
                  (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) := by
          intro name slot hLive hLocation
          cases hOldRel with
          | stack liveStackOnly _activeNoWrap _state =>
              exact False.elim (liveStackOnly name slot hLive hLocation)
          | scratch state =>
              obtain ⟨reservation, hReservation, _hFrame⟩ :=
                state.frameReserved
              change
                targetEVMFinal.toMachineState.lookupMemory
                    (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) =
                  target.evm.toMachineState.lookupMemory
                    (EvmYul.UInt256.ofNat (scratchAddress frameBase slot))
              rw [hTargetShared]
              exact hEffect.scratchStable reservation hReservation
                (scratchAddress frameBase slot)
                (state.scratchAddress_reserved hLive hLocation hReservation)
                (state.scratchAddress_end_le_memory hLive hLocation)
                (state.scratchAddress_end_le_active hLive hLocation)
        have hMemoryMono :
            target.evm.toMachineState.memory.size ≤
              targetFinal.evm.toMachineState.memory.size := by
          change
            target.evm.toMachineState.memory.size ≤
              targetEVMFinal.toMachineState.memory.size
          rw [hTargetShared]
          exact hEffect.memoryMono
        have hActiveMono :
            target.evm.activeWords.toNat ≤
              targetFinal.evm.activeWords.toNat := by
          change target.evm.activeWords.toNat ≤ targetEVMFinal.activeWords.toNat
          rw [hTargetShared]
          exact hEffect.activeMono
        have hFinalNoWrap :
            targetFinal.evm.activeWords.toNat * MemoryContract.wordBytes <
              EvmYul.UInt256.size := by
          change
            targetEVMFinal.activeWords.toNat * MemoryContract.wordBytes <
              EvmYul.UInt256.size
          rw [hTargetShared]
          exact hEffect.activeNoWrap
        have hRebased :=
          hOldRel.rebase_prefix
            (sourceFinal := sourceFinal) (targetFinal := targetFinal)
            (oldPrefix := values.reverse) (newPrefix := outputs.reverse)
            (baseStack := initialTarget.evm.stack)
            (by simpa [sourceFinal, targetFinal] using hSharedEVM)
            hStack (by simpa [targetFinal] using hTargetStack)
            hScratchStable (by rfl) hMemoryMono hActiveMono hFinalNoWrap
        have hOutputsLength :
            outputs.length = Expressions.Structured.BasicOp.outputs op :=
          Locals.Source.PrimitiveSemantics.structured_eval_length hSourceEval
        have hFinalState :
            ActivationStateRel contract plan live
              (stackOffset + Expressions.Structured.BasicOp.outputs op)
              frameBase mode sourceFinal targetFinal := by
          simpa [List.length_reverse, hOutputsLength] using hRebased
        have hAllocatorEffect :
            AllocatorEffect config allocatorDepth target targetFinal := by
          apply TargetEffect.to_allocatorEffect hConfig hReady
          simpa [targetFinal, hTargetShared] using hEffect
        rw [hSourceOpen, hTargetOpen]
        apply Simulation.Interaction.Rel.done
        apply Simulation.Interaction.ExceptRel.ok
        exact
          ⟨⟨hFinalState, hOutputsLength,
              by simpa [targetFinal] using hTargetStack⟩,
            hAllocatorEffect⟩

end FallibleClosedSpec

namespace ResourceFamily

/-- `gas()` and `msize()` preserve allocator state for every shared answer. -/
theorem resourceForward
    {op : Structured.BasicOp} {kind : Simulation.ResourceQuery}
    (family : AllocationInteractionOrdinaryPrimitive.ResourceFamily op kind)
    (contract : MemoryContract.Contract) :
    PrimitiveForward contract op where
  preserve := by
    intro globalFrameWords allocatorDepth config plan live stackOffset
      frameBase mode source initialTarget target values _hConfig hLength hRel
      hStack _hSafe hReady
    have hValues : values = [] := by
      apply List.eq_nil_of_length_eq_zero
      cases family <;>
        simpa [Expressions.Structured.BasicOp.inputs] using hLength
    subst values
    cases family with
    | gas =>
        rw [Locals.InteractionSemantics.Primitive.openEval_gas,
          Structured.InteractionSemantics.BasicInstr.openStep_gas]
        apply Simulation.Interaction.Rel.request
        intro value
        apply Simulation.Interaction.Rel.done
        apply Simulation.Interaction.ExceptRel.ok
        refine ⟨⟨?_, rfl, ?_⟩, ?_⟩
        · simpa [Locals.InteractionSemantics.Primitive.finish,
            Locals.InteractionSemantics.Primitive.isolated,
            Assembly.InteractionSemantics.PrimOp.resourceStep,
            Simulation.Interaction.map, StateRel.pushTarget,
            StateRel.pushTargetBy] using hRel.push_target_by 1 value
        · simp [Assembly.InteractionSemantics.PrimOp.resourceStep,
            Locals.InteractionSemantics.Primitive.finish,
            Locals.InteractionSemantics.Primitive.isolated,
            StateRel.pushTarget, StateRel.pushTargetBy, hStack,
            EvmYul.Stack.push, EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
        · apply AllocatorEffect.of_machine_eq hReady
          rfl
    | msize =>
        rw [Locals.InteractionSemantics.Primitive.openEval_msize,
          Structured.InteractionSemantics.BasicInstr.openStep_msize]
        apply Simulation.Interaction.Rel.request
        intro value
        apply Simulation.Interaction.Rel.done
        apply Simulation.Interaction.ExceptRel.ok
        refine ⟨⟨?_, rfl, ?_⟩, ?_⟩
        · simpa [Locals.InteractionSemantics.Primitive.finish,
            Locals.InteractionSemantics.Primitive.isolated,
            Assembly.InteractionSemantics.PrimOp.resourceStep,
            Simulation.Interaction.map, StateRel.pushTarget,
            StateRel.pushTargetBy] using hRel.push_target_by 1 value
        · simp [Assembly.InteractionSemantics.PrimOp.resourceStep,
            Locals.InteractionSemantics.Primitive.finish,
            Locals.InteractionSemantics.Primitive.isolated,
            StateRel.pushTarget, StateRel.pushTargetBy, hStack,
            EvmYul.Stack.push, EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
        · apply AllocatorEffect.of_machine_eq hReady
          rfl

end ResourceFamily

/-- All CALL-family responses preserve allocator resources. -/
theorem call_resourceForward (contract : MemoryContract.Contract)
    (kind : Simulation.CallKind) :
    PrimitiveForward contract (AllocationInteractionPrimitive.callOp kind) where
  preserve := by
    intro globalFrameWords allocatorDepth config plan live stackOffset
      frameBase mode source initialTarget target values hConfig hLength hRel
      hStack hSafe hReady
    obtain ⟨parsed, hDecoded⟩ :=
      AllocationInteractionPrimitive.callOperands_of_length
        kind values.reverse (by
          simpa [List.length_reverse] using hLength)
    have hCallSafe :
        AllocationInteractionPrimitive.CallMemorySafe contract kind values := by
      simpa using hSafe
    obtain ⟨hInput, hOutput⟩ := hCallSafe parsed hDecoded
    have hRelPrefix :
        ActivationStateRel contract plan live
          (stackOffset + values.reverse.length) frameBase mode source target := by
      simpa [List.length_reverse, hLength] using hRel
    let sourceEVM :=
      Locals.InteractionSemantics.Primitive.isolated source values
    have hSourceOperands :
        kind.evmOperands? sourceEVM.stack = some ([], parsed) := by
      simpa [sourceEVM, Locals.InteractionSemantics.Primitive.isolated] using
        hDecoded
    have hTargetOperands :
        kind.evmOperands? target.evm.stack =
          some (initialTarget.evm.stack, parsed) := by
      rw [hStack]
      exact kind.evmOperands?_append_of_some initialTarget.evm.stack hDecoded
    have hInputRel :
        SharedRel contract sourceEVM.toSharedState target.evm.toSharedState := by
      simpa [sourceEVM,
        Locals.InteractionSemantics.Primitive.isolated] using hRel.shared
    have hAllowed :
        kind.allowedIn
            (Simulation.ExternalFrame.ofShared sourceEVM.toSharedState) parsed =
          kind.allowedIn
            (Simulation.ExternalFrame.ofShared target.evm.toSharedState)
              parsed := by
      have hEnv := hInputRel.executionEnv_eq
      cases kind <;>
        simp [Simulation.CallKind.allowedIn,
          Simulation.ExternalFrame.ofShared, hEnv]
    have hWorld := hInputRel.openWorld_eq
    have hRequest := hInputRel.callRequest_eq kind parsed hInput
    cases kind with
    | call =>
        simp only [AllocationInteractionPrimitive.callOp]
        rw [Locals.InteractionSemantics.Primitive.openEval_call]
        · change
            Simulation.Interaction.Rel _
              (Simulation.Interaction.map
                (Locals.InteractionSemantics.Primitive.finish source)
                (Assembly.InteractionSemantics.PrimOp.callStep
                  .call sourceEVM))
              (Simulation.Interaction.map target.withEVM
                (Assembly.InteractionSemantics.PrimOp.callStep
                  .call target.evm))
          unfold Assembly.InteractionSemantics.PrimOp.callStep
          rw [hSourceOperands, hTargetOperands]
          simp only
          rw [hAllowed, hWorld, hRequest]
          split
          · apply Simulation.Interaction.Rel.request
            intro response
            apply Simulation.Interaction.Rel.done
            apply Simulation.Interaction.ExceptRel.ok
            refine ⟨⟨?_, rfl, ?_⟩, ?_⟩
            · exact hRelPrefix.finishCall sourceEVM rfl parsed.callLocal
                response hStack hInput hOutput
            · simp [Locals.InteractionSemantics.Primitive.finish,
                Structured.RunState.withEVM,
                Assembly.InteractionSemantics.EVMState.finishCall,
                Assembly.InteractionSemantics.EVMState.installWorld,
                EvmYul.EVM.State.incrPC]
            · apply allocatorEffect_of_finishExternalCall
                (returnData := response.returnData)
                (inputOffset := parsed.inputOffset)
                (inputSize := parsed.inputSize)
                (outputOffset := parsed.outputOffset)
                (outputSize := parsed.outputSize)
                hConfig hReady hInput hOutput
              simp [Structured.RunState.withEVM,
                Assembly.InteractionSemantics.EVMState.finishCall,
                Assembly.InteractionSemantics.EVMState.installWorld,
                Simulation.CallLocal.finishMachine,
                Simulation.CallOperands.callLocal,
                EvmYul.EVM.State.incrPC]
          · exact Simulation.Interaction.Rel.done
              (Simulation.Interaction.ExceptRel.error rfl)
        · simpa [Simulation.CallKind.inputArity] using hLength
    | callcode =>
        simp only [AllocationInteractionPrimitive.callOp]
        rw [Locals.InteractionSemantics.Primitive.openEval_callcode]
        · change
            Simulation.Interaction.Rel _
              (Simulation.Interaction.map
                (Locals.InteractionSemantics.Primitive.finish source)
                (Assembly.InteractionSemantics.PrimOp.callStep
                  .callcode sourceEVM))
              (Simulation.Interaction.map target.withEVM
                (Assembly.InteractionSemantics.PrimOp.callStep
                  .callcode target.evm))
          unfold Assembly.InteractionSemantics.PrimOp.callStep
          rw [hSourceOperands, hTargetOperands]
          simp only
          rw [hAllowed, hWorld, hRequest]
          split
          · apply Simulation.Interaction.Rel.request
            intro response
            apply Simulation.Interaction.Rel.done
            apply Simulation.Interaction.ExceptRel.ok
            refine ⟨⟨?_, rfl, ?_⟩, ?_⟩
            · exact hRelPrefix.finishCall sourceEVM rfl parsed.callLocal
                response hStack hInput hOutput
            · simp [Locals.InteractionSemantics.Primitive.finish,
                Structured.RunState.withEVM,
                Assembly.InteractionSemantics.EVMState.finishCall,
                Assembly.InteractionSemantics.EVMState.installWorld,
                EvmYul.EVM.State.incrPC]
            · apply allocatorEffect_of_finishExternalCall
                (returnData := response.returnData)
                (inputOffset := parsed.inputOffset)
                (inputSize := parsed.inputSize)
                (outputOffset := parsed.outputOffset)
                (outputSize := parsed.outputSize)
                hConfig hReady hInput hOutput
              simp [Structured.RunState.withEVM,
                Assembly.InteractionSemantics.EVMState.finishCall,
                Assembly.InteractionSemantics.EVMState.installWorld,
                Simulation.CallLocal.finishMachine,
                Simulation.CallOperands.callLocal,
                EvmYul.EVM.State.incrPC]
          · exact Simulation.Interaction.Rel.done
              (Simulation.Interaction.ExceptRel.error rfl)
        · simpa [Simulation.CallKind.inputArity] using hLength
    | delegatecall =>
        simp only [AllocationInteractionPrimitive.callOp]
        rw [Locals.InteractionSemantics.Primitive.openEval_delegatecall]
        · change
            Simulation.Interaction.Rel _
              (Simulation.Interaction.map
                (Locals.InteractionSemantics.Primitive.finish source)
                (Assembly.InteractionSemantics.PrimOp.callStep
                  .delegatecall sourceEVM))
              (Simulation.Interaction.map target.withEVM
                (Assembly.InteractionSemantics.PrimOp.callStep
                  .delegatecall target.evm))
          unfold Assembly.InteractionSemantics.PrimOp.callStep
          rw [hSourceOperands, hTargetOperands]
          simp only
          rw [hAllowed, hWorld, hRequest]
          split
          · apply Simulation.Interaction.Rel.request
            intro response
            apply Simulation.Interaction.Rel.done
            apply Simulation.Interaction.ExceptRel.ok
            refine ⟨⟨?_, rfl, ?_⟩, ?_⟩
            · exact hRelPrefix.finishCall sourceEVM rfl parsed.callLocal
                response hStack hInput hOutput
            · simp [Locals.InteractionSemantics.Primitive.finish,
                Structured.RunState.withEVM,
                Assembly.InteractionSemantics.EVMState.finishCall,
                Assembly.InteractionSemantics.EVMState.installWorld,
                EvmYul.EVM.State.incrPC]
            · apply allocatorEffect_of_finishExternalCall
                (returnData := response.returnData)
                (inputOffset := parsed.inputOffset)
                (inputSize := parsed.inputSize)
                (outputOffset := parsed.outputOffset)
                (outputSize := parsed.outputSize)
                hConfig hReady hInput hOutput
              simp [Structured.RunState.withEVM,
                Assembly.InteractionSemantics.EVMState.finishCall,
                Assembly.InteractionSemantics.EVMState.installWorld,
                Simulation.CallLocal.finishMachine,
                Simulation.CallOperands.callLocal,
                EvmYul.EVM.State.incrPC]
          · exact Simulation.Interaction.Rel.done
              (Simulation.Interaction.ExceptRel.error rfl)
        · simpa [Simulation.CallKind.inputArity] using hLength
    | staticcall =>
        simp only [AllocationInteractionPrimitive.callOp]
        rw [Locals.InteractionSemantics.Primitive.openEval_staticcall]
        · change
            Simulation.Interaction.Rel _
              (Simulation.Interaction.map
                (Locals.InteractionSemantics.Primitive.finish source)
                (Assembly.InteractionSemantics.PrimOp.callStep
                  .staticcall sourceEVM))
              (Simulation.Interaction.map target.withEVM
                (Assembly.InteractionSemantics.PrimOp.callStep
                  .staticcall target.evm))
          unfold Assembly.InteractionSemantics.PrimOp.callStep
          rw [hSourceOperands, hTargetOperands]
          simp only
          rw [hAllowed, hWorld, hRequest]
          split
          · apply Simulation.Interaction.Rel.request
            intro response
            apply Simulation.Interaction.Rel.done
            apply Simulation.Interaction.ExceptRel.ok
            refine ⟨⟨?_, rfl, ?_⟩, ?_⟩
            · exact hRelPrefix.finishCall sourceEVM rfl parsed.callLocal
                response hStack hInput hOutput
            · simp [Locals.InteractionSemantics.Primitive.finish,
                Structured.RunState.withEVM,
                Assembly.InteractionSemantics.EVMState.finishCall,
                Assembly.InteractionSemantics.EVMState.installWorld,
                EvmYul.EVM.State.incrPC]
            · apply allocatorEffect_of_finishExternalCall
                (returnData := response.returnData)
                (inputOffset := parsed.inputOffset)
                (inputSize := parsed.inputSize)
                (outputOffset := parsed.outputOffset)
                (outputSize := parsed.outputSize)
                hConfig hReady hInput hOutput
              simp [Structured.RunState.withEVM,
                Assembly.InteractionSemantics.EVMState.finishCall,
                Assembly.InteractionSemantics.EVMState.installWorld,
                Simulation.CallLocal.finishMachine,
                Simulation.CallOperands.callLocal,
                EvmYul.EVM.State.incrPC]
          · exact Simulation.Interaction.Rel.done
              (Simulation.Interaction.ExceptRel.error rfl)
        · simpa [Simulation.CallKind.inputArity] using hLength

/-- All CREATE-family responses preserve allocator resources. -/
theorem create_resourceForward (contract : MemoryContract.Contract)
    (kind : Simulation.CreateKind) :
    PrimitiveForward contract
      (AllocationInteractionPrimitive.createOp kind) where
  preserve := by
    intro globalFrameWords allocatorDepth config plan live stackOffset
      frameBase mode source initialTarget target values hConfig hLength hRel
      hStack hSafe hReady
    obtain ⟨parsed, hDecoded⟩ :=
      AllocationInteractionPrimitive.createOperands_of_length
        kind values.reverse (by
          simpa [List.length_reverse] using hLength)
    have hCreateSafe :
        AllocationInteractionPrimitive.CreateMemorySafe
          contract kind values := by
      simpa using hSafe
    have hInput := hCreateSafe parsed hDecoded
    have hRelPrefix :
        ActivationStateRel contract plan live
          (stackOffset + values.reverse.length) frameBase mode source target := by
      simpa [List.length_reverse, hLength] using hRel
    let sourceEVM :=
      Locals.InteractionSemantics.Primitive.isolated source values
    have hSourceOperands :
        kind.evmOperands? sourceEVM.stack = some ([], parsed) := by
      simpa [sourceEVM, Locals.InteractionSemantics.Primitive.isolated] using
        hDecoded
    have hTargetOperands :
        kind.evmOperands? target.evm.stack =
          some (initialTarget.evm.stack, parsed) := by
      rw [hStack]
      exact kind.evmOperands?_append_of_some initialTarget.evm.stack hDecoded
    have hInputRel :
        SharedRel contract sourceEVM.toSharedState target.evm.toSharedState := by
      simpa [sourceEVM,
        Locals.InteractionSemantics.Primitive.isolated] using hRel.shared
    have hPermission :
        (Simulation.ExternalFrame.ofShared sourceEVM.toSharedState).permission =
          (Simulation.ExternalFrame.ofShared target.evm.toSharedState).permission := by
      have hEnv := hInputRel.executionEnv_eq
      simpa [Simulation.ExternalFrame.ofShared] using
        congrArg EvmYul.ExecutionEnv.perm hEnv
    have hWorld := hInputRel.openWorld_eq
    have hRequest := hInputRel.createRequest_eq kind parsed hInput
    cases kind with
    | create =>
        simp only [AllocationInteractionPrimitive.createOp]
        rw [Locals.InteractionSemantics.Primitive.openEval_create]
        · change
            Simulation.Interaction.Rel _
              (Simulation.Interaction.map
                (Locals.InteractionSemantics.Primitive.finish source)
                (Assembly.InteractionSemantics.PrimOp.createStep
                  .create sourceEVM))
              (Simulation.Interaction.map target.withEVM
                (Assembly.InteractionSemantics.PrimOp.createStep
                  .create target.evm))
          unfold Assembly.InteractionSemantics.PrimOp.createStep
          rw [hSourceOperands, hTargetOperands]
          simp only
          rw [hPermission, hWorld, hRequest]
          split
          · apply Simulation.Interaction.Rel.request
            intro response
            apply Simulation.Interaction.Rel.done
            apply Simulation.Interaction.ExceptRel.ok
            refine ⟨⟨?_, rfl, ?_⟩, ?_⟩
            · exact hRelPrefix.finishCreate sourceEVM rfl parsed.createLocal
                response hStack hInput
            · simp [Locals.InteractionSemantics.Primitive.finish,
                Structured.RunState.withEVM,
                Assembly.InteractionSemantics.EVMState.finishCreate,
                Assembly.InteractionSemantics.EVMState.installWorld,
                EvmYul.EVM.State.incrPC]
            · apply allocatorEffect_of_finishExternalCall
                (returnData := response.returnData)
                (inputOffset := parsed.initOffset)
                (inputSize := parsed.initSize)
                (outputOffset := EvmYul.UInt256.ofNat 0)
                (outputSize := EvmYul.UInt256.ofNat 0)
                hConfig hReady hInput
                (by
                  have hZeroToNat :
                      (EvmYul.UInt256.ofNat 0).toNat = 0 :=
                    EvmYul.UInt256.toNat_ofNat_of_lt (by
                      unfold EvmYul.UInt256.size
                      omega)
                  rw [hZeroToNat]
                  exact Simulation.MemorySafety.windowSafe_zero contract 0)
              simp [Structured.RunState.withEVM,
                Assembly.InteractionSemantics.EVMState.finishCreate,
                Assembly.InteractionSemantics.EVMState.installWorld,
                Simulation.CreateLocal.finishMachine,
                Simulation.CreateOperands.createLocal,
                EvmYul.EVM.State.incrPC]
          · exact Simulation.Interaction.Rel.done
              (Simulation.Interaction.ExceptRel.error rfl)
        · simpa [Simulation.CreateKind.inputArity] using hLength

    | create2 =>
        simp only [AllocationInteractionPrimitive.createOp]
        rw [Locals.InteractionSemantics.Primitive.openEval_create2]
        · change
            Simulation.Interaction.Rel _
              (Simulation.Interaction.map
                (Locals.InteractionSemantics.Primitive.finish source)
                (Assembly.InteractionSemantics.PrimOp.createStep
                  .create2 sourceEVM))
              (Simulation.Interaction.map target.withEVM
                (Assembly.InteractionSemantics.PrimOp.createStep
                  .create2 target.evm))
          unfold Assembly.InteractionSemantics.PrimOp.createStep
          rw [hSourceOperands, hTargetOperands]
          simp only
          rw [hPermission, hWorld, hRequest]
          split
          · apply Simulation.Interaction.Rel.request
            intro response
            apply Simulation.Interaction.Rel.done
            apply Simulation.Interaction.ExceptRel.ok
            refine ⟨⟨?_, rfl, ?_⟩, ?_⟩
            · exact hRelPrefix.finishCreate sourceEVM rfl parsed.createLocal
                response hStack hInput
            · simp [Locals.InteractionSemantics.Primitive.finish,
                Structured.RunState.withEVM,
                Assembly.InteractionSemantics.EVMState.finishCreate,
                Assembly.InteractionSemantics.EVMState.installWorld,
                EvmYul.EVM.State.incrPC]
            · apply allocatorEffect_of_finishExternalCall
                (returnData := response.returnData)
                (inputOffset := parsed.initOffset)
                (inputSize := parsed.initSize)
                (outputOffset := EvmYul.UInt256.ofNat 0)
                (outputSize := EvmYul.UInt256.ofNat 0)
                hConfig hReady hInput
                (by
                  have hZeroToNat :
                      (EvmYul.UInt256.ofNat 0).toNat = 0 :=
                    EvmYul.UInt256.toNat_ofNat_of_lt (by
                      unfold EvmYul.UInt256.size
                      omega)
                  rw [hZeroToNat]
                  exact Simulation.MemorySafety.windowSafe_zero contract 0)
              simp [Structured.RunState.withEVM,
                Assembly.InteractionSemantics.EVMState.finishCreate,
                Assembly.InteractionSemantics.EVMState.installWorld,
                Simulation.CreateLocal.finishMachine,
                Simulation.CreateOperands.createLocal,
                EvmYul.EVM.State.incrPC]
          · exact Simulation.Interaction.Rel.done
              (Simulation.Interaction.ExceptRel.error rfl)
        · simpa [Simulation.CreateKind.inputArity] using hLength

theorem shared_resourceForward
    {op : Structured.BasicOp}
    (family : AllocationInteractionOrdinaryPrimitive.SharedFamily op)
    (contract : MemoryContract.Contract) :
    PrimitiveForward contract op :=
  ClosedSpec.resourceForward (family.toClosedSpec contract)

theorem log_resourceForward
    {op : Structured.BasicOp}
    (family : AllocationInteractionOrdinaryPrimitive.MemoryFamily.LogFamily op)
    (contract : MemoryContract.Contract) :
    PrimitiveForward contract op :=
  ClosedSpec.resourceForward (family.closedSpec contract)

/-- Complete resource capability for every primitive admitted by open semantics. -/
theorem canonicalPrimitiveForward
    (contract : MemoryContract.Contract) (op : Structured.BasicOp)
    (hSupported :
      Locals.InteractionSemantics.Primitive.supportsOpen op = true) :
    PrimitiveForward contract op := by
  cases op <;>
    first
    | exact ResourceFamily.resourceForward
        AllocationInteractionOrdinaryPrimitive.ResourceFamily.gas contract
    | exact ResourceFamily.resourceForward
        AllocationInteractionOrdinaryPrimitive.ResourceFamily.msize contract
    | exact ClosedSpec.resourceForward
        (AllocationInteractionOrdinaryPrimitive.MemoryFamily.mloadClosedSpec
          contract)
    | exact ClosedSpec.resourceForward
        (AllocationInteractionOrdinaryPrimitive.MemoryFamily.mstoreClosedSpec
          contract)
    | exact ClosedSpec.resourceForward
        (AllocationInteractionOrdinaryPrimitive.MemoryFamily.mstore8ClosedSpec
          contract)
    | exact ClosedSpec.resourceForward
        (AllocationInteractionOrdinaryPrimitive.MemoryFamily.calldatacopySpec
          contract).toClosedSpec
    | exact ClosedSpec.resourceForward
        (AllocationInteractionOrdinaryPrimitive.MemoryFamily.codecopySpec
          contract).toClosedSpec
    | exact FallibleClosedSpec.resourceForward
        (AllocationInteractionOrdinaryPrimitive.MemoryFamily.returndatacopySpec
          contract)
    | exact ClosedSpec.resourceForward
        (AllocationInteractionOrdinaryPrimitive.MemoryFamily.extcodecopySpec
          contract).toClosedSpec
    | exact ClosedSpec.resourceForward
        (AllocationInteractionOrdinaryPrimitive.MemoryFamily.mcopySpec
          contract).toClosedSpec
    | exact ClosedSpec.resourceForward
        (AllocationInteractionOrdinaryPrimitive.MemoryFamily.keccak256ClosedSpec
          contract)
    | exact log_resourceForward
        .log0 contract
    | exact log_resourceForward
        .log1 contract
    | exact log_resourceForward
        .log2 contract
    | exact log_resourceForward
        .log3 contract
    | exact log_resourceForward
        .log4 contract
    | exact call_resourceForward contract .call
    | exact call_resourceForward contract .callcode
    | exact call_resourceForward contract .delegatecall
    | exact call_resourceForward contract .staticcall
    | exact create_resourceForward contract .create
    | exact create_resourceForward contract .create2
    | exact shared_resourceForward (.bin _ rfl) contract
    | exact shared_resourceForward (.un _ rfl) contract
    | exact shared_resourceForward (.tri _ rfl) contract
    | exact shared_resourceForward (.pop rfl) contract
    | exact shared_resourceForward (.executionEnv _ rfl) contract
    | exact shared_resourceForward (.unaryExecutionEnv _ rfl) contract
    | exact shared_resourceForward (.state _ rfl) contract
    | exact shared_resourceForward (.unaryState _ rfl) contract
    | exact shared_resourceForward (.binaryState _ rfl) contract
    | exact shared_resourceForward .returnDataSize contract
    | (simp [Locals.InteractionSemantics.Primitive.supportsOpen] at hSupported)

end AllocationInteractionPrimitiveResource
end Functions
end EvmCompiler
