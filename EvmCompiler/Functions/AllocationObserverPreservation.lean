import EvmCompiler.Functions.AllocationLowering
import EvmCompiler.Functions.AllocationObserverRelation

namespace EvmCompiler
namespace Functions
namespace AllocationObserverPreservation

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word

open AllocationObserverRelation

private theorem take_succ_getLast!_of_getElem?_eq_some
    {α : Type} [Inhabited α] {values : List α} {index : Nat} {value : α}
    (hGet : values[index]? = some value) :
    (values.take (index + 1)).getLast! = value := by
  induction index generalizing values with
  | zero =>
      cases values with
      | nil =>
          simp at hGet
      | cons head tail =>
          simp at hGet
          subst head
          rfl
  | succ index ih =>
      cases values with
      | nil =>
          simp at hGet
      | cons head tail =>
          simp only [List.getElem?_cons_succ] at hGet
          have hTail := ih hGet
          have hIndex : index < tail.length :=
            List.getElem?_eq_some_iff.mp hGet |>.1
          have hLength :
              (tail.take (index + 1)).length = index + 1 := by
            simp [List.length_take,
              Nat.min_eq_left (Nat.succ_le_iff.mpr hIndex)]
          cases hTake : tail.take (index + 1) with
          | nil =>
              rw [hTake] at hLength
              simp at hLength
          | cons next rest =>
              rw [hTake] at hTail
              simpa [List.take_succ_cons, hTake] using hTail

private theorem dup?_continuingStep
    {depth : Nat} {op : Structured.BasicOp}
    (hOp : Locals.StackOp.dup? depth = some op) :
    op.toPrimOp.continuingStep? = some (.dup depth) := by
  match depth with
  | 0 => simp [Locals.StackOp.dup?] at hOp
  | 1 => simp [Locals.StackOp.dup?] at hOp; cases hOp; rfl
  | 2 => simp [Locals.StackOp.dup?] at hOp; cases hOp; rfl
  | 3 => simp [Locals.StackOp.dup?] at hOp; cases hOp; rfl
  | 4 => simp [Locals.StackOp.dup?] at hOp; cases hOp; rfl
  | 5 => simp [Locals.StackOp.dup?] at hOp; cases hOp; rfl
  | 6 => simp [Locals.StackOp.dup?] at hOp; cases hOp; rfl
  | 7 => simp [Locals.StackOp.dup?] at hOp; cases hOp; rfl
  | 8 => simp [Locals.StackOp.dup?] at hOp; cases hOp; rfl
  | 9 => simp [Locals.StackOp.dup?] at hOp; cases hOp; rfl
  | 10 => simp [Locals.StackOp.dup?] at hOp; cases hOp; rfl
  | 11 => simp [Locals.StackOp.dup?] at hOp; cases hOp; rfl
  | 12 => simp [Locals.StackOp.dup?] at hOp; cases hOp; rfl
  | 13 => simp [Locals.StackOp.dup?] at hOp; cases hOp; rfl
  | 14 => simp [Locals.StackOp.dup?] at hOp; cases hOp; rfl
  | 15 => simp [Locals.StackOp.dup?] at hOp; cases hOp; rfl
  | 16 => simp [Locals.StackOp.dup?] at hOp; cases hOp; rfl
  | depth + 17 => simp [Locals.StackOp.dup?] at hOp

namespace ObserverCode

theorem run_push {transcript : Trace}
    (value : Word)
    (target : Structured.ObserverSemantics.State transcript) :
    Structured.ObserverSemantics.Code.run
        [.push value] target =
      .ok
        (AllocationObserverRelation.StateRel.pushTargetBy
          33 value target) := by
  unfold Structured.ObserverSemantics.Code.run
    Structured.EffectSemantics.Code.run
  simp only [Structured.BasicInstr.step, Assembly.Target.stepInstr,
    Structured.ObserverSemantics.stateModel_evm,
    Structured.ObserverSemantics.stateModel_withEVM,
    Structured.ObserverSemantics.handler, Bind.bind, Except.bind]
  simp [Structured.EffectSemantics.Code.run, EvmYul.Stack.push,
    Simulation.ResourceReplay.State.withSource,
    AllocationObserverRelation.StateRel.pushTargetBy]

theorem run_dup {transcript : Trace}
    {target : Structured.ObserverSemantics.State transcript}
    {index : Nat} {value : Word} {op : Structured.BasicOp}
    (hOp : Locals.StackOp.dup? (index + 1) = some op)
    (hGet : target.source.evm.stack[index]? = some value) :
    Structured.ObserverSemantics.Code.run [.op op] target =
      .ok
        (AllocationObserverRelation.StateRel.pushTarget
          value target) := by
  have hIndex : index < target.source.evm.stack.length :=
    List.getElem?_eq_some_iff.mp hGet |>.1
  have hDepth : index + 1 ≤ target.source.evm.stack.length := by
    omega
  have hLast :
      (target.source.evm.stack.take (index + 1)).getLast! = value :=
    take_succ_getLast!_of_getElem?_eq_some hGet
  have hStep := dup?_continuingStep hOp
  have hObserver :
      Structured.ObserverSemantics.basicOpObserver? op = none := by
    cases op <;>
      simp [Structured.ObserverSemantics.basicOpObserver?,
        Structured.BasicOp.toPrimOp,
        Assembly.ResourceObserver.ofPrimOp?,
        Assembly.PrimOp.continuingStep?] at hStep ⊢
  unfold Structured.ObserverSemantics.Code.run
    Structured.EffectSemantics.Code.run
  simp only [Structured.BasicInstr.step, Structured.BasicOp.step,
    Assembly.Target.stepInstr,
    Structured.ObserverSemantics.stateModel_evm]
  rw [Assembly.PrimOp.step_eq_continuingStep_run hStep]
  unfold Assembly.PrimStep.run EvmYul.dup
  have hTakeLength :
      (target.source.evm.stack.take (index + 1)).length =
        index + 1 := by
    simp [List.length_take, Nat.min_eq_left hDepth]
  simp only [hTakeLength, ↓reduceIte]
  rw [hLast]
  simp [Structured.ObserverSemantics.stateModel_withEVM,
    Structured.ObserverSemantics.handler, hObserver,
    Structured.EffectSemantics.Code.run,
    AllocationObserverRelation.StateRel.pushTarget,
    AllocationObserverRelation.StateRel.pushTargetBy,
    Simulation.ResourceReplay.State.withSource,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem run_add {transcript : Trace}
    {target : Structured.ObserverSemantics.State transcript}
    {right left : Word} {rest : List Word}
    (hStack : target.source.evm.stack = right :: left :: rest) :
    Structured.ObserverSemantics.Code.run [.op .add] target =
      .ok
        (AllocationObserverRelation.StateRel.contractTargetBy
          1 (EvmYul.UInt256.add right left) rest target) := by
  unfold Structured.ObserverSemantics.Code.run
    Structured.EffectSemantics.Code.run
  simp only [Structured.BasicInstr.step, Structured.BasicOp.step,
    Assembly.Target.stepInstr,
    Structured.ObserverSemantics.stateModel_evm]
  simp only [Structured.BasicOp.toPrimOp]
  rw [Assembly.PrimOp.step_eq_continuingStep_run
    (by rfl : Assembly.PrimOp.add.continuingStep? =
      some (.bin EvmYul.UInt256.add))]
  unfold Assembly.PrimStep.run EvmYul.EVM.execBinOp
  rw [hStack]
  simp [Structured.ObserverSemantics.stateModel_withEVM,
    Structured.ObserverSemantics.handler,
    Structured.ObserverSemantics.basicOpObserver?,
    Structured.BasicOp.toPrimOp,
    Assembly.ResourceObserver.ofPrimOp?,
    Structured.EffectSemantics.Code.run,
    EvmYul.Stack.pop2, EvmYul.Stack.push, Id.run,
    AllocationObserverRelation.StateRel.contractTargetBy,
    Simulation.ResourceReplay.State.withSource,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem run_mload {transcript : Trace}
    {target : Structured.ObserverSemantics.State transcript}
    {address value : Word} {rest : List Word}
    (hStack : target.source.evm.stack = address :: rest)
    (hLoad :
      target.source.evm.toMachineState.mload address =
        (value, target.source.evm.toMachineState)) :
    Structured.ObserverSemantics.Code.run [.op .mload] target =
      .ok
        (AllocationObserverRelation.StateRel.contractTargetBy
          1 value rest target) := by
  unfold Structured.ObserverSemantics.Code.run
    Structured.EffectSemantics.Code.run
  simp only [Structured.BasicInstr.step, Structured.BasicOp.step,
    Assembly.Target.stepInstr,
    Structured.ObserverSemantics.stateModel_evm]
  simp only [Structured.BasicOp.toPrimOp]
  rw [Assembly.PrimOp.step_eq_continuingStep_run
    (by rfl : Assembly.PrimOp.mload.continuingStep? =
      some .mload)]
  unfold Assembly.PrimStep.run
  rw [hStack]
  simp only [EvmYul.Stack.pop]
  rw [hLoad]
  simp [Structured.ObserverSemantics.stateModel_withEVM,
    Structured.ObserverSemantics.handler,
    Structured.ObserverSemantics.basicOpObserver?,
    Structured.BasicOp.toPrimOp,
    Assembly.ResourceObserver.ofPrimOp?,
    Structured.EffectSemantics.Code.run,
    EvmYul.Stack.push, Id.run,
    AllocationObserverRelation.StateRel.contractTargetBy,
    Simulation.ResourceReplay.State.withSource,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem run_gas {transcript : Trace}
    {target targetConsumed :
      Structured.ObserverSemantics.State transcript}
    {value : Word}
    (hConsume :
      Simulation.ResourceReplay.consume? .gas target =
        some (value, targetConsumed)) :
    Structured.ObserverSemantics.Code.run
        [.op .gas] target =
      .ok
        (AllocationObserverRelation.StateRel.pushTarget
          value targetConsumed) := by
  unfold Structured.ObserverSemantics.Code.run
    Structured.EffectSemantics.Code.run
  simp only [Structured.BasicInstr.step, Structured.BasicOp.step,
    Assembly.Target.stepInstr]
  simp only [Structured.BasicOp.toPrimOp]
  have hGasStep :
      Assembly.PrimOp.gas.step target.source.evm =
        EvmYul.EVM.machineStateOp EvmYul.MachineState.gas
          target.source.evm := by
    rfl
  have hConsumedSource :
      targetConsumed.source = target.source :=
    Simulation.ResourceReplay.consume?_source hConsume
  simp only [Structured.ObserverSemantics.stateModel_evm]
  rw [hGasStep]
  simp only [EvmYul.EVM.machineStateOp, Id.run, Bind.bind, Except.bind]
  simp only [Structured.ObserverSemantics.stateModel_withEVM]
  unfold Structured.ObserverSemantics.handler
    Structured.ObserverSemantics.applyObserver
  simp only [Structured.ObserverSemantics.basicOpObserver?_gas]
  rw [Simulation.ResourceReplay.consume?_withSource]
  rw [hConsume]
  simp only [Option.map_some, Simulation.ResourceReplay.State.withSource]
  simp [Assembly.ResourceObserver.overwriteTop,
    Structured.EffectSemantics.Code.run,
    EvmYul.Stack.push, Structured.RunState.withEVM,
    hConsumedSource,
    Simulation.ResourceReplay.State.withSource,
    AllocationObserverRelation.StateRel.pushTarget,
    AllocationObserverRelation.StateRel.pushTargetBy,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem run_gas_none {transcript : Trace}
    {target : Structured.ObserverSemantics.State transcript}
    (hConsume :
      Simulation.ResourceReplay.consume? .gas target = none) :
    Structured.ObserverSemantics.Code.run [.op .gas] target =
      .error .InvalidInstruction := by
  unfold Structured.ObserverSemantics.Code.run
    Structured.EffectSemantics.Code.run
  simp only [Structured.BasicInstr.step, Structured.BasicOp.step,
    Assembly.Target.stepInstr, Structured.BasicOp.toPrimOp]
  have hGasStep :
      Assembly.PrimOp.gas.step target.source.evm =
        EvmYul.EVM.machineStateOp EvmYul.MachineState.gas
          target.source.evm := by
    rfl
  simp only [Structured.ObserverSemantics.stateModel_evm]
  rw [hGasStep]
  simp only [EvmYul.EVM.machineStateOp, Id.run, Bind.bind, Except.bind]
  simp only [Structured.ObserverSemantics.stateModel_withEVM]
  unfold Structured.ObserverSemantics.handler
    Structured.ObserverSemantics.applyObserver
  simp only [Structured.ObserverSemantics.basicOpObserver?_gas]
  rw [Simulation.ResourceReplay.consume?_withSource]
  rw [hConsume]
  rfl

theorem run_gas_backward {transcript : Trace}
    {target targetFinal :
      Structured.ObserverSemantics.State transcript}
    (hRun :
      Structured.ObserverSemantics.Code.run [.op .gas] target =
        .ok targetFinal) :
    ∃ value targetConsumed,
      Simulation.ResourceReplay.consume? .gas target =
          some (value, targetConsumed) ∧
        targetFinal =
          AllocationObserverRelation.StateRel.pushTarget
            value targetConsumed := by
  cases hConsume :
      Simulation.ResourceReplay.consume? .gas target with
  | none =>
      rw [run_gas_none hConsume] at hRun
      contradiction
  | some consumed =>
      rcases consumed with ⟨value, targetConsumed⟩
      have hExpected := run_gas hConsume
      rw [hExpected] at hRun
      cases hRun
      exact ⟨value, targetConsumed, rfl, rfl⟩

theorem run_msize {transcript : Trace}
    {target targetConsumed :
      Structured.ObserverSemantics.State transcript}
    {value : Word}
    (hConsume :
      Simulation.ResourceReplay.consume? .msize target =
        some (value, targetConsumed)) :
    Structured.ObserverSemantics.Code.run
        [.op .msize] target =
      .ok
        (AllocationObserverRelation.StateRel.pushTarget
          value targetConsumed) := by
  unfold Structured.ObserverSemantics.Code.run
    Structured.EffectSemantics.Code.run
  simp only [Structured.BasicInstr.step, Structured.BasicOp.step,
    Assembly.Target.stepInstr]
  simp only [Structured.BasicOp.toPrimOp]
  have hMsizeStep :
      Assembly.PrimOp.msize.step target.source.evm =
        EvmYul.EVM.machineStateOp EvmYul.MachineState.msize
          target.source.evm := by
    rfl
  have hConsumedSource :
      targetConsumed.source = target.source :=
    Simulation.ResourceReplay.consume?_source hConsume
  simp only [Structured.ObserverSemantics.stateModel_evm]
  rw [hMsizeStep]
  simp only [EvmYul.EVM.machineStateOp, Id.run, Bind.bind, Except.bind]
  simp only [Structured.ObserverSemantics.stateModel_withEVM]
  unfold Structured.ObserverSemantics.handler
    Structured.ObserverSemantics.applyObserver
  simp only [Structured.ObserverSemantics.basicOpObserver?_msize]
  rw [Simulation.ResourceReplay.consume?_withSource]
  rw [hConsume]
  simp only [Option.map_some, Simulation.ResourceReplay.State.withSource]
  simp [Assembly.ResourceObserver.overwriteTop,
    Structured.EffectSemantics.Code.run,
    EvmYul.Stack.push, Structured.RunState.withEVM,
    hConsumedSource,
    Simulation.ResourceReplay.State.withSource,
    AllocationObserverRelation.StateRel.pushTarget,
    AllocationObserverRelation.StateRel.pushTargetBy,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem run_msize_none {transcript : Trace}
    {target : Structured.ObserverSemantics.State transcript}
    (hConsume :
      Simulation.ResourceReplay.consume? .msize target = none) :
    Structured.ObserverSemantics.Code.run [.op .msize] target =
      .error .InvalidInstruction := by
  unfold Structured.ObserverSemantics.Code.run
    Structured.EffectSemantics.Code.run
  simp only [Structured.BasicInstr.step, Structured.BasicOp.step,
    Assembly.Target.stepInstr, Structured.BasicOp.toPrimOp]
  have hMsizeStep :
      Assembly.PrimOp.msize.step target.source.evm =
        EvmYul.EVM.machineStateOp EvmYul.MachineState.msize
          target.source.evm := by
    rfl
  simp only [Structured.ObserverSemantics.stateModel_evm]
  rw [hMsizeStep]
  simp only [EvmYul.EVM.machineStateOp, Id.run, Bind.bind, Except.bind]
  simp only [Structured.ObserverSemantics.stateModel_withEVM]
  unfold Structured.ObserverSemantics.handler
    Structured.ObserverSemantics.applyObserver
  simp only [Structured.ObserverSemantics.basicOpObserver?_msize]
  rw [Simulation.ResourceReplay.consume?_withSource]
  rw [hConsume]
  rfl

theorem run_msize_backward {transcript : Trace}
    {target targetFinal :
      Structured.ObserverSemantics.State transcript}
    (hRun :
      Structured.ObserverSemantics.Code.run [.op .msize] target =
        .ok targetFinal) :
    ∃ value targetConsumed,
      Simulation.ResourceReplay.consume? .msize target =
          some (value, targetConsumed) ∧
        targetFinal =
          AllocationObserverRelation.StateRel.pushTarget
            value targetConsumed := by
  cases hConsume :
      Simulation.ResourceReplay.consume? .msize target with
  | none =>
      rw [run_msize_none hConsume] at hRun
      contradiction
  | some consumed =>
      rcases consumed with ⟨value, targetConsumed⟩
      have hExpected := run_msize hConsume
      rw [hExpected] at hRun
      cases hRun
      exact ⟨value, targetConsumed, rfl, rfl⟩

end ObserverCode

namespace Expr

theorem literal_forward {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (value : Word)
    (hRel :
      AllocationObserverRelation.StateRel contract plan live
        stackOffset frameBase source target) :
    Functions.Source.Effectful.Expr.eval
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        (.lit value : Functions.Expr 1) source =
      .ok (source, [value]) ∧
    Structured.ObserverSemantics.Code.run
        [.push value] target =
      .ok
        (AllocationObserverRelation.StateRel.pushTargetBy
          33 value target) ∧
    AllocationObserverRelation.StateRel contract plan live
      (stackOffset + 1) frameBase source
      (AllocationObserverRelation.StateRel.pushTargetBy
        33 value target) := by
  exact
    ⟨rfl, ObserverCode.run_push value target,
      hRel.push_target_by 33 value⟩

theorem literal_backward {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target targetFinal :
      Structured.ObserverSemantics.State transcript}
    (value : Word)
    (hRel :
      AllocationObserverRelation.StateRel contract plan live
        stackOffset frameBase source target)
    (hRun :
      Structured.ObserverSemantics.Code.run [.push value] target =
        .ok targetFinal) :
    Functions.Source.Effectful.Expr.eval
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        (.lit value : Functions.Expr 1) source =
      .ok (source, [value]) ∧
    AllocationObserverRelation.StateRel contract plan live
      (stackOffset + 1) frameBase source targetFinal := by
  rw [ObserverCode.run_push value target] at hRun
  cases hRun
  exact ⟨rfl, hRel.push_target_by 33 value⟩

theorem stackVar_forward {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase depth : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {name : Locals.Name} {value : Word} {op : Structured.BasicOp}
    (hRel :
      AllocationObserverRelation.StateRel contract plan live
        stackOffset frameBase source target)
    (hLive : name ∈ live)
    (hLocation :
      Locals.Allocation.Plan.location? plan name =
        some (Locals.Allocation.LocalLocation.stack depth))
    (hSource : source.source.vars name = some value)
    (hOp :
      Locals.StackOp.dup? (stackOffset + depth + 1) = some op) :
    Functions.Source.Effectful.Expr.eval
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        (.var name : Functions.Expr 1) source =
      .ok (source, [value]) ∧
    Structured.ObserverSemantics.Code.run [.op op] target =
      .ok
        (AllocationObserverRelation.StateRel.pushTarget value target) ∧
    AllocationObserverRelation.StateRel contract plan live
      (stackOffset + 1) frameBase source
      (AllocationObserverRelation.StateRel.pushTarget value target) := by
  have hTargetGet :
      target.source.evm.stack[stackOffset + depth]? = some value := by
    rw [hRel.core.store.stack hLive hLocation, hSource]
  refine ⟨?_, ObserverCode.run_dup hOp hTargetGet,
    hRel.push_target value⟩
  simp [Functions.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.eval,
    Functions.ObserverSemantics.stateModel,
    Locals.ObserverSemantics.stateModel,
    Locals.Source.Effectful.StateModel.vars, hSource]

theorem stackVar_backward {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase depth : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target targetFinal :
      Structured.ObserverSemantics.State transcript}
    {name : Locals.Name} {value : Word} {op : Structured.BasicOp}
    (hRel :
      AllocationObserverRelation.StateRel contract plan live
        stackOffset frameBase source target)
    (hLive : name ∈ live)
    (hLocation :
      Locals.Allocation.Plan.location? plan name =
        some (Locals.Allocation.LocalLocation.stack depth))
    (hSource : source.source.vars name = some value)
    (hOp :
      Locals.StackOp.dup? (stackOffset + depth + 1) = some op)
    (hRun :
      Structured.ObserverSemantics.Code.run [.op op] target =
        .ok targetFinal) :
    Functions.Source.Effectful.Expr.eval
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        (.var name : Functions.Expr 1) source =
      .ok (source, [value]) ∧
    AllocationObserverRelation.StateRel contract plan live
      (stackOffset + 1) frameBase source targetFinal := by
  have hTargetGet :
      target.source.evm.stack[stackOffset + depth]? = some value := by
    rw [hRel.core.store.stack hLive hLocation, hSource]
  rw [ObserverCode.run_dup hOp hTargetGet] at hRun
  cases hRun
  refine ⟨?_, hRel.push_target value⟩
  simp [Functions.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.eval,
    Functions.ObserverSemantics.stateModel,
    Locals.ObserverSemantics.stateModel,
    Locals.Source.Effectful.StateModel.vars, hSource]

theorem scratchVar_forward {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords slot : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {name : Locals.Name} {value : Word} {op : Structured.BasicOp}
    (hRel :
      AllocationObserverRelation.ScratchStateRel contract plan live
        stackOffset frameBase frameDepth frameWords source target)
    (hLive : name ∈ live)
    (hLocation :
      Locals.Allocation.Plan.location? plan name =
        some (Locals.Allocation.LocalLocation.scratch slot))
    (hSource : source.source.vars name = some value)
    (hOp :
      Locals.StackOp.dup? (stackOffset + frameDepth + 1) = some op) :
    ∃ targetFinal,
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          (.var name : Functions.Expr 1) source =
        .ok (source, [value]) ∧
      Structured.ObserverSemantics.Code.run
          [ .op op,
            .push (AllocationSupport.slotOffset slot),
            .op .add,
            .op .mload ] target =
        .ok targetFinal ∧
      AllocationObserverRelation.ScratchStateRel contract plan live
        (stackOffset + 1) frameBase frameDepth frameWords
        source targetFinal := by
  let frameWord := EvmYul.UInt256.ofNat frameBase
  let offsetWord := AllocationSupport.slotOffset slot
  let address :=
    EvmYul.UInt256.add offsetWord frameWord
  let afterDup :=
    AllocationObserverRelation.StateRel.pushTarget frameWord target
  let afterPush :=
    AllocationObserverRelation.StateRel.pushTargetBy
      33 offsetWord afterDup
  let afterAdd :=
    AllocationObserverRelation.StateRel.contractTargetBy
      1 address target.source.evm.stack afterPush
  let targetFinal :=
    AllocationObserverRelation.StateRel.contractTargetBy
      1 value target.source.evm.stack afterAdd
  have hAddress :
      address =
        EvmYul.UInt256.ofNat
          (AllocationObserverRelation.scratchAddress frameBase slot) := by
    change
      EvmYul.UInt256.ofNat (32 * slot) +
          EvmYul.UInt256.ofNat frameBase =
        EvmYul.UInt256.ofNat
          (frameBase + MemoryContract.wordBytes * slot)
    rw [Assembly.UInt256_ofNat_add]
    simp [MemoryContract.wordBytes, Nat.add_comm]
  have hAfterDupRel :
      AllocationObserverRelation.ScratchStateRel contract plan live
        (stackOffset + 1) frameBase frameDepth frameWords
        source afterDup := by
    exact hRel.push_target frameWord
  have hAfterPushRel :
      AllocationObserverRelation.ScratchStateRel contract plan live
        (stackOffset + 2) frameBase frameDepth frameWords
        source afterPush := by
    exact hAfterDupRel.push_target_by 33 offsetWord
  have hAfterPushStack :
      afterPush.source.evm.stack =
        offsetWord :: frameWord :: target.source.evm.stack := by
    rfl
  have hAfterAddRel :
      AllocationObserverRelation.ScratchStateRel contract plan live
        (stackOffset + 1) frameBase frameDepth frameWords
        source afterAdd := by
    exact
      hAfterPushRel.contract_target_by
        (value := address) hAfterPushStack 1
  have hAfterAddStack :
      afterAdd.source.evm.stack =
        address :: target.source.evm.stack := by
    rfl
  have hLoad :
      afterAdd.source.evm.toMachineState.mload address =
        (value, afterAdd.source.evm.toMachineState) := by
    have hMachine :=
      hAfterAddRel.mload_machine_eq hLive hLocation
    have hStored :=
      hAfterAddRel.base.core.store.scratch hLive hLocation
    rw [hSource] at hStored
    simp only [Option.getD_some] at hStored
    simpa [hAddress, hStored] using hMachine
  have hFinalRel :
      AllocationObserverRelation.ScratchStateRel contract plan live
        (stackOffset + 1) frameBase frameDepth frameWords
        source targetFinal := by
    exact
      hAfterAddRel.replace_top_by
        (value := value) hAfterAddStack 1
  refine ⟨targetFinal, ?_, ?_, hFinalRel⟩
  · simp [Functions.Source.Effectful.Expr.eval,
      Locals.Source.Effectful.Expr.eval,
      Functions.ObserverSemantics.stateModel,
      Locals.ObserverSemantics.stateModel,
      Locals.Source.Effectful.StateModel.vars, hSource]
  · calc
      Structured.ObserverSemantics.Code.run
          [ .op op,
            .push offsetWord,
            .op .add,
            .op .mload ] target =
          (Structured.ObserverSemantics.Code.run [.op op] target).bind
            (Structured.ObserverSemantics.Code.run
              [ .push offsetWord, .op .add, .op .mload ]) := by
                rw [Structured.ObserverSemantics.Code.run_cons_eq_run_single_bind]
      _ =
          Structured.ObserverSemantics.Code.run
            [ .push offsetWord, .op .add, .op .mload ] afterDup := by
              rw [ObserverCode.run_dup hOp hRel.framePointer]
              rfl
      _ =
          (Structured.ObserverSemantics.Code.run
              [.push offsetWord] afterDup).bind
            (Structured.ObserverSemantics.Code.run
              [.op .add, .op .mload]) := by
                rw [Structured.ObserverSemantics.Code.run_cons_eq_run_single_bind]
      _ =
          Structured.ObserverSemantics.Code.run
            [.op .add, .op .mload] afterPush := by
              rw [ObserverCode.run_push offsetWord afterDup]
              rfl
      _ =
          (Structured.ObserverSemantics.Code.run
              [.op .add] afterPush).bind
            (Structured.ObserverSemantics.Code.run [.op .mload]) := by
                rw [Structured.ObserverSemantics.Code.run_cons_eq_run_single_bind]
      _ =
          Structured.ObserverSemantics.Code.run
            [.op .mload] afterAdd := by
              rw [ObserverCode.run_add hAfterPushStack]
              rfl
      _ = .ok targetFinal := by
        exact ObserverCode.run_mload hAfterAddStack hLoad

theorem scratchVar_backward {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords slot : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target targetFinal :
      Structured.ObserverSemantics.State transcript}
    {name : Locals.Name} {value : Word} {op : Structured.BasicOp}
    (hRel :
      AllocationObserverRelation.ScratchStateRel contract plan live
        stackOffset frameBase frameDepth frameWords source target)
    (hLive : name ∈ live)
    (hLocation :
      Locals.Allocation.Plan.location? plan name =
        some (Locals.Allocation.LocalLocation.scratch slot))
    (hSource : source.source.vars name = some value)
    (hOp :
      Locals.StackOp.dup? (stackOffset + frameDepth + 1) = some op)
    (hRun :
      Structured.ObserverSemantics.Code.run
          [ .op op,
            .push (AllocationSupport.slotOffset slot),
            .op .add,
            .op .mload ] target =
        .ok targetFinal) :
    Functions.Source.Effectful.Expr.eval
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        (.var name : Functions.Expr 1) source =
      .ok (source, [value]) ∧
    AllocationObserverRelation.ScratchStateRel contract plan live
      (stackOffset + 1) frameBase frameDepth frameWords
      source targetFinal := by
  obtain ⟨expected, hSourceEval, hExpectedRun, hExpectedRel⟩ :=
    scratchVar_forward hRel hLive hLocation hSource hOp
  rw [hExpectedRun] at hRun
  cases hRun
  exact ⟨hSourceEval, hExpectedRel⟩

theorem scratchVar_forward_of_compileCode {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords slot : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {name frameName : Locals.Name} {value : Word}
    {ctx : Locals.Ctx} {code : Structured.Code}
    (hRel :
      AllocationObserverRelation.ScratchStateRel contract plan live
        stackOffset frameBase frameDepth frameWords source target)
    (hLive : name ∈ live)
    (hLocation :
      Locals.Allocation.Plan.location? plan name =
        some (Locals.Allocation.LocalLocation.scratch slot))
    (hSource : source.source.vars name = some value)
    (hFrameDepth :
      Locals.Layout.lookupDepth? frameName ctx.layout =
        some (frameDepth + 1))
    (hCompile :
      Locals.Expr.compileCode ctx stackOffset
          (AllocationLowering.scratchLoadExpr frameName slot) =
        some code) :
    ∃ targetFinal,
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          (.var name : Functions.Expr 1) source =
        .ok (source, [value]) ∧
      Structured.ObserverSemantics.Code.run code target =
        .ok targetFinal ∧
      AllocationObserverRelation.ScratchStateRel contract plan live
        (stackOffset + 1) frameBase frameDepth frameWords
        source targetFinal := by
  cases hDup :
      Locals.StackOp.dup? (stackOffset + (frameDepth + 1)) with
  | none =>
      simp [AllocationLowering.scratchLoadExpr,
        AllocationLowering.scratchAddressExpr,
        AllocationLowering.exprSeqOne,
        AllocationLowering.exprSeqTwo,
        Locals.Expr.compileCode, Locals.ExprSeq.compileCode,
        hFrameDepth, hDup] at hCompile
  | some op =>
      have hCode :=
        AllocationLowering.scratchLoadExpr_compileCode
          (slot := slot) (offset := stackOffset) hFrameDepth hDup
      rw [hCode] at hCompile
      cases hCompile
      exact
        scratchVar_forward hRel hLive hLocation hSource
          (by
            simpa [Nat.add_assoc] using hDup)

theorem scratchVar_backward_of_compileCode {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords slot : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target targetFinal :
      Structured.ObserverSemantics.State transcript}
    {name frameName : Locals.Name} {value : Word}
    {ctx : Locals.Ctx} {code : Structured.Code}
    (hRel :
      AllocationObserverRelation.ScratchStateRel contract plan live
        stackOffset frameBase frameDepth frameWords source target)
    (hLive : name ∈ live)
    (hLocation :
      Locals.Allocation.Plan.location? plan name =
        some (Locals.Allocation.LocalLocation.scratch slot))
    (hSource : source.source.vars name = some value)
    (hFrameDepth :
      Locals.Layout.lookupDepth? frameName ctx.layout =
        some (frameDepth + 1))
    (hCompile :
      Locals.Expr.compileCode ctx stackOffset
          (AllocationLowering.scratchLoadExpr frameName slot) =
        some code)
    (hRun :
      Structured.ObserverSemantics.Code.run code target =
        .ok targetFinal) :
    Functions.Source.Effectful.Expr.eval
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        (.var name : Functions.Expr 1) source =
      .ok (source, [value]) ∧
    AllocationObserverRelation.ScratchStateRel contract plan live
      (stackOffset + 1) frameBase frameDepth frameWords
      source targetFinal := by
  cases hDup :
      Locals.StackOp.dup? (stackOffset + (frameDepth + 1)) with
  | none =>
      simp [AllocationLowering.scratchLoadExpr,
        AllocationLowering.scratchAddressExpr,
        AllocationLowering.exprSeqOne,
        AllocationLowering.exprSeqTwo,
        Locals.Expr.compileCode, Locals.ExprSeq.compileCode,
        hFrameDepth, hDup] at hCompile
  | some op =>
      have hCode :=
        AllocationLowering.scratchLoadExpr_compileCode
          (slot := slot) (offset := stackOffset) hFrameDepth hDup
      rw [hCode] at hCompile
      cases hCompile
      exact
        scratchVar_backward hRel hLive hLocation hSource
          (by
            simpa [Nat.add_assoc] using hDup)
          hRun

theorem gas_forward {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat} {value : Word}
    {source sourceConsumed : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hRel :
      AllocationObserverRelation.StateRel contract plan live
        stackOffset frameBase source target)
    (hConsume :
      Simulation.ResourceReplay.consume? .gas source =
        some (value, sourceConsumed)) :
    ∃ targetFinal,
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          (.prim .gas .nil : Functions.Expr 1) source =
        .ok (sourceConsumed, [value]) ∧
      Structured.ObserverSemantics.Code.run
          [.op .gas] target =
        .ok targetFinal ∧
      AllocationObserverRelation.StateRel contract plan live
        (stackOffset + 1) frameBase sourceConsumed targetFinal := by
  obtain ⟨targetConsumed, hTargetConsume, hConsumedRel⟩ :=
    hRel.consume_forward hConsume
  refine
    ⟨AllocationObserverRelation.StateRel.pushTarget
        value targetConsumed,
      Functions.ObserverSemantics.expr_eval_gas hConsume,
      ObserverCode.run_gas hTargetConsume,
      hConsumedRel.push_target value⟩

theorem msize_forward {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat} {value : Word}
    {source sourceConsumed : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hRel :
      AllocationObserverRelation.StateRel contract plan live
        stackOffset frameBase source target)
    (hConsume :
      Simulation.ResourceReplay.consume? .msize source =
        some (value, sourceConsumed)) :
    ∃ targetFinal,
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          (.prim .msize .nil : Functions.Expr 1) source =
        .ok (sourceConsumed, [value]) ∧
      Structured.ObserverSemantics.Code.run
          [.op .msize] target =
        .ok targetFinal ∧
      AllocationObserverRelation.StateRel contract plan live
        (stackOffset + 1) frameBase sourceConsumed targetFinal := by
  obtain ⟨targetConsumed, hTargetConsume, hConsumedRel⟩ :=
    hRel.consume_forward hConsume
  refine
    ⟨AllocationObserverRelation.StateRel.pushTarget
        value targetConsumed,
      Functions.ObserverSemantics.expr_eval_msize hConsume,
      ObserverCode.run_msize hTargetConsume,
      hConsumedRel.push_target value⟩

theorem gas_backward {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
    (hRel :
      AllocationObserverRelation.StateRel contract plan live
        stackOffset frameBase source target)
    (hRun :
      Structured.ObserverSemantics.Code.run [.op .gas] target =
        .ok targetFinal) :
    ∃ value sourceConsumed,
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          (.prim .gas .nil : Functions.Expr 1) source =
        .ok (sourceConsumed, [value]) ∧
      AllocationObserverRelation.StateRel contract plan live
        (stackOffset + 1) frameBase sourceConsumed targetFinal := by
  obtain ⟨value, targetConsumed, hTargetConsume, rfl⟩ :=
    ObserverCode.run_gas_backward hRun
  obtain ⟨sourceConsumed, hSourceConsume, hConsumedRel⟩ :=
    hRel.consume_backward hTargetConsume
  exact
    ⟨value, sourceConsumed,
      Functions.ObserverSemantics.expr_eval_gas hSourceConsume,
      hConsumedRel.push_target value⟩

theorem msize_backward {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
    (hRel :
      AllocationObserverRelation.StateRel contract plan live
        stackOffset frameBase source target)
    (hRun :
      Structured.ObserverSemantics.Code.run [.op .msize] target =
        .ok targetFinal) :
    ∃ value sourceConsumed,
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          (.prim .msize .nil : Functions.Expr 1) source =
        .ok (sourceConsumed, [value]) ∧
      AllocationObserverRelation.StateRel contract plan live
        (stackOffset + 1) frameBase sourceConsumed targetFinal := by
  obtain ⟨value, targetConsumed, hTargetConsume, rfl⟩ :=
    ObserverCode.run_msize_backward hRun
  obtain ⟨sourceConsumed, hSourceConsume, hConsumedRel⟩ :=
    hRel.consume_backward hTargetConsume
  exact
    ⟨value, sourceConsumed,
      Functions.ObserverSemantics.expr_eval_msize hSourceConsume,
      hConsumedRel.push_target value⟩

theorem gas_forward_scratch {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat} {value : Word}
    {source sourceConsumed : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hRel :
      AllocationObserverRelation.ScratchStateRel contract plan live
        stackOffset frameBase frameDepth frameWords source target)
    (hConsume :
      Simulation.ResourceReplay.consume? .gas source =
        some (value, sourceConsumed)) :
    ∃ targetFinal,
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          (.prim .gas .nil : Functions.Expr 1) source =
        .ok (sourceConsumed, [value]) ∧
      Structured.ObserverSemantics.Code.run [.op .gas] target =
        .ok targetFinal ∧
      AllocationObserverRelation.ScratchStateRel contract plan live
        (stackOffset + 1) frameBase frameDepth frameWords
        sourceConsumed targetFinal := by
  obtain ⟨targetConsumed, hTargetConsume, hConsumedRel⟩ :=
    hRel.consume_forward hConsume
  refine
    ⟨AllocationObserverRelation.StateRel.pushTarget
        value targetConsumed,
      Functions.ObserverSemantics.expr_eval_gas hConsume,
      ObserverCode.run_gas hTargetConsume,
      hConsumedRel.push_target value⟩

theorem gas_backward_scratch {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
    (hRel :
      AllocationObserverRelation.ScratchStateRel contract plan live
        stackOffset frameBase frameDepth frameWords source target)
    (hRun :
      Structured.ObserverSemantics.Code.run [.op .gas] target =
        .ok targetFinal) :
    ∃ value sourceConsumed,
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          (.prim .gas .nil : Functions.Expr 1) source =
        .ok (sourceConsumed, [value]) ∧
      AllocationObserverRelation.ScratchStateRel contract plan live
        (stackOffset + 1) frameBase frameDepth frameWords
        sourceConsumed targetFinal := by
  obtain ⟨value, targetConsumed, hTargetConsume, rfl⟩ :=
    ObserverCode.run_gas_backward hRun
  obtain ⟨sourceConsumed, hSourceConsume, hConsumedRel⟩ :=
    hRel.consume_backward hTargetConsume
  exact
    ⟨value, sourceConsumed,
      Functions.ObserverSemantics.expr_eval_gas hSourceConsume,
      hConsumedRel.push_target value⟩

theorem msize_forward_scratch {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat} {value : Word}
    {source sourceConsumed : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hRel :
      AllocationObserverRelation.ScratchStateRel contract plan live
        stackOffset frameBase frameDepth frameWords source target)
    (hConsume :
      Simulation.ResourceReplay.consume? .msize source =
        some (value, sourceConsumed)) :
    ∃ targetFinal,
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          (.prim .msize .nil : Functions.Expr 1) source =
        .ok (sourceConsumed, [value]) ∧
      Structured.ObserverSemantics.Code.run [.op .msize] target =
        .ok targetFinal ∧
      AllocationObserverRelation.ScratchStateRel contract plan live
        (stackOffset + 1) frameBase frameDepth frameWords
        sourceConsumed targetFinal := by
  obtain ⟨targetConsumed, hTargetConsume, hConsumedRel⟩ :=
    hRel.consume_forward hConsume
  refine
    ⟨AllocationObserverRelation.StateRel.pushTarget
        value targetConsumed,
      Functions.ObserverSemantics.expr_eval_msize hConsume,
      ObserverCode.run_msize hTargetConsume,
      hConsumedRel.push_target value⟩

theorem msize_backward_scratch {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
    (hRel :
      AllocationObserverRelation.ScratchStateRel contract plan live
        stackOffset frameBase frameDepth frameWords source target)
    (hRun :
      Structured.ObserverSemantics.Code.run [.op .msize] target =
        .ok targetFinal) :
    ∃ value sourceConsumed,
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          (.prim .msize .nil : Functions.Expr 1) source =
        .ok (sourceConsumed, [value]) ∧
      AllocationObserverRelation.ScratchStateRel contract plan live
        (stackOffset + 1) frameBase frameDepth frameWords
        sourceConsumed targetFinal := by
  obtain ⟨value, targetConsumed, hTargetConsume, rfl⟩ :=
    ObserverCode.run_msize_backward hRun
  obtain ⟨sourceConsumed, hSourceConsume, hConsumedRel⟩ :=
    hRel.consume_backward hTargetConsume
  exact
    ⟨value, sourceConsumed,
      Functions.ObserverSemantics.expr_eval_msize hSourceConsume,
      hConsumedRel.push_target value⟩

end Expr

end AllocationObserverPreservation
end Functions
end EvmCompiler
