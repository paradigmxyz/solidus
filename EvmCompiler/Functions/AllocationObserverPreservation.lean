import EvmCompiler.Functions.AllocationObserverRelation

namespace EvmCompiler
namespace Functions
namespace AllocationObserverPreservation

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word

open AllocationObserverRelation

namespace ObserverCode

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

end Expr

end AllocationObserverPreservation
end Functions
end EvmCompiler
