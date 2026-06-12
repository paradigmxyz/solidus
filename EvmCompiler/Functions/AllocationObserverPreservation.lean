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

private theorem swap?_continuingStep
    {depth : Nat} {op : Structured.BasicOp}
    (hOp : Locals.StackOp.swap? depth = some op) :
    op.toPrimOp.continuingStep? = some (.swap depth) := by
  match depth with
  | 0 => simp [Locals.StackOp.swap?] at hOp
  | 1 => simp [Locals.StackOp.swap?] at hOp; cases hOp; rfl
  | 2 => simp [Locals.StackOp.swap?] at hOp; cases hOp; rfl
  | 3 => simp [Locals.StackOp.swap?] at hOp; cases hOp; rfl
  | 4 => simp [Locals.StackOp.swap?] at hOp; cases hOp; rfl
  | 5 => simp [Locals.StackOp.swap?] at hOp; cases hOp; rfl
  | 6 => simp [Locals.StackOp.swap?] at hOp; cases hOp; rfl
  | 7 => simp [Locals.StackOp.swap?] at hOp; cases hOp; rfl
  | 8 => simp [Locals.StackOp.swap?] at hOp; cases hOp; rfl
  | 9 => simp [Locals.StackOp.swap?] at hOp; cases hOp; rfl
  | 10 => simp [Locals.StackOp.swap?] at hOp; cases hOp; rfl
  | 11 => simp [Locals.StackOp.swap?] at hOp; cases hOp; rfl
  | 12 => simp [Locals.StackOp.swap?] at hOp; cases hOp; rfl
  | 13 => simp [Locals.StackOp.swap?] at hOp; cases hOp; rfl
  | 14 => simp [Locals.StackOp.swap?] at hOp; cases hOp; rfl
  | 15 => simp [Locals.StackOp.swap?] at hOp; cases hOp; rfl
  | 16 => simp [Locals.StackOp.swap?] at hOp; cases hOp; rfl
  | depth + 17 => simp [Locals.StackOp.swap?] at hOp

private theorem swap_stack_eq_set
    {depth : Nat} {value old : Word} {rest : List Word}
    (hGet : rest[depth]? = some old) :
    let top := (value :: rest).take ((depth + 1) + 1)
    let bottom := (value :: rest).drop ((depth + 1) + 1)
    top.getLast! :: top.tail!.dropLast ++ [top.head!] ++ bottom =
      old :: rest.set depth value := by
  have hDepth : depth < rest.length :=
    List.getElem?_eq_some_iff.mp hGet |>.1
  have hStackGet :
      (value :: rest)[depth + 1]? = some old := by
    simpa using hGet
  have hLast :
      ((value :: rest).take ((depth + 1) + 1)).getLast! = old :=
    take_succ_getLast!_of_getElem?_eq_some hStackGet
  have hTake :
      (value :: rest).take ((depth + 1) + 1) =
        value :: rest.take (depth + 1) := by
    simp [Nat.add_assoc]
  have hTakeLength :
      (rest.take (depth + 1)).length = depth + 1 := by
    simp [List.length_take,
      Nat.min_eq_left (Nat.succ_le_iff.mpr hDepth)]
  have hDropLast :
      (rest.take (depth + 1)).dropLast = rest.take depth := by
    rw [List.dropLast_eq_take, hTakeLength]
    simp [List.take_take]
  simp only
  rw [hLast, hTake]
  simp only [List.tail!_cons, List.head!_cons]
  rw [hDropLast, List.set_eq_take_cons_drop value hDepth]
  simp [List.append_assoc]

namespace ObserverCode

theorem run_append {transcript : Trace}
    (left right : Structured.Code)
    (target : Structured.ObserverSemantics.State transcript) :
    Structured.ObserverSemantics.Code.run (left ++ right) target =
      (Structured.ObserverSemantics.Code.run left target).bind
        (Structured.ObserverSemantics.Code.run right) :=
  Structured.ObserverSemantics.Code.run_append left right target

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

theorem run_pop {transcript : Trace}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word} {rest : List Word}
    (hStack : target.source.evm.stack = value :: rest) :
    Structured.ObserverSemantics.Code.run [.op .pop] target =
      .ok
        (AllocationObserverRelation.StateRel.replaceStackBy
          1 rest target) := by
  unfold Structured.ObserverSemantics.Code.run
    Structured.EffectSemantics.Code.run
  simp only [Structured.BasicInstr.step, Structured.BasicOp.step,
    Assembly.Target.stepInstr,
    Structured.ObserverSemantics.stateModel_evm]
  simp only [Structured.BasicOp.toPrimOp]
  rw [Assembly.PrimOp.step_eq_continuingStep_run
    (by rfl : Assembly.PrimOp.pop.continuingStep? = some .pop)]
  unfold Assembly.PrimStep.run
  rw [hStack]
  simp [Structured.ObserverSemantics.stateModel_withEVM,
    Structured.ObserverSemantics.handler,
    Structured.ObserverSemantics.basicOpObserver?,
    Structured.BasicOp.toPrimOp,
    Assembly.ResourceObserver.ofPrimOp?,
    Structured.EffectSemantics.Code.run,
    EvmYul.Stack.pop,
    AllocationObserverRelation.StateRel.replaceStackBy,
    Simulation.ResourceReplay.State.withSource,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

/--
Running compiler cleanup made only of `POP`s drops exactly the requested stack
prefix and preserves every non-stack component observed by the allocation
relation.
-/
theorem run_replicate_pop {transcript : Trace}
    (count : Nat)
    {target : Structured.ObserverSemantics.State transcript}
    (hBound : count ≤ target.source.evm.stack.length) :
    ∃ final,
      Structured.ObserverSemantics.Code.run
          (List.replicate count (Structured.BasicInstr.op .pop))
          target =
        .ok final ∧
      final.cursor = target.cursor ∧
      final.source.evm.stack = target.source.evm.stack.drop count ∧
      final.source.evm.toSharedState =
        target.source.evm.toSharedState ∧
      final.source.returns = target.source.returns := by
  induction count generalizing target with
  | zero =>
      exact
        ⟨target, rfl,
          rfl, by simp, rfl, rfl⟩
  | succ count ih =>
      cases hStack : target.source.evm.stack with
      | nil =>
          simp [hStack] at hBound
      | cons value rest =>
          let mid :=
            AllocationObserverRelation.StateRel.replaceStackBy
              1 rest target
          have hPop :
              Structured.ObserverSemantics.Code.run
                  [.op .pop] target =
                .ok mid := by
            simpa [mid] using run_pop (target := target) hStack
          have hMidStack : mid.source.evm.stack = rest := by
            simp [mid,
              AllocationObserverRelation.StateRel.replaceStackBy,
              Simulation.ResourceReplay.State.withSource,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
          have hTailBound : count ≤ mid.source.evm.stack.length := by
            rw [hMidStack]
            simpa [hStack] using hBound
          obtain
              ⟨final, hTail, hCursor, hFinalStack,
                hShared, hReturns⟩ :=
            ih hTailBound
          refine ⟨final, ?_, ?_, ?_, ?_, ?_⟩
          · change
              Structured.ObserverSemantics.Code.run
                  ([.op .pop] ++
                    List.replicate count
                      (Structured.BasicInstr.op .pop))
                  target =
                .ok final
            rw [run_append, hPop]
            exact hTail
          · rw [hCursor]
            simp [mid,
              AllocationObserverRelation.StateRel.replaceStackBy,
              Simulation.ResourceReplay.State.withSource,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
          · rw [hFinalStack, hMidStack]
            simp [hStack]
          · rw [hShared]
            simp [mid,
              AllocationObserverRelation.StateRel.replaceStackBy,
              Simulation.ResourceReplay.State.withSource,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
          · rw [hReturns]
            simp [mid,
              AllocationObserverRelation.StateRel.replaceStackBy,
              Simulation.ResourceReplay.State.withSource,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]

theorem run_swap {transcript : Trace}
    {target : Structured.ObserverSemantics.State transcript}
    {depth : Nat} {value old : Word} {rest : List Word}
    {op : Structured.BasicOp}
    (hOp : Locals.StackOp.swap? (depth + 1) = some op)
    (hGet : rest[depth]? = some old)
    (hStack : target.source.evm.stack = value :: rest) :
    Structured.ObserverSemantics.Code.run [.op op] target =
      .ok
        (AllocationObserverRelation.StateRel.replaceStackBy
          1 (old :: rest.set depth value) target) := by
  have hStep := swap?_continuingStep hOp
  have hObserver :
      Structured.ObserverSemantics.basicOpObserver? op = none := by
    cases op <;>
      simp [Structured.ObserverSemantics.basicOpObserver?,
        Structured.BasicOp.toPrimOp,
        Assembly.ResourceObserver.ofPrimOp?,
        Assembly.PrimOp.continuingStep?] at hStep ⊢
  have hDepth : depth < rest.length :=
    List.getElem?_eq_some_iff.mp hGet |>.1
  have hTakeBound :
      (depth + 1) + 1 ≤ (value :: rest).length := by
    simp only [List.length_cons]
    omega
  have hTakeLength :
      ((value :: rest).take ((depth + 1) + 1)).length =
        (depth + 1) + 1 := by
    exact List.length_take_of_le hTakeBound
  have hSwap := swap_stack_eq_set (value := value) hGet
  unfold Structured.ObserverSemantics.Code.run
    Structured.EffectSemantics.Code.run
  simp only [Structured.BasicInstr.step, Structured.BasicOp.step,
    Assembly.Target.stepInstr,
    Structured.ObserverSemantics.stateModel_evm]
  rw [Assembly.PrimOp.step_eq_continuingStep_run hStep]
  unfold Assembly.PrimStep.run EvmYul.swap
  rw [hStack]
  simp only [hTakeLength, ↓reduceIte]
  rw [hSwap]
  simp [Structured.ObserverSemantics.stateModel_withEVM,
    Structured.ObserverSemantics.handler, hObserver,
    Structured.EffectSemantics.Code.run,
    AllocationObserverRelation.StateRel.replaceStackBy,
    Simulation.ResourceReplay.State.withSource,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem run_swap_pop {transcript : Trace}
    {target : Structured.ObserverSemantics.State transcript}
    {depth : Nat} {value old : Word} {rest : List Word}
    {op : Structured.BasicOp}
    (hOp : Locals.StackOp.swap? (depth + 1) = some op)
    (hGet : rest[depth]? = some old)
    (hStack : target.source.evm.stack = value :: rest) :
    Structured.ObserverSemantics.Code.run
        [.op op, .op .pop] target =
      .ok
        (AllocationObserverRelation.StateRel.replaceStackBy
          2 (rest.set depth value) target) := by
  change
    Structured.ObserverSemantics.Code.run
        ([.op op] ++ [.op .pop]) target =
      .ok
        (AllocationObserverRelation.StateRel.replaceStackBy
          2 (rest.set depth value) target)
  rw [run_append, run_swap hOp hGet hStack]
  simp only [Except.bind]
  rw [run_pop (target :=
    AllocationObserverRelation.StateRel.replaceStackBy
      1 (old :: rest.set depth value) target)
      (value := old) (rest := rest.set depth value) (by
        simp [AllocationObserverRelation.StateRel.replaceStackBy,
          Simulation.ResourceReplay.State.withSource,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC])]
  have hPC :
      target.source.evm.pc + EvmYul.UInt256.ofNat 1 +
          EvmYul.UInt256.ofNat 1 =
        target.source.evm.pc + EvmYul.UInt256.ofNat 2 := by
    rw [Assembly.UInt256_add_assoc, Assembly.UInt256_ofNat_add]
  simp [AllocationObserverRelation.StateRel.replaceStackBy,
    Simulation.ResourceReplay.State.withSource,
    Structured.RunState.withEVM,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC, hPC]

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

theorem run_sub {transcript : Trace}
    {target : Structured.ObserverSemantics.State transcript}
    {left right : Word} {rest : List Word}
    (hStack : target.source.evm.stack = left :: right :: rest) :
    Structured.ObserverSemantics.Code.run [.op .sub] target =
      .ok
        (AllocationObserverRelation.StateRel.contractTargetBy
          1 (EvmYul.UInt256.sub left right) rest target) := by
  unfold Structured.ObserverSemantics.Code.run
    Structured.EffectSemantics.Code.run
  simp only [Structured.BasicInstr.step, Structured.BasicOp.step,
    Assembly.Target.stepInstr,
    Structured.ObserverSemantics.stateModel_evm]
  simp only [Structured.BasicOp.toPrimOp]
  rw [Assembly.PrimOp.step_eq_continuingStep_run
    (by rfl : Assembly.PrimOp.sub.continuingStep? =
      some (.bin EvmYul.UInt256.sub))]
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

theorem run_mstore {transcript : Trace}
    {target : Structured.ObserverSemantics.State transcript}
    {address value : Word} {rest : List Word}
    (hStack : target.source.evm.stack = address :: value :: rest) :
    Structured.ObserverSemantics.Code.run [.op .mstore] target =
      .ok
        (AllocationObserverRelation.StateRel.mstoreTarget
          address value rest target) := by
  unfold Structured.ObserverSemantics.Code.run
    Structured.EffectSemantics.Code.run
  simp only [Structured.BasicInstr.step, Structured.BasicOp.step,
    Assembly.Target.stepInstr,
    Structured.ObserverSemantics.stateModel_evm]
  simp only [Structured.BasicOp.toPrimOp]
  rw [Assembly.PrimOp.step_eq_continuingStep_run
    (by rfl : Assembly.PrimOp.mstore.continuingStep? =
      some (.binaryMachineState EvmYul.MachineState.mstore))]
  unfold Assembly.PrimStep.run EvmYul.EVM.binaryMachineStateOp
  rw [hStack]
  simp [Structured.ObserverSemantics.stateModel_withEVM,
    Structured.ObserverSemantics.handler,
    Structured.ObserverSemantics.basicOpObserver?,
    Structured.BasicOp.toPrimOp,
    Assembly.ResourceObserver.ofPrimOp?,
    Structured.EffectSemantics.Code.run,
    EvmYul.Stack.pop2, Id.run,
    AllocationObserverRelation.StateRel.mstoreTarget,
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

namespace Frame

theorem allocatorInit_forward {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan}
    {stackOffset frameBase frameWords : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hRel :
      AllocationObserverRelation.StateRel contract plan []
        stackOffset frameBase source target)
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hActiveNoWrap :
      target.source.evm.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run
          (AllocationSupport.scratchAllocatorInitCode config) target =
        .ok targetFinal ∧
      AllocationObserverRelation.StateRel contract plan []
        stackOffset frameBase source targetFinal ∧
      AllocationObserverRelation.Frame.AllocatorReady config 0
        targetFinal := by
  let firstWord := EvmYul.UInt256.ofNat config.firstFrame
  let cellWord := EvmYul.UInt256.ofNat config.allocatorCell
  let afterFirst :=
    AllocationObserverRelation.StateRel.pushTargetBy
      33 firstWord target
  let afterCell :=
    AllocationObserverRelation.StateRel.pushTargetBy
      33 cellWord afterFirst
  let targetFinal :=
    AllocationObserverRelation.StateRel.mstoreTarget
      cellWord firstWord target.source.evm.stack afterCell
  obtain
    ⟨reservation, hReservation, hAllocator, _hFirst, _hLimit,
      _hWords, hWF, hHost, hPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  have hRegion :
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
  have hCellEnd :
      config.allocatorCell + MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
    have hContained := hRegion.2
    exact lt_of_le_of_lt hContained hWF.2
  have hCellHost :
      config.allocatorCell + MemoryContract.wordBytes < USize.size := by
    have hContained := hRegion.2
    exact lt_of_le_of_lt hContained hHost
  have hMachine :
      Compiler.MemoryRelation.MachineRel contract
        source.source.shared.toMachineState
        (afterCell.source.evm.toMachineState.mstore
          cellWord firstWord) := by
    have hBaseMachine :
        Compiler.MemoryRelation.MachineRel contract
          source.source.shared.toMachineState
          afterCell.source.evm.toMachineState := by
      simpa [afterCell, afterFirst,
        AllocationObserverRelation.StateRel.pushTargetBy,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] using hRel.core.machine
    exact
      Compiler.MemoryRelation.MachineRel.mstore_target
        config.allocatorCell firstWord hBaseMachine
        hReservation hRegion hCellEnd hCellHost
  have hFinalRel :
      AllocationObserverRelation.StateRel contract plan []
        stackOffset frameBase source targetFinal := by
    refine ⟨?_, ?_⟩
    · simpa [targetFinal,
        AllocationObserverRelation.StateRel.mstoreTarget] using hRel.cursor
    · refine ⟨?_, ?_, ?_⟩
      · simpa [targetFinal, cellWord,
          AllocationObserverRelation.StateRel.mstoreTarget,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] using hMachine
      · simpa [targetFinal, afterCell, afterFirst,
          AllocationObserverRelation.StateRel.pushTargetBy,
          AllocationObserverRelation.StateRel.mstoreTarget,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] using hRel.core.world
      · intro name location hLive _hLocation
        simp at hLive
  have hAfterCellActive :
      afterCell.source.evm.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
    simpa [afterCell, afterFirst,
      AllocationObserverRelation.StateRel.pushTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hActiveNoWrap
  have hReady :
      AllocationObserverRelation.Frame.AllocatorReady config 0
        targetFinal := by
    simpa [targetFinal, cellWord, firstWord] using
      (AllocationObserverRelation.Frame.allocatorReady_zero_after_init
        (target := afterCell) (rest := target.source.evm.stack)
        hConfig hAfterCellActive)
  have hAfterCellStack :
      afterCell.source.evm.stack =
        cellWord :: firstWord :: target.source.evm.stack := by
    rfl
  refine ⟨targetFinal, ?_, hFinalRel, hReady⟩
  simp only [AllocationSupport.scratchAllocatorInitCode]
  calc
    Structured.ObserverSemantics.Code.run
        [.push firstWord, .push cellWord, .op .mstore] target =
      (Structured.ObserverSemantics.Code.run
          [.push firstWord] target).bind
        (Structured.ObserverSemantics.Code.run
          [.push cellWord, .op .mstore]) := by
            rw [Structured.ObserverSemantics.Code.run_cons_eq_run_single_bind]
    _ =
      Structured.ObserverSemantics.Code.run
        [.push cellWord, .op .mstore] afterFirst := by
          rw [ObserverCode.run_push firstWord target]
          rfl
    _ =
      (Structured.ObserverSemantics.Code.run
          [.push cellWord] afterFirst).bind
        (Structured.ObserverSemantics.Code.run [.op .mstore]) := by
          rw [Structured.ObserverSemantics.Code.run_cons_eq_run_single_bind]
    _ =
      Structured.ObserverSemantics.Code.run [.op .mstore] afterCell := by
        rw [ObserverCode.run_push cellWord afterFirst]
        rfl
    _ = .ok targetFinal := by
      exact ObserverCode.run_mstore hAfterCellStack

theorem allocatorAdvance_forward {transcript : Trace}
    {contract : MemoryContract.Contract}
    {frameWords depth : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {sourceMachine : EvmYul.MachineState}
    {target : Structured.ObserverSemantics.State transcript}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady config depth target)
    (hMachine :
      Compiler.MemoryRelation.MachineRel contract sourceMachine
        target.source.evm.toMachineState) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run
          [ .push (AllocationSupport.word config.allocatorCell),
            .op .mload,
            .op .dup1,
            .push (AllocationSupport.frameBytes config.frameWords),
            .op .add,
            .push (AllocationSupport.word config.allocatorCell),
            .op .mstore ] target =
        .ok targetFinal ∧
      targetFinal.source.evm.stack =
        EvmYul.UInt256.ofNat
            (AllocationObserverRelation.Frame.baseAt config depth) ::
          target.source.evm.stack ∧
      Compiler.MemoryRelation.MachineRel contract sourceMachine
        targetFinal.source.evm.toMachineState ∧
      AllocationObserverRelation.Frame.AllocatorReady config (depth + 1)
        targetFinal := by
  let cellWord := AllocationSupport.word config.allocatorCell
  let baseWord :=
    EvmYul.UInt256.ofNat
      (AllocationObserverRelation.Frame.baseAt config depth)
  let bytesWord := AllocationSupport.frameBytes config.frameWords
  let nextWord :=
    EvmYul.UInt256.add bytesWord baseWord
  let afterCell :=
    AllocationObserverRelation.StateRel.pushTargetBy 33 cellWord target
  let afterLoad :=
    AllocationObserverRelation.StateRel.contractTargetBy
      1 baseWord target.source.evm.stack afterCell
  let afterDup :=
    AllocationObserverRelation.StateRel.pushTarget baseWord afterLoad
  let afterBytes :=
    AllocationObserverRelation.StateRel.pushTargetBy
      33 bytesWord afterDup
  let afterAdd :=
    AllocationObserverRelation.StateRel.contractTargetBy
      1 nextWord (baseWord :: target.source.evm.stack) afterBytes
  let afterCellStore :=
    AllocationObserverRelation.StateRel.pushTargetBy
      33 cellWord afterAdd
  let targetFinal :=
    AllocationObserverRelation.StateRel.mstoreTarget
      cellWord nextWord (baseWord :: target.source.evm.stack)
      afterCellStore
  obtain
    ⟨reservation, hReservation, hAllocator, _hFirst, _hLimit,
      _hWords, hWF, hHost, hPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  have hRegion :
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
  have hCellEnd :
      config.allocatorCell + MemoryContract.wordBytes <
        EvmYul.UInt256.size :=
    lt_of_le_of_lt hRegion.2 hWF.2
  have hCellHost :
      config.allocatorCell + MemoryContract.wordBytes < USize.size :=
    lt_of_le_of_lt hRegion.2 hHost
  have hCellAddress :
      (EvmYul.UInt256.ofNat config.allocatorCell).toNat =
        config.allocatorCell :=
    EvmYul.UInt256.toNat_ofNat_of_lt (by omega)
  have hNextWord :
      nextWord =
        EvmYul.UInt256.ofNat
          (AllocationObserverRelation.Frame.baseAt config (depth + 1)) := by
    change
      EvmYul.UInt256.ofNat
            (MemoryContract.wordBytes * config.frameWords) +
          EvmYul.UInt256.ofNat
            (AllocationObserverRelation.Frame.baseAt config depth) =
        EvmYul.UInt256.ofNat
          (AllocationObserverRelation.Frame.baseAt config (depth + 1))
    rw [Assembly.UInt256_ofNat_add]
    rw [AllocationObserverRelation.Frame.baseAt_succ]
    simp [AllocationObserverRelation.Frame.bytes, Nat.add_comm]
  have hAfterCellStack :
      afterCell.source.evm.stack =
        cellWord :: target.source.evm.stack := by
    rfl
  have hLoad :
      afterCell.source.evm.toMachineState.mload cellWord =
        (baseWord, afterCell.source.evm.toMachineState) := by
    have hBaseLoad :=
      Compiler.MemoryRelation.mload_eq_lookup_of_end_le
        target.source.evm.toMachineState config.allocatorCell
        hCellAddress
        (by simpa [MemoryContract.wordBytes] using hReady.cellActive)
    rw [hReady.allocatorAt] at hBaseLoad
    simpa [afterCell, cellWord, baseWord,
      AllocationSupport.word,
      AllocationObserverRelation.StateRel.pushTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hBaseLoad
  have hAfterLoadStack :
      afterLoad.source.evm.stack =
        baseWord :: target.source.evm.stack := by
    rfl
  have hAfterLoadTop :
      afterLoad.source.evm.stack[0]? = some baseWord := by
    simp [hAfterLoadStack]
  have hAfterBytesStack :
      afterBytes.source.evm.stack =
        bytesWord :: baseWord :: baseWord :: target.source.evm.stack := by
    rfl
  have hAfterCellStoreStack :
      afterCellStore.source.evm.stack =
        cellWord :: nextWord :: baseWord :: target.source.evm.stack := by
    rfl
  have hIntermediateMachine :
      afterCellStore.source.evm.toMachineState =
        target.source.evm.toMachineState := by
    rfl
  have hFinalMachine :
      Compiler.MemoryRelation.MachineRel contract sourceMachine
        targetFinal.source.evm.toMachineState := by
    have hStored :=
      Compiler.MemoryRelation.MachineRel.mstore_target
        config.allocatorCell nextWord
        (by simpa [hIntermediateMachine] using hMachine)
        hReservation hRegion hCellEnd hCellHost
    simpa [targetFinal, cellWord, AllocationSupport.word,
      AllocationObserverRelation.StateRel.mstoreTarget,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hStored
  have hActiveEq :=
    Compiler.MemoryRelation.mstore_activeWords_eq_of_end_le
      target.source.evm.toMachineState config.allocatorCell nextWord
      hCellAddress
      (by simpa [MemoryContract.wordBytes] using hReady.cellActive)
  have hMemoryEq :=
    Compiler.MemoryRelation.writeWord_memory_size_eq_of_end_le
      target.source.evm.toMachineState config.allocatorCell nextWord
      hCellAddress
      (by simpa [MemoryContract.wordBytes] using hCellHost)
      (by simpa [MemoryContract.wordBytes] using hReady.cellAllocated)
  have hAllocatorAt :
      AllocationObserverRelation.Frame.AllocatorAt config (depth + 1)
        targetFinal := by
    have hLookup :=
      Compiler.MemoryRelation.lookupMemory_mstore_same
        target.source.evm.toMachineState config.allocatorCell nextWord
        hCellAddress
        (by simpa [MemoryContract.wordBytes] using hCellHost)
        (by simpa [MemoryContract.wordBytes] using hReady.cellAllocated)
        (by simpa [MemoryContract.wordBytes] using hReady.cellActive)
        (by simpa [MemoryContract.wordBytes] using hReady.activeNoWrap)
    rw [hNextWord] at hLookup
    simpa [AllocationObserverRelation.Frame.AllocatorAt,
      targetFinal, cellWord, AllocationSupport.word, hNextWord,
      AllocationObserverRelation.StateRel.mstoreTarget,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, hIntermediateMachine] using hLookup
  have hFinalReady :
      AllocationObserverRelation.Frame.AllocatorReady config (depth + 1)
        targetFinal := by
    refine
      { allocatorAt := hAllocatorAt
        cellActive := ?_
        cellAllocated := ?_
        activeNoWrap := ?_ }
    · simpa [targetFinal, cellWord, AllocationSupport.word,
        AllocationObserverRelation.StateRel.mstoreTarget,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, hIntermediateMachine, hActiveEq] using
          hReady.cellActive
    · simpa [targetFinal, cellWord, AllocationSupport.word,
        AllocationObserverRelation.StateRel.mstoreTarget,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, hIntermediateMachine,
        EvmYul.MachineState.mstore, hMemoryEq] using
          hReady.cellAllocated
    · simpa [targetFinal, cellWord, AllocationSupport.word,
        AllocationObserverRelation.StateRel.mstoreTarget,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, hIntermediateMachine, hActiveEq] using
          hReady.activeNoWrap
  have hFinalStack :
      targetFinal.source.evm.stack =
        baseWord :: target.source.evm.stack := by
    rfl
  refine
    ⟨targetFinal, ?_, hFinalStack, hFinalMachine, hFinalReady⟩
  calc
    Structured.ObserverSemantics.Code.run
        [ .push cellWord, .op .mload, .op .dup1,
          .push bytesWord, .op .add, .push cellWord, .op .mstore ] target =
      (Structured.ObserverSemantics.Code.run [.push cellWord] target).bind
        (Structured.ObserverSemantics.Code.run
          [.op .mload, .op .dup1, .push bytesWord, .op .add,
            .push cellWord, .op .mstore]) := by
              rw [Structured.ObserverSemantics.Code.run_cons_eq_run_single_bind]
    _ =
      Structured.ObserverSemantics.Code.run
        [.op .mload, .op .dup1, .push bytesWord, .op .add,
          .push cellWord, .op .mstore] afterCell := by
            rw [ObserverCode.run_push cellWord target]
            rfl
    _ =
      (Structured.ObserverSemantics.Code.run [.op .mload] afterCell).bind
        (Structured.ObserverSemantics.Code.run
          [.op .dup1, .push bytesWord, .op .add,
            .push cellWord, .op .mstore]) := by
              rw [Structured.ObserverSemantics.Code.run_cons_eq_run_single_bind]
    _ =
      Structured.ObserverSemantics.Code.run
        [.op .dup1, .push bytesWord, .op .add,
          .push cellWord, .op .mstore] afterLoad := by
            rw [ObserverCode.run_mload hAfterCellStack hLoad]
            rfl
    _ =
      (Structured.ObserverSemantics.Code.run [.op .dup1] afterLoad).bind
        (Structured.ObserverSemantics.Code.run
          [.push bytesWord, .op .add, .push cellWord, .op .mstore]) := by
            rw [Structured.ObserverSemantics.Code.run_cons_eq_run_single_bind]
    _ =
      Structured.ObserverSemantics.Code.run
        [.push bytesWord, .op .add, .push cellWord, .op .mstore]
        afterDup := by
          rw [ObserverCode.run_dup (by rfl) hAfterLoadTop]
          rfl
    _ =
      (Structured.ObserverSemantics.Code.run
          [.push bytesWord] afterDup).bind
        (Structured.ObserverSemantics.Code.run
          [.op .add, .push cellWord, .op .mstore]) := by
            rw [Structured.ObserverSemantics.Code.run_cons_eq_run_single_bind]
    _ =
      Structured.ObserverSemantics.Code.run
        [.op .add, .push cellWord, .op .mstore] afterBytes := by
          rw [ObserverCode.run_push bytesWord afterDup]
          rfl
    _ =
      (Structured.ObserverSemantics.Code.run [.op .add] afterBytes).bind
        (Structured.ObserverSemantics.Code.run
          [.push cellWord, .op .mstore]) := by
            rw [Structured.ObserverSemantics.Code.run_cons_eq_run_single_bind]
    _ =
      Structured.ObserverSemantics.Code.run
        [.push cellWord, .op .mstore] afterAdd := by
          rw [ObserverCode.run_add hAfterBytesStack]
          rfl
    _ =
      (Structured.ObserverSemantics.Code.run
          [.push cellWord] afterAdd).bind
        (Structured.ObserverSemantics.Code.run [.op .mstore]) := by
            rw [Structured.ObserverSemantics.Code.run_cons_eq_run_single_bind]
    _ =
      Structured.ObserverSemantics.Code.run [.op .mstore] afterCellStore := by
        rw [ObserverCode.run_push cellWord afterAdd]
        rfl
    _ = .ok targetFinal := by
      exact ObserverCode.run_mstore hAfterCellStoreStack

theorem framePrealloc_forward {transcript : Trace}
    {contract : MemoryContract.Contract}
    {frameWords allocatorDepth frameDepth : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {sourceMachine : EvmYul.MachineState}
    {target : Structured.ObserverSemantics.State transcript}
    {rest : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hPositive : 0 < config.frameWords)
    (hBudget :
      AllocationObserverRelation.Frame.Budget config frameDepth)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady
        config allocatorDepth target)
    (hMachine :
      Compiler.MemoryRelation.MachineRel contract sourceMachine
        target.source.evm.toMachineState)
    (hStack :
      target.source.evm.stack =
        EvmYul.UInt256.ofNat
            (AllocationObserverRelation.Frame.baseAt config frameDepth) ::
          rest) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run
          (AllocationSupport.framePreallocCode config.frameWords) target =
        .ok targetFinal ∧
      targetFinal.source.evm.stack =
        EvmYul.UInt256.ofNat
            (AllocationObserverRelation.Frame.baseAt config frameDepth) ::
          rest ∧
      Compiler.MemoryRelation.MachineRel contract sourceMachine
        targetFinal.source.evm.toMachineState ∧
      AllocationObserverRelation.Frame.AllocatorReady config allocatorDepth
        targetFinal ∧
      AllocationObserverRelation.Frame.baseAt config frameDepth +
          AllocationObserverRelation.Frame.bytes config ≤
        targetFinal.source.evm.activeWords.toNat *
          MemoryContract.wordBytes ∧
      AllocationObserverRelation.Frame.baseAt config frameDepth +
          AllocationObserverRelation.Frame.bytes config ≤
        targetFinal.source.evm.toMachineState.memory.size := by
  cases hWords : config.frameWords with
  | zero =>
      simp [hWords] at hPositive
  | succ slot =>
      let frameBase :=
        AllocationObserverRelation.Frame.baseAt config frameDepth
      let frameWord := EvmYul.UInt256.ofNat frameBase
      let zeroWord := AllocationSupport.zeroWord
      let offsetWord := AllocationSupport.slotOffset slot
      let address := EvmYul.UInt256.add offsetWord frameWord
      let afterZero :=
        AllocationObserverRelation.StateRel.pushTargetBy
          33 zeroWord target
      let afterDup :=
        AllocationObserverRelation.StateRel.pushTarget frameWord afterZero
      let afterOffset :=
        AllocationObserverRelation.StateRel.pushTargetBy
          33 offsetWord afterDup
      let afterAdd :=
        AllocationObserverRelation.StateRel.contractTargetBy
          1 address (zeroWord :: frameWord :: rest) afterOffset
      let targetFinal :=
        AllocationObserverRelation.StateRel.mstoreTarget
          address zeroWord (frameWord :: rest) afterAdd
      obtain
        ⟨reservation, hReservation, hAllocator, hFirst, hLimit,
          hConfigWords, hWF, hHost, hReservationPositive, _hFits⟩ :=
        AllocationSupport.scratchFrameConfig?_sound hConfig
      have hConfigWords' : config.frameWords = slot + 1 := by
        omega
      have hFrameEnd :
          AllocationObserverRelation.scratchAddress frameBase slot +
              MemoryContract.wordBytes =
            frameBase + AllocationObserverRelation.Frame.bytes config := by
        simp [AllocationObserverRelation.scratchAddress,
          AllocationObserverRelation.Frame.bytes,
          hConfigWords', MemoryContract.wordBytes,
          Nat.mul_add, Nat.add_assoc]
      have hBaseLower :
          config.firstFrame ≤ frameBase := by
        have hMono :=
          AllocationObserverRelation.Frame.baseAt_mono config
            (Nat.zero_le frameDepth)
        simpa [frameBase] using hMono
      have hCellBeforeFrame :
          config.allocatorCell + MemoryContract.wordBytes ≤ frameBase := by
        rw [hAllocator]
        rw [hFirst] at hBaseLower
        unfold MemoryContract.ScratchReservation.allocatorCell
        unfold MemoryContract.ScratchReservation.frameBase at hBaseLower
        simpa using hBaseLower
      have hCellBeforeAddress :
          config.allocatorCell + MemoryContract.wordBytes ≤
            AllocationObserverRelation.scratchAddress frameBase slot := by
        exact hCellBeforeFrame.trans
          (Nat.le_add_right frameBase
            (MemoryContract.wordBytes * slot))
      have hFrameNoWrap :
          frameBase + AllocationObserverRelation.Frame.bytes config <
            EvmYul.UInt256.size :=
        AllocationObserverRelation.Frame.noWrap_of_budget_of_scratchFrameConfig?
          hConfig hBudget
      have hFrameHost :
          frameBase + AllocationObserverRelation.Frame.bytes config <
            USize.size :=
        AllocationObserverRelation.Frame.hostAddressable_of_budget_of_scratchFrameConfig?
          hConfig hBudget
      have hAddressEnd :
          AllocationObserverRelation.scratchAddress frameBase slot +
              MemoryContract.wordBytes <
            EvmYul.UInt256.size := by
        rw [hFrameEnd]
        exact hFrameNoWrap
      have hAddressHost :
          AllocationObserverRelation.scratchAddress frameBase slot +
              MemoryContract.wordBytes <
            USize.size := by
        rw [hFrameEnd]
        exact hFrameHost
      have hAddressLt :
          AllocationObserverRelation.scratchAddress frameBase slot <
            EvmYul.UInt256.size := by
        omega
      have hAddressToNat :
          (EvmYul.UInt256.ofNat
            (AllocationObserverRelation.scratchAddress
              frameBase slot)).toNat =
            AllocationObserverRelation.scratchAddress frameBase slot :=
        EvmYul.UInt256.toNat_ofNat_of_lt hAddressLt
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
      have hRegion :
          reservation.containsRegion
            (AllocationObserverRelation.scratchAddress frameBase slot) 1 := by
        constructor
        · have hReservationBase :
              reservation.base ≤ config.firstFrame := by
            rw [hFirst]
            unfold MemoryContract.ScratchReservation.frameBase
            omega
          exact hReservationBase.trans
            (hBaseLower.trans
              (Nat.le_add_right frameBase
                (MemoryContract.wordBytes * slot)))
        · change
            AllocationObserverRelation.scratchAddress frameBase slot +
                MemoryContract.wordBytes ≤
              reservation.endExclusive
          rw [hFrameEnd, ← hLimit]
          exact hBudget
      have hAfterZeroStack :
          afterZero.source.evm.stack =
            zeroWord :: frameWord :: rest := by
        simp [afterZero,
          AllocationObserverRelation.StateRel.pushTargetBy, hStack,
          frameWord, frameBase,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      have hAfterZeroFrame :
          afterZero.source.evm.stack[1]? = some frameWord := by
        simp [hAfterZeroStack]
      have hAfterDupStack :
          afterDup.source.evm.stack =
            frameWord :: zeroWord :: frameWord :: rest := by
        simp [afterDup,
          AllocationObserverRelation.StateRel.pushTarget,
          AllocationObserverRelation.StateRel.pushTargetBy,
          hAfterZeroStack,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      have hAfterOffsetStack :
          afterOffset.source.evm.stack =
            offsetWord :: frameWord :: zeroWord :: frameWord :: rest := by
        simp [afterOffset,
          AllocationObserverRelation.StateRel.pushTargetBy,
          hAfterDupStack,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      have hAfterAddStack :
          afterAdd.source.evm.stack =
            address :: zeroWord :: frameWord :: rest := by
        rfl
      have hBaseMachine :
          afterAdd.source.evm.toMachineState =
            target.source.evm.toMachineState := by
        rfl
      have hFinalMachine :
          Compiler.MemoryRelation.MachineRel contract sourceMachine
            targetFinal.source.evm.toMachineState := by
        have hStored :=
          Compiler.MemoryRelation.MachineRel.mstore_target
            (AllocationObserverRelation.scratchAddress frameBase slot)
            zeroWord
            (by simpa [hBaseMachine] using hMachine)
            hReservation hRegion hAddressEnd hAddressHost
        simpa [targetFinal, hAddress,
          AllocationObserverRelation.StateRel.mstoreTarget,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] using hStored
      have hFinalActiveNoWrap :
          targetFinal.source.evm.activeWords.toNat *
              MemoryContract.wordBytes <
            EvmYul.UInt256.size := by
        simpa [targetFinal, hAddress,
          AllocationObserverRelation.StateRel.mstoreTarget,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, MemoryContract.wordBytes] using
            (Compiler.MemoryRelation.mstore_activeBytes_lt_size_of_activeBytes_lt_size
                target.source.evm.toMachineState
                (AllocationObserverRelation.scratchAddress frameBase slot)
                zeroWord
                (by simpa [MemoryContract.wordBytes] using
                  hReady.activeNoWrap)
                (by simpa [MemoryContract.wordBytes] using hAddressHost))
      have hCellAddress :
          (EvmYul.UInt256.ofNat config.allocatorCell).toNat =
            config.allocatorCell :=
        EvmYul.UInt256.toNat_ofNat_of_lt (by omega)
      have hAllocatorPreserved :
          AllocationObserverRelation.Frame.AllocatorAt config allocatorDepth
            targetFinal := by
        have hLookup :=
          Compiler.MemoryRelation.lookupMemory_mstore_disjoint_growing
            target.source.evm.toMachineState
            (AllocationObserverRelation.scratchAddress frameBase slot)
            config.allocatorCell zeroWord
            hAddressToNat hCellAddress
            (by simpa [MemoryContract.wordBytes] using hAddressHost)
            (by simpa [MemoryContract.wordBytes] using
              hReady.cellAllocated)
            (by simpa [MemoryContract.wordBytes] using hReady.cellActive)
            (by simpa [MemoryContract.wordBytes] using hReady.activeNoWrap)
            (Or.inl
              (by simpa [MemoryContract.wordBytes] using
                hCellBeforeAddress))
        rw [hReady.allocatorAt] at hLookup
        simpa [AllocationObserverRelation.Frame.AllocatorAt,
          targetFinal, hAddress,
          AllocationObserverRelation.StateRel.mstoreTarget,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC,
          hBaseMachine] using hLookup
      have hActiveMono :=
        Compiler.MemoryRelation.activeWords_toNat_le_mstore
          target.source.evm.toMachineState
          (AllocationObserverRelation.scratchAddress frameBase slot)
          zeroWord hAddressEnd
      have hMemoryMono :=
        Compiler.MemoryRelation.writeWord_memory_size_ge
          target.source.evm.toMachineState
          (AllocationObserverRelation.scratchAddress frameBase slot)
          zeroWord hAddressToNat
          (by simpa [MemoryContract.wordBytes] using hAddressHost)
      have hFinalReady :
          AllocationObserverRelation.Frame.AllocatorReady
            config allocatorDepth
            targetFinal := by
        refine
          { allocatorAt := hAllocatorPreserved
            cellActive := ?_
            cellAllocated := ?_
            activeNoWrap := hFinalActiveNoWrap }
        · have hCell := hReady.cellActive
          have hScaled :
              target.source.evm.activeWords.toNat *
                    MemoryContract.wordBytes ≤
                (target.source.evm.toMachineState.mstore
                    (EvmYul.UInt256.ofNat
                      (AllocationObserverRelation.scratchAddress
                        frameBase slot))
                    zeroWord).activeWords.toNat *
                  MemoryContract.wordBytes := by
            exact Nat.mul_le_mul_right MemoryContract.wordBytes hActiveMono
          simpa [targetFinal, hAddress,
            AllocationObserverRelation.StateRel.mstoreTarget,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC] using hCell.trans hScaled
        · have hCell := hReady.cellAllocated
          simpa [targetFinal, hAddress,
            AllocationObserverRelation.StateRel.mstoreTarget,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC,
            EvmYul.MachineState.mstore] using hCell.trans hMemoryMono
      have hFrameActive :
          frameBase + AllocationObserverRelation.Frame.bytes config ≤
            targetFinal.source.evm.activeWords.toNat *
              MemoryContract.wordBytes := by
        rw [← hFrameEnd]
        simpa [targetFinal, hAddress,
          AllocationObserverRelation.StateRel.mstoreTarget,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, MemoryContract.wordBytes] using
            (Compiler.MemoryRelation.mstore_end_le_activeBytes
              target.source.evm.toMachineState
              (AllocationObserverRelation.scratchAddress frameBase slot)
              zeroWord
              (by simpa [MemoryContract.wordBytes] using hAddressEnd))
      have hFrameAllocated :
          frameBase + AllocationObserverRelation.Frame.bytes config ≤
            targetFinal.source.evm.toMachineState.memory.size := by
        rw [← hFrameEnd]
        simpa [targetFinal, hAddress,
          AllocationObserverRelation.StateRel.mstoreTarget,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC,
          EvmYul.MachineState.mstore] using
            (Compiler.MemoryRelation.writeWord_memory_size_ge_end
              target.source.evm.toMachineState
              (AllocationObserverRelation.scratchAddress frameBase slot)
              zeroWord hAddressToNat
              (by simpa [MemoryContract.wordBytes] using hAddressHost))
      have hFinalStack :
          targetFinal.source.evm.stack = frameWord :: rest := by
        rfl
      refine
        ⟨targetFinal, ?_, hFinalStack, hFinalMachine, hFinalReady,
          hFrameActive, hFrameAllocated⟩
      simp only [AllocationSupport.framePreallocCode, hWords]
      calc
        Structured.ObserverSemantics.Code.run
            [ .push zeroWord, .op .dup2, .push offsetWord,
              .op .add, .op .mstore ] target =
          (Structured.ObserverSemantics.Code.run
              [.push zeroWord] target).bind
            (Structured.ObserverSemantics.Code.run
              [.op .dup2, .push offsetWord, .op .add, .op .mstore]) := by
                rw [Structured.ObserverSemantics.Code.run_cons_eq_run_single_bind]
        _ =
          Structured.ObserverSemantics.Code.run
            [.op .dup2, .push offsetWord, .op .add, .op .mstore]
            afterZero := by
              rw [ObserverCode.run_push zeroWord target]
              rfl
        _ =
          (Structured.ObserverSemantics.Code.run
              [.op .dup2] afterZero).bind
            (Structured.ObserverSemantics.Code.run
              [.push offsetWord, .op .add, .op .mstore]) := by
                rw [Structured.ObserverSemantics.Code.run_cons_eq_run_single_bind]
        _ =
          Structured.ObserverSemantics.Code.run
            [.push offsetWord, .op .add, .op .mstore] afterDup := by
              rw [ObserverCode.run_dup (by rfl) hAfterZeroFrame]
              rfl
        _ =
          (Structured.ObserverSemantics.Code.run
              [.push offsetWord] afterDup).bind
            (Structured.ObserverSemantics.Code.run
              [.op .add, .op .mstore]) := by
                rw [Structured.ObserverSemantics.Code.run_cons_eq_run_single_bind]
        _ =
          Structured.ObserverSemantics.Code.run
            [.op .add, .op .mstore] afterOffset := by
              rw [ObserverCode.run_push offsetWord afterDup]
              rfl
        _ =
          (Structured.ObserverSemantics.Code.run
              [.op .add] afterOffset).bind
            (Structured.ObserverSemantics.Code.run [.op .mstore]) := by
                rw [Structured.ObserverSemantics.Code.run_cons_eq_run_single_bind]
        _ =
          Structured.ObserverSemantics.Code.run [.op .mstore] afterAdd := by
            rw [ObserverCode.run_add hAfterOffsetStack]
            rfl
        _ = .ok targetFinal := by
          exact ObserverCode.run_mstore hAfterAddStack

theorem scratchFrameAcquire_forward {transcript : Trace}
    {contract : MemoryContract.Contract}
    {frameWords depth : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {sourceMachine : EvmYul.MachineState}
    {target : Structured.ObserverSemantics.State transcript}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hPositive : 0 < config.frameWords)
    (hBudget :
      AllocationObserverRelation.Frame.Budget config depth)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady config depth target)
    (hMachine :
      Compiler.MemoryRelation.MachineRel contract sourceMachine
        target.source.evm.toMachineState) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run
          (AllocationSupport.scratchFrameAcquireCode config) target =
        .ok targetFinal ∧
      targetFinal.source.evm.stack =
        EvmYul.UInt256.ofNat
            (AllocationObserverRelation.Frame.baseAt config depth) ::
          target.source.evm.stack ∧
      Compiler.MemoryRelation.MachineRel contract sourceMachine
        targetFinal.source.evm.toMachineState ∧
      AllocationObserverRelation.Frame.AllocatorReady config (depth + 1)
        targetFinal ∧
      AllocationObserverRelation.Frame.baseAt config depth +
          AllocationObserverRelation.Frame.bytes config ≤
        targetFinal.source.evm.activeWords.toNat *
          MemoryContract.wordBytes ∧
      AllocationObserverRelation.Frame.baseAt config depth +
          AllocationObserverRelation.Frame.bytes config ≤
        targetFinal.source.evm.toMachineState.memory.size := by
  obtain
    ⟨advanced, hAdvanceRun, hAdvanceStack,
      hAdvanceMachine, hAdvanceReady⟩ :=
    allocatorAdvance_forward hConfig hReady hMachine
  obtain
    ⟨targetFinal, hPreallocRun, hFinalStack,
      hFinalMachine, hFinalReady, hFrameActive, hFrameAllocated⟩ :=
    framePrealloc_forward
      (allocatorDepth := depth + 1) (frameDepth := depth)
      hConfig hPositive hBudget hAdvanceReady hAdvanceMachine
      hAdvanceStack
  refine
    ⟨targetFinal, ?_, hFinalStack, hFinalMachine, hFinalReady,
      hFrameActive, hFrameAllocated⟩
  unfold AllocationSupport.scratchFrameAcquireCode
  rw [ObserverCode.run_append]
  rw [hAdvanceRun]
  exact hPreallocRun

theorem scratchFrameAcquire_backward {transcript : Trace}
    {contract : MemoryContract.Contract}
    {frameWords depth : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {sourceMachine : EvmYul.MachineState}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hPositive : 0 < config.frameWords)
    (hBudget :
      AllocationObserverRelation.Frame.Budget config depth)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady config depth target)
    (hMachine :
      Compiler.MemoryRelation.MachineRel contract sourceMachine
        target.source.evm.toMachineState)
    (hRun :
      Structured.ObserverSemantics.Code.run
          (AllocationSupport.scratchFrameAcquireCode config) target =
        .ok targetFinal) :
    targetFinal.source.evm.stack =
        EvmYul.UInt256.ofNat
            (AllocationObserverRelation.Frame.baseAt config depth) ::
          target.source.evm.stack ∧
      Compiler.MemoryRelation.MachineRel contract sourceMachine
        targetFinal.source.evm.toMachineState ∧
      AllocationObserverRelation.Frame.AllocatorReady config (depth + 1)
        targetFinal ∧
      AllocationObserverRelation.Frame.baseAt config depth +
          AllocationObserverRelation.Frame.bytes config ≤
        targetFinal.source.evm.activeWords.toNat *
          MemoryContract.wordBytes ∧
      AllocationObserverRelation.Frame.baseAt config depth +
          AllocationObserverRelation.Frame.bytes config ≤
        targetFinal.source.evm.toMachineState.memory.size := by
  obtain
    ⟨expected, hExpectedRun, hExpectedStack, hExpectedMachine,
      hExpectedReady, hExpectedActive, hExpectedAllocated⟩ :=
    scratchFrameAcquire_forward
      hConfig hPositive hBudget hReady hMachine
  rw [hExpectedRun] at hRun
  cases hRun
  exact
    ⟨hExpectedStack, hExpectedMachine, hExpectedReady,
      hExpectedActive, hExpectedAllocated⟩

theorem scratchFrameRelease_forward {transcript : Trace}
    {contract : MemoryContract.Contract}
    {frameWords depth : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {sourceMachine : EvmYul.MachineState}
    {target : Structured.ObserverSemantics.State transcript}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hBudget :
      AllocationObserverRelation.Frame.Budget config depth)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady
        config (depth + 1) target)
    (hMachine :
      Compiler.MemoryRelation.MachineRel contract sourceMachine
        target.source.evm.toMachineState) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run
          (AllocationSupport.scratchFrameReleaseCode config) target =
        .ok targetFinal ∧
      targetFinal.source.evm.stack = target.source.evm.stack ∧
      Compiler.MemoryRelation.MachineRel contract sourceMachine
        targetFinal.source.evm.toMachineState ∧
      AllocationObserverRelation.Frame.AllocatorReady config depth
        targetFinal := by
  let bytesWord := AllocationSupport.frameBytes config.frameWords
  let cellWord := AllocationSupport.word config.allocatorCell
  let currentWord :=
    EvmYul.UInt256.ofNat
      (AllocationObserverRelation.Frame.baseAt config (depth + 1))
  let priorWord :=
    EvmYul.UInt256.ofNat
      (AllocationObserverRelation.Frame.baseAt config depth)
  let afterBytes :=
    AllocationObserverRelation.StateRel.pushTargetBy 33 bytesWord target
  let afterCell :=
    AllocationObserverRelation.StateRel.pushTargetBy
      33 cellWord afterBytes
  let afterLoad :=
    AllocationObserverRelation.StateRel.contractTargetBy
      1 currentWord (bytesWord :: target.source.evm.stack) afterCell
  let afterSub :=
    AllocationObserverRelation.StateRel.contractTargetBy
      1 priorWord target.source.evm.stack afterLoad
  let afterCellStore :=
    AllocationObserverRelation.StateRel.pushTargetBy 33 cellWord afterSub
  let targetFinal :=
    AllocationObserverRelation.StateRel.mstoreTarget
      cellWord priorWord target.source.evm.stack afterCellStore
  obtain
    ⟨reservation, hReservation, hAllocator, _hFirst, _hLimit,
      _hWords, hWF, hHost, _hPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  have hRegion :
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
  have hCellEnd :
      config.allocatorCell + MemoryContract.wordBytes <
        EvmYul.UInt256.size :=
    lt_of_le_of_lt hRegion.2 hWF.2
  have hCellHost :
      config.allocatorCell + MemoryContract.wordBytes < USize.size :=
    lt_of_le_of_lt hRegion.2 hHost
  have hCellAddress :
      (EvmYul.UInt256.ofNat config.allocatorCell).toNat =
        config.allocatorCell :=
    EvmYul.UInt256.toNat_ofNat_of_lt (by omega)
  have hPriorWord :
      EvmYul.UInt256.sub currentWord bytesWord = priorWord := by
    change
      EvmYul.UInt256.sub
          (EvmYul.UInt256.ofNat
            (AllocationObserverRelation.Frame.baseAt config (depth + 1)))
          (EvmYul.UInt256.ofNat
            (MemoryContract.wordBytes * config.frameWords)) =
        EvmYul.UInt256.ofNat
          (AllocationObserverRelation.Frame.baseAt config depth)
    rw [AllocationObserverRelation.Frame.baseAt_succ]
    exact
      Assembly.UInt256_ofNat_add_sub_right
        (AllocationObserverRelation.Frame.baseAt config depth)
        (AllocationObserverRelation.Frame.bytes config)
        (AllocationObserverRelation.Frame.noWrap_of_budget_of_scratchFrameConfig?
          hConfig hBudget)
  have hAfterCellStack :
      afterCell.source.evm.stack =
        cellWord :: bytesWord :: target.source.evm.stack := by
    rfl
  have hLoad :
      afterCell.source.evm.toMachineState.mload cellWord =
        (currentWord, afterCell.source.evm.toMachineState) := by
    have hBaseLoad :=
      Compiler.MemoryRelation.mload_eq_lookup_of_end_le
        target.source.evm.toMachineState config.allocatorCell
        hCellAddress
        (by simpa [MemoryContract.wordBytes] using hReady.cellActive)
    rw [hReady.allocatorAt] at hBaseLoad
    simpa [afterCell, afterBytes, cellWord, currentWord,
      AllocationSupport.word,
      AllocationObserverRelation.StateRel.pushTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hBaseLoad
  have hAfterLoadStack :
      afterLoad.source.evm.stack =
        currentWord :: bytesWord :: target.source.evm.stack := by
    rfl
  have hAfterCellStoreStack :
      afterCellStore.source.evm.stack =
        cellWord :: priorWord :: target.source.evm.stack := by
    rfl
  have hIntermediateMachine :
      afterCellStore.source.evm.toMachineState =
        target.source.evm.toMachineState := by
    rfl
  have hFinalMachine :
      Compiler.MemoryRelation.MachineRel contract sourceMachine
        targetFinal.source.evm.toMachineState := by
    have hStored :=
      Compiler.MemoryRelation.MachineRel.mstore_target
        config.allocatorCell priorWord
        (by simpa [hIntermediateMachine] using hMachine)
        hReservation hRegion hCellEnd hCellHost
    simpa [targetFinal, cellWord, AllocationSupport.word,
      AllocationObserverRelation.StateRel.mstoreTarget,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hStored
  have hActiveEq :=
    Compiler.MemoryRelation.mstore_activeWords_eq_of_end_le
      target.source.evm.toMachineState config.allocatorCell priorWord
      hCellAddress
      (by simpa [MemoryContract.wordBytes] using hReady.cellActive)
  have hMemoryEq :=
    Compiler.MemoryRelation.writeWord_memory_size_eq_of_end_le
      target.source.evm.toMachineState config.allocatorCell priorWord
      hCellAddress
      (by simpa [MemoryContract.wordBytes] using hCellHost)
      (by simpa [MemoryContract.wordBytes] using hReady.cellAllocated)
  have hAllocatorAt :
      AllocationObserverRelation.Frame.AllocatorAt config depth
        targetFinal := by
    have hLookup :=
      Compiler.MemoryRelation.lookupMemory_mstore_same
        target.source.evm.toMachineState config.allocatorCell priorWord
        hCellAddress
        (by simpa [MemoryContract.wordBytes] using hCellHost)
        (by simpa [MemoryContract.wordBytes] using hReady.cellAllocated)
        (by simpa [MemoryContract.wordBytes] using hReady.cellActive)
        (by simpa [MemoryContract.wordBytes] using hReady.activeNoWrap)
    simpa [AllocationObserverRelation.Frame.AllocatorAt,
      targetFinal, cellWord, AllocationSupport.word,
      AllocationObserverRelation.StateRel.mstoreTarget,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, hIntermediateMachine] using hLookup
  have hFinalReady :
      AllocationObserverRelation.Frame.AllocatorReady config depth
        targetFinal := by
    refine
      { allocatorAt := hAllocatorAt
        cellActive := ?_
        cellAllocated := ?_
        activeNoWrap := ?_ }
    · simpa [targetFinal, cellWord, AllocationSupport.word,
        AllocationObserverRelation.StateRel.mstoreTarget,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, hIntermediateMachine, hActiveEq] using
          hReady.cellActive
    · simpa [targetFinal, cellWord, AllocationSupport.word,
        AllocationObserverRelation.StateRel.mstoreTarget,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, hIntermediateMachine,
        EvmYul.MachineState.mstore, hMemoryEq] using
          hReady.cellAllocated
    · simpa [targetFinal, cellWord, AllocationSupport.word,
        AllocationObserverRelation.StateRel.mstoreTarget,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, hIntermediateMachine, hActiveEq] using
          hReady.activeNoWrap
  have hFinalStack :
      targetFinal.source.evm.stack = target.source.evm.stack := by
    rfl
  refine
    ⟨targetFinal, ?_, hFinalStack, hFinalMachine, hFinalReady⟩
  simp only [AllocationSupport.scratchFrameReleaseCode]
  calc
    Structured.ObserverSemantics.Code.run
        [ .push bytesWord, .push cellWord, .op .mload, .op .sub,
          .push cellWord, .op .mstore ] target =
      (Structured.ObserverSemantics.Code.run [.push bytesWord] target).bind
        (Structured.ObserverSemantics.Code.run
          [.push cellWord, .op .mload, .op .sub,
            .push cellWord, .op .mstore]) := by
              rw [Structured.ObserverSemantics.Code.run_cons_eq_run_single_bind]
    _ =
      Structured.ObserverSemantics.Code.run
        [.push cellWord, .op .mload, .op .sub,
          .push cellWord, .op .mstore] afterBytes := by
            rw [ObserverCode.run_push bytesWord target]
            rfl
    _ =
      (Structured.ObserverSemantics.Code.run [.push cellWord] afterBytes).bind
        (Structured.ObserverSemantics.Code.run
          [.op .mload, .op .sub, .push cellWord, .op .mstore]) := by
              rw [Structured.ObserverSemantics.Code.run_cons_eq_run_single_bind]
    _ =
      Structured.ObserverSemantics.Code.run
        [.op .mload, .op .sub, .push cellWord, .op .mstore]
        afterCell := by
          rw [ObserverCode.run_push cellWord afterBytes]
          rfl
    _ =
      (Structured.ObserverSemantics.Code.run [.op .mload] afterCell).bind
        (Structured.ObserverSemantics.Code.run
          [.op .sub, .push cellWord, .op .mstore]) := by
              rw [Structured.ObserverSemantics.Code.run_cons_eq_run_single_bind]
    _ =
      Structured.ObserverSemantics.Code.run
        [.op .sub, .push cellWord, .op .mstore] afterLoad := by
          rw [ObserverCode.run_mload hAfterCellStack hLoad]
          rfl
    _ =
      (Structured.ObserverSemantics.Code.run [.op .sub] afterLoad).bind
        (Structured.ObserverSemantics.Code.run
          [.push cellWord, .op .mstore]) := by
              rw [Structured.ObserverSemantics.Code.run_cons_eq_run_single_bind]
    _ =
      Structured.ObserverSemantics.Code.run
        [.push cellWord, .op .mstore] afterSub := by
          rw [ObserverCode.run_sub hAfterLoadStack]
          rw [hPriorWord]
          rfl
    _ =
      (Structured.ObserverSemantics.Code.run
          [.push cellWord] afterSub).bind
        (Structured.ObserverSemantics.Code.run [.op .mstore]) := by
              rw [Structured.ObserverSemantics.Code.run_cons_eq_run_single_bind]
    _ =
      Structured.ObserverSemantics.Code.run [.op .mstore]
        afterCellStore := by
          rw [ObserverCode.run_push cellWord afterSub]
          rfl
    _ = .ok targetFinal := by
      exact ObserverCode.run_mstore hAfterCellStoreStack

theorem scratchFrameRelease_backward {transcript : Trace}
    {contract : MemoryContract.Contract}
    {frameWords depth : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {sourceMachine : EvmYul.MachineState}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hBudget :
      AllocationObserverRelation.Frame.Budget config depth)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady
        config (depth + 1) target)
    (hMachine :
      Compiler.MemoryRelation.MachineRel contract sourceMachine
        target.source.evm.toMachineState)
    (hRun :
      Structured.ObserverSemantics.Code.run
          (AllocationSupport.scratchFrameReleaseCode config) target =
        .ok targetFinal) :
    targetFinal.source.evm.stack = target.source.evm.stack ∧
      Compiler.MemoryRelation.MachineRel contract sourceMachine
        targetFinal.source.evm.toMachineState ∧
      AllocationObserverRelation.Frame.AllocatorReady config depth
        targetFinal := by
  obtain
    ⟨expected, hExpectedRun, hExpectedStack, hExpectedMachine,
      hExpectedReady⟩ :=
    scratchFrameRelease_forward hConfig hBudget hReady hMachine
  rw [hExpectedRun] at hRun
  cases hRun
  exact ⟨hExpectedStack, hExpectedMachine, hExpectedReady⟩

end Frame

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
    {stackOffset frameBase planDepth depth : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {name : Locals.Name} {value : Word} {op : Structured.BasicOp}
    (hRel :
      AllocationObserverRelation.StateRel contract plan live
        stackOffset frameBase source target)
    (hLive : name ∈ live)
    (hLocation :
      Locals.Allocation.Plan.location? plan name =
        some (Locals.Allocation.LocalLocation.stack planDepth))
    (hCurrentDepth :
      Locals.Layout.lookupDepth? name
          (AllocationObserverRelation.currentStackOrder plan live) =
        some (depth + 1))
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
    rw [hRel.core.store.stack_at hLive hLocation hCurrentDepth, hSource]
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
    {stackOffset frameBase planDepth depth : Nat}
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
        some (Locals.Allocation.LocalLocation.stack planDepth))
    (hCurrentDepth :
      Locals.Layout.lookupDepth? name
          (AllocationObserverRelation.currentStackOrder plan live) =
        some (depth + 1))
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
    rw [hRel.core.store.stack_at hLive hLocation hCurrentDepth, hSource]
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
        source targetFinal ∧
      targetFinal.source.evm.stack =
        value :: target.source.evm.stack := by
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
  refine ⟨targetFinal, ?_, ?_, hFinalRel, rfl⟩
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
      source targetFinal ∧
    targetFinal.source.evm.stack =
      value :: target.source.evm.stack := by
  obtain
      ⟨expected, hSourceEval, hExpectedRun, hExpectedRel, hExpectedStack⟩ :=
    scratchVar_forward hRel hLive hLocation hSource hOp
  rw [hExpectedRun] at hRun
  cases hRun
  exact ⟨hSourceEval, hExpectedRel, hExpectedStack⟩

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
      obtain
          ⟨targetFinal, hSourceEval, hTargetRun, hTargetRel, _hStack⟩ :=
        scratchVar_forward hRel hLive hLocation hSource
          (by
            simpa [Nat.add_assoc] using hDup)
      exact ⟨targetFinal, hSourceEval, hTargetRun, hTargetRel⟩

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
      obtain ⟨hSourceEval, hTargetRel, _hStack⟩ :=
        scratchVar_backward hRel hLive hLocation hSource
          (by
            simpa [Nat.add_assoc] using hDup)
          hRun
      exact ⟨hSourceEval, hTargetRel⟩

theorem scratchAssignTop_forward_live {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords slot : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {name : Locals.Name} {value : Word} {rest : List Word}
    {op : Structured.BasicOp}
    {reservation : MemoryContract.ScratchReservation}
    (hRel :
      AllocationObserverRelation.ScratchStateRel contract plan beforeLive
        (stackOffset + 1) frameBase frameDepth frameWords source target)
    (hStack : target.source.evm.stack = value :: rest)
    (hWF : plan.WellFormed)
    (hAfter :
      ∀ other, other ∈ afterLive →
        other = name ∨ other ∈ beforeLive)
    (hStackOrder :
      AllocationObserverRelation.currentStackOrder plan afterLive =
        AllocationObserverRelation.currentStackOrder plan beforeLive)
    (hNameAfter : name ∈ afterLive)
    (hLocation :
      plan.location? name =
        some (Locals.Allocation.LocalLocation.scratch slot))
    (hAssignedBound : slot < frameWords)
    (hReservation : contract.scratch? = some reservation)
    (hRegion :
      reservation.containsRegion
        (AllocationObserverRelation.scratchAddress frameBase slot) 1)
    (hOp :
      Locals.StackOp.dup? (stackOffset + frameDepth + 2) = some op) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run
          [ .op op,
            .push (AllocationSupport.slotOffset slot),
            .op .add,
            .op .mstore ] target =
        .ok targetFinal ∧
      AllocationObserverRelation.ScratchStateRel contract plan afterLive
        stackOffset frameBase frameDepth frameWords
        (source.withSource (source.source.insert name value))
        targetFinal := by
  let frameWord := EvmYul.UInt256.ofNat frameBase
  let offsetWord := AllocationSupport.slotOffset slot
  let address := EvmYul.UInt256.add offsetWord frameWord
  let afterDup :=
    AllocationObserverRelation.StateRel.pushTarget frameWord target
  let afterPush :=
    AllocationObserverRelation.StateRel.pushTargetBy
      33 offsetWord afterDup
  let afterAdd :=
    AllocationObserverRelation.StateRel.contractTargetBy
      1 address (value :: rest) afterPush
  let targetFinal :=
    AllocationObserverRelation.StateRel.mstoreTarget
      address value rest afterAdd
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
      AllocationObserverRelation.ScratchStateRel contract plan beforeLive
        (stackOffset + 2) frameBase frameDepth frameWords
        source afterDup := by
    exact hRel.push_target frameWord
  have hAfterPushRel :
      AllocationObserverRelation.ScratchStateRel contract plan beforeLive
        (stackOffset + 3) frameBase frameDepth frameWords
        source afterPush := by
    exact hAfterDupRel.push_target_by 33 offsetWord
  have hAfterPushStack :
      afterPush.source.evm.stack =
        offsetWord :: frameWord :: value :: rest := by
    simp [afterPush, afterDup,
      AllocationObserverRelation.StateRel.pushTarget,
      AllocationObserverRelation.StateRel.pushTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, hStack]
  have hAfterAddRel :
      AllocationObserverRelation.ScratchStateRel contract plan beforeLive
        (stackOffset + 2) frameBase frameDepth frameWords
        source afterAdd := by
    exact
      hAfterPushRel.contract_target_by
        (value := address) hAfterPushStack 1
  have hAfterAddStack :
      afterAdd.source.evm.stack =
        address :: value :: rest := by
    rfl
  have hAfterAddStack' :
      afterAdd.source.evm.stack =
        EvmYul.UInt256.ofNat
            (AllocationObserverRelation.scratchAddress frameBase slot) ::
          value :: rest := by
    simpa [hAddress] using hAfterAddStack
  have hFinalRel :
      AllocationObserverRelation.ScratchStateRel contract plan afterLive
        stackOffset frameBase frameDepth frameWords
        (source.withSource (source.source.insert name value))
        targetFinal := by
    simpa [targetFinal, hAddress] using
      (hAfterAddRel.assign_scratch_live hWF hAfter hStackOrder
        hNameAfter hLocation
        hAssignedBound hReservation hRegion hAfterAddStack')
  have hFramePointer :
      target.source.evm.stack[stackOffset + frameDepth + 1]? =
        some frameWord := by
    simpa [frameWord,
      show stackOffset + 1 + frameDepth =
        stackOffset + frameDepth + 1 by omega] using hRel.framePointer
  refine ⟨targetFinal, ?_, hFinalRel⟩
  calc
    Structured.ObserverSemantics.Code.run
        [ .op op,
          .push offsetWord,
          .op .add,
          .op .mstore ] target =
      (Structured.ObserverSemantics.Code.run [.op op] target).bind
        (Structured.ObserverSemantics.Code.run
          [ .push offsetWord, .op .add, .op .mstore ]) := by
            rw [Structured.ObserverSemantics.Code.run_cons_eq_run_single_bind]
    _ =
      Structured.ObserverSemantics.Code.run
        [ .push offsetWord, .op .add, .op .mstore ] afterDup := by
          rw [ObserverCode.run_dup
            (by simpa [Nat.add_assoc] using hOp) hFramePointer]
          rfl
    _ =
      (Structured.ObserverSemantics.Code.run
          [.push offsetWord] afterDup).bind
        (Structured.ObserverSemantics.Code.run
          [.op .add, .op .mstore]) := by
            rw [Structured.ObserverSemantics.Code.run_cons_eq_run_single_bind]
    _ =
      Structured.ObserverSemantics.Code.run
        [.op .add, .op .mstore] afterPush := by
          rw [ObserverCode.run_push offsetWord afterDup]
          rfl
    _ =
      (Structured.ObserverSemantics.Code.run [.op .add] afterPush).bind
        (Structured.ObserverSemantics.Code.run [.op .mstore]) := by
          rw [Structured.ObserverSemantics.Code.run_cons_eq_run_single_bind]
    _ =
      Structured.ObserverSemantics.Code.run [.op .mstore] afterAdd := by
        rw [ObserverCode.run_add hAfterPushStack]
        rfl
    _ = .ok targetFinal := by
      exact ObserverCode.run_mstore hAfterAddStack

theorem scratchAssignTop_backward_live {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords slot : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target targetFinal :
      Structured.ObserverSemantics.State transcript}
    {name : Locals.Name} {value : Word} {rest : List Word}
    {op : Structured.BasicOp}
    {reservation : MemoryContract.ScratchReservation}
    (hRel :
      AllocationObserverRelation.ScratchStateRel contract plan beforeLive
        (stackOffset + 1) frameBase frameDepth frameWords source target)
    (hStack : target.source.evm.stack = value :: rest)
    (hWF : plan.WellFormed)
    (hAfter :
      ∀ other, other ∈ afterLive →
        other = name ∨ other ∈ beforeLive)
    (hStackOrder :
      AllocationObserverRelation.currentStackOrder plan afterLive =
        AllocationObserverRelation.currentStackOrder plan beforeLive)
    (hNameAfter : name ∈ afterLive)
    (hLocation :
      plan.location? name =
        some (Locals.Allocation.LocalLocation.scratch slot))
    (hAssignedBound : slot < frameWords)
    (hReservation : contract.scratch? = some reservation)
    (hRegion :
      reservation.containsRegion
        (AllocationObserverRelation.scratchAddress frameBase slot) 1)
    (hOp :
      Locals.StackOp.dup? (stackOffset + frameDepth + 2) = some op)
    (hRun :
      Structured.ObserverSemantics.Code.run
          [ .op op,
            .push (AllocationSupport.slotOffset slot),
            .op .add,
            .op .mstore ] target =
        .ok targetFinal) :
    AllocationObserverRelation.ScratchStateRel contract plan afterLive
      stackOffset frameBase frameDepth frameWords
      (source.withSource (source.source.insert name value))
      targetFinal := by
  obtain ⟨expected, hExpectedRun, hExpectedRel⟩ :=
    scratchAssignTop_forward_live hRel hStack hWF hAfter hStackOrder
      hNameAfter
      hLocation hAssignedBound hReservation hRegion hOp
  rw [hExpectedRun] at hRun
  cases hRun
  exact hExpectedRel

theorem scratchAssignTop_forward_of_storeTopSlotCode?_live
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords slot : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {name : Locals.Name} {value : Word} {rest : List Word}
    {code : Structured.Code}
    {reservation : MemoryContract.ScratchReservation}
    (hRel :
      AllocationObserverRelation.ScratchStateRel contract plan beforeLive
        (stackOffset + 1) frameBase frameDepth frameWords source target)
    (hStack : target.source.evm.stack = value :: rest)
    (hWF : plan.WellFormed)
    (hAfter :
      ∀ other, other ∈ afterLive →
        other = name ∨ other ∈ beforeLive)
    (hStackOrder :
      AllocationObserverRelation.currentStackOrder plan afterLive =
        AllocationObserverRelation.currentStackOrder plan beforeLive)
    (hNameAfter : name ∈ afterLive)
    (hLocation :
      plan.location? name =
        some (Locals.Allocation.LocalLocation.scratch slot))
    (hAssignedBound : slot < frameWords)
    (hReservation : contract.scratch? = some reservation)
    (hRegion :
      reservation.containsRegion
        (AllocationObserverRelation.scratchAddress frameBase slot) 1)
    (hCode :
      AllocationSupport.storeTopSlotCode?
          (stackOffset + frameDepth + 1) slot =
        some code) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run code target =
        .ok targetFinal ∧
      AllocationObserverRelation.ScratchStateRel contract plan afterLive
        stackOffset frameBase frameDepth frameWords
        (source.withSource (source.source.insert name value))
        targetFinal := by
  cases hDup :
      Locals.StackOp.dup?
        ((stackOffset + frameDepth + 1) + 1) with
  | none =>
      simp [AllocationSupport.storeTopSlotCode?,
        AllocationSupport.slotAddressCode?,
        AllocationSupport.dupCode?, hDup] at hCode
  | some op =>
      simp [AllocationSupport.storeTopSlotCode?,
        AllocationSupport.slotAddressCode?,
        AllocationSupport.dupCode?, hDup] at hCode
      subst code
      exact
        scratchAssignTop_forward_live hRel hStack hWF hAfter hStackOrder
          hNameAfter hLocation hAssignedBound hReservation hRegion
          (by simpa [Nat.add_assoc] using hDup)

theorem scratchAssignTop_backward_of_storeTopSlotCode?_live
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords slot : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target targetFinal :
      Structured.ObserverSemantics.State transcript}
    {name : Locals.Name} {value : Word} {rest : List Word}
    {code : Structured.Code}
    {reservation : MemoryContract.ScratchReservation}
    (hRel :
      AllocationObserverRelation.ScratchStateRel contract plan beforeLive
        (stackOffset + 1) frameBase frameDepth frameWords source target)
    (hStack : target.source.evm.stack = value :: rest)
    (hWF : plan.WellFormed)
    (hAfter :
      ∀ other, other ∈ afterLive →
        other = name ∨ other ∈ beforeLive)
    (hStackOrder :
      AllocationObserverRelation.currentStackOrder plan afterLive =
        AllocationObserverRelation.currentStackOrder plan beforeLive)
    (hNameAfter : name ∈ afterLive)
    (hLocation :
      plan.location? name =
        some (Locals.Allocation.LocalLocation.scratch slot))
    (hAssignedBound : slot < frameWords)
    (hReservation : contract.scratch? = some reservation)
    (hRegion :
      reservation.containsRegion
        (AllocationObserverRelation.scratchAddress frameBase slot) 1)
    (hCode :
      AllocationSupport.storeTopSlotCode?
          (stackOffset + frameDepth + 1) slot =
        some code)
    (hRun :
      Structured.ObserverSemantics.Code.run code target =
        .ok targetFinal) :
    AllocationObserverRelation.ScratchStateRel contract plan afterLive
      stackOffset frameBase frameDepth frameWords
      (source.withSource (source.source.insert name value))
      targetFinal := by
  obtain ⟨expected, hExpectedRun, hExpectedRel⟩ :=
    scratchAssignTop_forward_of_storeTopSlotCode?_live
      hRel hStack hWF hAfter hStackOrder hNameAfter hLocation hAssignedBound
      hReservation hRegion hCode
  rw [hExpectedRun] at hRun
  cases hRun
  exact hExpectedRel

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

theorem literal_forward_result {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (value : Word)
    (hRel :
      AllocationObserverRelation.StateRel contract plan live
        stackOffset frameBase source target) :
    ∃ targetFinal,
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          (.lit value : Functions.Expr 1) source =
        .ok (source, [value]) ∧
      Structured.ObserverSemantics.Code.run [.push value] target =
        .ok targetFinal ∧
      AllocationObserverRelation.ExprResultRel contract plan live
        stackOffset frameBase 1 source target targetFinal [value] := by
  obtain ⟨hSource, hTarget, hFinalRel⟩ :=
    literal_forward value hRel
  refine
    ⟨AllocationObserverRelation.StateRel.pushTargetBy 33 value target,
      hSource, hTarget, ?_⟩
  exact ⟨by simpa using hFinalRel, rfl, rfl⟩

theorem literal_forward_result_scratch {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (value : Word)
    (hRel :
      AllocationObserverRelation.ScratchStateRel contract plan live
        stackOffset frameBase frameDepth frameWords source target) :
    ∃ targetFinal,
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          (.lit value : Functions.Expr 1) source =
        .ok (source, [value]) ∧
      Structured.ObserverSemantics.Code.run [.push value] target =
        .ok targetFinal ∧
      AllocationObserverRelation.ScratchExprResultRel contract plan live
        stackOffset frameBase frameDepth frameWords 1
        source target targetFinal [value] := by
  let targetFinal :=
    AllocationObserverRelation.StateRel.pushTargetBy 33 value target
  exact
    ⟨targetFinal, rfl, ObserverCode.run_push value target,
      hRel.push_target_by 33 value, rfl, rfl⟩

theorem stackVar_forward_result {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase planDepth depth : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {name : Locals.Name} {value : Word} {op : Structured.BasicOp}
    (hRel :
      AllocationObserverRelation.StateRel contract plan live
        stackOffset frameBase source target)
    (hLive : name ∈ live)
    (hLocation :
      plan.location? name = some (.stack planDepth))
    (hCurrentDepth :
      Locals.Layout.lookupDepth? name
          (AllocationObserverRelation.currentStackOrder plan live) =
        some (depth + 1))
    (hSource : source.source.vars name = some value)
    (hOp :
      Locals.StackOp.dup? (stackOffset + depth + 1) = some op) :
    ∃ targetFinal,
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          (.var name : Functions.Expr 1) source =
        .ok (source, [value]) ∧
      Structured.ObserverSemantics.Code.run [.op op] target =
        .ok targetFinal ∧
      AllocationObserverRelation.ExprResultRel contract plan live
        stackOffset frameBase 1 source target targetFinal [value] := by
  obtain ⟨hSourceEval, hTargetRun, hFinalRel⟩ :=
    stackVar_forward hRel hLive hLocation hCurrentDepth hSource hOp
  refine
    ⟨AllocationObserverRelation.StateRel.pushTarget value target,
      hSourceEval, hTargetRun, ?_⟩
  exact ⟨by simpa using hFinalRel, rfl, rfl⟩

theorem stackVar_forward_result_scratch {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords planDepth depth : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {name : Locals.Name} {value : Word} {op : Structured.BasicOp}
    (hRel :
      AllocationObserverRelation.ScratchStateRel contract plan live
        stackOffset frameBase frameDepth frameWords source target)
    (hLive : name ∈ live)
    (hLocation :
      plan.location? name = some (.stack planDepth))
    (hCurrentDepth :
      Locals.Layout.lookupDepth? name
          (AllocationObserverRelation.currentStackOrder plan live) =
        some (depth + 1))
    (hSource : source.source.vars name = some value)
    (hOp :
      Locals.StackOp.dup? (stackOffset + depth + 1) = some op) :
    ∃ targetFinal,
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          (.var name : Functions.Expr 1) source =
        .ok (source, [value]) ∧
      Structured.ObserverSemantics.Code.run [.op op] target =
        .ok targetFinal ∧
      AllocationObserverRelation.ScratchExprResultRel contract plan live
        stackOffset frameBase frameDepth frameWords 1
        source target targetFinal [value] := by
  have hTargetGet :
      target.source.evm.stack[stackOffset + depth]? = some value := by
    rw [hRel.base.core.store.stack_at
      hLive hLocation hCurrentDepth, hSource]
  let targetFinal :=
    AllocationObserverRelation.StateRel.pushTarget value target
  refine
    ⟨targetFinal, ?_, ObserverCode.run_dup hOp hTargetGet,
      hRel.push_target value, rfl, rfl⟩
  simp [Functions.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.eval,
    Functions.ObserverSemantics.stateModel,
    Locals.ObserverSemantics.stateModel,
    Locals.Source.Effectful.StateModel.vars, hSource]

theorem scratchVar_forward_result {transcript : Trace}
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
      plan.location? name = some (.scratch slot))
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
      AllocationObserverRelation.ScratchExprResultRel contract plan live
        stackOffset frameBase frameDepth frameWords 1
        source target targetFinal [value] := by
  obtain
      ⟨targetFinal, hSourceEval, hTargetRun, hFinalRel, hStack⟩ :=
    scratchVar_forward hRel hLive hLocation hSource hOp
  exact
    ⟨targetFinal, hSourceEval, hTargetRun,
      ⟨by simpa using hFinalRel, rfl, by simpa using hStack⟩⟩

theorem gas_forward_result_scratch {transcript : Trace}
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
      AllocationObserverRelation.ScratchExprResultRel contract plan live
        stackOffset frameBase frameDepth frameWords 1
        sourceConsumed target targetFinal [value] := by
  obtain ⟨targetConsumed, hTargetConsume, hConsumedRel⟩ :=
    hRel.consume_forward hConsume
  let targetFinal :=
    AllocationObserverRelation.StateRel.pushTarget value targetConsumed
  have hTargetSource :
      targetConsumed.source = target.source :=
    Simulation.ResourceReplay.consume?_source hTargetConsume
  refine
    ⟨targetFinal,
      Functions.ObserverSemantics.expr_eval_gas hConsume,
      ObserverCode.run_gas hTargetConsume,
      hConsumedRel.push_target value, rfl, ?_⟩
  simp [targetFinal,
    AllocationObserverRelation.StateRel.pushTarget,
    AllocationObserverRelation.StateRel.pushTargetBy,
    Simulation.ResourceReplay.State.withSource,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC, hTargetSource]

theorem msize_forward_result_scratch {transcript : Trace}
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
      AllocationObserverRelation.ScratchExprResultRel contract plan live
        stackOffset frameBase frameDepth frameWords 1
        sourceConsumed target targetFinal [value] := by
  obtain ⟨targetConsumed, hTargetConsume, hConsumedRel⟩ :=
    hRel.consume_forward hConsume
  let targetFinal :=
    AllocationObserverRelation.StateRel.pushTarget value targetConsumed
  have hTargetSource :
      targetConsumed.source = target.source :=
    Simulation.ResourceReplay.consume?_source hTargetConsume
  refine
    ⟨targetFinal,
      Functions.ObserverSemantics.expr_eval_msize hConsume,
      ObserverCode.run_msize hTargetConsume,
      hConsumedRel.push_target value, rfl, ?_⟩
  simp [targetFinal,
    AllocationObserverRelation.StateRel.pushTarget,
    AllocationObserverRelation.StateRel.pushTargetBy,
    Simulation.ResourceReplay.State.withSource,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC, hTargetSource]

/--
Literal preservation through the representation-neutral activation relation.
-/
theorem literal_forward_result_activation {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (value : Word)
    (hRel :
      AllocationObserverRelation.ActivationStateRel contract plan live
        stackOffset frameBase mode source target) :
    ∃ targetFinal,
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          (.lit value : Functions.Expr 1) source =
        .ok (source, [value]) ∧
      Structured.ObserverSemantics.Code.run [.push value] target =
        .ok targetFinal ∧
      AllocationObserverRelation.ActivationExprResultRel
        contract plan live stackOffset frameBase 1 mode
        source target targetFinal [value] := by
  let targetFinal :=
    AllocationObserverRelation.StateRel.pushTargetBy 33 value target
  exact
    ⟨targetFinal, rfl, ObserverCode.run_push value target,
      hRel.push_target_by 33 value, rfl, rfl⟩

/--
Stack-local reads preserve either activation representation.
-/
theorem stackVar_forward_result_activation {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase planDepth depth : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {name : Locals.Name} {value : Word} {op : Structured.BasicOp}
    (hRel :
      AllocationObserverRelation.ActivationStateRel contract plan live
        stackOffset frameBase mode source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hCurrentDepth :
      Locals.Layout.lookupDepth? name
          (AllocationObserverRelation.currentStackOrder plan live) =
        some (depth + 1))
    (hSource : source.source.vars name = some value)
    (hOp :
      Locals.StackOp.dup? (stackOffset + depth + 1) = some op) :
    ∃ targetFinal,
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          (.var name : Functions.Expr 1) source =
        .ok (source, [value]) ∧
      Structured.ObserverSemantics.Code.run [.op op] target =
        .ok targetFinal ∧
      AllocationObserverRelation.ActivationExprResultRel
        contract plan live stackOffset frameBase 1 mode
        source target targetFinal [value] := by
  have hTargetGet :
      target.source.evm.stack[stackOffset + depth]? = some value := by
    rw [hRel.base.core.store.stack_at
      hLive hLocation hCurrentDepth, hSource]
  let targetFinal :=
    AllocationObserverRelation.StateRel.pushTarget value target
  refine
    ⟨targetFinal, ?_, ObserverCode.run_dup hOp hTargetGet,
      hRel.push_target value, rfl, rfl⟩
  simp [Functions.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.eval,
    Functions.ObserverSemantics.stateModel,
    Locals.ObserverSemantics.stateModel,
    Locals.Source.Effectful.StateModel.vars, hSource]

/--
Scratch-local reads are admitted only by the scratch constructor of the
activation relation.
-/
theorem scratchVar_forward_result_activation {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords slot : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {name : Locals.Name} {value : Word} {op : Structured.BasicOp}
    (hRel :
      AllocationObserverRelation.ActivationStateRel contract plan live
        stackOffset frameBase (.scratch frameDepth frameWords)
        source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot))
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
      AllocationObserverRelation.ActivationExprResultRel
        contract plan live stackOffset frameBase 1
        (.scratch frameDepth frameWords)
        source target targetFinal [value] := by
  cases hRel with
  | scratch state =>
      obtain
          ⟨targetFinal, hSourceEval, hTargetRun, hFinalRel⟩ :=
        scratchVar_forward_result
          state hLive hLocation hSource hOp
      exact
        ⟨targetFinal, hSourceEval, hTargetRun,
          .scratch hFinalRel.state, hFinalRel.valuesLength,
          hFinalRel.stack⟩

/--
Observer preservation through either activation representation.
-/
theorem observer_forward_result_activation {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {kind : Assembly.ResourceObserver} {op : Structured.BasicOp}
    {value : Word}
    {source sourceConsumed :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hRel :
      AllocationObserverRelation.ActivationStateRel contract plan live
        stackOffset frameBase mode source target)
    (hOp :
      (kind = .gas ∧ op = .gas) ∨
        (kind = .msize ∧ op = .msize))
    (hConsume :
      Simulation.ResourceReplay.consume? kind source =
        some (value, sourceConsumed)) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run [.op op] target =
        .ok targetFinal ∧
      AllocationObserverRelation.ActivationExprResultRel
        contract plan live stackOffset frameBase 1 mode
        sourceConsumed target targetFinal [value] := by
  obtain ⟨targetConsumed, hTargetConsume, hConsumedRel⟩ :=
    hRel.consume_forward hConsume
  let targetFinal :=
    AllocationObserverRelation.StateRel.pushTarget value targetConsumed
  have hTargetSource :
      targetConsumed.source = target.source :=
    Simulation.ResourceReplay.consume?_source hTargetConsume
  rcases hOp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine
      ⟨targetFinal, ObserverCode.run_gas hTargetConsume,
        hConsumedRel.push_target value, rfl, ?_⟩
    simp [targetFinal,
      AllocationObserverRelation.StateRel.pushTarget,
      AllocationObserverRelation.StateRel.pushTargetBy,
      Simulation.ResourceReplay.State.withSource,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, hTargetSource]
  · refine
      ⟨targetFinal, ObserverCode.run_msize hTargetConsume,
        hConsumedRel.push_target value, rfl, ?_⟩
    simp [targetFinal,
      AllocationObserverRelation.StateRel.pushTarget,
      AllocationObserverRelation.StateRel.pushTargetBy,
      Simulation.ResourceReplay.State.withSource,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, hTargetSource]

theorem literal_backward_result {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
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
    AllocationObserverRelation.ExprResultRel contract plan live
      stackOffset frameBase 1 source target targetFinal [value] := by
  rw [ObserverCode.run_push value target] at hRun
  cases hRun
  exact
    ⟨rfl,
      ⟨by simpa using hRel.push_target_by 33 value, rfl, rfl⟩⟩

theorem literal_backward_result_scratch {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
    (value : Word)
    (hRel :
      AllocationObserverRelation.ScratchStateRel contract plan live
        stackOffset frameBase frameDepth frameWords source target)
    (hRun :
      Structured.ObserverSemantics.Code.run [.push value] target =
        .ok targetFinal) :
    Functions.Source.Effectful.Expr.eval
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        (.lit value : Functions.Expr 1) source =
      .ok (source, [value]) ∧
    AllocationObserverRelation.ScratchExprResultRel contract plan live
      stackOffset frameBase frameDepth frameWords 1
      source target targetFinal [value] := by
  obtain ⟨expected, hSource, hExpectedRun, hExpectedRel⟩ :=
    literal_forward_result_scratch value hRel
  rw [hExpectedRun] at hRun
  cases hRun
  exact ⟨hSource, hExpectedRel⟩

theorem stackVar_backward_result {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase planDepth depth : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
    {name : Locals.Name} {value : Word} {op : Structured.BasicOp}
    (hRel :
      AllocationObserverRelation.StateRel contract plan live
        stackOffset frameBase source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hCurrentDepth :
      Locals.Layout.lookupDepth? name
          (AllocationObserverRelation.currentStackOrder plan live) =
        some (depth + 1))
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
    AllocationObserverRelation.ExprResultRel contract plan live
      stackOffset frameBase 1 source target targetFinal [value] := by
  have hTargetGet :
      target.source.evm.stack[stackOffset + depth]? = some value := by
    rw [hRel.core.store.stack_at hLive hLocation hCurrentDepth, hSource]
  rw [ObserverCode.run_dup hOp hTargetGet] at hRun
  cases hRun
  refine ⟨?_, ⟨by simpa using hRel.push_target value, rfl, rfl⟩⟩
  simp [Functions.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.eval,
    Functions.ObserverSemantics.stateModel,
    Locals.ObserverSemantics.stateModel,
    Locals.Source.Effectful.StateModel.vars, hSource]

theorem stackVar_backward_result_scratch {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords planDepth depth : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
    {name : Locals.Name} {value : Word} {op : Structured.BasicOp}
    (hRel :
      AllocationObserverRelation.ScratchStateRel contract plan live
        stackOffset frameBase frameDepth frameWords source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hCurrentDepth :
      Locals.Layout.lookupDepth? name
          (AllocationObserverRelation.currentStackOrder plan live) =
        some (depth + 1))
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
    AllocationObserverRelation.ScratchExprResultRel contract plan live
      stackOffset frameBase frameDepth frameWords 1
      source target targetFinal [value] := by
  obtain ⟨expected, hSourceEval, hExpectedRun, hExpectedRel⟩ :=
    stackVar_forward_result_scratch
      hRel hLive hLocation hCurrentDepth hSource hOp
  rw [hExpectedRun] at hRun
  cases hRun
  exact ⟨hSourceEval, hExpectedRel⟩

theorem scratchVar_backward_result {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords slot : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
    {name : Locals.Name} {value : Word} {op : Structured.BasicOp}
    (hRel :
      AllocationObserverRelation.ScratchStateRel contract plan live
        stackOffset frameBase frameDepth frameWords source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot))
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
    AllocationObserverRelation.ScratchExprResultRel contract plan live
      stackOffset frameBase frameDepth frameWords 1
      source target targetFinal [value] := by
  obtain ⟨hSourceEval, hFinalRel, hStack⟩ :=
    scratchVar_backward hRel hLive hLocation hSource hOp hRun
  exact
    ⟨hSourceEval,
      ⟨by simpa using hFinalRel, rfl, by simpa using hStack⟩⟩

theorem gas_backward_result_scratch {transcript : Trace}
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
      AllocationObserverRelation.ScratchExprResultRel contract plan live
        stackOffset frameBase frameDepth frameWords 1
        sourceConsumed target targetFinal [value] := by
  obtain ⟨value, targetConsumed, hTargetConsume, rfl⟩ :=
    ObserverCode.run_gas_backward hRun
  obtain ⟨sourceConsumed, hSourceConsume, hConsumedRel⟩ :=
    hRel.consume_backward hTargetConsume
  have hTargetSource :
      targetConsumed.source = target.source :=
    Simulation.ResourceReplay.consume?_source hTargetConsume
  refine
    ⟨value, sourceConsumed,
      Functions.ObserverSemantics.expr_eval_gas hSourceConsume,
      hConsumedRel.push_target value, rfl, ?_⟩
  simp [AllocationObserverRelation.StateRel.pushTarget,
    AllocationObserverRelation.StateRel.pushTargetBy,
    Simulation.ResourceReplay.State.withSource,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC, hTargetSource]

theorem msize_backward_result_scratch {transcript : Trace}
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
      AllocationObserverRelation.ScratchExprResultRel contract plan live
        stackOffset frameBase frameDepth frameWords 1
        sourceConsumed target targetFinal [value] := by
  obtain ⟨value, targetConsumed, hTargetConsume, rfl⟩ :=
    ObserverCode.run_msize_backward hRun
  obtain ⟨sourceConsumed, hSourceConsume, hConsumedRel⟩ :=
    hRel.consume_backward hTargetConsume
  have hTargetSource :
      targetConsumed.source = target.source :=
    Simulation.ResourceReplay.consume?_source hTargetConsume
  refine
    ⟨value, sourceConsumed,
      Functions.ObserverSemantics.expr_eval_msize hSourceConsume,
      hConsumedRel.push_target value, rfl, ?_⟩
  simp [AllocationObserverRelation.StateRel.pushTarget,
    AllocationObserverRelation.StateRel.pushTargetBy,
    Simulation.ResourceReplay.State.withSource,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC, hTargetSource]

end Expr

end AllocationObserverPreservation
end Functions
end EvmCompiler
