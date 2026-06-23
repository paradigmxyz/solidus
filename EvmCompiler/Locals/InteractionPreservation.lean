import EvmCompiler.Locals.InteractionSemantics
import EvmCompiler.Locals.Compiler
import EvmCompiler.Locals.PrimitivePreservation
import EvmCompiler.Expressions.InteractionSemantics
import EvmCompiler.Structured.InteractionPrimitivePreservation

namespace EvmCompiler
namespace Locals
namespace InteractionPreservation

private theorem take_succ_getLast?_getD_of_getElem?_eq_some
    {α : Type} [Inhabited α] {values : List α}
    {index : Nat} {value : α}
    (hGet : values[index]? = some value) :
    (values.take (index + 1)).getLast?.getD default = value := by
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

private theorem take_succ_getLast!_of_getElem?_eq_some
    {α : Type} [Inhabited α] {values : List α}
    {index : Nat} {value : α}
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
    (hOp : StackOp.dup? depth = some op) :
    op.toPrimOp.continuingStep? = some (.dup depth) := by
  match depth with
  | 0 => simp [StackOp.dup?] at hOp
  | 1 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 2 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 3 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 4 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 5 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 6 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 7 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 8 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 9 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 10 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 11 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 12 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 13 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 14 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 15 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 16 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | depth + 17 => simp [StackOp.dup?] at hOp

private theorem dup?_openStep
    {depth : Nat} {op : Structured.BasicOp}
    (hOp : StackOp.dup? depth = some op)
    (state : EVMState) :
    Assembly.InteractionSemantics.PrimOp.openStep
        op.toPrimOp state =
      .done ((Assembly.PrimStep.dup depth).run state) := by
  match depth with
  | 0 => simp [StackOp.dup?] at hOp
  | 1 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 2 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 3 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 4 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 5 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 6 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 7 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 8 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 9 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 10 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 11 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 12 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 13 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 14 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 15 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | 16 => simp [StackOp.dup?] at hOp; cases hOp; rfl
  | depth + 17 => simp [StackOp.dup?] at hOp

private theorem swap?_openStep
    {depth : Nat} {op : Structured.BasicOp}
    (hOp : StackOp.swap? depth = some op)
    (state : EVMState) :
    Assembly.InteractionSemantics.PrimOp.openStep
        op.toPrimOp state =
      .done ((Assembly.PrimStep.swap depth).run state) := by
  match depth with
  | 0 => simp [StackOp.swap?] at hOp
  | 1 => simp [StackOp.swap?] at hOp; cases hOp; rfl
  | 2 => simp [StackOp.swap?] at hOp; cases hOp; rfl
  | 3 => simp [StackOp.swap?] at hOp; cases hOp; rfl
  | 4 => simp [StackOp.swap?] at hOp; cases hOp; rfl
  | 5 => simp [StackOp.swap?] at hOp; cases hOp; rfl
  | 6 => simp [StackOp.swap?] at hOp; cases hOp; rfl
  | 7 => simp [StackOp.swap?] at hOp; cases hOp; rfl
  | 8 => simp [StackOp.swap?] at hOp; cases hOp; rfl
  | 9 => simp [StackOp.swap?] at hOp; cases hOp; rfl
  | 10 => simp [StackOp.swap?] at hOp; cases hOp; rfl
  | 11 => simp [StackOp.swap?] at hOp; cases hOp; rfl
  | 12 => simp [StackOp.swap?] at hOp; cases hOp; rfl
  | 13 => simp [StackOp.swap?] at hOp; cases hOp; rfl
  | 14 => simp [StackOp.swap?] at hOp; cases hOp; rfl
  | 15 => simp [StackOp.swap?] at hOp; cases hOp; rfl
  | 16 => simp [StackOp.swap?] at hOp; cases hOp; rfl
  | depth + 17 => simp [StackOp.swap?] at hOp

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
  simp [List.drop_succ_cons, List.append_assoc]

private theorem pop_openStep (state : EVMState) :
    Assembly.InteractionSemantics.PrimOp.openStep
        Structured.BasicOp.pop.toPrimOp state =
      .done (Assembly.PrimStep.pop.run state) := by
  rfl

namespace Code

theorem openRun_push (value : Word) (target : Structured.RunState) :
    Structured.InteractionSemantics.Code.openRun
        [.push value] target =
      .done
        (.ok
          (target.withEVM
            (target.evm.replaceStackAndIncrPC
              (value :: target.evm.stack) (pcΔ := 33)))) := by
  simp [Structured.InteractionSemantics.Code.openRun,
    Structured.EffectSemantics.Control.Code.run,
    Structured.InteractionSemantics.handler,
    Structured.InteractionSemantics.BasicInstr.openStep,
    Structured.InteractionSemantics.BasicInstr.openStepEVM,
    Structured.BasicInstr.step, Assembly.Target.stepInstr,
    Assembly.Target.stepInstrWith, EvmYul.Stack.push,
    Simulation.Interaction.map, Simulation.Interaction.bind_pure,
    Simulation.Interaction.pure]
  rfl

theorem openRun_bindLocals (offset : Nat) (layout : Layout)
    (target : Structured.RunState) :
    Structured.InteractionSemantics.Code.openRun
        [.bindLocals offset layout] target =
      .done (.ok target) := by
  rfl

theorem openRun_add
    {target : Structured.RunState}
    {right left : Word} {rest : List Word}
    (hStack : target.evm.stack = right :: left :: rest) :
    Structured.InteractionSemantics.Code.openRun [.op .add] target =
      .done
        (.ok
          (target.withEVM
            (target.evm.replaceStackAndIncrPC
              (EvmYul.UInt256.add right left :: rest)))) := by
  unfold Structured.InteractionSemantics.Code.openRun
  simp only [Structured.EffectSemantics.Control.Code.run,
    Structured.InteractionSemantics.handler,
    Structured.InteractionSemantics.BasicInstr.openStep,
    Structured.InteractionSemantics.BasicInstr.openStepEVM]
  simp only [Structured.BasicOp.toPrimOp]
  rw [Assembly.InteractionSemantics.PrimOp.openStep_of_continuingStep
    (by rfl : Assembly.PrimOp.add.continuingStep? =
      some (.bin EvmYul.UInt256.add)) (by decide) (by decide)]
  unfold Assembly.PrimStep.run EvmYul.EVM.execBinOp
  rw [hStack]
  rfl

theorem openRun_mstore
    {target : Structured.RunState}
    {address value : Word} {rest : List Word}
    (hStack : target.evm.stack = address :: value :: rest) :
    Structured.InteractionSemantics.Code.openRun [.op .mstore] target =
      .done
        (.ok
          (target.withEVM
            (({ target.evm with
                toMachineState :=
                  target.evm.toMachineState.mstore address value
              }).replaceStackAndIncrPC rest))) := by
  unfold Structured.InteractionSemantics.Code.openRun
  simp only [Structured.EffectSemantics.Control.Code.run,
    Structured.InteractionSemantics.handler,
    Structured.InteractionSemantics.BasicInstr.openStep,
    Structured.InteractionSemantics.BasicInstr.openStepEVM]
  simp only [Structured.BasicOp.toPrimOp]
  rw [Assembly.InteractionSemantics.PrimOp.openStep_of_continuingStep
    (by rfl : Assembly.PrimOp.mstore.continuingStep? =
      some (.binaryMachineState EvmYul.MachineState.mstore))
    (by decide) (by decide)]
  unfold Assembly.PrimStep.run EvmYul.EVM.binaryMachineStateOp
  rw [hStack]
  rfl

theorem openRun_dup
    {target : Structured.RunState}
    {index : Nat} {value : Word} {op : Structured.BasicOp}
    (hOp : StackOp.dup? (index + 1) = some op)
    (hGet : target.evm.stack[index]? = some value) :
    Structured.InteractionSemantics.Code.openRun [.op op] target =
      .done
        (.ok
          (target.withEVM
            (target.evm.replaceStackAndIncrPC
              (value :: target.evm.stack)))) := by
  have hIndex : index < target.evm.stack.length :=
    List.getElem?_eq_some_iff.mp hGet |>.1
  have hDepth : index + 1 ≤ target.evm.stack.length := by
    omega
  have hLast :
      (target.evm.stack.take (index + 1)).getLast?.getD default =
        value :=
    take_succ_getLast?_getD_of_getElem?_eq_some hGet
  have hTakeLength :
      (target.evm.stack.take (index + 1)).length =
        index + 1 := by
    simp [List.length_take, Nat.min_eq_left hDepth]
  unfold Structured.InteractionSemantics.Code.openRun
  simp only [Structured.EffectSemantics.Control.Code.run,
    Structured.InteractionSemantics.handler,
    Structured.InteractionSemantics.BasicInstr.openStep,
    Structured.InteractionSemantics.BasicInstr.openStepEVM]
  rw [dup?_openStep hOp]
  unfold Assembly.PrimStep.run EvmYul.dup
  simp [hTakeLength, hLast, Simulation.Interaction.map,
    Simulation.Interaction.bind_pure, Simulation.Interaction.pure]
  rfl

theorem openRun_pop
    {target : Structured.RunState}
    {value : Word} {rest : List Word}
    (hStack : target.evm.stack = value :: rest) :
    Structured.InteractionSemantics.Code.openRun
        [.op .pop] target =
      .done
        (.ok
          (target.withEVM
            (target.evm.replaceStackAndIncrPC rest))) := by
  have hRun :
      Assembly.PrimStep.pop.run target.evm =
        .ok (target.evm.replaceStackAndIncrPC rest) := by
    unfold Assembly.PrimStep.run
    rw [hStack]
    rfl
  unfold Structured.InteractionSemantics.Code.openRun
  simp only [Structured.EffectSemantics.Control.Code.run,
    Structured.InteractionSemantics.handler,
    Structured.InteractionSemantics.BasicInstr.openStep,
    Structured.InteractionSemantics.BasicInstr.openStepEVM]
  rw [pop_openStep, hRun]
  rfl

theorem openRun_replicate_pop
    (count : Nat) {target : Structured.RunState}
    (hBound : count ≤ target.evm.stack.length) :
    ∃ final,
      Structured.InteractionSemantics.Code.openRun
          (List.replicate count (.op .pop)) target =
        .done (.ok final) ∧
      final.evm.stack = target.evm.stack.drop count ∧
      final.evm.toSharedState = target.evm.toSharedState ∧
      final.returns = target.returns := by
  induction count generalizing target with
  | zero =>
      exact ⟨target, rfl, by simp, rfl, rfl⟩
  | succ count ih =>
      cases hStack : target.evm.stack with
      | nil =>
          simp [hStack] at hBound
      | cons value rest =>
          let middle :=
            target.withEVM
              (target.evm.replaceStackAndIncrPC rest)
          have hMiddleStack :
              middle.evm.stack = rest := by
            simp [middle,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
          have hTailBound :
              count ≤ middle.evm.stack.length := by
            rw [hMiddleStack]
            simpa [hStack] using hBound
          obtain ⟨final, hTailRun, hFinalStack,
              hFinalShared, hFinalReturns⟩ :=
            ih hTailBound
          refine ⟨final, ?_, ?_, ?_, ?_⟩
          · change
              Structured.InteractionSemantics.Code.openRun
                  ([.op .pop] ++
                    List.replicate count (.op .pop)) target =
                .done (.ok final)
            rw [Structured.InteractionSemantics.Code.openRun_append,
              openRun_pop (target := target) (value := value)
                (rest := rest) hStack]
            change
              Structured.InteractionSemantics.Code.openRun
                  (List.replicate count (.op .pop)) middle =
                .done (.ok final)
            exact hTailRun
          · rw [hFinalStack, hMiddleStack]
            simp
          · exact hFinalShared.trans (by
              simp [middle,
                EvmYul.EVM.State.replaceStackAndIncrPC,
                EvmYul.EVM.State.incrPC])
          · exact hFinalReturns.trans (by simp [middle])

theorem openRun_swap
    {target : Structured.RunState}
    {depth : Nat} {value old : Word} {rest : List Word}
    {op : Structured.BasicOp}
    (hOp : StackOp.swap? (depth + 1) = some op)
    (hGet : rest[depth]? = some old)
    (hStack : target.evm.stack = value :: rest) :
    Structured.InteractionSemantics.Code.openRun [.op op] target =
      .done
        (.ok
          (target.withEVM
            (target.evm.replaceStackAndIncrPC
              (old :: rest.set depth value)))) := by
  have hDepth : depth < rest.length :=
    List.getElem?_eq_some_iff.mp hGet |>.1
  have hTakeBound :
      (depth + 1) + 1 ≤ (value :: rest).length := by
    simp only [List.length_cons]
    omega
  have hTakeLength :
      ((value :: rest).take ((depth + 1) + 1)).length =
        (depth + 1) + 1 :=
    List.length_take_of_le hTakeBound
  have hSwap := swap_stack_eq_set (value := value) hGet
  have hRun :
      (Assembly.PrimStep.swap (depth + 1)).run target.evm =
        .ok
          (target.evm.replaceStackAndIncrPC
            (old :: rest.set depth value)) := by
    change EvmYul.swap (depth + 1) target.evm =
      .ok
        (target.evm.replaceStackAndIncrPC
          (old :: rest.set depth value))
    unfold EvmYul.swap
    rw [hStack, if_pos hTakeLength, hSwap]
  unfold Structured.InteractionSemantics.Code.openRun
  simp only [Structured.EffectSemantics.Control.Code.run,
    Structured.InteractionSemantics.handler,
    Structured.InteractionSemantics.BasicInstr.openStep,
    Structured.InteractionSemantics.BasicInstr.openStepEVM]
  rw [swap?_openStep hOp, hRun]
  rfl

theorem openRun_swap_pop
    {target : Structured.RunState}
    {depth : Nat} {value old : Word} {rest : List Word}
    {op : Structured.BasicOp}
    (hOp : StackOp.swap? (depth + 1) = some op)
    (hGet : rest[depth]? = some old)
    (hStack : target.evm.stack = value :: rest) :
    ∃ final,
      Structured.InteractionSemantics.Code.openRun
          [.op op, .op .pop] target =
        .done (.ok final) ∧
      final.evm.stack = rest.set depth value ∧
      final.evm.toSharedState = target.evm.toSharedState ∧
      final.returns = target.returns := by
  let afterSwap :=
    target.withEVM
      (target.evm.replaceStackAndIncrPC
        (old :: rest.set depth value))
  let final :=
    afterSwap.withEVM
      (afterSwap.evm.replaceStackAndIncrPC
        (rest.set depth value))
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · change
      Structured.InteractionSemantics.Code.openRun
          ([Structured.BasicInstr.op op] ++
            [Structured.BasicInstr.op .pop]) target =
        .done (.ok final)
    rw [Structured.InteractionSemantics.Code.openRun_append,
      openRun_swap hOp hGet hStack]
    change
      Structured.InteractionSemantics.Code.openRun
          [.op .pop] afterSwap =
        .done (.ok final)
    exact
      openRun_pop
        (target := afterSwap) (value := old)
        (rest := rest.set depth value) (by
          simp [afterSwap,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC])
  · simp [final, afterSwap,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · simp [final, afterSwap,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · simp [final, afterSwap]

end Code

namespace Primitive

def ResultRel (baseStack : EvmYul.Stack Word)
    (returns : List Structured.ReturnDest)
    (initialVars : Locals.Source.Store)
    (source : Locals.Source.State × List Word)
    (target : Structured.RunState) : Prop :=
  target.returns = returns ∧
    source.1.vars = initialVars ∧
      target.evm.toSharedState = source.1.shared ∧
        target.evm.stack = source.2.reverse ++ baseStack

abbrev OutcomeRel (baseStack : EvmYul.Stack Word)
    (returns : List Structured.ReturnDest)
    (initialVars : Locals.Source.Store) :
    Except EVMException (Locals.Source.State × List Word) →
      Except EVMException Structured.RunState → Prop :=
  Simulation.Interaction.ExceptRel
    (fun _sourceError _targetError => True)
    (ResultRel baseStack returns initialVars)

/--
One stack-free Locals primitive is preserved by its emitted Structured
instruction for every exact resource answer and external-world response.
-/
theorem openEval_op
    {op : Structured.BasicOp}
    {source : Locals.Source.State} {values : List Word}
    {target : Structured.RunState}
    (baseStack : EvmYul.Stack Word)
    (hLength :
      values.length = Expressions.Structured.BasicOp.inputs op)
    (hSupports :
      InteractionSemantics.Primitive.supportsOpen op = true)
    (hShared :
      target.evm.toSharedState = source.shared)
    (hStack :
      target.evm.stack = values.reverse ++ baseStack) :
    Simulation.Interaction.Rel
      (OutcomeRel baseStack target.returns source.vars)
      (InteractionSemantics.Primitive.openEval op source values)
      (Structured.InteractionSemantics.BasicInstr.openStep
        (.op op) target) := by
  have hArity :=
    InteractionSemantics.Primitive.stackArity_of_supportsOpen
      hSupports
  have hBound :
      Expressions.Structured.BasicOp.inputs op ≤
        (InteractionSemantics.Primitive.isolated source values).stack.length := by
    simpa [InteractionSemantics.Primitive.isolated,
      List.length_reverse, hLength]
  have hRaw :=
    Structured.InteractionPrimitivePreservation.BasicOp.openStepEVM_frame_rel
      (source :=
        InteractionSemantics.Primitive.isolated source values)
      (target := target.evm)
      baseStack hArity hBound
      (by
        simpa [InteractionSemantics.Primitive.isolated] using hShared)
      (by
        simpa [InteractionSemantics.Primitive.isolated] using hStack)
  simp only [InteractionSemantics.Primitive.openEval,
    hLength, hSupports, ↓reduceIte]
  unfold Structured.InteractionSemantics.BasicInstr.openStep
  apply Simulation.Interaction.Rel.bind hRaw
  intro sourceFinal targetFinal hFrame
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · exact hFrame.1
      · simpa [InteractionSemantics.Primitive.finish,
          List.reverse_reverse] using hFrame.2

def TerminalResultRel
    (returns : List Structured.ReturnDest)
    (source : Locals.Source.State)
    (target : Structured.RunState) : Prop :=
  source.shared = target.evm.toSharedState ∧
    target.returns = returns

abbrev TerminalOutcomeRel
    (returns : List Structured.ReturnDest) :
    Except EVMException Locals.Source.State →
      Except EVMException Structured.RunState → Prop :=
  Simulation.Interaction.ExceptRel
    (fun _sourceError _targetError => True)
    (TerminalResultRel returns)

/--
Terminal execution consumes exactly its source-owned argument prefix and is
insensitive to the caller-owned target stack suffix. This is the terminal
counterpart of primitive frame preservation.
-/
theorem openTerminal_frame
    {kind : Assembly.HaltKind}
    {source : Locals.Source.State}
    {values : List Word}
    {target : Structured.RunState}
    {baseStack : List Word}
    (hLength : values.length = kind.argCount)
    (hShared : target.evm.toSharedState = source.shared)
    (hStack :
      target.evm.stack = values.reverse ++ baseStack) :
    Simulation.Interaction.Rel
      (TerminalOutcomeRel target.returns)
      (InteractionSemantics.Primitive.openTerminal
        kind source values)
      (Structured.InteractionSemantics.Terminal.openStep
        kind target) := by
  let isolated :=
    InteractionSemantics.Primitive.isolated source values
  have hBound : kind.argCount ≤ isolated.stack.length := by
    simp [isolated,
      InteractionSemantics.Primitive.isolated,
      List.length_reverse, hLength]
  by_cases hAllowed : Structured.Terminal.Allowed kind isolated
  swap
  · rcases Structured.Terminal.not_allowed_iff.mp hAllowed with
      ⟨rfl, hSourcePermission⟩
    have hTargetPermission :
        target.evm.executionEnv.perm = false := by
      change target.evm.toSharedState.executionEnv.perm = false
      rw [hShared]
      simpa [isolated,
        InteractionSemantics.Primitive.isolated] using hSourcePermission
    have hSourceStep :
        Structured.Terminal.step .selfdestruct isolated =
          .error .StaticModeViolation := by
      change Assembly.PrimOp.selfdestruct.step isolated = _
      exact Assembly.PrimOp.step_selfdestruct_of_static
        isolated hSourcePermission
    have hTargetStep :
        Assembly.InteractionSemantics.PrimOp.openStep
            .selfdestruct target.evm =
          .done (.error .StaticModeViolation) := by
      rw [Assembly.InteractionSemantics.PrimOp.openStep_closed
        (by rfl) (by decide) (by decide)]
      rw [Assembly.PrimOp.step_selfdestruct_of_static
        target.evm hTargetPermission]
    have hSourceRun :
        InteractionSemantics.Primitive.openTerminal
            .selfdestruct source values =
          .done (.error .StaticModeViolation) := by
      unfold InteractionSemantics.Primitive.openTerminal
      change
        Simulation.Interaction.map
            (fun final => source.withShared final.toSharedState)
            (.done (Structured.Terminal.step .selfdestruct isolated)) = _
      rw [hSourceStep]
      rfl
    have hTargetRun :
        Structured.InteractionSemantics.Terminal.openStep
            .selfdestruct target =
          .done (.error .StaticModeViolation) := by
      unfold Structured.InteractionSemantics.Terminal.openStep
      change
        Simulation.Interaction.map target.withEVM
            (Assembly.InteractionSemantics.PrimOp.openStep
              .selfdestruct target.evm) = _
      rw [hTargetStep]
      rfl
    rw [hSourceRun, hTargetRun]
    exact Simulation.Interaction.Rel.done
      (Simulation.Interaction.ExceptRel.error trivial)
  obtain ⟨isolatedFinal, hIsolated⟩ :=
    Structured.Terminal.exists_step_of_argCount_le
      kind isolated hBound hAllowed
  have hSourceEval :
      Locals.Source.PrimitiveSemantics.structured.terminal
          kind source.shared values =
        .ok isolatedFinal.toSharedState := by
    unfold Locals.Source.PrimitiveSemantics.structured
    change
      (match Structured.Terminal.step kind isolated with
        | .ok state' => Except.ok state'.toSharedState
        | .error err => Except.error err) =
        Except.ok isolatedFinal.toSharedState
    rw [hIsolated]
  obtain ⟨targetFinal, hTargetStep, hFinalShared,
      _isolatedFinal, _hIsolatedAgain, _hFinalStack⟩ :=
    Locals.Source.PrimitiveSemantics.structured_terminal_step_exists
      hSourceEval hShared hStack
  have hSourceRun :
      InteractionSemantics.Primitive.openTerminal
          kind source values =
        .done
          (.ok
            (source.withShared isolatedFinal.toSharedState)) := by
    unfold InteractionSemantics.Primitive.openTerminal
      Simulation.Interaction.map
    change
      Simulation.Interaction.bind
          (.done (Structured.Terminal.step kind isolated))
          _ =
        _
    rw [hIsolated]
    rfl
  have hTargetOpen :
      Assembly.InteractionSemantics.PrimOp.openStep
          kind.toPrimOp target.evm =
        .done (.ok targetFinal) := by
    have hExternal :
        Simulation.ExternalKind.ofEVMOperation?
            kind.toPrimOp.toEVM = none := by
      cases kind <;> rfl
    have hGas : kind.toPrimOp ≠ .gas := by
      cases kind <;> simp [Assembly.HaltKind.toPrimOp]
    have hMsize : kind.toPrimOp ≠ .msize := by
      cases kind <;> simp [Assembly.HaltKind.toPrimOp]
    rw [Assembly.InteractionSemantics.PrimOp.openStep_closed
      hExternal hGas hMsize]
    have hPrimitiveStep :
        kind.toPrimOp.step target.evm =
          .ok targetFinal := by
      simpa [Structured.Terminal.step] using hTargetStep
    rw [hPrimitiveStep]
  rw [hSourceRun]
  unfold Structured.InteractionSemantics.Terminal.openStep
    Simulation.Interaction.map
  rw [hTargetOpen]
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  exact ⟨hFinalShared.symm, rfl⟩

def OutputLength (output : Nat) :
    Except EVMException (Locals.Source.State × List Word) → Prop
  | .error _ => True
  | .ok result => result.2.length = output

/--
Every successful branch of one accepted open primitive returns its declared
number of stack-free source values.
-/
theorem openEval_length
    {op : Structured.BasicOp}
    {source : Locals.Source.State} {values : List Word}
    (hLength :
      values.length = Expressions.Structured.BasicOp.inputs op)
    (hSupports :
      InteractionSemantics.Primitive.supportsOpen op = true) :
    Simulation.Interaction.AllDone
      (OutputLength (Expressions.Structured.BasicOp.outputs op))
      (InteractionSemantics.Primitive.openEval op source values) := by
  have hArity :=
    InteractionSemantics.Primitive.stackArity_of_supportsOpen
      hSupports
  have hRaw :=
    Structured.InteractionPrimitivePreservation.BasicOp.openStepEVM_outputLength
      (state :=
        InteractionSemantics.Primitive.isolated source values)
      hArity
      (by
        simpa [InteractionSemantics.Primitive.isolated,
          List.length_reverse] using hLength)
  simp only [InteractionSemantics.Primitive.openEval,
    hLength, hSupports, ↓reduceIte]
  apply Simulation.Interaction.AllDone.map
    (InteractionSemantics.Primitive.finish source) hRaw
  · intro error _
    exact True.intro
  · intro final hFinal
    change
      (InteractionSemantics.Primitive.finish source final).2.length =
        Expressions.Structured.BasicOp.outputs op
    simpa [InteractionSemantics.Primitive.finish,
      List.length_reverse] using hFinal

end Primitive

namespace Frame

/--
Statement-boundary realization of the stack-free Locals state.

The active compiler layout occupies exactly the target stack prefix; `suffix`
is caller-owned and remains abstract. The relation owns no allocation plan;
physical stack scheduling belongs to the upper Functions allocation pass.
-/
structure StateRel (layout : Layout) (suffix : List Word)
    (returns : List Structured.ReturnDest)
    (source : Locals.Source.State)
    (target : Structured.RunState) : Prop where
  shared :
    target.evm.toSharedState = source.shared
  returns :
    target.returns = returns
  stackLength :
    target.evm.stack.length = layout.length + suffix.length
  suffix :
    target.evm.stack.drop layout.length = suffix
  slot :
    ∀ {index : Nat} {name : Name},
      layout[index]? = some name →
        target.evm.stack[index]? = source.vars name
  defined :
    ∀ {name : Name}, name ∈ layout →
      ∃ value, source.vars name = some value
  storeScoped :
    ∀ {name : Name}, name ∉ layout →
      source.vars name = none

/--
The source lexical destinations and target stack depths describe the same
control scopes. `leaveRetc` is zero because internal return-value protocol is
owned by Functions allocation rather than the stack-free Locals language.
-/
structure CtxRel (source : Locals.Source.Ctx)
    (target : Locals.Ctx) : Prop where
  layout :
    target.layout = source.scope
  breakDepth :
    target.breakDepth? = source.breakScope?.map List.length
  continueDepth :
    target.continueDepth? = source.continueScope?.map List.length
  leaveDepth :
    target.leaveDepth? = source.leaveScope?.map List.length
  leaveRetc :
    target.leaveRetc = 0
  breakSuffix :
    ∀ {scope : List Name},
      source.breakScope? = some scope →
        ∃ pre, source.scope = pre ++ scope
  continueSuffix :
    ∀ {scope : List Name},
      source.continueScope? = some scope →
        ∃ pre, source.scope = pre ++ scope
  leaveSuffix :
    ∀ {scope : List Name},
      source.leaveScope? = some scope →
        ∃ pre, source.scope = pre ++ scope

namespace CtxRel

theorem initial :
    CtxRel Locals.Source.Ctx.initial Locals.Ctx.initial := by
  constructor
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro scope hScope
    simp [Locals.Source.Ctx.initial] at hScope
  · intro scope hScope
    simp [Locals.Source.Ctx.initial] at hScope
  · intro scope hScope
    simp [Locals.Source.Ctx.initial] at hScope

theorem prependScope
    {source : Locals.Source.Ctx} {target : Locals.Ctx}
    (hRel : CtxRel source target) (name : Name) :
    CtxRel
      { source with scope := name :: source.scope }
      (target.withLayout (name :: target.layout)) := by
  constructor
  · simp [Locals.Ctx.withLayout, hRel.layout]
  · simpa [Locals.Ctx.withLayout] using hRel.breakDepth
  · simpa [Locals.Ctx.withLayout] using hRel.continueDepth
  · simpa [Locals.Ctx.withLayout] using hRel.leaveDepth
  · simpa [Locals.Ctx.withLayout] using hRel.leaveRetc
  · intro scope hScope
    obtain ⟨pre, hPrefix⟩ := hRel.breakSuffix hScope
    exact ⟨name :: pre, by simp [hPrefix]⟩
  · intro scope hScope
    obtain ⟨pre, hPrefix⟩ := hRel.continueSuffix hScope
    exact ⟨name :: pre, by simp [hPrefix]⟩
  · intro scope hScope
    obtain ⟨pre, hPrefix⟩ := hRel.leaveSuffix hScope
    exact ⟨name :: pre, by simp [hPrefix]⟩

theorem withoutLoopControl
    {source : Locals.Source.Ctx} {target : Locals.Ctx}
    (hRel : CtxRel source target) :
    CtxRel source.withoutLoopControl target.withoutLoopControl := by
  constructor
  · simpa [Locals.Source.Ctx.withoutLoopControl,
      Locals.Ctx.withoutLoopControl] using hRel.layout
  · rfl
  · rfl
  · simpa [Locals.Source.Ctx.withoutLoopControl,
      Locals.Ctx.withoutLoopControl] using hRel.leaveDepth
  · simpa [Locals.Source.Ctx.withoutLoopControl,
      Locals.Ctx.withoutLoopControl] using hRel.leaveRetc
  · intro scope hScope
    simp [Locals.Source.Ctx.withoutLoopControl] at hScope
  · intro scope hScope
    simp [Locals.Source.Ctx.withoutLoopControl] at hScope
  · intro scope hScope
    exact hRel.leaveSuffix hScope

theorem withLoopControl
    {source : Locals.Source.Ctx} {target : Locals.Ctx}
    (hRel : CtxRel source target) :
    CtxRel
      (source.withLoopControl source.scope source.scope)
      (target.withLoopControl target.layout.length) := by
  constructor
  · simpa [Locals.Source.Ctx.withLoopControl,
      Locals.Ctx.withLoopControl] using hRel.layout
  · simp [Locals.Source.Ctx.withLoopControl,
      Locals.Ctx.withLoopControl, hRel.layout]
  · simp [Locals.Source.Ctx.withLoopControl,
      Locals.Ctx.withLoopControl, hRel.layout]
  · simpa [Locals.Source.Ctx.withLoopControl,
      Locals.Ctx.withLoopControl] using hRel.leaveDepth
  · simpa [Locals.Source.Ctx.withLoopControl,
      Locals.Ctx.withLoopControl] using hRel.leaveRetc
  · intro scope hScope
    simp [Locals.Source.Ctx.withLoopControl] at hScope
    subst scope
    exact
      ⟨[], by
        simp [Locals.Source.Ctx.withLoopControl]⟩
  · intro scope hScope
    simp [Locals.Source.Ctx.withLoopControl] at hScope
    subst scope
    exact
      ⟨[], by
        simp [Locals.Source.Ctx.withLoopControl]⟩
  · intro scope hScope
    exact hRel.leaveSuffix hScope

theorem breakLayout
    {source : Locals.Source.Ctx} {target : Locals.Ctx}
    (hRel : CtxRel source target)
    {scope : List Name}
    (hScope : source.breakScope? = some scope) :
    ∃ pre,
      target.layout = pre ++ scope ∧
        target.breakDepth? = some scope.length := by
  obtain ⟨pre, hLayout⟩ := hRel.breakSuffix hScope
  refine ⟨pre, ?_, ?_⟩
  · exact hRel.layout.trans hLayout
  · rw [hRel.breakDepth, hScope]
    rfl

theorem continueLayout
    {source : Locals.Source.Ctx} {target : Locals.Ctx}
    (hRel : CtxRel source target)
    {scope : List Name}
    (hScope : source.continueScope? = some scope) :
    ∃ pre,
      target.layout = pre ++ scope ∧
        target.continueDepth? = some scope.length := by
  obtain ⟨pre, hLayout⟩ := hRel.continueSuffix hScope
  refine ⟨pre, ?_, ?_⟩
  · exact hRel.layout.trans hLayout
  · rw [hRel.continueDepth, hScope]
    rfl

theorem leaveLayout
    {source : Locals.Source.Ctx} {target : Locals.Ctx}
    (hRel : CtxRel source target)
    {scope : List Name}
    (hScope : source.leaveScope? = some scope) :
    ∃ pre,
      target.layout = pre ++ scope ∧
        target.leaveDepth? = some scope.length := by
  obtain ⟨pre, hLayout⟩ := hRel.leaveSuffix hScope
  refine ⟨pre, ?_, ?_⟩
  · exact hRel.layout.trans hLayout
  · rw [hRel.leaveDepth, hScope]
    rfl

end CtxRel

end Frame

namespace Expr

structure StateRel (layout : Layout) (offset : Nat)
    (source : Locals.Source.State)
    (target : Structured.RunState) : Prop where
  shared :
    target.evm.toSharedState = source.shared
  store :
    ∀ {name : Name} {depth : Nat},
      Layout.lookupDepth? name layout = some (depth + 1) →
        ∃ value,
          source.vars name = some value ∧
            target.evm.stack[offset + depth]? = some value

structure ResultRel (results : Nat)
    (initialSource : Locals.Source.State)
    (initialTarget : Structured.RunState)
    (source : Locals.Source.State × List Word)
    (target : Structured.RunState) : Prop where
  length :
    source.2.length = results
  vars :
    source.1.vars = initialSource.vars
  returns :
    target.returns = initialTarget.returns
  shared :
    target.evm.toSharedState = source.1.shared
  stack :
    target.evm.stack =
      source.2.reverse ++ initialTarget.evm.stack

end Expr

namespace Frame.StateRel

theorem expr
    {layout : Layout} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hRel : Frame.StateRel layout suffix returns source target) :
    Expr.StateRel layout 0 source target := by
  constructor
  · exact hRel.shared
  · intro name depth hDepth
    have hAt :
        layout[depth]? = some name :=
      Layout.getElem?_eq_some_of_lookupDepth?_eq_some hDepth
    have hMem : name ∈ layout :=
      List.mem_of_getElem? hAt
    obtain ⟨value, hValue⟩ := hRel.defined hMem
    refine ⟨value, hValue, ?_⟩
    have hSlot := hRel.slot hAt
    rw [hValue] at hSlot
    simpa using hSlot

theorem ofExprResultZero
    {layout : Layout} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {initialSource sourceFinal : Locals.Source.State}
    {values : List Word}
    {initialTarget targetFinal : Structured.RunState}
    (hInitial :
      Frame.StateRel layout suffix returns initialSource initialTarget)
    (hResult :
      Expr.ResultRel 0 initialSource initialTarget
        (sourceFinal, values) targetFinal) :
    Frame.StateRel layout suffix returns sourceFinal targetFinal := by
  cases values with
  | cons value rest =>
      have hLength := hResult.length
      simp at hLength
  | nil =>
    constructor
    · exact hResult.shared
    · exact hResult.returns.trans hInitial.returns
    · simpa [hResult.stack] using hInitial.stackLength
    · simpa [hResult.stack] using hInitial.suffix
    · intro index name hAt
      rw [hResult.stack, hResult.vars]
      simpa using hInitial.slot hAt
    · intro name hMem
      rw [hResult.vars]
      exact hInitial.defined hMem
    · intro name hNotMem
      rw [hResult.vars]
      exact hInitial.storeScoped hNotMem

/--
Popping the one value produced by a compiled condition restores the complete
incoming local frame while retaining the expression's final shared state.
-/
theorem ofExprResultOnePop
    {layout : Layout} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {initialSource sourceFinal : Locals.Source.State}
    {value : Word}
    {initialTarget targetAfterExpr : Structured.RunState}
    (hInitial :
      Frame.StateRel layout suffix returns initialSource initialTarget)
    (hResult :
      Expr.ResultRel 1 initialSource initialTarget
        (sourceFinal, [value]) targetAfterExpr) :
    Frame.StateRel layout suffix returns sourceFinal
      (targetAfterExpr.withEVM
        { targetAfterExpr.evm with
          stack := initialTarget.evm.stack }) := by
  constructor
  · simpa using hResult.shared
  · exact hResult.returns.trans hInitial.returns
  · simpa using hInitial.stackLength
  · simpa using hInitial.suffix
  · intro index name hAt
    rw [hResult.vars]
    simpa using hInitial.slot hAt
  · intro name hMem
    rw [hResult.vars]
    exact hInitial.defined hMem
  · intro name hNotMem
    rw [hResult.vars]
    exact hInitial.storeScoped hNotMem

theorem ofExprResultOneInsert
    {layout : Layout} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {name : Name} {value : Word}
    {initialSource sourceFinal : Locals.Source.State}
    {initialTarget targetFinal : Structured.RunState}
    (hFresh : name ∉ layout)
    (hInitial :
      Frame.StateRel layout suffix returns initialSource initialTarget)
    (hResult :
      Expr.ResultRel 1 initialSource initialTarget
        (sourceFinal, [value]) targetFinal) :
    Frame.StateRel (name :: layout) suffix returns
      (sourceFinal.insert name value) targetFinal := by
  constructor
  · exact hResult.shared
  · exact hResult.returns.trans hInitial.returns
  · rw [hResult.stack]
    simpa [hInitial.stackLength, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
  · rw [hResult.stack]
    simpa using hInitial.suffix
  · intro index slotName hAt
    cases index with
    | zero =>
        simp at hAt
        subst slotName
        simp [hResult.stack, Locals.Source.State.insert]
    | succ index =>
        simp only [List.getElem?_cons_succ] at hAt
        have hMem : slotName ∈ layout :=
          List.mem_of_getElem? hAt
        have hNe : slotName ≠ name := by
          intro hEq
          subst slotName
          exact hFresh hMem
        rw [hResult.stack]
        simp only [List.getElem?_cons_succ]
        rw [show
          (sourceFinal.insert name value).vars slotName =
            sourceFinal.vars slotName by
          simp [Locals.Source.State.insert,
            Locals.Source.Store.insert, hNe]]
        rw [hResult.vars]
        exact hInitial.slot hAt
  · intro slotName hMem
    rcases List.mem_cons.mp hMem with hEq | hTail
    · subst slotName
      exact
        ⟨value, by
          simp [Locals.Source.State.insert,
            Locals.Source.Store.insert]⟩
    · obtain ⟨oldValue, hOldValue⟩ :=
        hInitial.defined hTail
      have hNe : slotName ≠ name := by
        intro hEq
        subst slotName
        exact hFresh hTail
      refine ⟨oldValue, ?_⟩
      rw [show
        (sourceFinal.insert name value).vars slotName =
          sourceFinal.vars slotName by
        simp [Locals.Source.State.insert,
          Locals.Source.Store.insert, hNe]]
      rw [hResult.vars]
      exact hOldValue
  · intro slotName hNotMem
    have hNe : slotName ≠ name := by
      intro hEq
      subst slotName
      exact hNotMem (by simp)
    have hNotTail : slotName ∉ layout := by
      intro hMem
      exact hNotMem (List.mem_cons_of_mem name hMem)
    rw [show
      (sourceFinal.insert name value).vars slotName =
        sourceFinal.vars slotName by
      simp [Locals.Source.State.insert,
        Locals.Source.Store.insert, hNe]]
    rw [hResult.vars]
    exact hInitial.storeScoped hNotTail

/--
Replace one existing local with the single expression result emitted above the
active layout. The target-side stack equation is exactly the effect of the
compiler's `SWAP depth; POP` sequence.
-/
theorem ofExprResultOneAssign
    {layout : Layout} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {name : Name} {depth : Nat} {value : Word}
    {initialSource sourceFinal : Locals.Source.State}
    {initialTarget targetAfterValue finalTarget : Structured.RunState}
    (hNodup : layout.Nodup)
    (hDepth :
      Layout.lookupDepth? name layout = some (depth + 1))
    (hInitial :
      Frame.StateRel layout suffix returns initialSource initialTarget)
    (hResult :
      Expr.ResultRel 1 initialSource initialTarget
        (sourceFinal, [value]) targetAfterValue)
    (hFinalShared :
      finalTarget.evm.toSharedState =
        targetAfterValue.evm.toSharedState)
    (hFinalReturns :
      finalTarget.returns = targetAfterValue.returns)
    (hFinalStack :
      finalTarget.evm.stack =
        initialTarget.evm.stack.set depth value) :
    Frame.StateRel layout suffix returns
      (sourceFinal.insert name value) finalTarget := by
  have hAt :
      layout[depth]? = some name :=
    Layout.getElem?_eq_some_of_lookupDepth?_eq_some hDepth
  have hDepthBound : depth < layout.length :=
    List.getElem?_eq_some_iff.mp hAt |>.1
  have hStackDepthBound :
      depth < initialTarget.evm.stack.length := by
    rw [hInitial.stackLength]
    omega
  constructor
  · rw [hFinalShared]
    simpa [Locals.Source.State.insert] using hResult.shared
  · exact hFinalReturns.trans (hResult.returns.trans hInitial.returns)
  · rw [hFinalStack, List.length_set]
    exact hInitial.stackLength
  · rw [hFinalStack, List.drop_set_of_lt hDepthBound]
    exact hInitial.suffix
  · intro index slotName hSlot
    by_cases hIndex : index = depth
    · subst index
      rw [hAt] at hSlot
      cases hSlot
      rw [hFinalStack,
        List.getElem?_set_eq_of_lt value hStackDepthBound]
      simp [Locals.Source.State.insert,
        Locals.Source.Store.insert]
    · have hName : slotName ≠ name := by
        intro hEq
        subst slotName
        have hOtherDepth :=
          Layout.lookupDepth?_eq_some_of_getElem?_eq_some_of_nodup
            hNodup hSlot
        rw [hDepth] at hOtherDepth
        cases hOtherDepth
        exact hIndex rfl
      rw [hFinalStack,
        List.getElem?_set_of_lt' value
          initialTarget.evm.stack hStackDepthBound]
      simp only [if_neg (Ne.symm hIndex)]
      rw [show
        (sourceFinal.insert name value).vars slotName =
          sourceFinal.vars slotName by
        simp [Locals.Source.State.insert,
          Locals.Source.Store.insert, hName]]
      rw [hResult.vars]
      exact hInitial.slot hSlot
  · intro slotName hMem
    by_cases hName : slotName = name
    · subst slotName
      exact
        ⟨value, by
          simp [Locals.Source.State.insert,
            Locals.Source.Store.insert]⟩
    · obtain ⟨oldValue, hOldValue⟩ :=
        hInitial.defined hMem
      refine ⟨oldValue, ?_⟩
      rw [show
        (sourceFinal.insert name value).vars slotName =
          sourceFinal.vars slotName by
        simp [Locals.Source.State.insert,
          Locals.Source.Store.insert, hName]]
      rw [hResult.vars]
      exact hOldValue
  · intro slotName hNotMem
    have hName : slotName ≠ name := by
      intro hEq
      subst slotName
      exact hNotMem
        (Layout.mem_of_lookupDepth?_eq_some hDepth)
    rw [show
      (sourceFinal.insert name value).vars slotName =
        sourceFinal.vars slotName by
      simp [Locals.Source.State.insert,
        Locals.Source.Store.insert, hName]]
    rw [hResult.vars]
    exact hInitial.storeScoped hNotMem

/--
Dropping an exact layout prefix realizes source lexical restriction to the
remaining suffix layout.
-/
theorem restrictPrefix
    {pre kept : Layout} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {initialTarget finalTarget : Structured.RunState}
    (hInitial :
      Frame.StateRel (pre ++ kept) suffix returns source initialTarget)
    (hFinalStack :
      finalTarget.evm.stack =
        initialTarget.evm.stack.drop pre.length)
    (hFinalShared :
      finalTarget.evm.toSharedState =
        initialTarget.evm.toSharedState)
    (hFinalReturns :
      finalTarget.returns = initialTarget.returns) :
    Frame.StateRel kept suffix returns
      (source.restrictTo kept) finalTarget := by
  constructor
  · rw [hFinalShared]
    simpa [Locals.Source.State.restrictTo] using hInitial.shared
  · exact hFinalReturns.trans hInitial.returns
  · rw [hFinalStack, List.length_drop, hInitial.stackLength]
    simp only [List.length_append]
    omega
  · rw [hFinalStack, List.drop_drop]
    simpa [List.length_append, Nat.add_assoc] using hInitial.suffix
  · intro index name hAt
    have hOriginalAt :
        (pre ++ kept)[pre.length + index]? = some name := by
      rw [List.getElem?_append_right
        (Nat.le_add_right pre.length index)]
      simpa using hAt
    rw [hFinalStack, List.getElem?_drop]
    rw [show pre.length + index = pre.length + index by rfl]
    rw [show
      (source.restrictTo kept).vars name =
        source.vars name by
      simp [Locals.Source.State.restrictTo,
        Locals.Source.Store.restrictTo_mem
          (List.mem_of_getElem? hAt)]]
    exact hInitial.slot hOriginalAt
  · intro name hMem
    obtain ⟨value, hValue⟩ :=
      hInitial.defined
        (List.mem_append_right pre hMem)
    exact
      ⟨value, by
        simpa [Locals.Source.State.restrictTo,
          Locals.Source.Store.restrictTo_mem hMem] using hValue⟩
  · intro name hNotMem
    simp [Locals.Source.State.restrictTo,
      Locals.Source.Store.restrictTo_not_mem hNotMem]

theorem restrictSelf
    {layout : Layout} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hRel : Frame.StateRel layout suffix returns source target) :
    Frame.StateRel layout suffix returns
      (source.restrictTo layout) target := by
  have hLayout : layout = ([] : Layout) ++ layout := by
    simp
  have hRel' :
      Frame.StateRel (([] : Layout) ++ layout) suffix returns
        source target := by
    simpa using hRel
  exact
    restrictPrefix hRel' (by simp) (by rfl) (by rfl)

/--
Successful ordinary cleanup compilation drops exactly the discarded lexical
prefix and realizes source restriction to the kept suffix.
-/
theorem openRun_cleanupTo
    {ctx : Locals.Ctx} {pre kept : Layout}
    {code : Structured.Code} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hLayout : ctx.layout = pre ++ kept)
    (hCode : ctx.cleanupTo? kept.length = some code)
    (hInitial :
      Frame.StateRel ctx.layout suffix returns source target) :
    ∃ final,
      Structured.InteractionSemantics.Code.openRun code target =
        .done (.ok final) ∧
      Frame.StateRel kept suffix returns
        (source.restrictTo kept) final := by
  have hTargetDepth :
      kept.length ≤ ctx.layout.length := by
    rw [hLayout, List.length_append]
    omega
  unfold Locals.Ctx.cleanupTo? at hCode
  rw [if_pos hTargetDepth] at hCode
  have hCount :
      ctx.layout.length - kept.length = pre.length := by
    rw [hLayout, List.length_append]
    omega
  cases hCode
  rw [hCount]
  have hInitial' :
      Frame.StateRel (pre ++ kept) suffix returns source target := by
    simpa [hLayout] using hInitial
  have hBound :
      pre.length ≤ target.evm.stack.length := by
    rw [hInitial'.stackLength, List.length_append]
    omega
  obtain ⟨final, hRun, hFinalStack,
      hFinalShared, hFinalReturns⟩ :=
    Code.openRun_replicate_pop pre.length hBound
  exact
    ⟨final, hRun,
      restrictPrefix hInitial'
        hFinalStack hFinalShared hFinalReturns⟩

end Frame.StateRel

namespace Expr

abbrev OutcomeRel (results : Nat)
    (initialSource : Locals.Source.State)
    (initialTarget : Structured.RunState) :
    Except EVMException (Locals.Source.State × List Word) →
      Except EVMException Structured.RunState → Prop :=
  Simulation.Interaction.ExceptRel
    (fun _sourceError _targetError => True)
    (ResultRel results initialSource initialTarget)

namespace ResultRel

theorem stateRel
    {layout : Layout} {offset results : Nat}
    {initialSource sourceFinal : Locals.Source.State}
    {values : List Word}
    {initialTarget targetFinal : Structured.RunState}
    (hInitial :
      StateRel layout offset initialSource initialTarget)
    (hResult :
      ResultRel results initialSource initialTarget
        (sourceFinal, values) targetFinal) :
    StateRel layout (offset + results)
      sourceFinal targetFinal := by
  constructor
  · exact hResult.shared
  · intro name depth hDepth
    obtain ⟨value, hSource, hTarget⟩ :=
      hInitial.store hDepth
    refine ⟨value, ?_, ?_⟩
    · rw [hResult.vars]
      exact hSource
    · rw [hResult.stack]
      have hPrefix :
          values.reverse.length = results := by
        simpa using hResult.length
      rw [show
          offset + results + depth =
            values.reverse.length + (offset + depth) by
            omega]
      rw [List.getElem?_append_right
        (Nat.le_add_right values.reverse.length
          (offset + depth))]
      simpa using hTarget

end ResultRel

mutual
  /--
  Every open-supported, scoped Locals expression is preserved by its existing
  Structured code compiler for every exact resource answer and external-world
  response.
  -/
  theorem openEval_compileCode
      {results : Nat} (expr : Locals.Expr results)
      (ctx : Locals.Ctx) (offset : Nat)
      {code : Structured.Code}
      {source : Locals.Source.State}
      {target : Structured.RunState}
      (hScoped : Scope.ExprScoped ctx.layout expr)
      (hSupported :
        InteractionSemantics.Expr.OpenSupported expr)
      (hCompile :
        Locals.Expr.compileCode ctx offset expr = some code)
      (hInitial :
        StateRel ctx.layout offset source target) :
      Simulation.Interaction.Rel
        (OutcomeRel results source target)
        (InteractionSemantics.Expr.openEval expr source)
        (Structured.InteractionSemantics.Code.openRun
          code target) := by
    cases expr with
    | lit value =>
        simp [Locals.Expr.compileCode] at hCompile
        subst code
        rw [Code.openRun_push]
        change
          Simulation.Interaction.Rel
            (OutcomeRel 1 source target)
            (.done (.ok (source, [value])))
            (.done
              (.ok
                (target.withEVM
                  (target.evm.replaceStackAndIncrPC
                    (value :: target.evm.stack) (pcΔ := 33)))))
        apply Simulation.Interaction.Rel.done
        apply Simulation.Interaction.ExceptRel.ok
        constructor
        · rfl
        · rfl
        · rfl
        · simpa using hInitial.shared
        · simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
    | var name =>
        have hMem : name ∈ ctx.layout := by
          simpa [Scope.ExprScoped, Scope.Contains] using hScoped
        obtain ⟨depth, hDepth⟩ :=
          Layout.exists_lookupDepth?_eq_some_of_mem hMem
        cases hDup :
            StackOp.dup? (offset + (depth + 1)) with
        | none =>
            simp [Locals.Expr.compileCode, hDepth, hDup] at hCompile
        | some op =>
            have hCode :
                code = [.op op] := by
              simpa [Locals.Expr.compileCode, hDepth, hDup] using
                hCompile.symm
            subst code
            obtain ⟨value, hSource, hTarget⟩ :=
              hInitial.store hDepth
            have hDup' :
                StackOp.dup? ((offset + depth) + 1) =
                  some op := by
              simpa [Nat.add_assoc] using hDup
            rw [Code.openRun_dup hDup' hTarget]
            change
              Simulation.Interaction.Rel
                (OutcomeRel 1 source target)
                (match source.vars name with
                | some value =>
                    Simulation.Interaction.pure (source, [value])
                | none =>
                    Simulation.Interaction.error
                      (.InvalidInstruction : EVMException))
                (.done
                  (.ok
                    (target.withEVM
                      (target.evm.replaceStackAndIncrPC
                        (value :: target.evm.stack)))))
            rw [hSource]
            apply Simulation.Interaction.Rel.done
            apply Simulation.Interaction.ExceptRel.ok
            constructor
            · rfl
            · rfl
            · rfl
            · simpa using hInitial.shared
            · simp [EvmYul.EVM.State.replaceStackAndIncrPC,
                EvmYul.EVM.State.incrPC]
    | code lower =>
        exact False.elim hScoped
    | prim op args =>
        have hArgsScoped :
            Scope.ExprSeqScoped ctx.layout args := by
          simpa [Scope.ExprScoped] using hScoped
        have hOpSupported :
            InteractionSemantics.Primitive.supportsOpen op = true :=
          hSupported.1
        have hArgsSupported :
            InteractionSemantics.ExprSeq.OpenSupported args :=
          hSupported.2
        cases hArgsCompile :
            Locals.ExprSeq.compileCode ctx offset args with
        | none =>
            simp [Locals.Expr.compileCode, hArgsCompile] at hCompile
        | some argsCode =>
            have hCode :
                code = argsCode ++ [.op op] := by
              simpa [Locals.Expr.compileCode, hArgsCompile] using
                hCompile.symm
            subst code
            rw [Structured.InteractionSemantics.Code.openRun_append]
            have hArgsRel :=
              openEvalSeq_compileCode args ctx offset
                hArgsScoped hArgsSupported hArgsCompile hInitial
            change
              Simulation.Interaction.Rel
                (OutcomeRel
                  (Expressions.Structured.BasicOp.outputs op)
                  source target)
                (Simulation.Interaction.bind
                  (InteractionSemantics.ExprSeq.openEval args source)
                  (fun result =>
                    InteractionSemantics.Primitive.openEval
                      op result.1 result.2))
                (Simulation.Interaction.bind
                  (Structured.InteractionSemantics.Code.openRun
                    argsCode target)
                  (Structured.InteractionSemantics.Code.openRun
                    [.op op]))
            apply Simulation.Interaction.Rel.bind hArgsRel
            intro sourceArgs targetArgs hArgsResult
            rcases sourceArgs with ⟨sourceAfterArgs, values⟩
            have hPrimitive :=
              Primitive.openEval_op
                (source := sourceAfterArgs)
                (values := values)
                (target := targetArgs)
                target.evm.stack
                hArgsResult.length hOpSupported
                hArgsResult.shared hArgsResult.stack
            have hPrimitiveCode :
                Simulation.Interaction.Rel
                  (Primitive.OutcomeRel
                    target.evm.stack targetArgs.returns
                    sourceAfterArgs.vars)
                  (InteractionSemantics.Primitive.openEval
                    op sourceAfterArgs values)
                  (Structured.InteractionSemantics.Code.openRun
                    [.op op] targetArgs) := by
              simpa using hPrimitive
            have hLength :=
              Primitive.openEval_length
                (source := sourceAfterArgs)
                (values := values)
                hArgsResult.length hOpSupported
            have hBoth :=
              Simulation.Interaction.Rel.strengthen_left
                hPrimitiveCode hLength
            apply Simulation.Interaction.Rel.mono hBoth
            intro sourceDone targetDone hDone
            rcases hDone with ⟨hPrimitiveDone, hOutputLength⟩
            cases hPrimitiveDone with
            | error _ =>
                exact
                  Simulation.Interaction.ExceptRel.error True.intro
            | ok hPrimitiveResult =>
                apply Simulation.Interaction.ExceptRel.ok
                constructor
                · exact hOutputLength
                · exact
                    hPrimitiveResult.2.1.trans
                      hArgsResult.vars
                · exact
                    hPrimitiveResult.1.trans
                      hArgsResult.returns
                · exact hPrimitiveResult.2.2.1
                · exact hPrimitiveResult.2.2.2

  /--
  Expression sequences preserve left-to-right source evaluation and place the
  concatenated result vector above the unchanged target frame.
  -/
  theorem openEvalSeq_compileCode
      {results : Nat} (exprs : Locals.ExprSeq results)
      (ctx : Locals.Ctx) (offset : Nat)
      {code : Structured.Code}
      {source : Locals.Source.State}
      {target : Structured.RunState}
      (hScoped : Scope.ExprSeqScoped ctx.layout exprs)
      (hSupported :
        InteractionSemantics.ExprSeq.OpenSupported exprs)
      (hCompile :
        Locals.ExprSeq.compileCode ctx offset exprs = some code)
      (hInitial :
        StateRel ctx.layout offset source target) :
      Simulation.Interaction.Rel
        (OutcomeRel results source target)
        (InteractionSemantics.ExprSeq.openEval exprs source)
        (Structured.InteractionSemantics.Code.openRun
          code target) := by
    cases exprs with
    | nil =>
        simp [Locals.ExprSeq.compileCode] at hCompile
        subst code
        change
          Simulation.Interaction.Rel
            (OutcomeRel 0 source target)
            (.done (.ok (source, [])))
            (.done (.ok target))
        apply Simulation.Interaction.Rel.done
        apply Simulation.Interaction.ExceptRel.ok
        constructor
        · rfl
        · rfl
        · rfl
        · exact hInitial.shared
        · rfl
    | @cons left right head tail =>
        have hHeadScoped :
            Scope.ExprScoped ctx.layout head :=
          hScoped.1
        have hTailScoped :
            Scope.ExprSeqScoped ctx.layout tail :=
          hScoped.2
        have hHeadSupported :
            InteractionSemantics.Expr.OpenSupported head :=
          hSupported.1
        have hTailSupported :
            InteractionSemantics.ExprSeq.OpenSupported tail :=
          hSupported.2
        cases hHeadCompile :
            Locals.Expr.compileCode ctx offset head with
        | none =>
            simp [Locals.ExprSeq.compileCode, hHeadCompile] at hCompile
        | some headCode =>
            cases hTailCompile :
                Locals.ExprSeq.compileCode
                  ctx (offset + left) tail with
            | none =>
                simp [Locals.ExprSeq.compileCode, hHeadCompile,
                  hTailCompile] at hCompile
            | some tailCode =>
                have hCode :
                    code = headCode ++ tailCode := by
                  simpa [Locals.ExprSeq.compileCode, hHeadCompile,
                    hTailCompile] using hCompile.symm
                subst code
                rw [Structured.InteractionSemantics.Code.openRun_append]
                have hHeadRel :=
                  openEval_compileCode head ctx offset
                    hHeadScoped hHeadSupported hHeadCompile hInitial
                change
                  Simulation.Interaction.Rel
                    (OutcomeRel (left + right) source target)
                    (Simulation.Interaction.bind
                      (InteractionSemantics.Expr.openEval head source)
                      (fun headResult =>
                        Simulation.Interaction.bind
                          (InteractionSemantics.ExprSeq.openEval
                            tail headResult.1)
                          (fun tailResult =>
                            Simulation.Interaction.pure
                              (tailResult.1,
                                headResult.2 ++ tailResult.2))))
                    (Simulation.Interaction.bind
                      (Structured.InteractionSemantics.Code.openRun
                        headCode target)
                      (Structured.InteractionSemantics.Code.openRun
                        tailCode))
                apply Simulation.Interaction.Rel.bind hHeadRel
                intro sourceHead targetHead hHeadResult
                rcases sourceHead with
                  ⟨sourceAfterHead, headValues⟩
                have hNextInitial :=
                  hHeadResult.stateRel hInitial
                have hTailRel :=
                  openEvalSeq_compileCode tail ctx (offset + left)
                    hTailScoped hTailSupported hTailCompile
                    hNextInitial
                rw [← Simulation.Interaction.bind_pure
                  (Structured.InteractionSemantics.Code.openRun
                    tailCode targetHead)]
                apply Simulation.Interaction.Rel.bind hTailRel
                intro sourceTail targetTail hTailResult
                rcases sourceTail with
                  ⟨sourceAfterTail, tailValues⟩
                apply Simulation.Interaction.Rel.done
                apply Simulation.Interaction.ExceptRel.ok
                constructor
                · simp [hHeadResult.length, hTailResult.length]
                · exact
                    hTailResult.vars.trans hHeadResult.vars
                · exact
                    hTailResult.returns.trans hHeadResult.returns
                · exact hTailResult.shared
                · rw [hTailResult.stack, hHeadResult.stack,
                    List.reverse_append, List.append_assoc]
end

abbrev OneOutcomeRel
    (initialSource : Locals.Source.State)
    (initialTarget : Structured.RunState) :
    Except EVMException (Locals.Source.State × Word) →
      Except EVMException Structured.RunState → Prop :=
  Simulation.Interaction.ExceptRel
    (fun _sourceError _targetError => True)
    (fun source target =>
      ResultRel 1 initialSource initialTarget
        (source.1, [source.2]) target)

/--
The one-result source adapter used by statement semantics preserves the same
compiled expression code and open interaction order.
-/
theorem openEvalOne_compileCode
    (expr : Locals.Expr 1)
    (ctx : Locals.Ctx) (offset : Nat)
    {code : Structured.Code}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hScoped : Scope.ExprScoped ctx.layout expr)
    (hSupported :
      InteractionSemantics.Expr.OpenSupported expr)
    (hCompile :
      Locals.Expr.compileCode ctx offset expr = some code)
    (hInitial :
      StateRel ctx.layout offset source target) :
    Simulation.Interaction.Rel
      (OneOutcomeRel source target)
      (InteractionSemantics.Expr.openEvalOne expr source)
      (Structured.InteractionSemantics.Code.openRun
        code target) := by
  have hEval :=
    openEval_compileCode expr ctx offset
      hScoped hSupported hCompile hInitial
  unfold InteractionSemantics.Expr.openEvalOne
    Locals.Source.Effectful.Expr.Control.evalOne
  rw [← Simulation.Interaction.bind_pure
    (Structured.InteractionSemantics.Code.openRun code target)]
  apply Simulation.Interaction.Rel.bind hEval
  intro sourceResult targetFinal hResult
  rcases sourceResult with ⟨sourceFinal, values⟩
  cases values with
  | nil =>
      have hLength := hResult.length
      simp at hLength
  | cons value rest =>
      cases rest with
      | nil =>
          apply Simulation.Interaction.Rel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact hResult
      | cons next tail =>
          have hLength := hResult.length
          simp at hLength

structure ConditionResultRel
    (layout : Layout) (suffix : List Word)
    (returns : List Structured.ReturnDest)
    (source : Locals.Source.State × Bool)
    (target : Structured.RunState × Bool) : Prop where
  condition : source.2 = target.2
  state : Frame.StateRel layout suffix returns source.1 target.1

abbrev ConditionOutcomeRel
    (layout : Layout) (suffix : List Word)
    (returns : List Structured.ReturnDest) :
    Except EVMException (Locals.Source.State × Bool) →
      Except EVMException (Structured.RunState × Bool) → Prop :=
  Simulation.Interaction.ExceptRel
    (fun _sourceError _targetError => True)
    (ConditionResultRel layout suffix returns)

/--
One compiled condition produces the same Boolean and restores the incoming
target frame after popping its result word.
-/
theorem openEvalCondition_compileCode
    (expr : Locals.Expr 1) (ctx : Locals.Ctx)
    {code : Structured.Code}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hScoped : Scope.ExprScoped ctx.layout expr)
    (hSupported :
      InteractionSemantics.Expr.OpenSupported expr)
    (hCompile :
      Locals.Expr.compileCode ctx 0 expr = some code)
    (hInitial :
      Frame.StateRel ctx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (ConditionOutcomeRel ctx.layout suffix returns)
      (InteractionSemantics.Expr.openEvalCondition expr source)
      (Expressions.InteractionSemantics.Expr.openRunCondition
        (.code code) target) := by
  have hOne :=
    openEvalOne_compileCode expr ctx 0
      hScoped hSupported hCompile hInitial.expr
  unfold InteractionSemantics.Expr.openEvalCondition
    Locals.Source.Effectful.Expr.Control.evalCondition
  unfold Expressions.InteractionSemantics.Expr.openRunCondition
    Expressions.EffectSemantics.Control.Expr.runCondition
    Expressions.EffectSemantics.Control.Expr.run
  apply Simulation.Interaction.Rel.bind hOne
  intro sourceResult targetAfterExpr hResult
  rcases sourceResult with ⟨sourceFinal, value⟩
  let targetFinal :=
    targetAfterExpr.withEVM
      { targetAfterExpr.evm with stack := target.evm.stack }
  have hTargetStack :
      targetAfterExpr.evm.stack = value :: target.evm.stack := by
    simpa using hResult.stack
  have hPop :
      Structured.EffectSemantics.Control.Code.popCondition
          (M := Simulation.Interaction EVMException)
          Structured.EffectSemantics.Ordinary.runStateModel
          targetAfterExpr =
        Simulation.Interaction.pure
          (targetFinal, value != EvmYul.UInt256.ofNat 0) := by
    unfold Structured.EffectSemantics.Control.Code.popCondition
    rw [Structured.EffectSemantics.Ordinary.runStateModel_evm,
      hTargetStack]
    rfl
  rw [hPop]
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  exact
    { condition := rfl
      state :=
        Frame.StateRel.ofExprResultOnePop hInitial hResult }

end Expr

namespace Stmt

namespace TargetBlock

/-- A singleton Expressions block exposes its statement at the residual fuel. -/
theorem openRun_single_stmt
    (program : Expressions.Program) (fuel : Nat)
    (stmt : Expressions.Stmt) (state : Structured.RunState) :
    Expressions.InteractionSemantics.Block.openRun
        program (fuel + 2) { stmts := [stmt] } state =
      Expressions.InteractionSemantics.Stmt.openRun
        program (fuel + 1) stmt state := by
  unfold Expressions.InteractionSemantics.Block.openRun
    Expressions.InteractionSemantics.Stmt.openRun
  simp only [Expressions.EffectSemantics.Control.Block.run]
  change
    Simulation.Interaction.bind
        (Expressions.EffectSemantics.Control.Stmt.run
          Structured.EffectSemantics.Ordinary.runStateModel
          Structured.InteractionSemantics.handler
          program (fuel + 1) stmt state)
        _ =
      Expressions.EffectSemantics.Control.Stmt.run
        Structured.EffectSemantics.Ordinary.runStateModel
        Structured.InteractionSemantics.handler
        program (fuel + 1) stmt state
  conv_rhs =>
    rw [← Simulation.Interaction.bind_pure
      (Expressions.EffectSemantics.Control.Stmt.run
        Structured.EffectSemantics.Ordinary.runStateModel
        Structured.InteractionSemantics.handler
        program (fuel + 1) stmt state)]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Expressions.EffectSemantics.Control.Stmt.run
        Structured.EffectSemantics.Ordinary.runStateModel
        Structured.InteractionSemantics.handler
        program (fuel + 1) stmt state))
  intro outcome _
  rcases outcome with ⟨outcomeState, outcomeMode⟩
  cases outcomeMode <;> rfl

theorem openRun_single_stmt_of_fuel
    (program : Expressions.Program) (targetFuel : Nat)
    (stmt : Expressions.Stmt) (state : Structured.RunState)
    (hFuel : 2 ≤ targetFuel) :
    Expressions.InteractionSemantics.Block.openRun
        program targetFuel { stmts := [stmt] } state =
      Expressions.InteractionSemantics.Stmt.openRun
        program (targetFuel - 1) stmt state := by
  let extra := targetFuel - 2
  have hFuelEq : targetFuel = extra + 2 := by
    omega
  rw [hFuelEq, openRun_single_stmt]
  congr 3

theorem openRun_single_code
    (program : Expressions.Program) (fuel : Nat)
    (code : Structured.Code) (state : Structured.RunState) :
    Expressions.InteractionSemantics.Block.openRun
        program (fuel + 2) { stmts := [.code code] } state =
      Expressions.InteractionSemantics.Stmt.openRun
        program (fuel + 1) (.code code) state := by
  unfold Expressions.InteractionSemantics.Block.openRun
    Expressions.InteractionSemantics.Stmt.openRun
  simp only [Expressions.EffectSemantics.Control.Block.run,
    Expressions.EffectSemantics.Control.Stmt.run]
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Structured.EffectSemantics.Control.Code.run
            Structured.InteractionSemantics.handler code state)
          (fun final =>
            Simulation.Interaction.pure
              (Structured.Outcome.regular final)))
        (fun outcome =>
          match outcome.mode with
          | .regular =>
              Simulation.Interaction.pure
                (Structured.Outcome.regular outcome.state)
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure outcome) =
      Simulation.Interaction.bind
        (Structured.EffectSemantics.Control.Code.run
          Structured.InteractionSemantics.handler code state)
        (fun final =>
          Simulation.Interaction.pure
            (Structured.Outcome.regular final))
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Structured.EffectSemantics.Control.Code.run
        Structured.InteractionSemantics.handler code state))
  intro final _
  rfl

theorem openRun_single_code_done
    (program : Expressions.Program) (targetFuel : Nat)
    (code : Structured.Code)
    (source final : Structured.RunState)
    (hFuel : 2 ≤ targetFuel)
    (hRun :
      Structured.InteractionSemantics.Code.openRun code source =
        .done (.ok final)) :
    Expressions.InteractionSemantics.Block.openRun
        program targetFuel { stmts := [.code code] } source =
      .done (.ok (Structured.Outcome.regular final)) := by
  let extra := targetFuel - 2
  have hFuelEq : targetFuel = extra + 2 := by
    omega
  rw [hFuelEq, openRun_single_code]
  unfold Structured.InteractionSemantics.Code.openRun at hRun
  unfold Expressions.InteractionSemantics.Stmt.openRun
  simp only [Expressions.EffectSemantics.Control.Stmt.run]
  rw [hRun]
  rfl

theorem openRun_code_brk
    (program : Expressions.Program) (fuel : Nat)
    (code : Structured.Code)
    (source final : Structured.RunState)
    (hRun :
      Structured.InteractionSemantics.Code.openRun code source =
        .done (.ok final)) :
    Expressions.InteractionSemantics.Block.openRun
        program (fuel + 3)
        { stmts := [.code code, .brk] } source =
      .done (.ok (Structured.Outcome.brk final)) := by
  unfold Structured.InteractionSemantics.Code.openRun at hRun
  unfold Expressions.InteractionSemantics.Block.openRun
  simp only [Expressions.EffectSemantics.Control.Block.run,
    Expressions.EffectSemantics.Control.Stmt.run]
  rw [hRun]
  rfl

theorem openRun_code_cont
    (program : Expressions.Program) (fuel : Nat)
    (code : Structured.Code)
    (source final : Structured.RunState)
    (hRun :
      Structured.InteractionSemantics.Code.openRun code source =
        .done (.ok final)) :
    Expressions.InteractionSemantics.Block.openRun
        program (fuel + 3)
        { stmts := [.code code, .cont] } source =
      .done (.ok (Structured.Outcome.cont final)) := by
  unfold Structured.InteractionSemantics.Code.openRun at hRun
  unfold Expressions.InteractionSemantics.Block.openRun
  simp only [Expressions.EffectSemantics.Control.Block.run,
    Expressions.EffectSemantics.Control.Stmt.run]
  rw [hRun]
  rfl

theorem openRun_code_leave
    (program : Expressions.Program) (fuel : Nat)
    (code : Structured.Code)
    (source final : Structured.RunState)
    (hRun :
      Structured.InteractionSemantics.Code.openRun code source =
        .done (.ok final))
    (hReturns : final.returns ≠ []) :
    Expressions.InteractionSemantics.Block.openRun
        program (fuel + 3)
        { stmts := [.code code, .leave] } source =
      .done (.ok (Structured.Outcome.leave final)) := by
  unfold Structured.InteractionSemantics.Code.openRun at hRun
  unfold Expressions.InteractionSemantics.Block.openRun
  simp only [Expressions.EffectSemantics.Control.Block.run,
    Expressions.EffectSemantics.Control.Stmt.run]
  rw [hRun]
  dsimp [EvmCompiler.Simulation.Interaction.instMonad,
    Simulation.Interaction.bind,
    Simulation.Interaction.pure]
  cases hFinalReturns : final.returns with
  | nil => contradiction
  | cons head tail => rfl

theorem openRun_code_terminal
    (program : Expressions.Program) (fuel : Nat)
    (code : Structured.Code) (kind : Assembly.HaltKind)
    (state : Structured.RunState) :
    Expressions.InteractionSemantics.Block.openRun
        program (fuel + 3)
        { stmts := [.code code, .terminal kind] } state =
      Simulation.Interaction.bind
        (Structured.InteractionSemantics.Code.openRun code state)
        (fun afterCode =>
          Simulation.Interaction.bind
            (Structured.InteractionSemantics.Terminal.openStep
              kind afterCode)
            (fun final =>
              Simulation.Interaction.pure
                (Structured.Outcome.halt kind final))) := by
  unfold Expressions.InteractionSemantics.Block.openRun
    Structured.InteractionSemantics.Code.openRun
    Structured.InteractionSemantics.Terminal.openStep
  simp only [Expressions.EffectSemantics.Control.Block.run,
    Expressions.EffectSemantics.Control.Stmt.run]
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Structured.EffectSemantics.Control.Code.run
            Structured.InteractionSemantics.handler code state)
          (fun final =>
            Simulation.Interaction.pure
              (Structured.Outcome.regular final)))
        _ =
      _
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Structured.EffectSemantics.Control.Code.run
        Structured.InteractionSemantics.handler code state))
  intro final _
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.pure
          (Structured.Outcome.regular final))
        _ =
      _
  unfold Simulation.Interaction.pure
  rw [Simulation.Interaction.bind_done_ok]
  simp only [Structured.Outcome.regular_mode,
    Structured.Outcome.regular_state]
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Structured.InteractionSemantics.handler.stepTerminal
            kind final)
          (fun terminalFinal =>
            Simulation.Interaction.done
              (.ok
                (Structured.Outcome.halt kind terminalFinal))))
        _ =
      _
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Structured.InteractionSemantics.handler.stepTerminal
        kind final))
  intro terminalFinal _
  rfl

end TargetBlock

abbrev StateOutcomeRel (layout : Layout) (suffix : List Word)
    (returns : List Structured.ReturnDest) :
    Except EVMException Locals.Source.State →
      Except EVMException Structured.RunState → Prop :=
  Simulation.Interaction.ExceptRel
    (fun _sourceError _targetError => True)
    (Frame.StateRel layout suffix returns)

/--
One source-owned assignment is preserved by the ordinary Locals compiler code.
Any open effects in the assigned expression occur before the silent
`SWAP; POP; bindLocals` stack update.
-/
theorem openAssign_compileCode
    (ctx : Locals.Ctx) {name : Name} (valueExpr : Locals.Expr 1)
    {depth : Nat} {valueCode : Structured.Code}
    {swapOp : Structured.BasicOp}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hNodup : ctx.layout.Nodup)
    (hDepth :
      Layout.lookupDepth? name ctx.layout = some (depth + 1))
    (hValueScoped :
      Scope.ExprScoped ctx.layout valueExpr)
    (hValueSupported :
      InteractionSemantics.Expr.OpenSupported valueExpr)
    (hValueCompile :
      Locals.Expr.compileCode ctx 0 valueExpr = some valueCode)
    (hSwap :
      StackOp.swap? (depth + 1) = some swapOp)
    (hInitial :
      Frame.StateRel ctx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (StateOutcomeRel ctx.layout suffix returns)
      (Simulation.Interaction.bind
        (InteractionSemantics.Expr.openEvalOne valueExpr source)
        (fun result =>
          Simulation.Interaction.pure
            (result.1.insert name result.2)))
      (Structured.InteractionSemantics.Code.openRun
        (valueCode ++
          [.op swapOp, .op .pop] ++
            Locals.bindLocals 0 ctx.layout)
        target) := by
  rw [List.append_assoc,
    Structured.InteractionSemantics.Code.openRun_append]
  have hValueRel :=
    Expr.openEvalOne_compileCode valueExpr ctx 0
      hValueScoped hValueSupported hValueCompile hInitial.expr
  apply Simulation.Interaction.Rel.bind hValueRel
  intro sourceAfterValue targetAfterValue hValueResult
  rcases sourceAfterValue with ⟨sourceFinal, value⟩
  have hAt :
      ctx.layout[depth]? = some name :=
    Layout.getElem?_eq_some_of_lookupDepth?_eq_some hDepth
  have hMem : name ∈ ctx.layout :=
    List.mem_of_getElem? hAt
  obtain ⟨old, hOld⟩ := hInitial.defined hMem
  have hOldStack :
      target.evm.stack[depth]? = some old := by
    have hSlot := hInitial.slot hAt
    rw [hOld] at hSlot
    exact hSlot
  have hValueStack :
      targetAfterValue.evm.stack =
        value :: target.evm.stack := by
    simpa using hValueResult.stack
  obtain ⟨finalTarget, hSwapRun, hFinalStack,
      hFinalShared, hFinalReturns⟩ :=
    Code.openRun_swap_pop hSwap hOldStack hValueStack
  rw [Structured.InteractionSemantics.Code.openRun_append,
    hSwapRun]
  change
    Simulation.Interaction.Rel
      (StateOutcomeRel ctx.layout suffix returns)
      (Simulation.Interaction.pure
        (sourceFinal.insert name value))
      (Structured.InteractionSemantics.Code.openRun
        (Locals.bindLocals 0 ctx.layout) finalTarget)
  rw [show
      Locals.bindLocals 0 ctx.layout =
        [.bindLocals 0 ctx.layout] by rfl,
    Code.openRun_bindLocals]
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  exact
    Frame.StateRel.ofExprResultOneAssign
      hNodup hDepth hInitial hValueResult
        hFinalShared hFinalReturns hFinalStack

structure RegularResultRel (targetCtx : Locals.Ctx)
    (suffix : List Word) (returns : List Structured.ReturnDest)
    (source :
      Locals.Source.Effectful.Outcome Locals.Source.State ×
        Locals.Source.Ctx)
    (target : Structured.Outcome) : Prop where
  sourceMode : source.1.mode = .regular
  targetMode : target.mode = .regular
  context : Frame.CtxRel source.2 targetCtx
  state :
    Frame.StateRel targetCtx.layout suffix returns
      source.1.state target.state

abbrev RegularOutcomeRel (targetCtx : Locals.Ctx)
    (suffix : List Word) (returns : List Structured.ReturnDest) :
    Except EVMException
        (Locals.Source.Effectful.Outcome Locals.Source.State ×
          Locals.Source.Ctx) →
      Except EVMException Structured.Outcome → Prop :=
  Simulation.Interaction.ExceptRel
    (fun _sourceError _targetError => True)
    (RegularResultRel targetCtx suffix returns)

/--
Mode-indexed adjacent outcome relation for the Locals pass. Normal completion
uses the compiler's final context. Abrupt lexical exits retain only their
already-checked cleaned frame, making the result stable under regular prefixes
and unreachable suffixes. Terminal outcomes discard the local-frame
representation and retain only shared state and return-stack agreement.
-/
inductive OpenResultRel (finalCtx : Locals.Ctx)
    (suffix : List Word) (returns : List Structured.ReturnDest) :
    (Locals.Source.Effectful.Outcome Locals.Source.State ×
      Locals.Source.Ctx) →
    Structured.Outcome → Prop
  | regular {source sourceCtx target} :
      Frame.CtxRel sourceCtx finalCtx →
      Frame.StateRel finalCtx.layout suffix returns source target →
      OpenResultRel finalCtx suffix returns
        (Locals.Source.Effectful.Outcome.regular source, sourceCtx)
        (Structured.Outcome.regular target)
  | brk {source sourceCtx target scope} :
      Frame.StateRel scope suffix returns source target →
      OpenResultRel finalCtx suffix returns
        (Locals.Source.Effectful.Outcome.brk source, sourceCtx)
        (Structured.Outcome.brk target)
  | cont {source sourceCtx target scope} :
      Frame.StateRel scope suffix returns source target →
      OpenResultRel finalCtx suffix returns
        (Locals.Source.Effectful.Outcome.cont source, sourceCtx)
        (Structured.Outcome.cont target)
  | leave {source sourceCtx target scope} :
      Frame.StateRel scope suffix returns source target →
      OpenResultRel finalCtx suffix returns
        (Locals.Source.Effectful.Outcome.leave source, sourceCtx)
        (Structured.Outcome.leave target)
  | halt {kind source sourceCtx target} :
      source.shared = target.evm.toSharedState →
      target.returns = returns →
      OpenResultRel finalCtx suffix returns
        (Locals.Source.Effectful.Outcome.halt kind source, sourceCtx)
        (Structured.Outcome.halt kind target)

abbrev OpenOutcomeRel (finalCtx : Locals.Ctx)
    (suffix : List Word) (returns : List Structured.ReturnDest) :
    Except EVMException
        (Locals.Source.Effectful.Outcome Locals.Source.State ×
          Locals.Source.Ctx) →
      Except EVMException Structured.Outcome → Prop :=
  Simulation.Interaction.ExceptRel
    (fun _sourceError _targetError => True)
    (OpenResultRel finalCtx suffix returns)

/--
Outcome relation after leaving a lexical scope. Regular completion has already
restored the outer compiler frame; abrupt completion retains the checked frame
at which it arose. This is the common result interface for blocks and all
control statements that execute scoped child blocks.
-/
inductive ScopedResultRel (outerCtx : Locals.Ctx)
    (suffix : List Word) (returns : List Structured.ReturnDest) :
    Locals.Source.Effectful.Outcome Locals.Source.State →
      Structured.Outcome → Prop
  | regular {source target} :
      Frame.StateRel outerCtx.layout suffix returns source target →
      ScopedResultRel outerCtx suffix returns
        (Locals.Source.Effectful.Outcome.regular source)
        (Structured.Outcome.regular target)
  | brk {source target scope} :
      Frame.StateRel scope suffix returns source target →
      ScopedResultRel outerCtx suffix returns
        (Locals.Source.Effectful.Outcome.brk source)
        (Structured.Outcome.brk target)
  | cont {source target scope} :
      Frame.StateRel scope suffix returns source target →
      ScopedResultRel outerCtx suffix returns
        (Locals.Source.Effectful.Outcome.cont source)
        (Structured.Outcome.cont target)
  | leave {source target scope} :
      Frame.StateRel scope suffix returns source target →
      ScopedResultRel outerCtx suffix returns
        (Locals.Source.Effectful.Outcome.leave source)
        (Structured.Outcome.leave target)
  | halt {kind source target} :
      source.shared = target.evm.toSharedState →
      target.returns = returns →
      ScopedResultRel outerCtx suffix returns
        (Locals.Source.Effectful.Outcome.halt kind source)
        (Structured.Outcome.halt kind target)

abbrev ScopedOutcomeRel (outerCtx : Locals.Ctx)
    (suffix : List Word) (returns : List Structured.ReturnDest) :
    Except EVMException
        (Locals.Source.Effectful.Outcome Locals.Source.State) →
      Except EVMException Structured.Outcome → Prop :=
  Simulation.Interaction.ExceptRel
    (fun _sourceError _targetError => True)
    (ScopedResultRel outerCtx suffix returns)

/--
Optional control-scope refinement carried alongside the ordinary outcome
relation. Generic statements use `any`; loop bodies use `loop` so that a
`break` or `continue` can later be reinterpreted without recovering a target
frame from an erased existential.
-/
structure ControlPolicy where
  brk : Layout → Prop
  cont : Layout → Prop
  leave : Layout → Prop

namespace ControlPolicy

def any : ControlPolicy where
  brk := fun _ => True
  cont := fun _ => True
  leave := fun _ => True

def loop (scope : Layout) : ControlPolicy where
  brk := fun frame => frame = scope
  cont := fun frame => frame = scope
  leave := fun _ => True

def noLoop : ControlPolicy where
  brk := fun _ => False
  cont := fun _ => False
  leave := fun _ => True

def ContextCompatible (policy : ControlPolicy)
    (ctx : Locals.Source.Ctx) : Prop :=
  (∀ {scope}, ctx.breakScope? = some scope → policy.brk scope) ∧
  (∀ {scope}, ctx.continueScope? = some scope → policy.cont scope) ∧
  (∀ {scope}, ctx.leaveScope? = some scope → policy.leave scope)

theorem any_contextCompatible (ctx : Locals.Source.Ctx) :
    ContextCompatible any ctx := by
  constructor
  · intro scope hScope
    trivial
  constructor
  · intro scope hScope
    trivial
  · intro scope hScope
    trivial

theorem contextCompatible_scope
    {policy : ControlPolicy} {ctx : Locals.Source.Ctx}
    (hCompatible : ContextCompatible policy ctx)
    (scope : List Name) :
    ContextCompatible policy { ctx with scope := scope } := by
  simpa [ContextCompatible] using hCompatible

theorem contextCompatible_withoutLoopControl
    {policy : ControlPolicy} {ctx : Locals.Source.Ctx}
    (hCompatible : ContextCompatible policy ctx) :
    ContextCompatible policy ctx.withoutLoopControl := by
  refine ⟨?_, ?_, ?_⟩
  · intro scope hScope
    simp [Locals.Source.Ctx.withoutLoopControl] at hScope
  · intro scope hScope
    simp [Locals.Source.Ctx.withoutLoopControl] at hScope
  · intro scope hScope
    exact hCompatible.2.2 hScope

theorem loop_contextCompatible
    (ctx : Locals.Source.Ctx) (scope : Layout) :
    ContextCompatible (loop scope)
      (ctx.withLoopControl scope scope) := by
  refine ⟨?_, ?_, ?_⟩
  · intro current hCurrent
    simp [Locals.Source.Ctx.withLoopControl] at hCurrent
    exact hCurrent.symm
  · intro current hCurrent
    simp [Locals.Source.Ctx.withLoopControl] at hCurrent
    exact hCurrent.symm
  · intro current hCurrent
    trivial

theorem noLoop_contextCompatible_withoutLoopControl
    (ctx : Locals.Source.Ctx) :
    ContextCompatible noLoop ctx.withoutLoopControl := by
  refine ⟨?_, ?_, ?_⟩
  · intro scope hScope
    simp [Locals.Source.Ctx.withoutLoopControl] at hScope
  · intro scope hScope
    simp [Locals.Source.Ctx.withoutLoopControl] at hScope
  · intro scope hScope
    trivial

end ControlPolicy

/-- The ordinary adjacent outcome relation strengthened by a control policy. -/
inductive PolicyOpenResultRel (policy : ControlPolicy)
    (finalCtx : Locals.Ctx)
    (suffix : List Word) (returns : List Structured.ReturnDest) :
    (Locals.Source.Effectful.Outcome Locals.Source.State ×
      Locals.Source.Ctx) →
    Structured.Outcome → Prop
  | regular {source sourceCtx target} :
      ControlPolicy.ContextCompatible policy sourceCtx →
      Frame.CtxRel sourceCtx finalCtx →
      Frame.StateRel finalCtx.layout suffix returns source target →
      PolicyOpenResultRel policy finalCtx suffix returns
        (Locals.Source.Effectful.Outcome.regular source, sourceCtx)
        (Structured.Outcome.regular target)
  | brk {source sourceCtx target scope} :
      ControlPolicy.ContextCompatible policy sourceCtx →
      policy.brk scope →
      Frame.StateRel scope suffix returns source target →
      PolicyOpenResultRel policy finalCtx suffix returns
        (Locals.Source.Effectful.Outcome.brk source, sourceCtx)
        (Structured.Outcome.brk target)
  | cont {source sourceCtx target scope} :
      ControlPolicy.ContextCompatible policy sourceCtx →
      policy.cont scope →
      Frame.StateRel scope suffix returns source target →
      PolicyOpenResultRel policy finalCtx suffix returns
        (Locals.Source.Effectful.Outcome.cont source, sourceCtx)
        (Structured.Outcome.cont target)
  | leave {source sourceCtx target scope} :
      ControlPolicy.ContextCompatible policy sourceCtx →
      policy.leave scope →
      Frame.StateRel scope suffix returns source target →
      PolicyOpenResultRel policy finalCtx suffix returns
        (Locals.Source.Effectful.Outcome.leave source, sourceCtx)
        (Structured.Outcome.leave target)
  | halt {kind source sourceCtx target} :
      ControlPolicy.ContextCompatible policy sourceCtx →
      source.shared = target.evm.toSharedState →
      target.returns = returns →
      PolicyOpenResultRel policy finalCtx suffix returns
        (Locals.Source.Effectful.Outcome.halt kind source, sourceCtx)
        (Structured.Outcome.halt kind target)

abbrev PolicyOpenOutcomeRel (policy : ControlPolicy)
    (finalCtx : Locals.Ctx)
    (suffix : List Word) (returns : List Structured.ReturnDest) :
    Except EVMException
        (Locals.Source.Effectful.Outcome Locals.Source.State ×
          Locals.Source.Ctx) →
      Except EVMException Structured.Outcome → Prop :=
  Simulation.Interaction.ExceptRel
    (fun _sourceError _targetError => True)
    (PolicyOpenResultRel policy finalCtx suffix returns)

theorem PolicyOpenResultRel.forget
    {policy : ControlPolicy}
    {finalCtx : Locals.Ctx}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source :
      Locals.Source.Effectful.Outcome Locals.Source.State ×
        Locals.Source.Ctx}
    {target : Structured.Outcome}
    (hRel :
      PolicyOpenResultRel policy finalCtx suffix returns source target) :
    OpenResultRel finalCtx suffix returns source target := by
  cases hRel with
  | regular _ hCtx hState => exact OpenResultRel.regular hCtx hState
  | brk _ _ hState => exact OpenResultRel.brk hState
  | cont _ _ hState => exact OpenResultRel.cont hState
  | leave _ _ hState => exact OpenResultRel.leave hState
  | halt _ hShared hReturns => exact OpenResultRel.halt hShared hReturns

/-- Scoped outcomes retain policy evidence for abrupt child completion. -/
inductive PolicyScopedResultRel (policy : ControlPolicy)
    (outerCtx : Locals.Ctx)
    (suffix : List Word) (returns : List Structured.ReturnDest) :
    Locals.Source.Effectful.Outcome Locals.Source.State →
      Structured.Outcome → Prop
  | regular {source target} :
      Frame.StateRel outerCtx.layout suffix returns source target →
      PolicyScopedResultRel policy outerCtx suffix returns
        (Locals.Source.Effectful.Outcome.regular source)
        (Structured.Outcome.regular target)
  | brk {source target scope} :
      policy.brk scope →
      Frame.StateRel scope suffix returns source target →
      PolicyScopedResultRel policy outerCtx suffix returns
        (Locals.Source.Effectful.Outcome.brk source)
        (Structured.Outcome.brk target)
  | cont {source target scope} :
      policy.cont scope →
      Frame.StateRel scope suffix returns source target →
      PolicyScopedResultRel policy outerCtx suffix returns
        (Locals.Source.Effectful.Outcome.cont source)
        (Structured.Outcome.cont target)
  | leave {source target scope} :
      policy.leave scope →
      Frame.StateRel scope suffix returns source target →
      PolicyScopedResultRel policy outerCtx suffix returns
        (Locals.Source.Effectful.Outcome.leave source)
        (Structured.Outcome.leave target)
  | halt {kind source target} :
      source.shared = target.evm.toSharedState →
      target.returns = returns →
      PolicyScopedResultRel policy outerCtx suffix returns
        (Locals.Source.Effectful.Outcome.halt kind source)
        (Structured.Outcome.halt kind target)

abbrev PolicyScopedOutcomeRel (policy : ControlPolicy)
    (outerCtx : Locals.Ctx)
    (suffix : List Word) (returns : List Structured.ReturnDest) :
    Except EVMException
        (Locals.Source.Effectful.Outcome Locals.Source.State) →
      Except EVMException Structured.Outcome → Prop :=
  Simulation.Interaction.ExceptRel
    (fun _sourceError _targetError => True)
    (PolicyScopedResultRel policy outerCtx suffix returns)

theorem PolicyScopedResultRel.forget
    {policy : ControlPolicy}
    {outerCtx : Locals.Ctx}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.Effectful.Outcome Locals.Source.State}
    {target : Structured.Outcome}
    (hRel :
      PolicyScopedResultRel policy outerCtx suffix returns source target) :
    ScopedResultRel outerCtx suffix returns source target := by
  cases hRel with
  | regular hState => exact ScopedResultRel.regular hState
  | brk _ hState => exact ScopedResultRel.brk hState
  | cont _ hState => exact ScopedResultRel.cont hState
  | leave _ hState => exact ScopedResultRel.leave hState
  | halt hShared hReturns => exact ScopedResultRel.halt hShared hReturns

theorem PolicyScopedResultRel.withContext
    {policy : ControlPolicy}
    {outerCtx : Locals.Ctx}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.Effectful.Outcome Locals.Source.State}
    {target : Structured.Outcome}
    {sourceCtx : Locals.Source.Ctx}
    (hPolicyCtx : ControlPolicy.ContextCompatible policy sourceCtx)
    (hCtx : Frame.CtxRel sourceCtx outerCtx)
    (hRel :
      PolicyScopedResultRel policy outerCtx suffix returns source target) :
    PolicyOpenResultRel policy outerCtx suffix returns
      (source, sourceCtx) target := by
  cases hRel with
  | regular hState =>
      exact PolicyOpenResultRel.regular hPolicyCtx hCtx hState
  | brk hPolicy hState =>
      exact PolicyOpenResultRel.brk hPolicyCtx hPolicy hState
  | cont hPolicy hState =>
      exact PolicyOpenResultRel.cont hPolicyCtx hPolicy hState
  | leave hPolicy hState =>
      exact PolicyOpenResultRel.leave hPolicyCtx hPolicy hState
  | halt hShared hReturns =>
      exact PolicyOpenResultRel.halt hPolicyCtx hShared hReturns

theorem policy_forward_scoped_withContext
    {truncated : EVMException → Prop}
    {policy : ControlPolicy}
    {outerCtx : Locals.Ctx}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {sourceCtx : Locals.Source.Ctx}
    {sourceRun :
      Simulation.Interaction EVMException
        (Locals.Source.Effectful.Outcome Locals.Source.State)}
    {targetRun :
      Simulation.Interaction EVMException Structured.Outcome}
    (hPolicyCtx : ControlPolicy.ContextCompatible policy sourceCtx)
    (hCtx : Frame.CtxRel sourceCtx outerCtx)
    (hRel :
      Simulation.Interaction.ForwardRel
        truncated
        (PolicyScopedOutcomeRel policy outerCtx suffix returns)
        sourceRun targetRun) :
    Simulation.Interaction.ForwardRel
      truncated
      (PolicyOpenOutcomeRel policy outerCtx suffix returns)
      (Simulation.Interaction.bind sourceRun
        (fun outcome =>
          Simulation.Interaction.pure (outcome, sourceCtx)))
      targetRun := by
  conv_rhs =>
    rw [← Simulation.Interaction.bind_pure targetRun]
  apply Simulation.Interaction.ForwardRel.bind hRel
  intro sourceResult targetResult hResult
  apply Simulation.Interaction.ForwardRel.done
  apply Simulation.Interaction.ExceptRel.ok
  exact hResult.withContext hPolicyCtx hCtx

theorem ScopedResultRel.withContext
    {outerCtx : Locals.Ctx}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.Effectful.Outcome Locals.Source.State}
    {target : Structured.Outcome}
    {sourceCtx : Locals.Source.Ctx}
    (hCtx : Frame.CtxRel sourceCtx outerCtx)
    (hRel : ScopedResultRel outerCtx suffix returns source target) :
    OpenResultRel outerCtx suffix returns (source, sourceCtx) target := by
  cases hRel with
  | regular hState => exact OpenResultRel.regular hCtx hState
  | brk hState => exact OpenResultRel.brk hState
  | cont hState => exact OpenResultRel.cont hState
  | leave hState => exact OpenResultRel.leave hState
  | halt hShared hReturns => exact OpenResultRel.halt hShared hReturns

theorem forward_scoped_withContext
    {truncated : EVMException → Prop}
    {outerCtx : Locals.Ctx}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {sourceCtx : Locals.Source.Ctx}
    {sourceRun :
      Simulation.Interaction EVMException
        (Locals.Source.Effectful.Outcome Locals.Source.State)}
    {targetRun :
      Simulation.Interaction EVMException Structured.Outcome}
    (hCtx : Frame.CtxRel sourceCtx outerCtx)
    (hRel :
      Simulation.Interaction.ForwardRel
        truncated
        (ScopedOutcomeRel outerCtx suffix returns)
        sourceRun targetRun) :
    Simulation.Interaction.ForwardRel
      truncated
      (OpenOutcomeRel outerCtx suffix returns)
      (Simulation.Interaction.bind sourceRun
        (fun outcome =>
          Simulation.Interaction.pure (outcome, sourceCtx)))
      targetRun := by
  conv_rhs =>
    rw [← Simulation.Interaction.bind_pure targetRun]
  apply Simulation.Interaction.ForwardRel.bind hRel
  intro sourceResult targetResult hResult
  apply Simulation.Interaction.ForwardRel.done
  apply Simulation.Interaction.ExceptRel.ok
  exact hResult.withContext hCtx

namespace SwitchCompile

/-- Structural relation between source and compiled switch selection. -/
inductive SelectedRel (ctx : Locals.Ctx) :
    Option Locals.Block → Option Expressions.Block → Prop
  | none : SelectedRel ctx none none
  | some {source : Locals.Block} {target : Expressions.Block}
      {bodyCode : List Expressions.Stmt} {bodyCtx : Locals.Ctx} :
      Locals.Block.compileOpen ctx source = some (bodyCode, bodyCtx) →
      Locals.finishScoped ctx bodyCtx bodyCode = some target →
      SelectedRel ctx (some source) (some target)

theorem SelectedRel.some_parts
    {ctx : Locals.Ctx} {source : Locals.Block}
    {target : Option Expressions.Block}
    (hRel : SelectedRel ctx (Option.some source) target) :
    ∃ targetBody bodyCode bodyCtx,
      target = Option.some targetBody ∧
        Locals.Block.compileOpen ctx source =
          Option.some (bodyCode, bodyCtx) ∧
        Locals.finishScoped ctx bodyCtx bodyCode =
          Option.some targetBody := by
  cases hRel with
  | some hCompile hFinish =>
      exact ⟨_, _, _, rfl, hCompile, hFinish⟩

theorem SelectedRel.none_target
    {ctx : Locals.Ctx} {target : Option Expressions.Block}
    (hRel : SelectedRel ctx Option.none target) : target = Option.none := by
  cases hRel
  rfl

/--
The ordinary case/default compiler preserves branch selection and records the
adjacent open-body and cleanup artifacts for the selected branch.
-/
theorem selectedRel_of_compile
    (ctx : Locals.Ctx) (value : Word)
    {cases : List (Word × Locals.Block)}
    {defaultBody : Option Locals.Block}
    {compiledCases : List (Word × Expressions.Block)}
    {compiledDefault : Option Expressions.Block}
    (hCases :
      Locals.CaseList.compile ctx cases = some compiledCases)
    (hDefault :
      Locals.Default.compile ctx defaultBody = some compiledDefault) :
    SelectedRel ctx
      (Locals.Source.Switch.select value cases defaultBody)
      (Expressions.EffectSemantics.Switch.select
        value compiledCases compiledDefault) := by
  induction cases generalizing compiledCases with
  | nil =>
      simp [Locals.CaseList.compile] at hCases
      subst compiledCases
      cases defaultBody with
      | none =>
          simp [Locals.Default.compile] at hDefault
          subst compiledDefault
          exact SelectedRel.none
      | some body =>
          cases hBody : Locals.Block.compileOpen ctx body with
          | none =>
              simp [Locals.Default.compile, hBody] at hDefault
          | some bodyResult =>
              rcases bodyResult with ⟨bodyCode, bodyCtx⟩
              cases hFinish :
                  Locals.finishScoped ctx bodyCtx bodyCode with
              | none =>
                  simp [Locals.Default.compile, hBody, hFinish] at hDefault
              | some compiledBody =>
                  simp [Locals.Default.compile, hBody, hFinish] at hDefault
                  subst compiledDefault
                  exact SelectedRel.some hBody hFinish
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      cases hBody : Locals.Block.compileOpen ctx body with
      | none =>
          simp [Locals.CaseList.compile, hBody] at hCases
      | some bodyResult =>
          rcases bodyResult with ⟨bodyCode, bodyCtx⟩
          cases hFinish :
              Locals.finishScoped ctx bodyCtx bodyCode with
          | none =>
              simp [Locals.CaseList.compile, hBody, hFinish] at hCases
          | some compiledBody =>
              cases hRest : Locals.CaseList.compile ctx rest with
              | none =>
                  simp [Locals.CaseList.compile, hBody, hFinish, hRest]
                    at hCases
              | some compiledRest =>
                  simp [Locals.CaseList.compile, hBody, hFinish, hRest]
                    at hCases
                  subst compiledCases
                  by_cases hMatch : caseValue = value
                  · simp [Locals.Source.Switch.select,
                      Expressions.EffectSemantics.Switch.select, hMatch]
                    exact SelectedRel.some hBody hFinish
                  · simpa [Locals.Source.Switch.select,
                      Expressions.EffectSemantics.Switch.select, hMatch]
                      using ih hRest

end SwitchCompile

theorem RegularResultRel.toOpen
    {finalCtx : Locals.Ctx}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source :
      Locals.Source.Effectful.Outcome Locals.Source.State ×
        Locals.Source.Ctx}
    {target : Structured.Outcome}
    (hRel :
      RegularResultRel finalCtx suffix returns source target) :
    OpenResultRel finalCtx suffix returns source target := by
  rcases source with ⟨sourceOutcome, sourceCtx⟩
  rcases sourceOutcome with ⟨sourceState, sourceMode⟩
  rcases target with ⟨targetState, targetMode⟩
  cases hRel.sourceMode
  cases hRel.targetMode
  exact OpenResultRel.regular hRel.context hRel.state

theorem open_of_regular
    {finalCtx : Locals.Ctx}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {sourceRun :
      Simulation.Interaction EVMException
        (Locals.Source.Effectful.Outcome Locals.Source.State ×
          Locals.Source.Ctx)}
    {targetRun :
      Simulation.Interaction EVMException Structured.Outcome}
    (hRel :
      Simulation.Interaction.Rel
        (RegularOutcomeRel finalCtx suffix returns)
        sourceRun targetRun) :
    Simulation.Interaction.Rel
      (OpenOutcomeRel finalCtx suffix returns)
      sourceRun targetRun := by
  apply Simulation.Interaction.Rel.mono hRel
  intro sourceDone targetDone hDone
  cases hDone with
  | error _ =>
      exact Simulation.Interaction.ExceptRel.error trivial
  | ok hResult =>
      exact
        Simulation.Interaction.ExceptRel.ok
          (RegularResultRel.toOpen hResult)

/--
A source-owned zero-result expression statement preserves the current frame
and context through its ordinary compiled code statement.
-/
theorem openRun_expr_generated
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx : Locals.Ctx)
    (fuel : Nat) (expr : Locals.Expr 0)
    {code : Structured.Code}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hScoped : Scope.ExprScoped targetCtx.layout expr)
    (hSupported :
      InteractionSemantics.Expr.OpenSupported expr)
    (hCompile :
      Locals.Expr.compileCode targetCtx 0 expr = some code)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (RegularOutcomeRel targetCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx fuel (.expr expr) source)
      (Expressions.InteractionSemantics.Stmt.openRun
        targetProgram fuel (.code code) target) := by
  have hExpr :=
    Expr.openEval_compileCode expr targetCtx 0
      hScoped hSupported hCompile hInitial.expr
  have hWrapped :
      Simulation.Interaction.Rel
        (RegularOutcomeRel targetCtx suffix returns)
        (Simulation.Interaction.bind
          (InteractionSemantics.Expr.openEval expr source)
          (fun result =>
            Simulation.Interaction.pure
              (Locals.Source.Effectful.Outcome.regular result.1,
                sourceCtx)))
        (Simulation.Interaction.bind
          (Structured.InteractionSemantics.Code.openRun code target)
          (fun final =>
            Simulation.Interaction.pure
              (Structured.Outcome.regular final))) := by
    apply Simulation.Interaction.Rel.bind hExpr
    intro sourceFinal targetFinal hFinal
    apply Simulation.Interaction.Rel.done
    apply Simulation.Interaction.ExceptRel.ok
    exact
      { sourceMode := rfl
        targetMode := rfl
        context := hCtx
        state :=
          Frame.StateRel.ofExprResultZero hInitial hFinal }
  unfold InteractionSemantics.Expr.openEval
    Structured.InteractionSemantics.Code.openRun at hWrapped
  unfold InteractionSemantics.Stmt.openRun
    Expressions.InteractionSemantics.Stmt.openRun
    InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel
  simp only [Locals.Source.Effectful.Control.Stmt.run,
    Expressions.EffectSemantics.Control.Stmt.run]
  exact hWrapped

/--
A fresh source local is preserved by expression evaluation followed by the
ordinary silent `bindLocals` marker.
-/
theorem openRun_let_generated
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx : Locals.Ctx)
    (fuel : Nat) {name : Name} (valueExpr : Locals.Expr 1)
    {valueCode : Structured.Code}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hFresh : name ∉ targetCtx.layout)
    (hValueScoped :
      Scope.ExprScoped targetCtx.layout valueExpr)
    (hValueSupported :
      InteractionSemantics.Expr.OpenSupported valueExpr)
    (hValueCompile :
      Locals.Expr.compileCode targetCtx 0 valueExpr = some valueCode)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (RegularOutcomeRel
        (targetCtx.withLayout (name :: targetCtx.layout))
        suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx fuel (.let_ name valueExpr) source)
      (Expressions.InteractionSemantics.Stmt.openRun
        targetProgram fuel
        (.code
          (valueCode ++
            Locals.bindLocals 0 (name :: targetCtx.layout)))
        target) := by
  have hValue :=
    Expr.openEvalOne_compileCode valueExpr targetCtx 0
      hValueScoped hValueSupported hValueCompile hInitial.expr
  have hCore :
      Simulation.Interaction.Rel
        (RegularOutcomeRel
          (targetCtx.withLayout (name :: targetCtx.layout))
          suffix returns)
        (Simulation.Interaction.bind
          (InteractionSemantics.Expr.openEvalOne valueExpr source)
          (fun result =>
            Simulation.Interaction.pure
              (Locals.Source.Effectful.Outcome.regular
                (result.1.insert name result.2),
                { sourceCtx with
                  scope := name :: sourceCtx.scope })))
        (Simulation.Interaction.bind
          (Structured.InteractionSemantics.Code.openRun valueCode target)
          (fun targetAfterValue =>
            Simulation.Interaction.bind
              (Structured.InteractionSemantics.Code.openRun
                (Locals.bindLocals 0 (name :: targetCtx.layout))
                targetAfterValue)
              (fun final =>
                Simulation.Interaction.pure
                  (Structured.Outcome.regular final)))) := by
    apply Simulation.Interaction.Rel.bind hValue
    intro sourceAfterValue targetAfterValue hValueResult
    rcases sourceAfterValue with ⟨sourceFinal, value⟩
    rw [show
        Locals.bindLocals 0 (name :: targetCtx.layout) =
          [.bindLocals 0 (name :: targetCtx.layout)] by rfl,
      Code.openRun_bindLocals]
    apply Simulation.Interaction.Rel.done
    apply Simulation.Interaction.ExceptRel.ok
    exact
      { sourceMode := rfl
        targetMode := rfl
        context := hCtx.prependScope name
        state :=
          Frame.StateRel.ofExprResultOneInsert
            hFresh hInitial hValueResult }
  unfold InteractionSemantics.Expr.openEvalOne
    InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel at hCore
  unfold InteractionSemantics.Stmt.openRun
    Expressions.InteractionSemantics.Stmt.openRun
    InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel
  simp only [Locals.Source.Effectful.Control.Stmt.run,
    Locals.Source.Effectful.StateModel.insert,
    Expressions.EffectSemantics.Control.Stmt.run]
  change
    Simulation.Interaction.Rel
      (RegularOutcomeRel
        (targetCtx.withLayout (name :: targetCtx.layout))
        suffix returns)
      _
      (Simulation.Interaction.bind
        (Structured.InteractionSemantics.Code.openRun
          (valueCode ++
            Locals.bindLocals 0 (name :: targetCtx.layout))
          target)
        (fun final =>
          Simulation.Interaction.pure
            (Structured.Outcome.regular final)))
  rw [Structured.InteractionSemantics.Code.openRun_append]
  simpa [Simulation.Interaction.bind_assoc] using hCore

/--
Checked source-statement form of assignment preservation. This theorem uses the
ordinary source statement semantics and the ordinary emitted Expressions code
statement; the external-effect tree is inherited solely from the assigned
expression.
-/
theorem openRun_assign_generated
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx : Locals.Ctx)
    (fuel : Nat) {name : Name} (valueExpr : Locals.Expr 1)
    {depth : Nat} {valueCode : Structured.Code}
    {swapOp : Structured.BasicOp}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hNodup : targetCtx.layout.Nodup)
    (hDepth :
      Layout.lookupDepth? name targetCtx.layout = some (depth + 1))
    (hValueScoped :
      Scope.ExprScoped targetCtx.layout valueExpr)
    (hValueSupported :
      InteractionSemantics.Expr.OpenSupported valueExpr)
    (hValueCompile :
      Locals.Expr.compileCode targetCtx 0 valueExpr = some valueCode)
    (hSwap :
      StackOp.swap? (depth + 1) = some swapOp)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (RegularOutcomeRel targetCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx fuel (.assign name valueExpr) source)
      (Expressions.InteractionSemantics.Stmt.openRun
        targetProgram fuel
        (.code
          (valueCode ++
            [.op swapOp, .op .pop] ++
              Locals.bindLocals 0 targetCtx.layout))
        target) := by
  have hMem :
      name ∈ targetCtx.layout :=
    Layout.mem_of_lookupDepth?_eq_some hDepth
  obtain ⟨old, hOld⟩ := hInitial.defined hMem
  have hContains :
      source.vars.contains name = true := by
    simp [Locals.Source.Store.contains, hOld]
  have hAssign :=
    openAssign_compileCode targetCtx valueExpr
      hNodup hDepth hValueScoped hValueSupported
      hValueCompile hSwap hInitial
  have hWrapped :
      Simulation.Interaction.Rel
        (RegularOutcomeRel targetCtx suffix returns)
        (Simulation.Interaction.bind
          (Simulation.Interaction.bind
            (InteractionSemantics.Expr.openEvalOne valueExpr source)
            (fun result =>
              Simulation.Interaction.pure
                (result.1.insert name result.2)))
          (fun final =>
            Simulation.Interaction.pure
              (Locals.Source.Effectful.Outcome.regular final,
                sourceCtx)))
        (Simulation.Interaction.bind
          (Structured.InteractionSemantics.Code.openRun
            (valueCode ++
              [.op swapOp, .op .pop] ++
                Locals.bindLocals 0 targetCtx.layout)
            target)
          (fun final =>
            Simulation.Interaction.pure
              (Structured.Outcome.regular final))) := by
    apply Simulation.Interaction.Rel.bind hAssign
    intro sourceFinal targetFinal hFinal
    apply Simulation.Interaction.Rel.done
    apply Simulation.Interaction.ExceptRel.ok
    exact
      { sourceMode := rfl
        targetMode := rfl
        context := hCtx
        state := hFinal }
  unfold InteractionSemantics.Expr.openEvalOne
    Structured.InteractionSemantics.Code.openRun
    InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel at hWrapped
  simp only [Locals.Source.State.insert] at hWrapped
  unfold InteractionSemantics.Stmt.openRun
    Expressions.InteractionSemantics.Stmt.openRun
    InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel
  simp only [Locals.Source.Effectful.Control.Stmt.run,
    Locals.Source.Effectful.StateModel.vars,
    Expressions.EffectSemantics.Control.Stmt.run]
  dsimp only [id]
  rw [hContains]
  simp only [Locals.Source.Effectful.StateModel.withVars,
    if_true,
    Locals.Source.State.withVars]
  simpa [Simulation.Interaction.bind_assoc] using hWrapped

/--
Compiler-facing zero-result expression theorem. All emitted code and final
context evidence are derived from the existing `Stmt.compile`.
-/
theorem openRun_expr_of_compile
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (fuel : Nat) (expr : Locals.Expr 0)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hCompile :
      Locals.Stmt.compile targetCtx (.expr expr) =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hScoped : Scope.ExprScoped targetCtx.layout expr)
    (hSupported :
      InteractionSemantics.Expr.OpenSupported expr)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (RegularOutcomeRel finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx (fuel + 1) (.expr expr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (fuel + 2) { stmts := stmts } target) := by
  cases hCode :
      Locals.Expr.compileCode targetCtx 0 expr with
  | none =>
      simp [Locals.Stmt.compile, hCode] at hCompile
  | some code =>
      simp [Locals.Stmt.compile, hCode] at hCompile
      rcases hCompile with ⟨rfl, rfl⟩
      simp only [Locals.codeStmt]
      rw [TargetBlock.openRun_single_code]
      exact
        openRun_expr_generated
          sourceProgram targetProgram sourceCtx targetCtx
          (fuel + 1) expr hCtx hScoped hSupported hCode hInitial

/--
Compiler-facing fresh-local theorem, deriving the emitted layout marker and
final context from the ordinary compiler result.
-/
theorem openRun_let_of_compile
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (fuel : Nat) {name : Name} (valueExpr : Locals.Expr 1)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hCompile :
      Locals.Stmt.compile targetCtx (.let_ name valueExpr) =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hFresh : name ∉ targetCtx.layout)
    (hValueScoped :
      Scope.ExprScoped targetCtx.layout valueExpr)
    (hValueSupported :
      InteractionSemantics.Expr.OpenSupported valueExpr)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (RegularOutcomeRel finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx (fuel + 1)
          (.let_ name valueExpr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (fuel + 2) { stmts := stmts } target) := by
  cases hCode :
      Locals.Expr.compileCode targetCtx 0 valueExpr with
  | none =>
      simp [Locals.Stmt.compile, hCode] at hCompile
  | some valueCode =>
      simp [Locals.Stmt.compile, hCode] at hCompile
      rcases hCompile with ⟨rfl, rfl⟩
      simp only [Locals.codeStmt]
      rw [TargetBlock.openRun_single_code]
      exact
        openRun_let_generated
          sourceProgram targetProgram sourceCtx targetCtx
          (fuel + 1) valueExpr hCtx hFresh
          hValueScoped hValueSupported
          hCode hInitial

/--
Compiler-facing assignment theorem. The stack depth, expression code, SWAP
opcode, emitted statement, and final context all come from the ordinary
compiler result.
-/
theorem openRun_assign_of_compile
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (fuel : Nat) {name : Name} (valueExpr : Locals.Expr 1)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hCompile :
      Locals.Stmt.compile targetCtx (.assign name valueExpr) =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hNodup : targetCtx.layout.Nodup)
    (hValueScoped :
      Scope.ExprScoped targetCtx.layout valueExpr)
    (hValueSupported :
      InteractionSemantics.Expr.OpenSupported valueExpr)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (RegularOutcomeRel finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx (fuel + 1)
          (.assign name valueExpr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (fuel + 2) { stmts := stmts } target) := by
  cases hDepth :
      Layout.lookupDepth? name targetCtx.layout with
  | none =>
      simp [Locals.Stmt.compile, hDepth] at hCompile
  | some rawDepth =>
      cases rawDepth with
      | zero =>
          simp [Locals.Stmt.compile, hDepth, StackOp.swap?]
            at hCompile
      | succ depth =>
          cases hCode :
              Locals.Expr.compileCode targetCtx 0 valueExpr with
          | none =>
              simp [Locals.Stmt.compile, hDepth, hCode]
                at hCompile
          | some valueCode =>
              cases hSwap :
                  StackOp.swap? (depth + 1) with
              | none =>
                  simp [Locals.Stmt.compile, hDepth, hCode, hSwap]
                    at hCompile
              | some swapOp =>
                  simp [Locals.Stmt.compile, hDepth, hCode, hSwap]
                    at hCompile
                  rcases hCompile with ⟨rfl, rfl⟩
                  simp only [Locals.codeStmt]
                  rw [TargetBlock.openRun_single_code]
                  simpa [List.append_assoc] using
                    openRun_assign_generated
                      sourceProgram targetProgram sourceCtx targetCtx
                      (fuel + 1) valueExpr hCtx hNodup hDepth hValueScoped
                      hValueSupported hCode hSwap hInitial

/--
Compiler-facing `break` preservation. The ordinary compiler supplies the
selected lexical depth and cleanup code; the proof exposes the corresponding
source scope and relates the abrupt outcomes directly.
-/
theorem policy_openRun_brk_of_compile
    (policy : ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (fuel : Nat)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hCompile :
      Locals.Stmt.compile targetCtx .brk =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hPolicy : ControlPolicy.ContextCompatible policy sourceCtx)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (PolicyOpenOutcomeRel policy finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx fuel .brk source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (fuel + 3) { stmts := stmts } target) := by
  obtain ⟨depth, cleanup, hDepth, hCleanup, rfl, rfl⟩ :=
    Locals.Stmt.compile_brk_components hCompile
  cases hScope : sourceCtx.breakScope? with
  | none =>
      have hDepthRel := hCtx.breakDepth
      rw [hScope] at hDepthRel
      simp at hDepthRel
      rw [hDepthRel] at hDepth
      contradiction
  | some scope =>
      obtain ⟨pre, hLayout, hScopeDepth⟩ :=
        hCtx.breakLayout hScope
      rw [hDepth] at hScopeDepth
      cases hScopeDepth
      obtain ⟨finalTarget, hCleanupRun, hFinal⟩ :=
        hInitial.openRun_cleanupTo hLayout hCleanup
      have hTargetRun :=
        TargetBlock.openRun_code_brk
          targetProgram fuel cleanup target finalTarget hCleanupRun
      unfold InteractionSemantics.Stmt.openRun
        InteractionSemantics.stateModel
        Locals.Source.Effectful.Ordinary.stateModel
      simp only [Locals.Source.Effectful.Control.Stmt.run]
      rw [hScope]
      rw [show
          Expressions.InteractionSemantics.Block.openRun
              targetProgram (fuel + 3)
              { stmts :=
                  Locals.codeStmt cleanup ++
                    [Expressions.Stmt.brk] }
              target =
            .done (.ok (Structured.Outcome.brk finalTarget)) by
          simpa [Locals.codeStmt] using hTargetRun]
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact
        PolicyOpenResultRel.brk hPolicy (hPolicy.1 hScope) hFinal

theorem openRun_brk_of_compile
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (fuel : Nat)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hCompile :
      Locals.Stmt.compile targetCtx .brk =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (OpenOutcomeRel finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx fuel .brk source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (fuel + 3) { stmts := stmts } target) := by
  have hRel :=
    policy_openRun_brk_of_compile
      ControlPolicy.any sourceProgram targetProgram
      sourceCtx targetCtx finalCtx fuel hCompile hCtx
      (ControlPolicy.any_contextCompatible sourceCtx) hInitial
  apply Simulation.Interaction.Rel.mono hRel
  intro sourceDone targetDone hDone
  cases hDone with
  | error _ => exact Simulation.Interaction.ExceptRel.error trivial
  | ok hResult =>
      exact Simulation.Interaction.ExceptRel.ok hResult.forget

/--
Compiler-facing `continue` preservation, using the compiler-owned loop-scope
depth and cleanup code.
-/
theorem policy_openRun_cont_of_compile
    (policy : ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (fuel : Nat)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hCompile :
      Locals.Stmt.compile targetCtx .cont =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hPolicy : ControlPolicy.ContextCompatible policy sourceCtx)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (PolicyOpenOutcomeRel policy finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx fuel .cont source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (fuel + 3) { stmts := stmts } target) := by
  obtain ⟨depth, cleanup, hDepth, hCleanup, rfl, rfl⟩ :=
    Locals.Stmt.compile_cont_components hCompile
  cases hScope : sourceCtx.continueScope? with
  | none =>
      have hDepthRel := hCtx.continueDepth
      rw [hScope] at hDepthRel
      simp at hDepthRel
      rw [hDepthRel] at hDepth
      contradiction
  | some scope =>
      obtain ⟨pre, hLayout, hScopeDepth⟩ :=
        hCtx.continueLayout hScope
      rw [hDepth] at hScopeDepth
      cases hScopeDepth
      obtain ⟨finalTarget, hCleanupRun, hFinal⟩ :=
        hInitial.openRun_cleanupTo hLayout hCleanup
      have hTargetRun :=
        TargetBlock.openRun_code_cont
          targetProgram fuel cleanup target finalTarget hCleanupRun
      unfold InteractionSemantics.Stmt.openRun
        InteractionSemantics.stateModel
        Locals.Source.Effectful.Ordinary.stateModel
      simp only [Locals.Source.Effectful.Control.Stmt.run]
      rw [hScope]
      rw [show
          Expressions.InteractionSemantics.Block.openRun
              targetProgram (fuel + 3)
              { stmts :=
                  Locals.codeStmt cleanup ++
                    [Expressions.Stmt.cont] }
              target =
            .done (.ok (Structured.Outcome.cont finalTarget)) by
          simpa [Locals.codeStmt] using hTargetRun]
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact
        PolicyOpenResultRel.cont hPolicy (hPolicy.2.1 hScope) hFinal

theorem openRun_cont_of_compile
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (fuel : Nat)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hCompile :
      Locals.Stmt.compile targetCtx .cont =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (OpenOutcomeRel finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx fuel .cont source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (fuel + 3) { stmts := stmts } target) := by
  have hRel :=
    policy_openRun_cont_of_compile
      ControlPolicy.any sourceProgram targetProgram
      sourceCtx targetCtx finalCtx fuel hCompile hCtx
      (ControlPolicy.any_contextCompatible sourceCtx) hInitial
  apply Simulation.Interaction.Rel.mono hRel
  intro sourceDone targetDone hDone
  cases hDone with
  | error _ => exact Simulation.Interaction.ExceptRel.error trivial
  | ok hResult =>
      exact Simulation.Interaction.ExceptRel.ok hResult.forget

/--
Compiler-facing `leave` preservation. At this boundary `leaveRetc = 0`, so the
ordinary preserving cleanup reduces to the same lexical frame restriction used
by source semantics. A live return destination is supplied by the enclosing
function activation.
-/
theorem policy_openRun_leave_of_compile
    (policy : ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (fuel : Nat)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hCompile :
      Locals.Stmt.compile targetCtx .leave =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hPolicy : ControlPolicy.ContextCompatible policy sourceCtx)
    (hReturns : returns ≠ [])
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (PolicyOpenOutcomeRel policy finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx fuel .leave source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (fuel + 3) { stmts := stmts } target) := by
  obtain ⟨depth, cleanup, hDepth, hCleanup, rfl, rfl⟩ :=
    Locals.Stmt.compile_leave_components hCompile
  cases hScope : sourceCtx.leaveScope? with
  | none =>
      have hDepthRel := hCtx.leaveDepth
      rw [hScope] at hDepthRel
      simp at hDepthRel
      rw [hDepthRel] at hDepth
      contradiction
  | some scope =>
      obtain ⟨pre, hLayout, hScopeDepth⟩ :=
        hCtx.leaveLayout hScope
      rw [hDepth] at hScopeDepth
      cases hScopeDepth
      have hCleanupZero :
          Locals.Ctx.cleanupToPreserving?
              finalCtx 0 scope.length =
            some cleanup := by
        simpa [hCtx.leaveRetc] using hCleanup
      have hCleanupPlain :
          Locals.Ctx.cleanupTo? finalCtx scope.length =
            some cleanup := by
        simpa using hCleanupZero
      obtain ⟨finalTarget, hCleanupRun, hFinal⟩ :=
        hInitial.openRun_cleanupTo hLayout hCleanupPlain
      have hFinalReturns : finalTarget.returns ≠ [] := by
        rw [hFinal.returns]
        exact hReturns
      have hTargetRun :=
        TargetBlock.openRun_code_leave
          targetProgram fuel cleanup target finalTarget
            hCleanupRun hFinalReturns
      unfold InteractionSemantics.Stmt.openRun
        InteractionSemantics.stateModel
        Locals.Source.Effectful.Ordinary.stateModel
      simp only [Locals.Source.Effectful.Control.Stmt.run]
      rw [hScope]
      rw [show
          Expressions.InteractionSemantics.Block.openRun
              targetProgram (fuel + 3)
              { stmts :=
                  Locals.codeStmt cleanup ++
                    [Expressions.Stmt.leave] }
              target =
            .done (.ok (Structured.Outcome.leave finalTarget)) by
          simpa [Locals.codeStmt] using hTargetRun]
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact
        PolicyOpenResultRel.leave hPolicy (hPolicy.2.2 hScope) hFinal

theorem openRun_leave_of_compile
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (fuel : Nat)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hCompile :
      Locals.Stmt.compile targetCtx .leave =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hReturns : returns ≠ [])
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (OpenOutcomeRel finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx fuel .leave source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (fuel + 3) { stmts := stmts } target) := by
  have hRel :=
    policy_openRun_leave_of_compile
      ControlPolicy.any sourceProgram targetProgram
      sourceCtx targetCtx finalCtx fuel hCompile hCtx
      (ControlPolicy.any_contextCompatible sourceCtx)
      hReturns hInitial
  apply Simulation.Interaction.Rel.mono hRel
  intro sourceDone targetDone hDone
  cases hDone with
  | error _ => exact Simulation.Interaction.ExceptRel.error trivial
  | ok hResult =>
      exact Simulation.Interaction.ExceptRel.ok hResult.forget

/--
Compiler-facing terminal-with-arguments preservation. Argument evaluation may
contain arbitrary ordered open effects; terminal execution then consumes only
that exact value prefix and leaves all caller-owned stack data abstract.
-/
theorem openRun_terminalArgs_of_compile
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (fuel : Nat) (kind : Assembly.HaltKind)
    (args : Locals.ExprSeq kind.argCount)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hCompile :
      Locals.Stmt.compile targetCtx (.terminalArgs kind args) =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hScoped : Scope.ExprSeqScoped targetCtx.layout args)
    (hSupported :
      InteractionSemantics.ExprSeq.OpenSupported args)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (OpenOutcomeRel finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx fuel
          (.terminalArgs kind args) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (fuel + 3) { stmts := stmts } target) := by
  obtain ⟨argsCode, hArgsCode, rfl, rfl⟩ :=
    Locals.Stmt.compile_terminalArgs_components hCompile
  have hArgs :=
    Expr.openEvalSeq_compileCode args finalCtx 0
      hScoped hSupported hArgsCode hInitial.expr
  have hCore :
      Simulation.Interaction.Rel
        (OpenOutcomeRel finalCtx suffix returns)
        (Simulation.Interaction.bind
          (InteractionSemantics.ExprSeq.openEval args source)
          (fun result =>
            Simulation.Interaction.bind
              (InteractionSemantics.Primitive.openTerminal
                kind result.1 result.2)
              (fun final =>
                Simulation.Interaction.pure
                  (Locals.Source.Effectful.Outcome.halt kind final,
                    sourceCtx))))
        (Simulation.Interaction.bind
          (Structured.InteractionSemantics.Code.openRun
            argsCode target)
          (fun afterArgs =>
            Simulation.Interaction.bind
              (Structured.InteractionSemantics.Terminal.openStep
                kind afterArgs)
              (fun final =>
                Simulation.Interaction.pure
                  (Structured.Outcome.halt kind final)))) := by
    apply Simulation.Interaction.Rel.bind hArgs
    intro sourceAfterArgs targetAfterArgs hArgsResult
    rcases sourceAfterArgs with ⟨sourceAfterArgs, values⟩
    have hTerminal :=
      Primitive.openTerminal_frame
        hArgsResult.length hArgsResult.shared hArgsResult.stack
    apply Simulation.Interaction.Rel.bind hTerminal
    intro sourceFinal targetFinal hTerminalResult
    apply Simulation.Interaction.Rel.done
    apply Simulation.Interaction.ExceptRel.ok
    apply OpenResultRel.halt hTerminalResult.1
    exact
      hTerminalResult.2.trans
        (hArgsResult.returns.trans hInitial.returns)
  unfold InteractionSemantics.Stmt.openRun
    InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel
  simp only [Locals.Source.Effectful.Control.Stmt.run]
  rw [show
      Expressions.InteractionSemantics.Block.openRun
          targetProgram (fuel + 3)
          { stmts :=
              Locals.codeStmt argsCode ++
                [Expressions.Stmt.terminal kind] }
          target =
        Simulation.Interaction.bind
          (Structured.InteractionSemantics.Code.openRun
            argsCode target)
          (fun afterArgs =>
            Simulation.Interaction.bind
              (Structured.InteractionSemantics.Terminal.openStep
                kind afterArgs)
              (fun final =>
                Simulation.Interaction.pure
                  (Structured.Outcome.halt kind final))) by
      simpa [Locals.codeStmt] using
        TargetBlock.openRun_code_terminal
          targetProgram fuel argsCode kind target]
  exact hCore

/--
Compiler-facing plain-terminal preservation for the genuinely zero-argument
terminal form. Argument-taking halts are represented by `terminalArgs`; this
premise prevents a bare target terminal from consuming caller-frame words.
-/
theorem openRun_terminal_of_compile
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (fuel : Nat) (kind : Assembly.HaltKind)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hCompile :
      Locals.Stmt.compile targetCtx (.terminal kind) =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hArgCount : kind.argCount = 0)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (OpenOutcomeRel finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx fuel (.terminal kind) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (fuel + 3) { stmts := stmts } target) := by
  obtain ⟨rfl, rfl⟩ :=
    Locals.Stmt.compile_terminal_components hCompile
  have hLayout :
      finalCtx.layout = finalCtx.layout ++ ([] : Layout) := by
    simp
  have hCleanup :
      Locals.Ctx.cleanupTo? finalCtx 0 =
        some finalCtx.cleanupAll := by
    simp [Locals.Ctx.cleanupTo?, Locals.Ctx.cleanupAll]
  obtain ⟨afterCleanup, hCleanupRun, hCleanupFrame⟩ :=
    hInitial.openRun_cleanupTo hLayout hCleanup
  have hLength :
      ([] : List Word).length = kind.argCount := by
    simpa [hArgCount]
  have hCleanupStack :
      afterCleanup.evm.stack =
        ([] : List Word).reverse ++ suffix := by
    simpa using hCleanupFrame.suffix
  have hCleanupShared :
      afterCleanup.evm.toSharedState = source.shared := by
    simpa [Locals.Source.State.restrictTo] using
      hCleanupFrame.shared
  have hTerminal :=
    Primitive.openTerminal_frame
      (source := source)
      hLength hCleanupShared hCleanupStack
  have hWrapped :
      Simulation.Interaction.Rel
        (OpenOutcomeRel finalCtx suffix returns)
        (Simulation.Interaction.bind
          (InteractionSemantics.Primitive.openTerminal
            kind source [])
          (fun final =>
            Simulation.Interaction.pure
              (Locals.Source.Effectful.Outcome.halt kind final,
                sourceCtx)))
        (Simulation.Interaction.bind
          (Structured.InteractionSemantics.Terminal.openStep
            kind afterCleanup)
          (fun final =>
            Simulation.Interaction.pure
              (Structured.Outcome.halt kind final))) := by
    apply Simulation.Interaction.Rel.bind hTerminal
    intro sourceFinal targetFinal hTerminalResult
    apply Simulation.Interaction.Rel.done
    apply Simulation.Interaction.ExceptRel.ok
    apply OpenResultRel.halt hTerminalResult.1
    exact
      hTerminalResult.2.trans hCleanupFrame.returns
  unfold InteractionSemantics.Stmt.openRun
    InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel
  simp only [Locals.Source.Effectful.Control.Stmt.run]
  rw [show
      Expressions.InteractionSemantics.Block.openRun
          targetProgram (fuel + 3)
          { stmts :=
              Locals.codeStmt finalCtx.cleanupAll ++
                [Expressions.Stmt.terminal kind] }
          target =
        Simulation.Interaction.bind
          (Structured.InteractionSemantics.Code.openRun
            finalCtx.cleanupAll target)
          (fun afterCode =>
            Simulation.Interaction.bind
              (Structured.InteractionSemantics.Terminal.openStep
                kind afterCode)
              (fun final =>
                Simulation.Interaction.pure
                  (Structured.Outcome.halt kind final))) by
      simpa [Locals.codeStmt] using
        TargetBlock.openRun_code_terminal
          targetProgram fuel finalCtx.cleanupAll kind target]
  rw [hCleanupRun]
  exact hWrapped

end Stmt

namespace Block

def FuelTruncated (error : EVMException) : Prop :=
  error = .InvalidInstruction

/--
The empty source block is the base case of fuel-indexed forward preservation.
Zero source fuel is recorded as truncation; any positive source/target budgets
produce the same regular frame.
-/
theorem openRun_empty
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hTargetFuel : 1 ≤ targetFuel)
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.ForwardRel
      FuelTruncated
      (Stmt.OpenOutcomeRel targetCtx suffix returns)
      (InteractionSemantics.Block.openRun
        sourceProgram sourceCtx sourceFuel { stmts := [] } source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := [] } target) := by
  cases sourceFuel with
  | zero =>
      unfold InteractionSemantics.Block.openRun
        InteractionSemantics.stateModel
        Locals.Source.Effectful.Ordinary.stateModel
      simp only [Locals.Source.Effectful.Control.Block.runOpen]
      apply Simulation.Interaction.ForwardRel.truncated
      rfl
  | succ sourceFuel =>
      cases targetFuel with
      | zero =>
          omega
      | succ targetFuel =>
          unfold InteractionSemantics.Block.openRun
            Expressions.InteractionSemantics.Block.openRun
            InteractionSemantics.stateModel
            Locals.Source.Effectful.Ordinary.stateModel
          simp only [Locals.Source.Effectful.Control.Block.runOpen,
            Expressions.EffectSemantics.Control.Block.run]
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact Stmt.OpenResultRel.regular hCtx hInitial

end Block

namespace Stmt.Forward

/--
Fuel-lower-bound adapter for compiler-facing zero-result expression
statements. Expression statement semantics is fuel-insensitive; only the
enclosing target singleton block requires two units of control fuel.
-/
theorem expr_of_compile
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (expr : Locals.Expr 0)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hTargetFuel : 2 ≤ targetFuel)
    (hCompile :
      Locals.Stmt.compile targetCtx (.expr expr) =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hScoped : Scope.ExprScoped targetCtx.layout expr)
    (hSupported :
      InteractionSemantics.Expr.OpenSupported expr)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (OpenOutcomeRel finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.expr expr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := stmts } target) := by
  let extra := targetFuel - 2
  have hFuelEq : targetFuel = extra + 2 := by
    omega
  have hRel :=
    openRun_expr_of_compile
      sourceProgram targetProgram sourceCtx targetCtx finalCtx
      extra expr hCompile hCtx hScoped hSupported hInitial
  have hSourceEq :
      InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx sourceFuel (.expr expr) source =
        InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx (extra + 1) (.expr expr) source := by
    unfold InteractionSemantics.Stmt.openRun
      InteractionSemantics.stateModel
      Locals.Source.Effectful.Ordinary.stateModel
    simp only [Locals.Source.Effectful.Control.Stmt.run]
  rw [hSourceEq, hFuelEq]
  exact
    Simulation.Interaction.ForwardRel.ofRel
      (open_of_regular hRel)

theorem let_of_compile
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    {name : Name} (valueExpr : Locals.Expr 1)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hTargetFuel : 2 ≤ targetFuel)
    (hCompile :
      Locals.Stmt.compile targetCtx (.let_ name valueExpr) =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hFresh : name ∉ targetCtx.layout)
    (hScoped : Scope.ExprScoped targetCtx.layout valueExpr)
    (hSupported :
      InteractionSemantics.Expr.OpenSupported valueExpr)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (OpenOutcomeRel finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel
          (.let_ name valueExpr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := stmts } target) := by
  let extra := targetFuel - 2
  have hFuelEq : targetFuel = extra + 2 := by
    omega
  have hRel :=
    openRun_let_of_compile
      sourceProgram targetProgram sourceCtx targetCtx finalCtx
      extra valueExpr hCompile hCtx hFresh hScoped hSupported hInitial
  have hSourceEq :
      InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx sourceFuel
            (.let_ name valueExpr) source =
        InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx (extra + 1)
            (.let_ name valueExpr) source := by
    unfold InteractionSemantics.Stmt.openRun
      InteractionSemantics.stateModel
      Locals.Source.Effectful.Ordinary.stateModel
    simp only [Locals.Source.Effectful.Control.Stmt.run]
  rw [hSourceEq, hFuelEq]
  exact
    Simulation.Interaction.ForwardRel.ofRel
      (open_of_regular hRel)

theorem assign_of_compile
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    {name : Name} (valueExpr : Locals.Expr 1)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hTargetFuel : 2 ≤ targetFuel)
    (hCompile :
      Locals.Stmt.compile targetCtx (.assign name valueExpr) =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hNodup : targetCtx.layout.Nodup)
    (hScoped : Scope.ExprScoped targetCtx.layout valueExpr)
    (hSupported :
      InteractionSemantics.Expr.OpenSupported valueExpr)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (OpenOutcomeRel finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel
          (.assign name valueExpr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := stmts } target) := by
  let extra := targetFuel - 2
  have hFuelEq : targetFuel = extra + 2 := by
    omega
  have hRel :=
    openRun_assign_of_compile
      sourceProgram targetProgram sourceCtx targetCtx finalCtx
      extra valueExpr hCompile hCtx hNodup hScoped hSupported hInitial
  have hSourceEq :
      InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx sourceFuel
            (.assign name valueExpr) source =
        InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx (extra + 1)
            (.assign name valueExpr) source := by
    unfold InteractionSemantics.Stmt.openRun
      InteractionSemantics.stateModel
      Locals.Source.Effectful.Ordinary.stateModel
    simp only [Locals.Source.Effectful.Control.Stmt.run]
  rw [hSourceEq, hFuelEq]
  exact
    Simulation.Interaction.ForwardRel.ofRel
      (open_of_regular hRel)

theorem policy_brk_of_compile
    (policy : ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hTargetFuel : 3 ≤ targetFuel)
    (hCompile :
      Locals.Stmt.compile targetCtx .brk =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hPolicy : ControlPolicy.ContextCompatible policy sourceCtx)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (PolicyOpenOutcomeRel policy finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel .brk source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := stmts } target) := by
  let extra := targetFuel - 3
  have hFuelEq : targetFuel = extra + 3 := by
    omega
  have hRel :=
    policy_openRun_brk_of_compile
      policy sourceProgram targetProgram sourceCtx targetCtx finalCtx
      extra hCompile hCtx hPolicy hInitial
  have hSourceEq :
      InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx sourceFuel .brk source =
        InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx extra .brk source := by
    unfold InteractionSemantics.Stmt.openRun
      InteractionSemantics.stateModel
      Locals.Source.Effectful.Ordinary.stateModel
    simp only [Locals.Source.Effectful.Control.Stmt.run]
  rw [hSourceEq, hFuelEq]
  exact Simulation.Interaction.ForwardRel.ofRel hRel

theorem brk_of_compile
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hTargetFuel : 3 ≤ targetFuel)
    (hCompile :
      Locals.Stmt.compile targetCtx .brk =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (OpenOutcomeRel finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel .brk source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := stmts } target) := by
  have hPolicy :=
    policy_brk_of_compile
      ControlPolicy.any sourceProgram targetProgram
      sourceCtx targetCtx finalCtx sourceFuel targetFuel
      hTargetFuel hCompile hCtx
      (ControlPolicy.any_contextCompatible sourceCtx) hInitial
  apply Simulation.Interaction.ForwardRel.mono hPolicy
  intro sourceDone targetDone hDone
  cases hDone with
  | error _ => exact Simulation.Interaction.ExceptRel.error trivial
  | ok hResult =>
      exact Simulation.Interaction.ExceptRel.ok hResult.forget

theorem policy_cont_of_compile
    (policy : ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hTargetFuel : 3 ≤ targetFuel)
    (hCompile :
      Locals.Stmt.compile targetCtx .cont =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hPolicy : ControlPolicy.ContextCompatible policy sourceCtx)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (PolicyOpenOutcomeRel policy finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel .cont source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := stmts } target) := by
  let extra := targetFuel - 3
  have hFuelEq : targetFuel = extra + 3 := by
    omega
  have hRel :=
    policy_openRun_cont_of_compile
      policy sourceProgram targetProgram sourceCtx targetCtx finalCtx
      extra hCompile hCtx hPolicy hInitial
  have hSourceEq :
      InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx sourceFuel .cont source =
        InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx extra .cont source := by
    unfold InteractionSemantics.Stmt.openRun
      InteractionSemantics.stateModel
      Locals.Source.Effectful.Ordinary.stateModel
    simp only [Locals.Source.Effectful.Control.Stmt.run]
  rw [hSourceEq, hFuelEq]
  exact Simulation.Interaction.ForwardRel.ofRel hRel

theorem cont_of_compile
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hTargetFuel : 3 ≤ targetFuel)
    (hCompile :
      Locals.Stmt.compile targetCtx .cont =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (OpenOutcomeRel finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel .cont source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := stmts } target) := by
  have hPolicy :=
    policy_cont_of_compile
      ControlPolicy.any sourceProgram targetProgram
      sourceCtx targetCtx finalCtx sourceFuel targetFuel
      hTargetFuel hCompile hCtx
      (ControlPolicy.any_contextCompatible sourceCtx) hInitial
  apply Simulation.Interaction.ForwardRel.mono hPolicy
  intro sourceDone targetDone hDone
  cases hDone with
  | error _ => exact Simulation.Interaction.ExceptRel.error trivial
  | ok hResult =>
      exact Simulation.Interaction.ExceptRel.ok hResult.forget

theorem policy_leave_of_compile
    (policy : ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hTargetFuel : 3 ≤ targetFuel)
    (hCompile :
      Locals.Stmt.compile targetCtx .leave =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hPolicy : ControlPolicy.ContextCompatible policy sourceCtx)
    (hReturns : returns ≠ [])
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (PolicyOpenOutcomeRel policy finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel .leave source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := stmts } target) := by
  let extra := targetFuel - 3
  have hFuelEq : targetFuel = extra + 3 := by
    omega
  have hRel :=
    policy_openRun_leave_of_compile
      policy sourceProgram targetProgram sourceCtx targetCtx finalCtx
      extra hCompile hCtx hPolicy hReturns hInitial
  have hSourceEq :
      InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx sourceFuel .leave source =
        InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx extra .leave source := by
    unfold InteractionSemantics.Stmt.openRun
      InteractionSemantics.stateModel
      Locals.Source.Effectful.Ordinary.stateModel
    simp only [Locals.Source.Effectful.Control.Stmt.run]
  rw [hSourceEq, hFuelEq]
  exact Simulation.Interaction.ForwardRel.ofRel hRel

theorem leave_of_compile
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hTargetFuel : 3 ≤ targetFuel)
    (hCompile :
      Locals.Stmt.compile targetCtx .leave =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hReturns : returns ≠ [])
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (OpenOutcomeRel finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel .leave source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := stmts } target) := by
  have hPolicy :=
    policy_leave_of_compile
      ControlPolicy.any sourceProgram targetProgram
      sourceCtx targetCtx finalCtx sourceFuel targetFuel
      hTargetFuel hCompile hCtx
      (ControlPolicy.any_contextCompatible sourceCtx)
      hReturns hInitial
  apply Simulation.Interaction.ForwardRel.mono hPolicy
  intro sourceDone targetDone hDone
  cases hDone with
  | error _ => exact Simulation.Interaction.ExceptRel.error trivial
  | ok hResult =>
      exact Simulation.Interaction.ExceptRel.ok hResult.forget

theorem terminal_of_compile
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (kind : Assembly.HaltKind)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hTargetFuel : 3 ≤ targetFuel)
    (hCompile :
      Locals.Stmt.compile targetCtx (.terminal kind) =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hArgCount : kind.argCount = 0)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (OpenOutcomeRel finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.terminal kind) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := stmts } target) := by
  let extra := targetFuel - 3
  have hFuelEq : targetFuel = extra + 3 := by
    omega
  have hRel :=
    openRun_terminal_of_compile
      sourceProgram targetProgram sourceCtx targetCtx finalCtx
      extra kind hCompile hCtx hArgCount hInitial
  have hSourceEq :
      InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx sourceFuel (.terminal kind) source =
        InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx extra (.terminal kind) source := by
    unfold InteractionSemantics.Stmt.openRun
      InteractionSemantics.stateModel
      Locals.Source.Effectful.Ordinary.stateModel
    simp only [Locals.Source.Effectful.Control.Stmt.run]
  rw [hSourceEq, hFuelEq]
  exact Simulation.Interaction.ForwardRel.ofRel hRel

theorem terminalArgs_of_compile
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (kind : Assembly.HaltKind)
    (args : Locals.ExprSeq kind.argCount)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hTargetFuel : 3 ≤ targetFuel)
    (hCompile :
      Locals.Stmt.compile targetCtx (.terminalArgs kind args) =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hScoped : Scope.ExprSeqScoped targetCtx.layout args)
    (hSupported :
      InteractionSemantics.ExprSeq.OpenSupported args)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (OpenOutcomeRel finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel
          (.terminalArgs kind args) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := stmts } target) := by
  let extra := targetFuel - 3
  have hFuelEq : targetFuel = extra + 3 := by
    omega
  have hRel :=
    openRun_terminalArgs_of_compile
      sourceProgram targetProgram sourceCtx targetCtx finalCtx
      extra kind args hCompile hCtx hScoped hSupported hInitial
  have hSourceEq :
      InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx sourceFuel
            (.terminalArgs kind args) source =
        InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx extra
            (.terminalArgs kind args) source := by
    unfold InteractionSemantics.Stmt.openRun
      InteractionSemantics.stateModel
      Locals.Source.Effectful.Ordinary.stateModel
    simp only [Locals.Source.Effectful.Control.Stmt.run]
  rw [hSourceEq, hFuelEq]
  exact Simulation.Interaction.ForwardRel.ofRel hRel

/--
Scoped block preservation from an already-related open body and the
compiler-owned cleanup. This is the shared child-block interface used by
lexical blocks, conditionals, switches, and loops.
-/
theorem scopedBlock_generated
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx)
    (targetCtx bodyCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (body : Locals.Block)
    (bodyCode : List Expressions.Stmt) (cleanup : Structured.Code)
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hLayout : ∃ pre, bodyCtx.layout = pre ++ targetCtx.layout)
    (hCleanup :
      bodyCtx.cleanupTo? targetCtx.layout.length = some cleanup)
    (hCleanupFuel : 2 ≤ targetFuel - bodyCode.length)
    (hBody :
      Simulation.Interaction.ForwardRel
        Block.FuelTruncated
        (OpenOutcomeRel bodyCtx suffix returns)
        (InteractionSemantics.Block.openRun
          sourceProgram sourceCtx sourceFuel body source)
        (Expressions.InteractionSemantics.Block.openRun
          targetProgram targetFuel { stmts := bodyCode } target)) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (ScopedOutcomeRel targetCtx suffix returns)
      (InteractionSemantics.Block.openRunScoped
        sourceProgram sourceCtx body sourceFuel source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel
          { stmts := bodyCode ++ Locals.codeStmt cleanup } target) := by
  rw [Expressions.InteractionSemantics.Block.openRun_append]
  unfold InteractionSemantics.Block.openRunScoped
    InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel
  unfold Locals.Source.Effectful.Control.Block.runScoped
  change
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (ScopedOutcomeRel targetCtx suffix returns)
      (Simulation.Interaction.bind
        (InteractionSemantics.Block.openRun
          sourceProgram sourceCtx sourceFuel body source)
        _)
      _
  apply Simulation.Interaction.ForwardRel.bind hBody
  intro sourceResult targetResult hResult
  cases hResult with
  | @regular sourceAfter sourceAfterCtx targetAfter hInnerCtx hState =>
      obtain ⟨pre, hLayout⟩ := hLayout
      obtain ⟨afterCleanup, hCleanupRun, hFinal⟩ :=
        hState.openRun_cleanupTo hLayout hCleanup
      have hTargetCleanup :=
        TargetBlock.openRun_single_code_done
          targetProgram (targetFuel - bodyCode.length)
          cleanup targetAfter afterCleanup
          hCleanupFuel hCleanupRun
      simp only [Structured.Outcome.regular_mode,
        Structured.Outcome.regular_state,
        Locals.Source.Effectful.Outcome.regular,
        Locals.codeStmt]
      rw [hTargetCleanup]
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      apply ScopedResultRel.regular
      simpa [hCtx.layout] using hFinal
  | brk hState =>
      apply Simulation.Interaction.ForwardRel.ofRel
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact ScopedResultRel.brk hState
  | cont hState =>
      apply Simulation.Interaction.ForwardRel.ofRel
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact ScopedResultRel.cont hState
  | leave hState =>
      apply Simulation.Interaction.ForwardRel.ofRel
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact ScopedResultRel.leave hState
  | halt hShared hReturns =>
      apply Simulation.Interaction.ForwardRel.ofRel
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact ScopedResultRel.halt hShared hReturns

theorem scopedBlock_abrupt_generated
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx)
    (targetCtx bodyCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (body : Locals.Block)
    (bodyCode : List Expressions.Stmt)
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hExit : Locals.StmtList.hasDirectExit body.stmts = true)
    (hBody :
      Simulation.Interaction.ForwardRel
        Block.FuelTruncated
        (OpenOutcomeRel bodyCtx suffix returns)
        (InteractionSemantics.Block.openRun
          sourceProgram sourceCtx sourceFuel body source)
        (Expressions.InteractionSemantics.Block.openRun
          targetProgram targetFuel { stmts := bodyCode } target)) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (ScopedOutcomeRel targetCtx suffix returns)
      (InteractionSemantics.Block.openRunScoped
        sourceProgram sourceCtx body sourceFuel source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := bodyCode } target) := by
  unfold InteractionSemantics.Block.openRunScoped
    InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel
    Locals.Source.Effectful.Control.Block.runScoped
  change
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (ScopedOutcomeRel targetCtx suffix returns)
      (Simulation.Interaction.bind
        (InteractionSemantics.Block.openRun
          sourceProgram sourceCtx sourceFuel body source) _)
      _
  have hNonregular :=
    InteractionSemantics.Abrupt.block_allDone_of_hasDirectExit
      sourceProgram sourceCtx sourceFuel body source hExit
  have hStrong :=
    Simulation.Interaction.ForwardRel.strengthen_left hBody hNonregular
  have hStrong' :
      Simulation.Interaction.ForwardRel
        Block.FuelTruncated
        (Simulation.Interaction.ExceptRel
          (fun (_ : EVMException) (_ : EVMException) => True)
          (fun sourceResult targetResult =>
            OpenResultRel bodyCtx suffix returns sourceResult targetResult ∧
              sourceResult.1.mode ≠ .regular))
        (InteractionSemantics.Block.openRun
          sourceProgram sourceCtx sourceFuel body source)
        (Expressions.InteractionSemantics.Block.openRun
          targetProgram targetFuel { stmts := bodyCode } target) := by
    apply Simulation.Interaction.ForwardRel.mono hStrong
    intro sourceDone targetDone hDone
    rcases hDone with ⟨hRelated, hMode⟩
    cases hRelated with
    | error _ => exact .error trivial
    | ok hOpen => exact .ok ⟨hOpen, hMode⟩
  conv_rhs =>
    rw [← Simulation.Interaction.bind_pure
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := bodyCode } target)]
  apply Simulation.Interaction.ForwardRel.bind hStrong'
  intro sourceResult targetResult hResult
  rcases hResult with ⟨hRelated, hMode⟩
  cases hRelated with
  | regular _hCtx _hState => exact False.elim (hMode rfl)
  | brk hState =>
      exact Simulation.Interaction.ForwardRel.done
        (.ok (ScopedResultRel.brk hState))
  | cont hState =>
      exact Simulation.Interaction.ForwardRel.done
        (.ok (ScopedResultRel.cont hState))
  | leave hState =>
      exact Simulation.Interaction.ForwardRel.done
        (.ok (ScopedResultRel.leave hState))
  | halt hShared hReturns =>
      exact Simulation.Interaction.ForwardRel.done
        (.ok (ScopedResultRel.halt hShared hReturns))

/--
Fuel-aligned loop recursion. Source fuel `n` is simulated by target fuel
`n + slack`; one iteration decrements both sides, while the fixed slack covers
the compiled body and post cleanup blocks. Exact body break/continue frames are
provided by the loop policy, and post execution forbids unconsumed loop exits.
-/
theorem if_generated
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx)
    (targetCtx bodyCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    (cond : Locals.Expr 1) (body : Locals.Block)
    (condCode : Structured.Code)
    (bodyCode : List Expressions.Stmt) (cleanup : Structured.Code)
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hTargetFuel : bodyCode.length + 4 ≤ targetFuel)
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hCondScoped : Scope.ExprScoped targetCtx.layout cond)
    (hCondSupported :
      InteractionSemantics.Expr.OpenSupported cond)
    (hCondCompile :
      Locals.Expr.compileCode targetCtx 0 cond = some condCode)
    (hLayout : ∃ pre, bodyCtx.layout = pre ++ targetCtx.layout)
    (hCleanup :
      bodyCtx.cleanupTo? targetCtx.layout.length = some cleanup)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target)
    (hBody :
      ∀ {sourceAfter : Locals.Source.State}
        {targetAfter : Structured.RunState},
        Frame.StateRel targetCtx.layout suffix returns
            sourceAfter targetAfter →
          Simulation.Interaction.ForwardRel
            Block.FuelTruncated
            (OpenOutcomeRel bodyCtx suffix returns)
            (InteractionSemantics.Block.openRun
              sourceProgram sourceCtx sourceFuel body sourceAfter)
            (Expressions.InteractionSemantics.Block.openRun
              targetProgram (targetFuel - 2)
                { stmts := bodyCode } targetAfter)) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (OpenOutcomeRel targetCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx (sourceFuel + 1)
          (.if_ cond body) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel
          { stmts :=
              [Expressions.Stmt.if_ (.code condCode)
                { stmts :=
                    bodyCode ++ Locals.codeStmt cleanup }] }
          target) := by
  rw [TargetBlock.openRun_single_stmt_of_fuel
    targetProgram targetFuel _ target (by omega)]
  have hTargetStmtFuel :
      targetFuel - 1 = (targetFuel - 2) + 1 := by
    omega
  rw [hTargetStmtFuel]
  unfold InteractionSemantics.Stmt.openRun
    InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel
    Expressions.InteractionSemantics.Stmt.openRun
  simp only [Locals.Source.Effectful.Control.Stmt.run,
    Expressions.EffectSemantics.Control.Stmt.run]
  have hCond :=
    Expr.openEvalCondition_compileCode
      cond targetCtx hCondScoped hCondSupported hCondCompile hInitial
  apply Simulation.Interaction.ForwardRel.bind
    (Simulation.Interaction.ForwardRel.ofRel hCond)
  intro sourceResult targetResult hResult
  rcases sourceResult with ⟨sourceAfter, sourceCond⟩
  rcases targetResult with ⟨targetAfter, targetCond⟩
  cases hResult.condition
  cases sourceCond with
  | false =>
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact OpenResultRel.regular hCtx hResult.state
  | true =>
      have hCleanupFuel :
          2 ≤ (targetFuel - 2) - bodyCode.length := by
        omega
      have hScoped :=
        scopedBlock_generated
          sourceProgram targetProgram sourceCtx targetCtx bodyCtx
          sourceFuel (targetFuel - 2) body bodyCode cleanup
          hCtx hLayout hCleanup hCleanupFuel (hBody hResult.state)
      exact forward_scoped_withContext hCtx hScoped

theorem if_generated_abrupt
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx)
    (targetCtx bodyCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    (cond : Locals.Expr 1) (body : Locals.Block)
    (condCode : Structured.Code)
    (bodyCode : List Expressions.Stmt)
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hTargetFuel : bodyCode.length + 4 ≤ targetFuel)
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hCondScoped : Scope.ExprScoped targetCtx.layout cond)
    (hCondSupported : InteractionSemantics.Expr.OpenSupported cond)
    (hCondCompile :
      Locals.Expr.compileCode targetCtx 0 cond = some condCode)
    (hExit : Locals.StmtList.hasDirectExit body.stmts = true)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target)
    (hBody :
      ∀ {sourceAfter : Locals.Source.State}
        {targetAfter : Structured.RunState},
        Frame.StateRel targetCtx.layout suffix returns
            sourceAfter targetAfter →
          Simulation.Interaction.ForwardRel
            Block.FuelTruncated
            (OpenOutcomeRel bodyCtx suffix returns)
            (InteractionSemantics.Block.openRun
              sourceProgram sourceCtx sourceFuel body sourceAfter)
            (Expressions.InteractionSemantics.Block.openRun
              targetProgram (targetFuel - 2)
                { stmts := bodyCode } targetAfter)) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (OpenOutcomeRel targetCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx (sourceFuel + 1) (.if_ cond body) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel
          { stmts :=
              [Expressions.Stmt.if_ (.code condCode)
                { stmts := bodyCode }] }
          target) := by
  rw [TargetBlock.openRun_single_stmt_of_fuel
    targetProgram targetFuel _ target (by omega)]
  have hTargetStmtFuel :
      targetFuel - 1 = (targetFuel - 2) + 1 := by
    omega
  rw [hTargetStmtFuel]
  unfold InteractionSemantics.Stmt.openRun
    InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel
    Expressions.InteractionSemantics.Stmt.openRun
  simp only [Locals.Source.Effectful.Control.Stmt.run,
    Expressions.EffectSemantics.Control.Stmt.run]
  have hCond :=
    Expr.openEvalCondition_compileCode
      cond targetCtx hCondScoped hCondSupported hCondCompile hInitial
  apply Simulation.Interaction.ForwardRel.bind
    (Simulation.Interaction.ForwardRel.ofRel hCond)
  intro sourceResult targetResult hResult
  rcases sourceResult with ⟨sourceAfter, sourceCond⟩
  rcases targetResult with ⟨targetAfter, targetCond⟩
  cases hResult.condition
  cases sourceCond with
  | false =>
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact OpenResultRel.regular hCtx hResult.state
  | true =>
      have hScoped :=
        scopedBlock_abrupt_generated
          sourceProgram targetProgram sourceCtx targetCtx bodyCtx
          sourceFuel (targetFuel - 2) body bodyCode hExit
          (hBody hResult.state)
      exact forward_scoped_withContext hCtx hScoped

/--
Switch preservation through the compiler-owned selection relation. Scrutinee
evaluation and its target stack pop are proved once; selected branches reuse
the shared scoped-child theorem.
-/
theorem switch_generated
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    (scrutinee : Locals.Expr 1)
    (cases : List (Word × Locals.Block))
    (defaultBody : Option Locals.Block)
    (scrutineeCode : Structured.Code)
    (compiledCases : List (Word × Expressions.Block))
    (compiledDefault : Option Expressions.Block)
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hTargetFuel : 4 ≤ targetFuel)
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hScrutineeScoped : Scope.ExprScoped targetCtx.layout scrutinee)
    (hScrutineeSupported :
      InteractionSemantics.Expr.OpenSupported scrutinee)
    (hScrutineeCompile :
      Locals.Expr.compileCode targetCtx 0 scrutinee =
        some scrutineeCode)
    (hCases :
      Locals.CaseList.compile targetCtx cases = some compiledCases)
    (hDefault :
      Locals.Default.compile targetCtx defaultBody =
        some compiledDefault)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target)
    (hSelected :
      ∀ {selected : Locals.Block}
        {selectedTarget : Expressions.Block}
        {bodyCode : List Expressions.Stmt}
        {bodyCtx : Locals.Ctx}
        (value : Word),
        Locals.Source.Switch.select value cases defaultBody =
            some selected →
        Locals.Block.compileOpen targetCtx selected =
            some (bodyCode, bodyCtx) →
          Locals.finishScoped targetCtx bodyCtx bodyCode =
            some selectedTarget →
          bodyCode.length + 4 ≤ targetFuel ∧
            (∃ pre, bodyCtx.layout = pre ++ targetCtx.layout) ∧
            ∀ {sourceAfter : Locals.Source.State}
              {targetAfter : Structured.RunState},
              Frame.StateRel targetCtx.layout suffix returns
                  sourceAfter targetAfter →
                Simulation.Interaction.ForwardRel
                  Block.FuelTruncated
                  (OpenOutcomeRel bodyCtx suffix returns)
                  (InteractionSemantics.Block.openRun
                    sourceProgram sourceCtx sourceFuel selected sourceAfter)
                  (Expressions.InteractionSemantics.Block.openRun
                    targetProgram (targetFuel - 2)
                      { stmts := bodyCode } targetAfter)) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (OpenOutcomeRel targetCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx (sourceFuel + 1)
          (.switch scrutinee cases defaultBody) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel
          { stmts :=
              [Expressions.Stmt.switch (.code scrutineeCode)
                compiledCases compiledDefault] }
          target) := by
  rw [TargetBlock.openRun_single_stmt_of_fuel
    targetProgram targetFuel _ target (by omega)]
  have hTargetStmtFuel :
      targetFuel - 1 = (targetFuel - 2) + 1 := by
    omega
  rw [hTargetStmtFuel]
  unfold InteractionSemantics.Stmt.openRun
    InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel
    Expressions.InteractionSemantics.Stmt.openRun
  simp only [Locals.Source.Effectful.Control.Stmt.run,
    Expressions.EffectSemantics.Control.Stmt.run]
  have hScrutinee :=
    Expr.openEvalOne_compileCode
      scrutinee targetCtx 0 hScrutineeScoped hScrutineeSupported
      hScrutineeCompile hInitial.expr
  apply Simulation.Interaction.ForwardRel.bind
    (Simulation.Interaction.ForwardRel.ofRel hScrutinee)
  intro sourceResult targetAfterExpr hExpr
  rcases sourceResult with ⟨sourceAfter, value⟩
  let targetAfter :=
    targetAfterExpr.withEVM
      { targetAfterExpr.evm with stack := target.evm.stack }
  have hTargetStack :
      targetAfterExpr.evm.stack = value :: target.evm.stack := by
    simpa using hExpr.stack
  have hPop :
      (Structured.EffectSemantics.Ordinary.runStateModel.evm
          targetAfterExpr).stack.pop =
        some (target.evm.stack, value) := by
    rw [Structured.EffectSemantics.Ordinary.runStateModel_evm,
      hTargetStack]
    rfl
  rw [hPop]
  simp only [Structured.EffectSemantics.Ordinary.runStateModel_withEVM,
    Structured.EffectSemantics.Ordinary.runStateModel_evm]
  have hSelect :=
    SwitchCompile.selectedRel_of_compile
      targetCtx value hCases hDefault
  cases hSourceSelect :
      Locals.Source.Switch.select value cases defaultBody with
  | none =>
      cases hTargetSelect :
          Expressions.EffectSemantics.Switch.select
            value compiledCases compiledDefault with
      | none =>
          simp only
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          apply OpenResultRel.regular hCtx
          simpa [targetAfter] using
            Frame.StateRel.ofExprResultOnePop hInitial hExpr
      | some selectedTarget =>
          rw [hSourceSelect, hTargetSelect] at hSelect
          cases hSelect
  | some selected =>
      cases hTargetSelect :
          Expressions.EffectSemantics.Switch.select
            value compiledCases compiledDefault with
      | none =>
          rw [hSourceSelect, hTargetSelect] at hSelect
          cases hSelect
      | some selectedTarget =>
          rw [hSourceSelect, hTargetSelect] at hSelect
          cases hSelect with
          | @some _ _ bodyCode bodyCtx hBodyCompile hFinish =>
              simp only
              obtain ⟨hSelectedFuel, hLayout, hBody⟩ :=
                hSelected value hSourceSelect hBodyCompile hFinish
              obtain ⟨cleanup, hCleanup, hSelectedTarget⟩ :=
                Locals.finishScoped_components hFinish
              subst selectedTarget
              have hCleanupFuel :
                  2 ≤ (targetFuel - 2) - bodyCode.length := by
                omega
              have hScoped :=
                scopedBlock_generated
                  sourceProgram targetProgram sourceCtx targetCtx bodyCtx
                  sourceFuel (targetFuel - 2) selected bodyCode cleanup
                  hCtx hLayout hCleanup hCleanupFuel
                  (hBody (by
                    simpa [targetAfter] using
                      Frame.StateRel.ofExprResultOnePop hInitial hExpr))
              exact forward_scoped_withContext hCtx hScoped

/--
Lexical block preservation is a thin statement wrapper around the shared
scoped-child theorem.
-/
theorem block_generated
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx)
    (targetCtx bodyCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (body : Locals.Block)
    (bodyCode : List Expressions.Stmt) (cleanup : Structured.Code)
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hLayout : ∃ pre, bodyCtx.layout = pre ++ targetCtx.layout)
    (hCleanup :
      bodyCtx.cleanupTo? targetCtx.layout.length = some cleanup)
    (hCleanupFuel : 2 ≤ targetFuel - bodyCode.length)
    (hBody :
      Simulation.Interaction.ForwardRel
        Block.FuelTruncated
        (OpenOutcomeRel bodyCtx suffix returns)
        (InteractionSemantics.Block.openRun
          sourceProgram sourceCtx sourceFuel body source)
        (Expressions.InteractionSemantics.Block.openRun
          targetProgram targetFuel { stmts := bodyCode } target)) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (OpenOutcomeRel targetCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.block body) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel
          { stmts := bodyCode ++ Locals.codeStmt cleanup } target) := by
  have hScoped :=
    scopedBlock_generated
      sourceProgram targetProgram sourceCtx targetCtx bodyCtx
      sourceFuel targetFuel body bodyCode cleanup
      hCtx hLayout hCleanup hCleanupFuel hBody
  unfold InteractionSemantics.Stmt.openRun
    InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel
  simp only [Locals.Source.Effectful.Control.Stmt.run]
  rw [← Simulation.Interaction.bind_pure
    (Expressions.InteractionSemantics.Block.openRun
      targetProgram targetFuel
        { stmts := bodyCode ++ Locals.codeStmt cleanup } target)]
  apply Simulation.Interaction.ForwardRel.bind hScoped
  intro sourceResult targetResult hResult
  apply Simulation.Interaction.ForwardRel.done
  apply Simulation.Interaction.ExceptRel.ok
  exact hResult.withContext hCtx

/--
Compiler-facing lexical block theorem. All body code, final layout, cleanup,
and target fuel arithmetic are derived from the ordinary `Stmt.compile`
result; the only recursive input is the adjacent theorem for the source body.
-/
theorem block_of_compile
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (body : Locals.Block)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hOwned : Locals.Source.Block.SourceOwned body)
    (hTargetFuel : stmts.length + 1 ≤ targetFuel)
    (hCompile :
      Locals.Stmt.compile targetCtx (.block body) =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hBody :
      ∀ {bodyCode : List Expressions.Stmt}
        {bodyCtx : Locals.Ctx},
        Locals.Block.compileOpen targetCtx body =
            some (bodyCode, bodyCtx) →
          Simulation.Interaction.ForwardRel
            Block.FuelTruncated
            (OpenOutcomeRel bodyCtx suffix returns)
            (InteractionSemantics.Block.openRun
              sourceProgram sourceCtx sourceFuel body source)
            (Expressions.InteractionSemantics.Block.openRun
              targetProgram targetFuel
                { stmts := bodyCode } target)) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (OpenOutcomeRel finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.block body) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := stmts } target) := by
  obtain ⟨bodyCode, bodyCtx, lowerBody,
    hBodyCompile, hFinish, hCode, hFinal⟩ :=
    Locals.Stmt.compile_block_components hCompile
  obtain ⟨cleanup, hCleanup, hLowerBody⟩ :=
    Locals.finishScoped_components hFinish
  subst finalCtx
  subst stmts
  rw [hLowerBody] at hTargetFuel ⊢
  have hLayout :=
    Locals.Block.compileOpen_layout_extends_of_sourceOwned
      hOwned hBodyCompile
  have hCleanupFuel : 2 ≤ targetFuel - bodyCode.length := by
    have hLen : bodyCode.length + 2 ≤ targetFuel := by
      simpa [Locals.codeStmt, List.length_append] using hTargetFuel
    omega
  exact
    block_generated
      sourceProgram targetProgram sourceCtx targetCtx bodyCtx
      sourceFuel targetFuel body bodyCode cleanup
      hCtx hLayout hCleanup hCleanupFuel
      (hBody hBodyCompile)

/--
Compiler-facing conditional theorem. Generated condition code, child code,
cleanup, and the unchanged final context are all recovered from the ordinary
compiler result. The recursive premise is confined to the adjacent source
body and supplies its local target-fuel bound.
-/
theorem if_of_compile
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    (cond : Locals.Expr 1) (body : Locals.Block)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hOwned : Locals.Source.Block.SourceOwned body)
    (hCompile :
      Locals.Stmt.compile targetCtx (.if_ cond body) =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hCondScoped : Scope.ExprScoped targetCtx.layout cond)
    (hCondSupported :
      InteractionSemantics.Expr.OpenSupported cond)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target)
    (hBody :
      ∀ {bodyCode : List Expressions.Stmt}
        {bodyCtx : Locals.Ctx},
        Locals.Block.compileOpen targetCtx body =
            some (bodyCode, bodyCtx) →
          bodyCode.length + 4 ≤ targetFuel ∧
          ∀ {sourceAfter : Locals.Source.State}
            {targetAfter : Structured.RunState},
            Frame.StateRel targetCtx.layout suffix returns
                sourceAfter targetAfter →
              Simulation.Interaction.ForwardRel
                Block.FuelTruncated
                (OpenOutcomeRel bodyCtx suffix returns)
                (InteractionSemantics.Block.openRun
                  sourceProgram sourceCtx sourceFuel body sourceAfter)
                (Expressions.InteractionSemantics.Block.openRun
                  targetProgram (targetFuel - 2)
                    { stmts := bodyCode } targetAfter)) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (OpenOutcomeRel finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx (sourceFuel + 1)
          (.if_ cond body) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := stmts } target) := by
  obtain ⟨condCode, bodyCode, bodyCtx, lowerBody,
    hCondCompile, hBodyCompile, hFinish, hCode, hFinal⟩ :=
    Locals.Stmt.compile_if_components hCompile
  obtain ⟨hTargetFuel, hBodyForward⟩ := hBody hBodyCompile
  subst finalCtx
  subst stmts
  rcases Locals.finishScopedOrAbrupt_components hFinish with
    hScoped | hAbrupt
  · obtain ⟨cleanup, hCleanup, hLowerBody⟩ :=
      Locals.finishScoped_components hScoped
    have hLayout :=
      Locals.Block.compileOpen_layout_extends_of_sourceOwned
        hOwned hBodyCompile
    subst lowerBody
    exact
      if_generated
        sourceProgram targetProgram sourceCtx targetCtx bodyCtx
        sourceFuel targetFuel cond body condCode bodyCode cleanup
        hTargetFuel hCtx hCondScoped hCondSupported hCondCompile
        hLayout hCleanup hInitial hBodyForward
  · rw [hAbrupt.2.2]
    exact
      if_generated_abrupt
        sourceProgram targetProgram sourceCtx targetCtx bodyCtx
        sourceFuel targetFuel cond body condCode bodyCode
        hTargetFuel hCtx hCondScoped hCondSupported hCondCompile
        hAbrupt.2.1 hInitial hBodyForward

/-- Compiler-facing switch theorem over the ordinary case/default compiler. -/
theorem switch_of_compile
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    (scrutinee : Locals.Expr 1)
    (cases : List (Word × Locals.Block))
    (defaultBody : Option Locals.Block)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hTargetFuel : 4 ≤ targetFuel)
    (hCompile :
      Locals.Stmt.compile targetCtx
          (.switch scrutinee cases defaultBody) =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hScrutineeScoped : Scope.ExprScoped targetCtx.layout scrutinee)
    (hScrutineeSupported :
      InteractionSemantics.Expr.OpenSupported scrutinee)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target)
    (hSelected :
      ∀ {selected : Locals.Block}
        {selectedTarget : Expressions.Block}
        {bodyCode : List Expressions.Stmt}
        {bodyCtx : Locals.Ctx}
        (value : Word),
        Locals.Source.Switch.select value cases defaultBody =
            some selected →
        Locals.Block.compileOpen targetCtx selected =
            some (bodyCode, bodyCtx) →
          Locals.finishScoped targetCtx bodyCtx bodyCode =
            some selectedTarget →
          bodyCode.length + 4 ≤ targetFuel ∧
            (∃ pre, bodyCtx.layout = pre ++ targetCtx.layout) ∧
            ∀ {sourceAfter : Locals.Source.State}
              {targetAfter : Structured.RunState},
              Frame.StateRel targetCtx.layout suffix returns
                  sourceAfter targetAfter →
                Simulation.Interaction.ForwardRel
                  Block.FuelTruncated
                  (OpenOutcomeRel bodyCtx suffix returns)
                  (InteractionSemantics.Block.openRun
                    sourceProgram sourceCtx sourceFuel selected sourceAfter)
                  (Expressions.InteractionSemantics.Block.openRun
                    targetProgram (targetFuel - 2)
                      { stmts := bodyCode } targetAfter)) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (OpenOutcomeRel finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx (sourceFuel + 1)
          (.switch scrutinee cases defaultBody) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := stmts } target) := by
  obtain ⟨scrutineeCode, compiledCases, compiledDefault,
    hScrutineeCompile, hCases, hDefault, hCode, hFinal⟩ :=
    Locals.Stmt.compile_switch_components hCompile
  subst finalCtx
  subst stmts
  exact
    switch_generated
      sourceProgram targetProgram sourceCtx targetCtx
      sourceFuel targetFuel scrutinee cases defaultBody
      scrutineeCode compiledCases compiledDefault
      hTargetFuel hCtx hScrutineeScoped hScrutineeSupported
      hScrutineeCompile hCases hDefault hInitial hSelected

end Stmt.Forward

namespace Block

/-- Policy-indexed sequence composition used when a control owner needs exact
abrupt frames. The policy context invariant is passed from a regular head into
the tail and is otherwise preserved with the abrupt outcome. -/
theorem forward_cons
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx)
    (middleCtx finalCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    (stmt : Locals.Stmt) (rest : List Locals.Stmt)
    (headCode tailCode : List Expressions.Stmt)
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hHead :
      Simulation.Interaction.ForwardRel
        FuelTruncated
        (Stmt.OpenOutcomeRel middleCtx suffix returns)
        (InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx sourceFuel stmt source)
        (Expressions.InteractionSemantics.Block.openRun
          targetProgram targetFuel { stmts := headCode } target))
    (hTail :
      ∀ {sourceMid : Locals.Source.State}
        {targetMid : Structured.RunState}
        {sourceMidCtx : Locals.Source.Ctx},
        Frame.CtxRel sourceMidCtx middleCtx →
        Frame.StateRel middleCtx.layout suffix returns
          sourceMid targetMid →
        Simulation.Interaction.ForwardRel
          FuelTruncated
          (Stmt.OpenOutcomeRel finalCtx suffix returns)
          (InteractionSemantics.Block.openRun
            sourceProgram sourceMidCtx sourceFuel
              { stmts := rest } sourceMid)
          (Expressions.InteractionSemantics.Block.openRun
            targetProgram (targetFuel - headCode.length)
              { stmts := tailCode } targetMid)) :
    Simulation.Interaction.ForwardRel
      FuelTruncated
      (Stmt.OpenOutcomeRel finalCtx suffix returns)
      (InteractionSemantics.Block.openRun
        sourceProgram sourceCtx (sourceFuel + 1)
          { stmts := stmt :: rest } source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel
          { stmts := headCode ++ tailCode } target) := by
  rw [Expressions.InteractionSemantics.Block.openRun_append]
  unfold InteractionSemantics.Block.openRun
    InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel
  simp only [Locals.Source.Effectful.Control.Block.runOpen]
  apply Simulation.Interaction.ForwardRel.bind hHead
  intro sourceResult targetResult hResult
  cases hResult with
  | regular hCtx hState =>
      exact hTail hCtx hState
  | brk hState =>
      apply Simulation.Interaction.ForwardRel.ofRel
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact Stmt.OpenResultRel.brk hState
  | cont hState =>
      apply Simulation.Interaction.ForwardRel.ofRel
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact Stmt.OpenResultRel.cont hState
  | leave hState =>
      apply Simulation.Interaction.ForwardRel.ofRel
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact Stmt.OpenResultRel.leave hState
  | halt hShared hReturns =>
      apply Simulation.Interaction.ForwardRel.ofRel
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact Stmt.OpenResultRel.halt hShared hReturns

end Block

end InteractionPreservation
end Locals
end EvmCompiler
