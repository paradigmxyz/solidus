import EvmCompiler.Locals.InteractionSemantics
import EvmCompiler.Locals.Compiler
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
is caller-owned and remains abstract. The relation owns no allocation plan or
scratch-frame data, which belong to the upper Functions allocation pass.
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

namespace CtxRel

theorem initial :
    CtxRel Locals.Source.Ctx.initial Locals.Ctx.initial := by
  constructor <;> rfl

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

end Expr

namespace Stmt

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

end Stmt

end InteractionPreservation
end Locals
end EvmCompiler
