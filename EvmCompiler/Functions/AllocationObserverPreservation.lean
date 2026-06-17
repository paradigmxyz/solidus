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
  rw [Structured.EffectSemantics.Code.run_cons]
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
  rw [Structured.EffectSemantics.Code.run_cons]
  simp only [Structured.BasicInstr.step, Structured.BasicOp.step,
    Assembly.Target.stepInstr_prim,
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
  rw [Structured.EffectSemantics.Code.run_cons]
  simp only [Structured.BasicInstr.step, Structured.BasicOp.step,
    Assembly.Target.stepInstr_prim,
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
  rw [Structured.EffectSemantics.Code.run_cons]
  simp only [Structured.BasicInstr.step, Structured.BasicOp.step,
    Assembly.Target.stepInstr_prim,
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

private theorem set_append_head
    {α : Type} (above : List α) (old new : α) (suffix : List α) :
    (above ++ old :: suffix).set above.length new =
      above ++ new :: suffix := by
  induction above with
  | nil =>
      rfl
  | cons head tail ih =>
      simp [ih]

/--
The compiler's restore sequence moves the value immediately below a prefix
back to the top while preserving the prefix order.
-/
theorem run_swapRestoreUpTo? {transcript : Trace}
    {depth : Nat} {code : Structured.Code}
    {above : List Word} {value : Word} {suffix : List Word}
    {target : Structured.ObserverSemantics.State transcript}
    (hCode : Locals.Ctx.swapRestoreUpTo? depth = some code)
    (hLength : above.length = depth)
    (hStack :
      target.source.evm.stack = above ++ value :: suffix) :
    ∃ final,
      Structured.ObserverSemantics.Code.run code target = .ok final ∧
      final.cursor = target.cursor ∧
      final.source.evm.stack = value :: above ++ suffix ∧
      final.source.evm.toSharedState =
        target.source.evm.toSharedState ∧
      final.source.returns = target.source.returns := by
  induction depth generalizing code above value suffix target with
  | zero =>
      simp [Locals.Ctx.swapRestoreUpTo?] at hCode
      subst code
      have hAbove : above = [] := List.eq_nil_of_length_eq_zero hLength
      subst above
      exact ⟨target, rfl, rfl, by simpa using hStack, rfl, rfl⟩
  | succ depth ih =>
      simp only [Locals.Ctx.swapRestoreUpTo?] at hCode
      cases hRest : Locals.Ctx.swapRestoreUpTo? depth with
      | none =>
          simp [hRest] at hCode
      | some restCode =>
          cases hOp : Locals.StackOp.swap? (depth + 1) with
          | none =>
              simp [hRest, hOp] at hCode
          | some op =>
              simp [hRest, hOp] at hCode
              subst code
              have hAboveNonempty : above ≠ [] := by
                intro hEmpty
                simp [hEmpty] at hLength
              let last := above.getLast hAboveNonempty
              let init := above.dropLast
              have hAboveEq : init ++ [last] = above := by
                exact List.dropLast_append_getLast hAboveNonempty
              have hInitLength : init.length = depth := by
                have hLengths := congrArg List.length hAboveEq
                simp only [List.length_append, List.length_singleton] at hLengths
                simp only [init] at hLengths ⊢
                omega
              have hStackInit :
                  target.source.evm.stack =
                    init ++ last :: value :: suffix := by
                rw [← hAboveEq] at hStack
                simpa [List.append_assoc] using hStack
              obtain
                  ⟨mid, hRestRun, hMidCursor, hMidStack,
                    hMidShared, hMidReturns⟩ :=
                ih hRest hInitLength hStackInit
              have hGet :
                  (init ++ value :: suffix)[depth]? = some value := by
                simp [hInitLength]
              let final :=
                AllocationObserverRelation.StateRel.replaceStackBy
                  1
                  (value ::
                    (init ++ value :: suffix).set depth last)
                  mid
              have hSwap :
                  Structured.ObserverSemantics.Code.run [.op op] mid =
                    .ok final := by
                apply run_swap hOp hGet
                simpa [List.append_assoc] using hMidStack
              refine ⟨final, ?_, ?_, ?_, ?_, ?_⟩
              · rw [run_append, hRestRun]
                exact hSwap
              · simpa [final,
                  AllocationObserverRelation.StateRel.replaceStackBy,
                  Simulation.ResourceReplay.State.withSource,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC] using hMidCursor
              · simp only [final,
                  AllocationObserverRelation.StateRel.replaceStackBy,
                  Simulation.ResourceReplay.State.withSource,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
                rw [← hInitLength, set_append_head, ← hAboveEq]
                simp [List.append_assoc]
              · simpa [final,
                  AllocationObserverRelation.StateRel.replaceStackBy,
                  Simulation.ResourceReplay.State.withSource,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC] using hMidShared
              · simpa [final,
                  AllocationObserverRelation.StateRel.replaceStackBy,
                  Simulation.ResourceReplay.State.withSource,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC] using hMidReturns

/--
One preserving cleanup step removes the first local below a fixed prefix of
return values and leaves that prefix in its original order.
-/
theorem run_cleanupOnePreserving? {transcript : Trace}
    {preserve : Nat} {code : Structured.Code}
    {values : List Word} {discarded : Word} {suffix : List Word}
    {target : Structured.ObserverSemantics.State transcript}
    (hCode : Locals.Ctx.cleanupOnePreserving? preserve = some code)
    (hLength : values.length = preserve)
    (hStack :
      target.source.evm.stack = values ++ discarded :: suffix) :
    ∃ final,
      Structured.ObserverSemantics.Code.run code target = .ok final ∧
      final.cursor = target.cursor ∧
      final.source.evm.stack = values ++ suffix ∧
      final.source.evm.toSharedState =
        target.source.evm.toSharedState ∧
      final.source.returns = target.source.returns := by
  cases preserve with
  | zero =>
      simp [Locals.Ctx.cleanupOnePreserving?] at hCode
      subst code
      have hValues : values = [] :=
        List.eq_nil_of_length_eq_zero hLength
      subst values
      let final :=
        AllocationObserverRelation.StateRel.replaceStackBy
          1 suffix target
      have hRun :
          Structured.ObserverSemantics.Code.run [.op .pop] target =
            .ok final := by
        simpa [final] using run_pop (target := target) hStack
      exact
        ⟨final, hRun,
          by simp [final,
            AllocationObserverRelation.StateRel.replaceStackBy,
            Simulation.ResourceReplay.State.withSource,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC],
          by simp [final,
            AllocationObserverRelation.StateRel.replaceStackBy,
            Simulation.ResourceReplay.State.withSource,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC],
          by simp [final,
            AllocationObserverRelation.StateRel.replaceStackBy,
            Simulation.ResourceReplay.State.withSource,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC],
          by simp [final,
            AllocationObserverRelation.StateRel.replaceStackBy,
            Simulation.ResourceReplay.State.withSource,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]⟩
  | succ preserve =>
      simp only [Locals.Ctx.cleanupOnePreserving?] at hCode
      cases hOp : Locals.StackOp.swap? (preserve + 1) with
      | none =>
          simp [hOp] at hCode
      | some op =>
          cases hRestore :
              Locals.Ctx.swapRestoreUpTo? preserve with
          | none =>
              simp [hOp, hRestore] at hCode
          | some restore =>
              simp [hOp, hRestore] at hCode
              subst code
              cases values with
              | nil =>
                  simp at hLength
              | cons value rest =>
                  have hRestLength : rest.length = preserve := by
                    simpa using Nat.succ.inj hLength
                  have hGet :
                      (rest ++ discarded :: suffix)[preserve]? =
                        some discarded := by
                    simp [hRestLength]
                  let mid :=
                    AllocationObserverRelation.StateRel.replaceStackBy
                      2
                      ((rest ++ discarded :: suffix).set preserve value)
                      target
                  have hHeadRun :
                      Structured.ObserverSemantics.Code.run
                          [.op op, .op .pop] target =
                        .ok mid := by
                    apply run_swap_pop hOp hGet
                    simpa [List.append_assoc] using hStack
                  have hMidStack :
                      mid.source.evm.stack = rest ++ value :: suffix := by
                    simp [mid,
                      AllocationObserverRelation.StateRel.replaceStackBy,
                      Simulation.ResourceReplay.State.withSource,
                      EvmYul.EVM.State.replaceStackAndIncrPC,
                      EvmYul.EVM.State.incrPC, hRestLength,
                      set_append_head]
                  obtain
                      ⟨final, hRestoreRun, hCursor, hFinalStack,
                        hShared, hReturns⟩ :=
                    run_swapRestoreUpTo? hRestore hRestLength hMidStack
                  refine ⟨final, ?_, hCursor, ?_, hShared, hReturns⟩
                  · change
                      Structured.ObserverSemantics.Code.run
                          ([.op op, .op .pop] ++ restore) target =
                        .ok final
                    rw [run_append, hHeadRun]
                    exact hRestoreRun
                  · simpa [List.append_assoc] using hFinalStack

/--
Repeated preserving cleanup removes a contiguous list of locals below the
preserved value prefix.
-/
theorem run_cleanupManyPreserving? {transcript : Trace}
    {count preserve : Nat} {code : Structured.Code}
    {values discarded suffix : List Word}
    {target : Structured.ObserverSemantics.State transcript}
    (hCode :
      Locals.Ctx.cleanupManyPreserving? count preserve = some code)
    (hValuesLength : values.length = preserve)
    (hDiscardedLength : discarded.length = count)
    (hStack :
      target.source.evm.stack = values ++ discarded ++ suffix) :
    ∃ final,
      Structured.ObserverSemantics.Code.run code target = .ok final ∧
      final.cursor = target.cursor ∧
      final.source.evm.stack = values ++ suffix ∧
      final.source.evm.toSharedState =
        target.source.evm.toSharedState ∧
      final.source.returns = target.source.returns := by
  induction count generalizing code discarded target with
  | zero =>
      simp [Locals.Ctx.cleanupManyPreserving?] at hCode
      subst code
      have hDiscarded : discarded = [] :=
        List.eq_nil_of_length_eq_zero hDiscardedLength
      subst discarded
      exact ⟨target, rfl, rfl, by simpa using hStack, rfl, rfl⟩
  | succ count ih =>
      simp only [Locals.Ctx.cleanupManyPreserving?] at hCode
      cases hHead :
          Locals.Ctx.cleanupOnePreserving? preserve with
      | none =>
          simp [hHead] at hCode
      | some headCode =>
          cases hTail :
              Locals.Ctx.cleanupManyPreserving? count preserve with
          | none =>
              simp [hHead, hTail] at hCode
          | some tailCode =>
              simp [hHead, hTail] at hCode
              subst code
              cases discarded with
              | nil =>
                  simp at hDiscardedLength
              | cons discardedHead discardedTail =>
                  have hTailLength :
                      discardedTail.length = count := by
                    simpa using Nat.succ.inj hDiscardedLength
                  obtain
                      ⟨mid, hHeadRun, hMidCursor, hMidStack,
                        hMidShared, hMidReturns⟩ :=
                    run_cleanupOnePreserving?
                      hHead hValuesLength
                      (by simpa [List.append_assoc] using hStack)
                  obtain
                      ⟨final, hTailRun, hFinalCursor, hFinalStack,
                        hFinalShared, hFinalReturns⟩ :=
                    ih hTail hTailLength
                      (by simpa [List.append_assoc] using hMidStack)
                  refine ⟨final, ?_, ?_, hFinalStack, ?_, ?_⟩
                  · rw [run_append, hHeadRun]
                    exact hTailRun
                  · exact hFinalCursor.trans hMidCursor
                  · exact hFinalShared.trans hMidShared
                  · exact hFinalReturns.trans hMidReturns

theorem run_add {transcript : Trace}
    {target : Structured.ObserverSemantics.State transcript}
    {right left : Word} {rest : List Word}
    (hStack : target.source.evm.stack = right :: left :: rest) :
    Structured.ObserverSemantics.Code.run [.op .add] target =
      .ok
        (AllocationObserverRelation.StateRel.contractTargetBy
          1 (EvmYul.UInt256.add right left) rest target) := by
  unfold Structured.ObserverSemantics.Code.run
  rw [Structured.EffectSemantics.Code.run_cons]
  simp only [Structured.BasicInstr.step, Structured.BasicOp.step,
    Assembly.Target.stepInstr_prim,
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
  rw [Structured.EffectSemantics.Code.run_cons]
  simp only [Structured.BasicInstr.step, Structured.BasicOp.step,
    Assembly.Target.stepInstr_prim,
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
  rw [Structured.EffectSemantics.Code.run_cons]
  simp only [Structured.BasicInstr.step, Structured.BasicOp.step,
    Assembly.Target.stepInstr_prim,
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
  rw [Structured.EffectSemantics.Code.run_cons]
  simp only [Structured.BasicInstr.step, Structured.BasicOp.step,
    Assembly.Target.stepInstr_prim,
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
  rw [Structured.EffectSemantics.Code.run_cons]
  simp only [Structured.BasicInstr.step, Structured.BasicOp.step,
    Assembly.Target.stepInstr_prim]
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
  rw [Structured.EffectSemantics.Code.run_cons]
  simp only [Structured.BasicInstr.step, Structured.BasicOp.step,
    Assembly.Target.stepInstr_prim, Structured.BasicOp.toPrimOp]
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
  rw [Structured.EffectSemantics.Code.run_cons]
  simp only [Structured.BasicInstr.step, Structured.BasicOp.step,
    Assembly.Target.stepInstr_prim]
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
  rw [Structured.EffectSemantics.Code.run_cons]
  simp only [Structured.BasicInstr.step, Structured.BasicOp.step,
    Assembly.Target.stepInstr_prim, Structured.BasicOp.toPrimOp]
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
        targetFinal ∧
      targetFinal.source.evm.stack = target.source.evm.stack := by
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
  refine ⟨targetFinal, ?_, hFinalRel, hReady, rfl⟩
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

/--
The concrete target state produced by the allocator-cell advance sequence.
This is proof-only state construction around the existing compiler code, not an
alternative compiler or interpreter.
-/
def allocatorAdvanceTarget {transcript : Trace}
    (config : AllocationObserverRelation.Frame.Config)
    (depth : Nat)
    (target : Structured.ObserverSemantics.State transcript) :
    Structured.ObserverSemantics.State transcript :=
  let cellWord := AllocationSupport.word config.allocatorCell
  let baseWord :=
    EvmYul.UInt256.ofNat
      (AllocationObserverRelation.Frame.baseAt config depth)
  let bytesWord := AllocationSupport.frameBytes config.frameWords
  let nextWord := EvmYul.UInt256.add bytesWord baseWord
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
  AllocationObserverRelation.StateRel.mstoreTarget
    cellWord nextWord (baseWord :: target.source.evm.stack)
    afterCellStore

/--
Exact execution of the existing allocator advance code. Keeping this theorem
separate lets noninterference proofs inspect the concrete final machine without
enlarging the established allocator preservation theorem.
-/
theorem allocatorAdvance_run_exact {transcript : Trace}
    {config : AllocationObserverRelation.Frame.Config}
    {depth : Nat}
    {target : Structured.ObserverSemantics.State transcript}
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady config depth target) :
    Structured.ObserverSemantics.Code.run
        [ .push (AllocationSupport.word config.allocatorCell),
          .op .mload,
          .op .dup1,
          .push (AllocationSupport.frameBytes config.frameWords),
          .op .add,
          .push (AllocationSupport.word config.allocatorCell),
          .op .mstore ] target =
      .ok (allocatorAdvanceTarget config depth target) := by
  let cellWord := AllocationSupport.word config.allocatorCell
  let baseWord :=
    EvmYul.UInt256.ofNat
      (AllocationObserverRelation.Frame.baseAt config depth)
  let bytesWord := AllocationSupport.frameBytes config.frameWords
  let nextWord := EvmYul.UInt256.add bytesWord baseWord
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
  have hCellLt : config.allocatorCell < EvmYul.UInt256.size := by
    exact lt_of_le_of_lt
      (Nat.le_add_right config.allocatorCell MemoryContract.wordBytes)
      (hReady.cellActive.trans_lt hReady.activeNoWrap)
  have hCellAddress :
      (EvmYul.UInt256.ofNat config.allocatorCell).toNat =
        config.allocatorCell :=
    EvmYul.UInt256.toNat_ofNat_of_lt hCellLt
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
  have hAfterLoadTop :
      afterLoad.source.evm.stack[0]? = some baseWord := by
    rfl
  have hAfterBytesStack :
      afterBytes.source.evm.stack =
        bytesWord :: baseWord :: baseWord :: target.source.evm.stack := by
    rfl
  have hAfterCellStoreStack :
      afterCellStore.source.evm.stack =
        cellWord :: nextWord :: baseWord :: target.source.evm.stack := by
    rfl
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
    _ = .ok (allocatorAdvanceTarget config depth target) := by
      simpa [allocatorAdvanceTarget, cellWord, baseWord, bytesWord,
        nextWord, afterCell, afterLoad, afterDup, afterBytes, afterAdd,
        afterCellStore] using
        (ObserverCode.run_mstore hAfterCellStoreStack)

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

@[simp] theorem allocatorAdvanceTarget_cursor {transcript : Trace}
    (config : AllocationObserverRelation.Frame.Config)
    (depth : Nat)
    (target : Structured.ObserverSemantics.State transcript) :
    (allocatorAdvanceTarget config depth target).cursor = target.cursor := by
  rfl

@[simp] theorem allocatorAdvanceTarget_stack {transcript : Trace}
    (config : AllocationObserverRelation.Frame.Config)
    (depth : Nat)
    (target : Structured.ObserverSemantics.State transcript) :
    (allocatorAdvanceTarget config depth target).source.evm.stack =
      EvmYul.UInt256.ofNat
          (AllocationObserverRelation.Frame.baseAt config depth) ::
        target.source.evm.stack := by
  rfl

@[simp] theorem allocatorAdvanceTarget_world {transcript : Trace}
    (config : AllocationObserverRelation.Frame.Config)
    (depth : Nat)
    (target : Structured.ObserverSemantics.State transcript) :
    (allocatorAdvanceTarget config depth target).source.evm.toSharedState.toState =
      target.source.evm.toSharedState.toState := by
  rfl

theorem allocatorAdvanceTarget_machine {transcript : Trace}
    (config : AllocationObserverRelation.Frame.Config)
    (depth : Nat)
    (target : Structured.ObserverSemantics.State transcript) :
    (allocatorAdvanceTarget config depth target).source.evm.toMachineState =
      target.source.evm.toMachineState.mstore
        (AllocationSupport.word config.allocatorCell)
        (EvmYul.UInt256.ofNat
          (AllocationObserverRelation.Frame.baseAt config (depth + 1))) := by
  have hNextWord :
      EvmYul.UInt256.add
          (AllocationSupport.frameBytes config.frameWords)
          (EvmYul.UInt256.ofNat
            (AllocationObserverRelation.Frame.baseAt config depth)) =
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
  simp [allocatorAdvanceTarget, hNextWord,
    AllocationObserverRelation.StateRel.pushTargetBy,
    AllocationObserverRelation.StateRel.pushTarget,
    AllocationObserverRelation.StateRel.contractTargetBy,
    AllocationObserverRelation.StateRel.mstoreTarget,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem allocatorAdvanceTarget_activeWords
    {transcript : Trace}
    {config : AllocationObserverRelation.Frame.Config}
    {depth : Nat}
    {target : Structured.ObserverSemantics.State transcript}
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady config depth target) :
    (allocatorAdvanceTarget config depth target).source.evm.activeWords =
      target.source.evm.activeWords := by
  have hCellLt : config.allocatorCell < EvmYul.UInt256.size := by
    exact lt_of_le_of_lt
      (Nat.le_add_right config.allocatorCell MemoryContract.wordBytes)
      (hReady.cellActive.trans_lt hReady.activeNoWrap)
  have hCellAddress :
      (EvmYul.UInt256.ofNat config.allocatorCell).toNat =
        config.allocatorCell :=
    EvmYul.UInt256.toNat_ofNat_of_lt hCellLt
  rw [allocatorAdvanceTarget_machine]
  simpa [AllocationSupport.word] using
    (Compiler.MemoryRelation.mstore_activeWords_eq_of_end_le
      target.source.evm.toMachineState config.allocatorCell
      (EvmYul.UInt256.ofNat
        (AllocationObserverRelation.Frame.baseAt config (depth + 1)))
      hCellAddress
      (by simpa [MemoryContract.wordBytes] using hReady.cellActive))

theorem allocatorAdvanceTarget_memorySize
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {frameWords depth : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {target : Structured.ObserverSemantics.State transcript}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady config depth target) :
    (allocatorAdvanceTarget config depth target).source.evm.toMachineState.memory.size =
      target.source.evm.toMachineState.memory.size := by
  obtain
    ⟨reservation, _hReservation, hAllocator, _hFirst, _hLimit,
      _hWords, _hWF, hHost, _hPositive, _hFits⟩ :=
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
  have hCellHost :
      config.allocatorCell + MemoryContract.wordBytes < USize.size :=
    lt_of_le_of_lt hRegion.2 hHost
  have hCellLt : config.allocatorCell < EvmYul.UInt256.size := by
    exact lt_of_le_of_lt
      (Nat.le_add_right config.allocatorCell MemoryContract.wordBytes)
      (hReady.cellActive.trans_lt hReady.activeNoWrap)
  have hCellAddress :
      (EvmYul.UInt256.ofNat config.allocatorCell).toNat =
        config.allocatorCell :=
    EvmYul.UInt256.toNat_ofNat_of_lt hCellLt
  rw [allocatorAdvanceTarget_machine]
  simpa [AllocationSupport.word, EvmYul.MachineState.mstore] using
    (Compiler.MemoryRelation.writeWord_memory_size_eq_of_end_le
      target.source.evm.toMachineState config.allocatorCell
      (EvmYul.UInt256.ofNat
        (AllocationObserverRelation.Frame.baseAt config (depth + 1)))
      hCellAddress
      (by simpa [MemoryContract.wordBytes] using hCellHost)
      (by simpa [MemoryContract.wordBytes] using hReady.cellAllocated))

theorem allocatorAdvanceTarget_lookupMemory
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {frameWords depth query : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {target : Structured.ObserverSemantics.State transcript}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady config depth target)
    (hAfterCell :
      config.allocatorCell + MemoryContract.wordBytes ≤ query)
    (hReadMemory :
      query + MemoryContract.wordBytes ≤
        target.source.evm.toMachineState.memory.size)
    (hReadActive :
      query + MemoryContract.wordBytes ≤
        target.source.evm.activeWords.toNat *
          MemoryContract.wordBytes) :
    (allocatorAdvanceTarget config depth target).source.evm.toMachineState.lookupMemory
        (EvmYul.UInt256.ofNat query) =
      target.source.evm.toMachineState.lookupMemory
        (EvmYul.UInt256.ofNat query) := by
  obtain
    ⟨reservation, _hReservation, hAllocator, _hFirst, _hLimit,
      _hWords, _hWF, hHost, _hPositive, _hFits⟩ :=
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
  have hCellHost :
      config.allocatorCell + MemoryContract.wordBytes < USize.size :=
    lt_of_le_of_lt hRegion.2 hHost
  have hCellLt : config.allocatorCell < EvmYul.UInt256.size := by
    exact lt_of_le_of_lt
      (Nat.le_add_right config.allocatorCell MemoryContract.wordBytes)
      (hReady.cellActive.trans_lt hReady.activeNoWrap)
  have hCellAddress :
      (EvmYul.UInt256.ofNat config.allocatorCell).toNat =
        config.allocatorCell :=
    EvmYul.UInt256.toNat_ofNat_of_lt hCellLt
  have hQueryLt : query < EvmYul.UInt256.size := by
    exact lt_of_le_of_lt
      (Nat.le_add_right query MemoryContract.wordBytes)
      (hReadActive.trans_lt hReady.activeNoWrap)
  have hQuery :
      (EvmYul.UInt256.ofNat query).toNat = query :=
    EvmYul.UInt256.toNat_ofNat_of_lt hQueryLt
  rw [allocatorAdvanceTarget_machine]
  simpa [AllocationSupport.word] using
    (Compiler.MemoryRelation.lookupMemory_mstore_disjoint
      target.source.evm.toMachineState config.allocatorCell query
      (EvmYul.UInt256.ofNat
        (AllocationObserverRelation.Frame.baseAt config (depth + 1)))
      hCellAddress hQuery
      (by simpa [MemoryContract.wordBytes] using hCellHost)
      (by simpa [MemoryContract.wordBytes] using hReady.cellAllocated)
      (by simpa [MemoryContract.wordBytes] using hReadMemory)
      (by simpa [MemoryContract.wordBytes] using hReady.cellActive)
      (Or.inr (by simpa [MemoryContract.wordBytes] using hAfterCell)))

/--
Updating the allocator metadata preserves every already-active word after the
metadata cell, as well as the observer cursor and shared world.
-/
theorem allocatorAdvance_preserves_word {transcript : Trace}
    {contract : MemoryContract.Contract}
    {frameWords depth query : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady config depth target)
    (hAfterCell :
      config.allocatorCell + MemoryContract.wordBytes ≤ query)
    (hReadMemory :
      query + MemoryContract.wordBytes ≤
        target.source.evm.toMachineState.memory.size)
    (hReadActive :
      query + MemoryContract.wordBytes ≤
        target.source.evm.activeWords.toNat *
          MemoryContract.wordBytes)
    (hRun :
      Structured.ObserverSemantics.Code.run
          [ .push (AllocationSupport.word config.allocatorCell),
            .op .mload,
            .op .dup1,
            .push (AllocationSupport.frameBytes config.frameWords),
            .op .add,
            .push (AllocationSupport.word config.allocatorCell),
            .op .mstore ] target =
        .ok targetFinal) :
    targetFinal.cursor = target.cursor ∧
      targetFinal.source.evm.toSharedState.toState =
        target.source.evm.toSharedState.toState ∧
      targetFinal.source.evm.activeWords =
        target.source.evm.activeWords ∧
      targetFinal.source.evm.toMachineState.memory.size =
        target.source.evm.toMachineState.memory.size ∧
      targetFinal.source.evm.toMachineState.lookupMemory
          (EvmYul.UInt256.ofNat query) =
        target.source.evm.toMachineState.lookupMemory
          (EvmYul.UInt256.ofNat query) := by
  have hExpected := allocatorAdvance_run_exact hReady
  rw [hExpected] at hRun
  have hFinal :
      targetFinal = allocatorAdvanceTarget config depth target := by
    exact Except.ok.inj hRun.symm
  subst targetFinal
  exact
    ⟨allocatorAdvanceTarget_cursor config depth target,
      allocatorAdvanceTarget_world config depth target,
      allocatorAdvanceTarget_activeWords hReady,
      allocatorAdvanceTarget_memorySize hConfig hReady,
      allocatorAdvanceTarget_lookupMemory
        hConfig hReady hAfterCell hReadMemory hReadActive⟩

/--
The concrete target state produced by preallocating the final word of a scratch
frame. The zero-width case is retained only to keep this definition total; the
execution theorem requires the compiler-established positive frame width.
-/
def framePreallocTarget {transcript : Trace}
    (config : AllocationObserverRelation.Frame.Config)
    (frameDepth : Nat)
    (rest : List Word)
    (target : Structured.ObserverSemantics.State transcript) :
    Structured.ObserverSemantics.State transcript :=
  match config.frameWords with
  | 0 => target
  | slot + 1 =>
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
      AllocationObserverRelation.StateRel.mstoreTarget
        address zeroWord (frameWord :: rest) afterAdd

theorem framePrealloc_run_exact {transcript : Trace}
    {config : AllocationObserverRelation.Frame.Config}
    {frameDepth : Nat}
    {target : Structured.ObserverSemantics.State transcript}
    {rest : List Word}
    (hPositive : 0 < config.frameWords)
    (hStack :
      target.source.evm.stack =
        EvmYul.UInt256.ofNat
            (AllocationObserverRelation.Frame.baseAt config frameDepth) ::
          rest) :
    Structured.ObserverSemantics.Code.run
        (AllocationSupport.framePreallocCode config.frameWords) target =
      .ok (framePreallocTarget config frameDepth rest target) := by
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
        _ = .ok (framePreallocTarget config frameDepth rest target) := by
          simpa [framePreallocTarget, hWords, frameBase, frameWord,
            zeroWord, offsetWord, address, afterZero, afterDup,
            afterOffset, afterAdd] using
            (ObserverCode.run_mstore hAfterAddStack)

@[simp] theorem framePreallocTarget_cursor {transcript : Trace}
    (config : AllocationObserverRelation.Frame.Config)
    (frameDepth : Nat)
    (rest : List Word)
    (target : Structured.ObserverSemantics.State transcript) :
    (framePreallocTarget config frameDepth rest target).cursor =
      target.cursor := by
  cases hWords : config.frameWords <;>
    simp [framePreallocTarget, hWords,
      AllocationObserverRelation.StateRel.pushTargetBy,
      AllocationObserverRelation.StateRel.pushTarget,
      AllocationObserverRelation.StateRel.contractTargetBy,
      AllocationObserverRelation.StateRel.mstoreTarget,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]

@[simp] theorem framePreallocTarget_world {transcript : Trace}
    (config : AllocationObserverRelation.Frame.Config)
    (frameDepth : Nat)
    (rest : List Word)
    (target : Structured.ObserverSemantics.State transcript) :
    (framePreallocTarget config frameDepth rest target).source.evm.toSharedState.toState =
      target.source.evm.toSharedState.toState := by
  cases hWords : config.frameWords <;>
    simp [framePreallocTarget, hWords,
      AllocationObserverRelation.StateRel.pushTargetBy,
      AllocationObserverRelation.StateRel.pushTarget,
      AllocationObserverRelation.StateRel.contractTargetBy,
      AllocationObserverRelation.StateRel.mstoreTarget,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]

theorem framePreallocTarget_machine_of_words {transcript : Trace}
    {config : AllocationObserverRelation.Frame.Config}
    {frameDepth slot : Nat}
    {rest : List Word}
    {target : Structured.ObserverSemantics.State transcript}
    (hWords : config.frameWords = slot + 1)
    (hAddress :
      EvmYul.UInt256.add
          (AllocationSupport.slotOffset slot)
          (EvmYul.UInt256.ofNat
            (AllocationObserverRelation.Frame.baseAt config frameDepth)) =
        EvmYul.UInt256.ofNat
          (AllocationObserverRelation.scratchAddress
            (AllocationObserverRelation.Frame.baseAt config frameDepth)
            slot)) :
    (framePreallocTarget config frameDepth rest target).source.evm.toMachineState =
      target.source.evm.toMachineState.mstore
        (EvmYul.UInt256.ofNat
          (AllocationObserverRelation.scratchAddress
            (AllocationObserverRelation.Frame.baseAt config frameDepth)
            slot))
        AllocationSupport.zeroWord := by
  simp [framePreallocTarget, hWords, hAddress,
    AllocationObserverRelation.StateRel.pushTargetBy,
    AllocationObserverRelation.StateRel.pushTarget,
    AllocationObserverRelation.StateRel.contractTargetBy,
    AllocationObserverRelation.StateRel.mstoreTarget,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem framePrealloc_last_address_facts
    {contract : MemoryContract.Contract}
    {frameWords frameDepth slot : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hBudget :
      AllocationObserverRelation.Frame.Budget config frameDepth)
    (hWords : config.frameWords = slot + 1) :
    let frameBase :=
      AllocationObserverRelation.Frame.baseAt config frameDepth
    let address :=
      AllocationObserverRelation.scratchAddress frameBase slot
    address + MemoryContract.wordBytes < EvmYul.UInt256.size ∧
      address + MemoryContract.wordBytes < USize.size ∧
      (EvmYul.UInt256.ofNat address).toNat = address ∧
      EvmYul.UInt256.add
          (AllocationSupport.slotOffset slot)
          (EvmYul.UInt256.ofNat frameBase) =
        EvmYul.UInt256.ofNat address := by
  let frameBase :=
    AllocationObserverRelation.Frame.baseAt config frameDepth
  let address :=
    AllocationObserverRelation.scratchAddress frameBase slot
  have hFrameEnd :
      address + MemoryContract.wordBytes =
        frameBase + AllocationObserverRelation.Frame.bytes config := by
    simp [address, frameBase, AllocationObserverRelation.scratchAddress,
      AllocationObserverRelation.Frame.bytes, hWords,
      MemoryContract.wordBytes, Nat.mul_add, Nat.add_assoc]
  have hAddressEnd :
      address + MemoryContract.wordBytes < EvmYul.UInt256.size := by
    rw [hFrameEnd]
    exact
      AllocationObserverRelation.Frame.noWrap_of_budget_of_scratchFrameConfig?
        hConfig hBudget
  have hAddressHost :
      address + MemoryContract.wordBytes < USize.size := by
    rw [hFrameEnd]
    exact
      AllocationObserverRelation.Frame.hostAddressable_of_budget_of_scratchFrameConfig?
        hConfig hBudget
  have hAddressLt : address < EvmYul.UInt256.size := by
    omega
  refine
    ⟨hAddressEnd, hAddressHost,
      EvmYul.UInt256.toNat_ofNat_of_lt hAddressLt, ?_⟩
  change
    EvmYul.UInt256.ofNat (32 * slot) +
        EvmYul.UInt256.ofNat frameBase =
      EvmYul.UInt256.ofNat
        (frameBase + MemoryContract.wordBytes * slot)
  rw [Assembly.UInt256_ofNat_add]
  simp [MemoryContract.wordBytes, Nat.add_comm]

theorem framePreallocTarget_lookupMemory
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {frameWords allocatorDepth frameDepth query : Nat}
    {config : AllocationObserverRelation.Frame.Config}
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
    (hBeforeFrame :
      query + MemoryContract.wordBytes ≤
        AllocationObserverRelation.Frame.baseAt config frameDepth)
    (hReadMemory :
      query + MemoryContract.wordBytes ≤
        target.source.evm.toMachineState.memory.size)
    (hReadActive :
      query + MemoryContract.wordBytes ≤
        target.source.evm.activeWords.toNat *
          MemoryContract.wordBytes) :
    (framePreallocTarget config frameDepth rest target).source.evm.toMachineState.lookupMemory
        (EvmYul.UInt256.ofNat query) =
      target.source.evm.toMachineState.lookupMemory
        (EvmYul.UInt256.ofNat query) := by
  cases hWords : config.frameWords with
  | zero =>
      simp [hWords] at hPositive
  | succ slot =>
      obtain
        ⟨hAddressEnd, hAddressHost, hAddressToNat, hAddress⟩ :=
        framePrealloc_last_address_facts hConfig hBudget hWords
      have hQueryLt : query < EvmYul.UInt256.size := by
        exact lt_of_le_of_lt
          (Nat.le_add_right query MemoryContract.wordBytes)
          (hReadActive.trans_lt hReady.activeNoWrap)
      have hQuery :
          (EvmYul.UInt256.ofNat query).toNat = query :=
        EvmYul.UInt256.toNat_ofNat_of_lt hQueryLt
      rw [framePreallocTarget_machine_of_words hWords hAddress]
      exact
        Compiler.MemoryRelation.lookupMemory_mstore_disjoint_growing
          target.source.evm.toMachineState
          (AllocationObserverRelation.scratchAddress
            (AllocationObserverRelation.Frame.baseAt config frameDepth)
            slot)
          query AllocationSupport.zeroWord hAddressToNat hQuery
          (by simpa [MemoryContract.wordBytes] using hAddressHost)
          (by simpa [MemoryContract.wordBytes] using hReadMemory)
          (by simpa [MemoryContract.wordBytes] using hReadActive)
          (by simpa [MemoryContract.wordBytes] using hReady.activeNoWrap)
          (Or.inl
            (hBeforeFrame.trans
              (Nat.le_add_right
                (AllocationObserverRelation.Frame.baseAt config frameDepth)
                (MemoryContract.wordBytes * slot))))

theorem framePreallocTarget_growth
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {frameWords frameDepth : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {target : Structured.ObserverSemantics.State transcript}
    {rest : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hPositive : 0 < config.frameWords)
    (hBudget :
      AllocationObserverRelation.Frame.Budget config frameDepth) :
    AllocationObserverRelation.Frame.TargetGrowth target
      (framePreallocTarget config frameDepth rest target) := by
  cases hWords : config.frameWords with
  | zero =>
      simp [hWords] at hPositive
  | succ slot =>
      obtain
        ⟨hAddressEnd, hAddressHost, hAddressToNat, hAddress⟩ :=
        framePrealloc_last_address_facts hConfig hBudget hWords
      have hMachine :=
        framePreallocTarget_machine_of_words
          (target := target) (rest := rest) hWords hAddress
      refine ⟨?_, ?_⟩
      · rw [hMachine]
        exact
          Compiler.MemoryRelation.activeWords_toNat_le_mstore
            target.source.evm.toMachineState
            (AllocationObserverRelation.scratchAddress
              (AllocationObserverRelation.Frame.baseAt config frameDepth)
              slot)
            AllocationSupport.zeroWord hAddressEnd
      · rw [hMachine]
        simpa [EvmYul.MachineState.mstore] using
          (Compiler.MemoryRelation.writeWord_memory_size_ge
            target.source.evm.toMachineState
            (AllocationObserverRelation.scratchAddress
              (AllocationObserverRelation.Frame.baseAt config frameDepth)
              slot)
            AllocationSupport.zeroWord hAddressToNat
            (by simpa [MemoryContract.wordBytes] using hAddressHost))

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

/--
Preallocating the next frame's final word preserves every already-active word
strictly below that frame.
-/
theorem framePrealloc_preserves_word {transcript : Trace}
    {contract : MemoryContract.Contract}
    {frameWords allocatorDepth frameDepth query : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
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
    (hStack :
      target.source.evm.stack =
        EvmYul.UInt256.ofNat
            (AllocationObserverRelation.Frame.baseAt config frameDepth) ::
          rest)
    (hBeforeFrame :
      query + MemoryContract.wordBytes ≤
        AllocationObserverRelation.Frame.baseAt config frameDepth)
    (hReadMemory :
      query + MemoryContract.wordBytes ≤
        target.source.evm.toMachineState.memory.size)
    (hReadActive :
      query + MemoryContract.wordBytes ≤
        target.source.evm.activeWords.toNat *
          MemoryContract.wordBytes)
    (hRun :
      Structured.ObserverSemantics.Code.run
          (AllocationSupport.framePreallocCode config.frameWords) target =
        .ok targetFinal) :
    targetFinal.cursor = target.cursor ∧
      targetFinal.source.evm.toSharedState.toState =
        target.source.evm.toSharedState.toState ∧
      targetFinal.source.evm.toMachineState.lookupMemory
          (EvmYul.UInt256.ofNat query) =
        target.source.evm.toMachineState.lookupMemory
          (EvmYul.UInt256.ofNat query) := by
  have hExpected := framePrealloc_run_exact hPositive hStack
  rw [hExpected] at hRun
  have hFinal :
      targetFinal = framePreallocTarget config frameDepth rest target := by
    exact Except.ok.inj hRun.symm
  subst targetFinal
  exact
    ⟨framePreallocTarget_cursor config frameDepth rest target,
      framePreallocTarget_world config frameDepth rest target,
      framePreallocTarget_lookupMemory
        hConfig hPositive hBudget hReady hBeforeFrame
        hReadMemory hReadActive⟩

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

theorem scratchFrameAcquire_cursor_world {transcript : Trace}
    {config : AllocationObserverRelation.Frame.Config}
    {depth : Nat}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
    (hPositive : 0 < config.frameWords)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady config depth target)
    (hRun :
      Structured.ObserverSemantics.Code.run
          (AllocationSupport.scratchFrameAcquireCode config) target =
        .ok targetFinal) :
    targetFinal.cursor = target.cursor ∧
      targetFinal.source.evm.toSharedState.toState =
        target.source.evm.toSharedState.toState := by
  let advanced := allocatorAdvanceTarget config depth target
  let expected :=
    framePreallocTarget config depth target.source.evm.stack advanced
  have hAdvanceRun :
      Structured.ObserverSemantics.Code.run
          [ .push (AllocationSupport.word config.allocatorCell),
            .op .mload,
            .op .dup1,
            .push (AllocationSupport.frameBytes config.frameWords),
            .op .add,
            .push (AllocationSupport.word config.allocatorCell),
            .op .mstore ] target =
        .ok advanced := by
    simpa [advanced] using allocatorAdvance_run_exact hReady
  have hAdvanceStack :
      advanced.source.evm.stack =
        EvmYul.UInt256.ofNat
            (AllocationObserverRelation.Frame.baseAt config depth) ::
          target.source.evm.stack := by
    simp [advanced]
  have hPreallocRun :
      Structured.ObserverSemantics.Code.run
          (AllocationSupport.framePreallocCode config.frameWords) advanced =
        .ok expected := by
    simpa [expected] using
      framePrealloc_run_exact hPositive hAdvanceStack
  have hExpectedRun :
      Structured.ObserverSemantics.Code.run
          (AllocationSupport.scratchFrameAcquireCode config) target =
        .ok expected := by
    unfold AllocationSupport.scratchFrameAcquireCode
    rw [ObserverCode.run_append, hAdvanceRun]
    exact hPreallocRun
  rw [hExpectedRun] at hRun
  have hFinal : targetFinal = expected := by
    exact Except.ok.inj hRun.symm
  subst targetFinal
  exact
    ⟨(framePreallocTarget_cursor
        config depth target.source.evm.stack advanced).trans
        (allocatorAdvanceTarget_cursor config depth target),
      (framePreallocTarget_world
        config depth target.source.evm.stack advanced).trans
        (allocatorAdvanceTarget_world config depth target)⟩

/--
Complete scratch-frame acquisition preserves every caller word between the
allocator metadata and the base of the newly acquired frame.
-/
theorem scratchFrameAcquire_preserves_word {transcript : Trace}
    {contract : MemoryContract.Contract}
    {frameWords depth query : Nat}
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
    (hAfterCell :
      config.allocatorCell + MemoryContract.wordBytes ≤ query)
    (hBeforeFrame :
      query + MemoryContract.wordBytes ≤
        AllocationObserverRelation.Frame.baseAt config depth)
    (hReadMemory :
      query + MemoryContract.wordBytes ≤
        target.source.evm.toMachineState.memory.size)
    (hReadActive :
      query + MemoryContract.wordBytes ≤
        target.source.evm.activeWords.toNat *
          MemoryContract.wordBytes)
    (hRun :
      Structured.ObserverSemantics.Code.run
          (AllocationSupport.scratchFrameAcquireCode config) target =
        .ok targetFinal) :
    targetFinal.cursor = target.cursor ∧
      targetFinal.source.evm.toSharedState.toState =
        target.source.evm.toSharedState.toState ∧
      targetFinal.source.evm.toMachineState.lookupMemory
          (EvmYul.UInt256.ofNat query) =
        target.source.evm.toMachineState.lookupMemory
          (EvmYul.UInt256.ofNat query) := by
  obtain
    ⟨advanced, hAdvanceRun, hAdvanceStack,
      hAdvanceMachine, hAdvanceReady⟩ :=
    allocatorAdvance_forward hConfig hReady hMachine
  obtain
    ⟨expected, hPreallocRun, _hFinalStack,
      _hFinalMachine, _hFinalReady, _hFrameActive, _hFrameAllocated⟩ :=
    framePrealloc_forward
      (allocatorDepth := depth + 1) (frameDepth := depth)
      hConfig hPositive hBudget hAdvanceReady hAdvanceMachine
      hAdvanceStack
  have hExpectedRun :
      Structured.ObserverSemantics.Code.run
          (AllocationSupport.scratchFrameAcquireCode config) target =
        .ok expected := by
    unfold AllocationSupport.scratchFrameAcquireCode
    rw [ObserverCode.run_append, hAdvanceRun]
    exact hPreallocRun
  rw [hExpectedRun] at hRun
  have hFinal : targetFinal = expected := by
    exact Except.ok.inj hRun.symm
  subst targetFinal
  obtain
    ⟨hAdvanceCursor, hAdvanceWorld, hAdvanceActive,
      hAdvanceMemory, hAdvanceLookup⟩ :=
    allocatorAdvance_preserves_word
      hConfig hReady hAfterCell hReadMemory hReadActive hAdvanceRun
  have hAdvancedReadMemory :
      query + MemoryContract.wordBytes ≤
        advanced.source.evm.toMachineState.memory.size := by
    simpa [hAdvanceMemory] using hReadMemory
  have hAdvancedReadActive :
      query + MemoryContract.wordBytes ≤
        advanced.source.evm.activeWords.toNat *
          MemoryContract.wordBytes := by
    simpa [hAdvanceActive] using hReadActive
  obtain
    ⟨hPreallocCursor, hPreallocWorld, hPreallocLookup⟩ :=
    framePrealloc_preserves_word
      hConfig hPositive hBudget hAdvanceReady hAdvanceStack
      hBeforeFrame hAdvancedReadMemory hAdvancedReadActive hPreallocRun
  exact
    ⟨hPreallocCursor.trans hAdvanceCursor,
      hPreallocWorld.trans hAdvanceWorld,
      hPreallocLookup.trans hAdvanceLookup⟩

theorem scratchFrameAcquire_boundedEffect {transcript : Trace}
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
    AllocationObserverRelation.Frame.BoundedEffect
      config (depth + 1) (depth + 1) target targetFinal := by
  let advanced := allocatorAdvanceTarget config depth target
  have hAdvanceRun :
      Structured.ObserverSemantics.Code.run
          [ .push (AllocationSupport.word config.allocatorCell),
            .op .mload,
            .op .dup1,
            .push (AllocationSupport.frameBytes config.frameWords),
            .op .add,
            .push (AllocationSupport.word config.allocatorCell),
            .op .mstore ] target =
        .ok advanced := by
    simpa [advanced] using allocatorAdvance_run_exact hReady
  have hAdvanceStack :
      advanced.source.evm.stack =
        EvmYul.UInt256.ofNat
            (AllocationObserverRelation.Frame.baseAt config depth) ::
          target.source.evm.stack := by
    simp [advanced]
  let expected :=
    framePreallocTarget config depth target.source.evm.stack advanced
  have hPreallocRun :
      Structured.ObserverSemantics.Code.run
          (AllocationSupport.framePreallocCode config.frameWords) advanced =
        .ok expected := by
    simpa [expected] using
      framePrealloc_run_exact hPositive hAdvanceStack
  have hExpectedRun :
      Structured.ObserverSemantics.Code.run
          (AllocationSupport.scratchFrameAcquireCode config) target =
        .ok expected := by
    unfold AllocationSupport.scratchFrameAcquireCode
    rw [ObserverCode.run_append, hAdvanceRun]
    exact hPreallocRun
  rw [hExpectedRun] at hRun
  have hFinal : targetFinal = expected := Except.ok.inj hRun.symm
  subst targetFinal
  obtain
    ⟨forwardFinal, hForwardRun, _hFinalStack, _hFinalMachine,
      hFinalReady, _hFrameActive, _hFrameAllocated⟩ :=
    scratchFrameAcquire_forward
      hConfig hPositive hBudget hReady hMachine
  rw [hExpectedRun] at hForwardRun
  have hForwardFinal : forwardFinal = expected :=
    Except.ok.inj hForwardRun.symm
  subst forwardFinal
  have hAdvanceGrowth :
      AllocationObserverRelation.Frame.TargetGrowth target advanced := by
    refine ⟨?_, ?_⟩
    · simpa [advanced, allocatorAdvanceTarget_activeWords hReady]
    · simpa [advanced, allocatorAdvanceTarget_memorySize hConfig hReady]
  have hPreallocGrowth :
      AllocationObserverRelation.Frame.TargetGrowth advanced expected := by
    simpa [expected] using
      (framePreallocTarget_growth
        (target := advanced) (rest := target.source.evm.stack)
        hConfig hPositive hBudget)
  have hGrowth := hAdvanceGrowth.trans hPreallocGrowth
  obtain
    ⟨reservation, _hReservation, hAllocator, hFirst, _hLimit,
      _hWords, _hWF, _hHost, _hPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  have hCellBeforeFirst :
      config.allocatorCell + MemoryContract.wordBytes ≤ config.firstFrame := by
    rw [hAllocator, hFirst]
    unfold MemoryContract.ScratchReservation.allocatorCell
      MemoryContract.ScratchReservation.frameBase
    omega
  refine
    { ready := hFinalReady
      growth := hGrowth
      prefixStable := ?_ }
  intro protectedDepth hProtectedDepth _hProtectedBudget
  refine
    { growth := hGrowth
      lookup := ?_ }
  intro address hStart hEnd hReadMemory hReadActive
  have hBeforeFrame :
      address + MemoryContract.wordBytes ≤
        AllocationObserverRelation.Frame.baseAt config depth :=
    hEnd.trans
      (AllocationObserverRelation.Frame.baseAt_mono config
        (Nat.le_of_lt_succ hProtectedDepth))
  exact
    (scratchFrameAcquire_preserves_word
      hConfig hPositive hBudget hReady hMachine
      (hCellBeforeFirst.trans hStart) hBeforeFrame
      hReadMemory hReadActive hExpectedRun).2.2

/--
Acquire a nested scratch frame while preserving the suspended caller
activation. The new frame pointer is added as one target-only stack prefix;
every caller spill remains unchanged below the new frame base.
-/
theorem scratchFrameAcquire_activation_forward {transcript : Trace}
    {contract : MemoryContract.Contract}
    {globalFrameWords depth stackOffset frameBase : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {plan : Locals.Allocation.Plan}
    {live : List Locals.Name}
    {mode : AllocationObserverRelation.ActivationMode}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hPositive : 0 < config.frameWords)
    (hBudget :
      AllocationObserverRelation.Frame.Budget config depth)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady config depth target)
    (hOwned :
      AllocationObserverRelation.Frame.ActivationOwned
        config depth frameBase mode)
    (hRel :
      AllocationObserverRelation.ActivationStateRel
        contract plan live stackOffset frameBase mode source target) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run
          (AllocationSupport.scratchFrameAcquireCode config) target =
        .ok targetFinal ∧
      AllocationObserverRelation.ActivationStateRel
        contract plan live (stackOffset + 1) frameBase mode
        source targetFinal ∧
      AllocationObserverRelation.Frame.AllocatorReady
        config (depth + 1) targetFinal ∧
      targetFinal.source.evm.stack =
        EvmYul.UInt256.ofNat
            (AllocationObserverRelation.Frame.baseAt config depth) ::
          target.source.evm.stack ∧
      AllocationObserverRelation.Frame.baseAt config depth +
          AllocationObserverRelation.Frame.bytes config ≤
        targetFinal.source.evm.activeWords.toNat *
          MemoryContract.wordBytes ∧
      AllocationObserverRelation.Frame.baseAt config depth +
          AllocationObserverRelation.Frame.bytes config ≤
        targetFinal.source.evm.toMachineState.memory.size ∧
      AllocationObserverRelation.Frame.BoundedEffect
        config (depth + 1) (depth + 1) target targetFinal := by
  obtain
    ⟨targetFinal, hRun, hFinalStack, hFinalMachine, hFinalReady,
      hNewFrameActive, hNewFrameAllocated⟩ :=
    scratchFrameAcquire_forward hConfig hPositive hBudget hReady
      hRel.base.core.machine
  obtain ⟨hCursor, hWorld⟩ :=
    scratchFrameAcquire_cursor_world hPositive hReady hRun
  have hEffect :=
    scratchFrameAcquire_boundedEffect
      hConfig hPositive hBudget hReady hRel.base.core.machine hRun
  refine
    ⟨targetFinal, hRun, ?_, hFinalReady, hFinalStack,
      hNewFrameActive, hNewFrameAllocated, hEffect⟩
  cases hRel with
  | stack hOnly _hActive hState =>
      have hStore :
          StoreRel plan live (stackOffset + 1) frameBase
            source.source targetFinal.source := by
        have hRebased :=
          StoreRel.rebase_prefix_stack_only
            (oldPrefix := [])
            (newPrefix :=
              [EvmYul.UInt256.ofNat
                (AllocationObserverRelation.Frame.baseAt config depth)])
            (baseStack := target.source.evm.stack)
            hOnly
            (by simpa using hState.core.store)
            (by simp)
            (by simpa using hFinalStack)
            rfl
        simpa using hRebased
      exact
        .stack hOnly hFinalReady.activeNoWrap
          { cursor := hState.cursor.trans hCursor.symm
            core :=
              { machine := hFinalMachine
                world := hState.core.world.trans hWorld.symm
                store := hStore } }
  | @scratch frameDepth frameWords _ _ hScratch =>
      have hScratchLookup :
          ∀ name slot,
            name ∈ live →
            plan.location? name = some (.scratch slot) →
            targetFinal.source.evm.toMachineState.lookupMemory
                (EvmYul.UInt256.ofNat
                  (AllocationObserverRelation.scratchAddress frameBase slot)) =
              target.source.evm.toMachineState.lookupMemory
                (EvmYul.UInt256.ofNat
                  (AllocationObserverRelation.scratchAddress frameBase slot)) := by
        intro name slot hLive hLocation
        have hSlot :=
          hScratch.scratchBound name slot hLive hLocation
        exact
          (scratchFrameAcquire_preserves_word
            hConfig hPositive hBudget hReady hScratch.base.core.machine
            (hOwned.allocatorCell_disjoint_scratchAddress hConfig)
            (hOwned.scratchAddress_end_le_allocatorBase hSlot)
            (hScratch.scratchAddress_end_le_memory hLive hLocation)
            (hScratch.scratchAddress_end_le_active hLive hLocation)
            hRun).2.2
      have hStore :
          StoreRel plan live (stackOffset + 1) frameBase
            source.source targetFinal.source := by
        have hRebased :=
          StoreRel.rebase_prefix_of_lookup
            (oldPrefix := [])
            (newPrefix :=
              [EvmYul.UInt256.ofNat
                (AllocationObserverRelation.Frame.baseAt config depth)])
            (baseStack := target.source.evm.stack)
            (by simpa using hScratch.base.core.store)
            (by simp)
            (by simpa using hFinalStack)
            hScratchLookup
            rfl
        simpa using hRebased
      have hBase :
          AllocationObserverRelation.StateRel contract plan live
            (stackOffset + 1) frameBase source targetFinal :=
        { cursor := hScratch.base.cursor.trans hCursor.symm
          core :=
            { machine := hFinalMachine
              world := hScratch.base.core.world.trans hWorld.symm
              store := hStore } }
      have hFramePointer :
          targetFinal.source.evm.stack[
              (stackOffset + 1) + frameDepth]? =
            some (EvmYul.UInt256.ofNat frameBase) := by
        rw [hFinalStack]
        rw [show
          (stackOffset + 1) + frameDepth =
            (stackOffset + frameDepth) + 1 by omega]
        simpa using hScratch.framePointer
      have hCallerFrameActive :
          frameBase + MemoryContract.wordBytes * frameWords ≤
            targetFinal.source.evm.activeWords.toNat *
              MemoryContract.wordBytes := by
        rw [hOwned.frameEnd_eq_allocatorBase]
        exact
          (Nat.le_add_right
              (AllocationObserverRelation.Frame.baseAt config depth)
              (AllocationObserverRelation.Frame.bytes config)).trans
            hNewFrameActive
      have hCallerFrameAllocated :
          frameBase + MemoryContract.wordBytes * frameWords ≤
            targetFinal.source.evm.toMachineState.memory.size := by
        rw [hOwned.frameEnd_eq_allocatorBase]
        exact
          (Nat.le_add_right
              (AllocationObserverRelation.Frame.baseAt config depth)
              (AllocationObserverRelation.Frame.bytes config)).trans
            hNewFrameAllocated
      exact
        .scratch
          { base := hBase
            framePointer := hFramePointer
            frameActive := hCallerFrameActive
            frameAllocated := hCallerFrameAllocated
            frameNoWrap := hScratch.frameNoWrap
            frameHostAddressable := hScratch.frameHostAddressable
            activeNoWrap := hFinalReady.activeNoWrap
            frameReserved := hScratch.frameReserved
            scratchBound := hScratch.scratchBound }

/--
Acquire a frame for an empty activation and make the new frame pointer the
owned runtime representation of that activation.

Unlike nested-call acquisition, there is no suspended caller frame and no live
local can depend on the previous frame base.
-/
theorem scratchFrameAcquire_empty_forward {transcript : Trace}
    {contract : MemoryContract.Contract}
    {globalFrameWords depth oldFrameBase : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {plan : Locals.Allocation.Plan}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hPositive : 0 < config.frameWords)
    (hBudget :
      AllocationObserverRelation.Frame.Budget config depth)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady config depth target)
    (hRel :
      AllocationObserverRelation.StateRel contract plan [] 0 oldFrameBase
        source target) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run
          (AllocationSupport.scratchFrameAcquireCode config) target =
        .ok targetFinal ∧
      AllocationObserverRelation.ActivationStateRel
        contract plan [] 0
          (AllocationObserverRelation.Frame.baseAt config depth)
          (.scratch 0 config.frameWords) source targetFinal ∧
      AllocationObserverRelation.Frame.AllocatorReady
        config (depth + 1) targetFinal ∧
      targetFinal.source.evm.stack =
        EvmYul.UInt256.ofNat
            (AllocationObserverRelation.Frame.baseAt config depth) ::
          target.source.evm.stack := by
  obtain
      ⟨targetFinal, hRun, hStack, hMachine, hFinalReady,
        hFrameActive, hFrameAllocated⟩ :=
    scratchFrameAcquire_forward
      hConfig hPositive hBudget hReady hRel.core.machine
  obtain ⟨hCursor, hWorld⟩ :=
    scratchFrameAcquire_cursor_world hPositive hReady hRun
  have hFrameNoWrap :
      AllocationObserverRelation.Frame.baseAt config depth +
          MemoryContract.wordBytes * config.frameWords <
        EvmYul.UInt256.size := by
    simpa [AllocationObserverRelation.Frame.bytes,
      MemoryContract.wordBytes] using
      AllocationObserverRelation.Frame.noWrap_of_budget_of_scratchFrameConfig?
        hConfig hBudget
  have hFrameHost :
      AllocationObserverRelation.Frame.baseAt config depth +
          MemoryContract.wordBytes * config.frameWords <
        USize.size := by
    simpa [AllocationObserverRelation.Frame.bytes,
      MemoryContract.wordBytes] using
      AllocationObserverRelation.Frame.hostAddressable_of_budget_of_scratchFrameConfig?
        hConfig hBudget
  have hFrameReserved :
      ∃ reservation,
        contract.scratch? = some reservation ∧
          reservation.containsRegion
            (AllocationObserverRelation.Frame.baseAt config depth)
            config.frameWords :=
    AllocationObserverRelation.Frame.reserved_of_budget_of_scratchFrameConfig?
      hConfig hBudget
  have hEntry :
      AllocationObserverRelation.ActivationCalleeEntryRel
        contract plan [] []
          (AllocationObserverRelation.Frame.baseAt config depth)
          (.scratch 0 config.frameWords) source targetFinal := by
    apply
      AllocationObserverRelation.ActivationCalleeEntryRel.scratch_empty
        (values := [])
        (suffix :=
          EvmYul.UInt256.ofNat
              (AllocationObserverRelation.Frame.baseAt config depth) ::
            target.source.evm.stack)
    · exact hRel.cursor.trans hCursor.symm
    · exact hMachine
    · exact hRel.core.world.trans hWorld.symm
    · rw [hStack]
      rfl
    · simpa [AllocationObserverRelation.Frame.bytes,
        MemoryContract.wordBytes] using hFrameActive
    · simpa [AllocationObserverRelation.Frame.bytes,
        MemoryContract.wordBytes] using hFrameAllocated
    · exact hFrameNoWrap
    · exact hFrameHost
    · exact hFinalReady.activeNoWrap
    · exact hFrameReserved
    · simp [Functions.Source.Store.lookupMany]
    · simpa using hStack
  exact
    ⟨targetFinal, hRun,
      AllocationObserverRelation.ActivationCalleeEntryRel.finish hEntry,
      hFinalReady, hStack⟩

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

/--
The concrete target state produced by the allocator release sequence.
-/
def scratchFrameReleaseTarget {transcript : Trace}
    (config : AllocationObserverRelation.Frame.Config)
    (depth : Nat)
    (target : Structured.ObserverSemantics.State transcript) :
    Structured.ObserverSemantics.State transcript :=
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
  AllocationObserverRelation.StateRel.mstoreTarget
    cellWord priorWord target.source.evm.stack afterCellStore

theorem scratchFrameRelease_run_exact {transcript : Trace}
    {contract : MemoryContract.Contract}
    {frameWords depth : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {target : Structured.ObserverSemantics.State transcript}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hBudget :
      AllocationObserverRelation.Frame.Budget config depth)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady
        config (depth + 1) target) :
    Structured.ObserverSemantics.Code.run
        (AllocationSupport.scratchFrameReleaseCode config) target =
      .ok (scratchFrameReleaseTarget config depth target) := by
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
  have hCellLt : config.allocatorCell < EvmYul.UInt256.size := by
    exact lt_of_le_of_lt
      (Nat.le_add_right config.allocatorCell MemoryContract.wordBytes)
      (hReady.cellActive.trans_lt hReady.activeNoWrap)
  have hCellAddress :
      (EvmYul.UInt256.ofNat config.allocatorCell).toNat =
        config.allocatorCell :=
    EvmYul.UInt256.toNat_ofNat_of_lt hCellLt
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
    _ = .ok (scratchFrameReleaseTarget config depth target) := by
      simpa [scratchFrameReleaseTarget, bytesWord, cellWord,
        currentWord, priorWord, afterBytes, afterCell, afterLoad,
        afterSub, afterCellStore] using
        (ObserverCode.run_mstore hAfterCellStoreStack)

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

@[simp] theorem scratchFrameReleaseTarget_cursor {transcript : Trace}
    (config : AllocationObserverRelation.Frame.Config)
    (depth : Nat)
    (target : Structured.ObserverSemantics.State transcript) :
    (scratchFrameReleaseTarget config depth target).cursor =
      target.cursor := by
  rfl

@[simp] theorem scratchFrameReleaseTarget_world {transcript : Trace}
    (config : AllocationObserverRelation.Frame.Config)
    (depth : Nat)
    (target : Structured.ObserverSemantics.State transcript) :
    (scratchFrameReleaseTarget config depth target).source.evm.toSharedState.toState =
      target.source.evm.toSharedState.toState := by
  rfl

@[simp] theorem scratchFrameReleaseTarget_stack {transcript : Trace}
    (config : AllocationObserverRelation.Frame.Config)
    (depth : Nat)
    (target : Structured.ObserverSemantics.State transcript) :
    (scratchFrameReleaseTarget config depth target).source.evm.stack =
      target.source.evm.stack := by
  rfl

theorem scratchFrameReleaseTarget_machine {transcript : Trace}
    (config : AllocationObserverRelation.Frame.Config)
    (depth : Nat)
    (target : Structured.ObserverSemantics.State transcript) :
    (scratchFrameReleaseTarget config depth target).source.evm.toMachineState =
      target.source.evm.toMachineState.mstore
        (AllocationSupport.word config.allocatorCell)
        (EvmYul.UInt256.ofNat
          (AllocationObserverRelation.Frame.baseAt config depth)) := by
  rfl

theorem scratchFrameReleaseTarget_activeWords
    {transcript : Trace}
    {config : AllocationObserverRelation.Frame.Config}
    {depth : Nat}
    {target : Structured.ObserverSemantics.State transcript}
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady
        config (depth + 1) target) :
    (scratchFrameReleaseTarget config depth target).source.evm.activeWords =
      target.source.evm.activeWords := by
  have hCellLt : config.allocatorCell < EvmYul.UInt256.size := by
    exact lt_of_le_of_lt
      (Nat.le_add_right config.allocatorCell MemoryContract.wordBytes)
      (hReady.cellActive.trans_lt hReady.activeNoWrap)
  have hCellAddress :
      (EvmYul.UInt256.ofNat config.allocatorCell).toNat =
        config.allocatorCell :=
    EvmYul.UInt256.toNat_ofNat_of_lt hCellLt
  rw [scratchFrameReleaseTarget_machine]
  simpa [AllocationSupport.word] using
    (Compiler.MemoryRelation.mstore_activeWords_eq_of_end_le
      target.source.evm.toMachineState config.allocatorCell
      (EvmYul.UInt256.ofNat
        (AllocationObserverRelation.Frame.baseAt config depth))
      hCellAddress
      (by simpa [MemoryContract.wordBytes] using hReady.cellActive))

theorem scratchFrameReleaseTarget_memorySize
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {frameWords depth : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {target : Structured.ObserverSemantics.State transcript}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady
        config (depth + 1) target) :
    (scratchFrameReleaseTarget config depth target).source.evm.toMachineState.memory.size =
      target.source.evm.toMachineState.memory.size := by
  obtain
    ⟨reservation, _hReservation, hAllocator, _hFirst, _hLimit,
      _hWords, _hWF, hHost, _hPositive, _hFits⟩ :=
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
  have hCellHost :
      config.allocatorCell + MemoryContract.wordBytes < USize.size :=
    lt_of_le_of_lt hRegion.2 hHost
  have hCellLt : config.allocatorCell < EvmYul.UInt256.size := by
    exact lt_of_le_of_lt
      (Nat.le_add_right config.allocatorCell MemoryContract.wordBytes)
      (hReady.cellActive.trans_lt hReady.activeNoWrap)
  have hCellAddress :
      (EvmYul.UInt256.ofNat config.allocatorCell).toNat =
        config.allocatorCell :=
    EvmYul.UInt256.toNat_ofNat_of_lt hCellLt
  rw [scratchFrameReleaseTarget_machine]
  simpa [AllocationSupport.word, EvmYul.MachineState.mstore] using
    (Compiler.MemoryRelation.writeWord_memory_size_eq_of_end_le
      target.source.evm.toMachineState config.allocatorCell
      (EvmYul.UInt256.ofNat
        (AllocationObserverRelation.Frame.baseAt config depth))
      hCellAddress
      (by simpa [MemoryContract.wordBytes] using hCellHost)
      (by simpa [MemoryContract.wordBytes] using hReady.cellAllocated))

theorem scratchFrameReleaseTarget_lookupMemory
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {frameWords depth query : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {target : Structured.ObserverSemantics.State transcript}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady
        config (depth + 1) target)
    (hAfterCell :
      config.allocatorCell + MemoryContract.wordBytes ≤ query)
    (hReadMemory :
      query + MemoryContract.wordBytes ≤
        target.source.evm.toMachineState.memory.size)
    (hReadActive :
      query + MemoryContract.wordBytes ≤
        target.source.evm.activeWords.toNat *
          MemoryContract.wordBytes) :
    (scratchFrameReleaseTarget config depth target).source.evm.toMachineState.lookupMemory
        (EvmYul.UInt256.ofNat query) =
      target.source.evm.toMachineState.lookupMemory
        (EvmYul.UInt256.ofNat query) := by
  obtain
    ⟨reservation, _hReservation, hAllocator, _hFirst, _hLimit,
      _hWords, _hWF, hHost, _hPositive, _hFits⟩ :=
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
  have hCellHost :
      config.allocatorCell + MemoryContract.wordBytes < USize.size :=
    lt_of_le_of_lt hRegion.2 hHost
  have hCellLt : config.allocatorCell < EvmYul.UInt256.size := by
    exact lt_of_le_of_lt
      (Nat.le_add_right config.allocatorCell MemoryContract.wordBytes)
      (hReady.cellActive.trans_lt hReady.activeNoWrap)
  have hCellAddress :
      (EvmYul.UInt256.ofNat config.allocatorCell).toNat =
        config.allocatorCell :=
    EvmYul.UInt256.toNat_ofNat_of_lt hCellLt
  have hQueryLt : query < EvmYul.UInt256.size := by
    exact lt_of_le_of_lt
      (Nat.le_add_right query MemoryContract.wordBytes)
      (hReadActive.trans_lt hReady.activeNoWrap)
  have hQuery :
      (EvmYul.UInt256.ofNat query).toNat = query :=
    EvmYul.UInt256.toNat_ofNat_of_lt hQueryLt
  rw [scratchFrameReleaseTarget_machine]
  simpa [AllocationSupport.word] using
    (Compiler.MemoryRelation.lookupMemory_mstore_disjoint
      target.source.evm.toMachineState config.allocatorCell query
      (EvmYul.UInt256.ofNat
        (AllocationObserverRelation.Frame.baseAt config depth))
      hCellAddress hQuery
      (by simpa [MemoryContract.wordBytes] using hCellHost)
      (by simpa [MemoryContract.wordBytes] using hReady.cellAllocated)
      (by simpa [MemoryContract.wordBytes] using hReadMemory)
      (by simpa [MemoryContract.wordBytes] using hReady.cellActive)
      (Or.inr (by simpa [MemoryContract.wordBytes] using hAfterCell)))

theorem scratchFrameRelease_boundedEffect {transcript : Trace}
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
    AllocationObserverRelation.Frame.BoundedEffect
      config depth (depth + 1) target targetFinal := by
  have hExact := scratchFrameRelease_run_exact hConfig hBudget hReady
  rw [hExact] at hRun
  have hFinal :
      targetFinal = scratchFrameReleaseTarget config depth target :=
    Except.ok.inj hRun.symm
  subst targetFinal
  obtain
    ⟨forwardFinal, hForwardRun, _hFinalStack, _hFinalMachine,
      hFinalReady⟩ :=
    scratchFrameRelease_forward hConfig hBudget hReady hMachine
  rw [hExact] at hForwardRun
  have hForwardFinal :
      forwardFinal = scratchFrameReleaseTarget config depth target :=
    Except.ok.inj hForwardRun.symm
  subst forwardFinal
  have hGrowth :
      AllocationObserverRelation.Frame.TargetGrowth target
        (scratchFrameReleaseTarget config depth target) := by
    refine ⟨?_, ?_⟩
    · simpa [scratchFrameReleaseTarget_activeWords hReady]
    · simpa [scratchFrameReleaseTarget_memorySize hConfig hReady]
  obtain
    ⟨reservation, _hReservation, hAllocator, hFirst, _hLimit,
      _hWords, _hWF, _hHost, _hPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  have hCellBeforeFirst :
      config.allocatorCell + MemoryContract.wordBytes ≤ config.firstFrame := by
    rw [hAllocator, hFirst]
    unfold MemoryContract.ScratchReservation.allocatorCell
      MemoryContract.ScratchReservation.frameBase
    omega
  refine
    { ready := hFinalReady
      growth := hGrowth
      prefixStable := ?_ }
  intro protectedDepth _hProtectedDepth _hProtectedBudget
  refine
    { growth := hGrowth
      lookup := ?_ }
  intro address hStart _hEnd hReadMemory hReadActive
  exact
    scratchFrameReleaseTarget_lookupMemory
      hConfig hReady (hCellBeforeFirst.trans hStart)
      hReadMemory hReadActive

/--
Release a nested scratch frame and restore the suspended caller activation at
its previous allocator depth.
-/
theorem scratchFrameRelease_activation_forward {transcript : Trace}
    {contract : MemoryContract.Contract}
    {globalFrameWords depth stackOffset frameBase : Nat}
    {config : AllocationObserverRelation.Frame.Config}
    {plan : Locals.Allocation.Plan}
    {live : List Locals.Name}
    {mode : AllocationObserverRelation.ActivationMode}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hBudget :
      AllocationObserverRelation.Frame.Budget config depth)
    (hReady :
      AllocationObserverRelation.Frame.AllocatorReady
        config (depth + 1) target)
    (hOwned :
      AllocationObserverRelation.Frame.ActivationOwned
        config depth frameBase mode)
    (hRel :
      AllocationObserverRelation.ActivationStateRel
        contract plan live stackOffset frameBase mode source target) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run
          (AllocationSupport.scratchFrameReleaseCode config) target =
        .ok targetFinal ∧
      AllocationObserverRelation.ActivationStateRel
        contract plan live stackOffset frameBase mode source targetFinal ∧
      AllocationObserverRelation.Frame.AllocatorReady
        config depth targetFinal ∧
      AllocationObserverRelation.Frame.ActivationOwned
        config depth frameBase mode ∧
      AllocationObserverRelation.Frame.BoundedEffect
        config depth (depth + 1) target targetFinal := by
  obtain
    ⟨targetFinal, hRun, hFinalStack, hFinalMachine, hFinalReady⟩ :=
    scratchFrameRelease_forward hConfig hBudget hReady
      hRel.base.core.machine
  have hEffect :=
    scratchFrameRelease_boundedEffect
      hConfig hBudget hReady hRel.base.core.machine hRun
  have hExact := scratchFrameRelease_run_exact hConfig hBudget hReady
  rw [hExact] at hRun
  have hFinal :
      targetFinal = scratchFrameReleaseTarget config depth target := by
    exact Except.ok.inj hRun.symm
  subst targetFinal
  refine
    ⟨scratchFrameReleaseTarget config depth target, hExact, ?_,
      hFinalReady, hOwned, hEffect⟩
  cases hRel with
  | stack hOnly _hActive hState =>
      have hStore :
          StoreRel plan live stackOffset frameBase
            source.source
            (scratchFrameReleaseTarget config depth target).source := by
        have hRebased :=
          StoreRel.rebase_prefix_stack_only
            (targetFinal :=
              (scratchFrameReleaseTarget config depth target).source)
            (oldPrefix := [])
            (newPrefix := [])
            (baseStack := target.source.evm.stack)
            hOnly
            (by simpa using hState.core.store)
            (by simp)
            (by rfl)
            rfl
        simpa using hRebased
      exact
        .stack hOnly hFinalReady.activeNoWrap
          { cursor :=
              hState.cursor.trans
                (scratchFrameReleaseTarget_cursor
                  config depth target).symm
            core :=
              { machine := hFinalMachine
                world :=
                  hState.core.world.trans
                    (scratchFrameReleaseTarget_world
                      config depth target).symm
                store := hStore } }
  | @scratch frameDepth frameWords _ _ hScratch =>
      have hScratchLookup :
          ∀ name slot,
            name ∈ live →
            plan.location? name = some (.scratch slot) →
            (scratchFrameReleaseTarget config depth target).source.evm.toMachineState.lookupMemory
                (EvmYul.UInt256.ofNat
                  (AllocationObserverRelation.scratchAddress frameBase slot)) =
              target.source.evm.toMachineState.lookupMemory
                (EvmYul.UInt256.ofNat
                  (AllocationObserverRelation.scratchAddress frameBase slot)) := by
        intro name slot hLive hLocation
        exact
          scratchFrameReleaseTarget_lookupMemory
            hConfig hReady
            (hOwned.allocatorCell_disjoint_scratchAddress hConfig)
            (hScratch.scratchAddress_end_le_memory hLive hLocation)
            (hScratch.scratchAddress_end_le_active hLive hLocation)
      have hStore :
          StoreRel plan live stackOffset frameBase
            source.source
            (scratchFrameReleaseTarget config depth target).source := by
        have hRebased :=
          StoreRel.rebase_prefix_of_lookup
            (targetFinal :=
              (scratchFrameReleaseTarget config depth target).source)
            (oldPrefix := [])
            (newPrefix := [])
            (baseStack := target.source.evm.stack)
            (by simpa using hScratch.base.core.store)
            (by simp)
            (by rfl)
            hScratchLookup
            rfl
        simpa using hRebased
      have hBase :
          AllocationObserverRelation.StateRel contract plan live
            stackOffset frameBase source
            (scratchFrameReleaseTarget config depth target) :=
        { cursor :=
            hScratch.base.cursor.trans
              (scratchFrameReleaseTarget_cursor
                config depth target).symm
          core :=
            { machine := hFinalMachine
              world :=
                hScratch.base.core.world.trans
                  (scratchFrameReleaseTarget_world
                    config depth target).symm
              store := hStore } }
      exact
        .scratch
          { base := hBase
            framePointer := by
              rw [scratchFrameReleaseTarget_stack config depth target]
              exact hScratch.framePointer
            frameActive := by
              simpa [scratchFrameReleaseTarget_activeWords hReady] using
                hScratch.frameActive
            frameAllocated := by
              simpa [scratchFrameReleaseTarget_memorySize hConfig hReady] using
                hScratch.frameAllocated
            frameNoWrap := hScratch.frameNoWrap
            frameHostAddressable := hScratch.frameHostAddressable
            activeNoWrap := hFinalReady.activeNoWrap
            frameReserved := hScratch.frameReserved
            scratchBound := hScratch.scratchBound }

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
        value :: target.source.evm.stack ∧
      targetFinal.source.evm.toMachineState =
        target.source.evm.toMachineState := by
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
  refine ⟨targetFinal, ?_, ?_, hFinalRel, rfl, ?_⟩
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
  · simp [targetFinal, afterAdd, afterPush, afterDup,
      AllocationObserverRelation.StateRel.pushTarget,
      AllocationObserverRelation.StateRel.pushTargetBy,
      AllocationObserverRelation.StateRel.contractTargetBy,
      Simulation.ResourceReplay.State.withSource,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]

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
      ⟨expected, hSourceEval, hExpectedRun, hExpectedRel, hExpectedStack,
        _hExpectedMachine⟩ :=
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
          ⟨targetFinal, hSourceEval, hTargetRun, hTargetRel, _hStack,
            _hMachine⟩ :=
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
        targetFinal ∧
      targetFinal.source.evm.stack = rest ∧
      targetFinal.source.evm.toMachineState =
        target.source.evm.toMachineState.mstore
          (EvmYul.UInt256.ofNat
            (AllocationObserverRelation.scratchAddress frameBase slot))
          value := by
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
  refine ⟨targetFinal, ?_, hFinalRel, rfl, ?_⟩
  · calc
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
  · simp [targetFinal, afterAdd, afterPush, afterDup, hAddress,
      AllocationObserverRelation.StateRel.mstoreTarget,
      AllocationObserverRelation.StateRel.pushTarget,
      AllocationObserverRelation.StateRel.pushTargetBy,
      AllocationObserverRelation.StateRel.contractTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]

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
  obtain
      ⟨expected, hExpectedRun, hExpectedRel, _hExpectedStack,
        _hExpectedMachine⟩ :=
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
        targetFinal ∧
      targetFinal.source.evm.stack = rest ∧
      targetFinal.source.evm.toMachineState =
        target.source.evm.toMachineState.mstore
          (EvmYul.UInt256.ofNat
            (AllocationObserverRelation.scratchAddress frameBase slot))
          value := by
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
      obtain
          ⟨targetFinal, hRun, hFinalRel, hFinalStack, hFinalMachine⟩ :=
        scratchAssignTop_forward_live hRel hStack hWF hAfter hStackOrder
          hNameAfter hLocation hAssignedBound hReservation hRegion
          (by simpa [Nat.add_assoc] using hDup)
      exact ⟨targetFinal, hRun, hFinalRel, hFinalStack, hFinalMachine⟩

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
  obtain
      ⟨expected, hExpectedRun, hExpectedRel, _hExpectedStack,
        _hExpectedMachine⟩ :=
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
      ⟨targetFinal, hSourceEval, hTargetRun, hFinalRel, hStack,
        _hMachine⟩ :=
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
