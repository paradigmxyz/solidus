import EvmCompiler.Locals.InteractionPreservation

namespace EvmCompiler
namespace Locals
namespace InteractionCleanupPreservation

abbrev Word := Assembly.Word

private theorem set_append_head
    {α : Type} (above : List α) (old new : α) (suffix : List α) :
    (above ++ old :: suffix).set above.length new =
      above ++ new :: suffix := by
  induction above with
  | nil => rfl
  | cons head tail ih => simp [ih]

theorem openRun_discardNameStackOnly?_top
    {ctx : Ctx} {name : Name} {code : Structured.Code}
    {discarded : Layout} {value : Word} {rest : List Word}
    {target : Structured.RunState}
    (hDepth : Layout.lookupDepth? name ctx.layout = some 1)
    (hCode : ctx.discardNameStackOnly? name = some (code, discarded))
    (hStack : target.evm.stack = value :: rest) :
    ∃ final,
      Structured.InteractionSemantics.Code.openRun code target =
          .done (.ok final) ∧
        discarded = Layout.discardAt 0 ctx.layout ∧
        final.evm.stack = rest ∧
        final.evm.toSharedState = target.evm.toSharedState ∧
        final.returns = target.returns := by
  unfold Ctx.discardNameStackOnly? at hCode
  simp [hDepth] at hCode
  rcases hCode with ⟨rfl, rfl⟩
  let final :=
    target.withEVM (target.evm.replaceStackAndIncrPC rest)
  exact
    ⟨final, InteractionPreservation.Code.openRun_pop hStack, rfl,
      by simp [final, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC],
      by simp [final, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC],
      by simp [final]⟩

theorem openRun_discardNameStackOnly?_buried
    {ctx : Ctx} {name : Name} {code : Structured.Code}
    {discarded : Layout} {depth : Nat}
    {value old : Word} {rest : List Word}
    {target : Structured.RunState}
    (hDepth : Layout.lookupDepth? name ctx.layout = some (depth + 2))
    (hBound : depth + 1 ≤ 16)
    (hCode : ctx.discardNameStackOnly? name = some (code, discarded))
    (hGet : rest[depth]? = some old)
    (hStack : target.evm.stack = value :: rest) :
    ∃ final,
      Structured.InteractionSemantics.Code.openRun code target =
          .done (.ok final) ∧
        discarded = Layout.discardAt (depth + 1) ctx.layout ∧
        final.evm.stack = rest.set depth value ∧
        final.evm.toSharedState = target.evm.toSharedState ∧
        final.returns = target.returns := by
  unfold Ctx.discardNameStackOnly? at hCode
  have hBound' : depth ≤ 15 := by omega
  simp [hDepth, hBound'] at hCode
  cases hOp : StackOp.swap? (depth + 1) with
  | none => simp [hOp] at hCode
  | some op =>
      simp [hOp] at hCode
      rcases hCode with ⟨hCode, hLayout⟩
      subst code
      subst discarded
      obtain ⟨final, hRun, hFinalStack, hShared, hReturns⟩ :=
        InteractionPreservation.Code.openRun_swap_pop hOp hGet hStack
      exact ⟨final, hRun, rfl, hFinalStack, hShared, hReturns⟩

/-- A compiler-owned direct discard realizes the symbolic `swapPopAt` model. -/
theorem openRun_discardNameStackOnly?_exact
    {ctx : Ctx} {name : Name} {code : Structured.Code}
    {discarded : Layout} {index : Nat} {old : Word}
    {target : Structured.RunState}
    (hDepth : Layout.lookupDepth? name ctx.layout = some (index + 1))
    (hCode : ctx.discardNameStackOnly? name = some (code, discarded))
    (hAt : target.evm.stack[index]? = some old) :
    ∃ final,
      Structured.InteractionSemantics.Code.openRun code target =
          .done (.ok final) ∧
        discarded = Layout.discardAt index ctx.layout ∧
        final.evm.stack = StackList.swapPopAt index target.evm.stack ∧
        final.evm.toSharedState = target.evm.toSharedState ∧
        final.returns = target.returns := by
  cases index with
  | zero =>
      cases hStack : target.evm.stack with
      | nil => simp [hStack] at hAt
      | cons head rest =>
          simp [hStack] at hAt
          subst head
          obtain ⟨final, hRun, hDiscarded, hFinalStack, hShared, hReturns⟩ :=
            openRun_discardNameStackOnly?_top
              (by simpa using hDepth) hCode hStack
          exact
            ⟨final, hRun, hDiscarded,
              by simpa [StackList.swapPopAt, hStack] using hFinalStack,
              hShared, hReturns⟩
  | succ index =>
      cases hStack : target.evm.stack with
      | nil => simp [hStack] at hAt
      | cons head rest =>
          have hRestAt : rest[index]? = some old := by
            simpa [hStack] using hAt
          have hBound : index + 1 ≤ 16 := by
            by_contra hNotBound
            have hNotBound' : ¬ index + 1 ≤ 16 := by omega
            unfold Ctx.discardNameStackOnly? at hCode
            simp [hDepth, hNotBound'] at hCode
            omega
          obtain ⟨final, hRun, hDiscarded, hFinalStack, hShared, hReturns⟩ :=
            openRun_discardNameStackOnly?_buried
              (by simpa [Nat.succ_eq_add_one] using hDepth)
              hBound hCode hRestAt hStack
          exact
            ⟨final, hRun, hDiscarded,
              by
                rw [hFinalStack]
                simp [StackList.swapPopAt, hRestAt],
              hShared, hReturns⟩

/-- The generated restore sequence moves one buried value above its prefix. -/
theorem openRun_swapRestoreUpTo?
    {depth : Nat} {code : Structured.Code}
    {above : List Word} {value : Word} {suffix : List Word}
    {target : Structured.RunState}
    (hCode : Locals.Ctx.swapRestoreUpTo? depth = some code)
    (hLength : above.length = depth)
    (hStack : target.evm.stack = above ++ value :: suffix) :
    ∃ final,
      Structured.InteractionSemantics.Code.openRun code target =
          .done (.ok final) ∧
        final.evm.stack = value :: above ++ suffix ∧
        final.evm.toSharedState = target.evm.toSharedState ∧
        final.returns = target.returns := by
  induction depth generalizing code above value suffix target with
  | zero =>
      simp [Locals.Ctx.swapRestoreUpTo?] at hCode
      subst code
      have hAbove : above = [] := List.eq_nil_of_length_eq_zero hLength
      subst above
      exact ⟨target, rfl, by simpa using hStack, rfl, rfl⟩
  | succ depth ih =>
      simp only [Locals.Ctx.swapRestoreUpTo?] at hCode
      cases hRest : Locals.Ctx.swapRestoreUpTo? depth with
      | none => simp [hRest] at hCode
      | some restCode =>
          cases hOp : Locals.StackOp.swap? (depth + 1) with
          | none => simp [hRest, hOp] at hCode
          | some op =>
              simp [hRest, hOp] at hCode
              subst code
              have hAboveNonempty : above ≠ [] := by
                intro hEmpty
                simp [hEmpty] at hLength
              let last := above.getLast hAboveNonempty
              let init := above.dropLast
              have hAboveEq : init ++ [last] = above :=
                List.dropLast_append_getLast hAboveNonempty
              have hInitLength : init.length = depth := by
                have hLengths := congrArg List.length hAboveEq
                simp only [List.length_append, List.length_singleton]
                  at hLengths
                simp only [init] at hLengths ⊢
                omega
              have hStackInit :
                  target.evm.stack = init ++ last :: value :: suffix := by
                rw [← hAboveEq] at hStack
                simpa [List.append_assoc] using hStack
              obtain ⟨mid, hRestRun, hMidStack, hMidShared, hMidReturns⟩ :=
                ih hRest hInitLength hStackInit
              have hGet :
                  (init ++ value :: suffix)[depth]? = some value := by
                simp [hInitLength]
              let final :=
                mid.withEVM
                  (mid.evm.replaceStackAndIncrPC
                    (value :: (init ++ value :: suffix).set depth last))
              have hSwap :
                  Structured.InteractionSemantics.Code.openRun [.op op] mid =
                    .done (.ok final) := by
                apply InteractionPreservation.Code.openRun_swap hOp hGet
                simpa [List.append_assoc] using hMidStack
              refine ⟨final, ?_, ?_, ?_, ?_⟩
              · change
                  Structured.InteractionSemantics.Code.openRun
                      (restCode ++ [.op op]) target =
                    .done (.ok final)
                rw [Structured.InteractionSemantics.Code.openRun_append,
                  hRestRun]
                exact hSwap
              · simp only [final,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
                rw [← hInitLength, set_append_head, ← hAboveEq]
                simp [List.append_assoc]
              · simpa [final,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC] using hMidShared
              · simpa [final] using hMidReturns

/-- One cleanup step removes one local below a preserved value prefix. -/
theorem openRun_cleanupOnePreserving?
    {preserve : Nat} {code : Structured.Code}
    {values : List Word} {discarded : Word} {suffix : List Word}
    {target : Structured.RunState}
    (hCode : Locals.Ctx.cleanupOnePreserving? preserve = some code)
    (hLength : values.length = preserve)
    (hStack : target.evm.stack = values ++ discarded :: suffix) :
    ∃ final,
      Structured.InteractionSemantics.Code.openRun code target =
          .done (.ok final) ∧
        final.evm.stack = values ++ suffix ∧
        final.evm.toSharedState = target.evm.toSharedState ∧
        final.returns = target.returns := by
  cases preserve with
  | zero =>
      simp [Locals.Ctx.cleanupOnePreserving?] at hCode
      subst code
      have hValues : values = [] :=
        List.eq_nil_of_length_eq_zero hLength
      subst values
      let final :=
        target.withEVM (target.evm.replaceStackAndIncrPC suffix)
      have hRun :
          Structured.InteractionSemantics.Code.openRun [.op .pop] target =
            .done (.ok final) := by
        exact InteractionPreservation.Code.openRun_pop hStack
      exact
        ⟨final, hRun,
          by simp [final, EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC],
          by simp [final, EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC],
          by simp [final]⟩
  | succ preserve =>
      simp only [Locals.Ctx.cleanupOnePreserving?] at hCode
      cases hOp : Locals.StackOp.swap? (preserve + 1) with
      | none => simp [hOp] at hCode
      | some op =>
          cases hRestore : Locals.Ctx.swapRestoreUpTo? preserve with
          | none => simp [hOp, hRestore] at hCode
          | some restore =>
              simp [hOp, hRestore] at hCode
              subst code
              cases values with
              | nil => simp at hLength
              | cons value rest =>
                  have hRestLength : rest.length = preserve := by
                    simpa using Nat.succ.inj hLength
                  have hGet :
                      (rest ++ discarded :: suffix)[preserve]? =
                        some discarded := by
                    simp [hRestLength]
                  obtain ⟨mid, hHeadRun, hMidStack, hMidShared, hMidReturns⟩ :=
                    InteractionPreservation.Code.openRun_swap_pop hOp hGet
                      (by simpa [List.append_assoc] using hStack)
                  have hMidStack' :
                      mid.evm.stack = rest ++ value :: suffix := by
                    rw [hMidStack, ← hRestLength, set_append_head]
                  obtain
                      ⟨final, hRestoreRun, hFinalStack,
                        hFinalShared, hFinalReturns⟩ :=
                    openRun_swapRestoreUpTo?
                      hRestore hRestLength hMidStack'
                  refine ⟨final, ?_, ?_, ?_, ?_⟩
                  · change
                      Structured.InteractionSemantics.Code.openRun
                          ([.op op, .op .pop] ++ restore) target =
                        .done (.ok final)
                    rw [Structured.InteractionSemantics.Code.openRun_append,
                      hHeadRun]
                    exact hRestoreRun
                  · simpa [List.append_assoc] using hFinalStack
                  · exact hFinalShared.trans hMidShared
                  · exact hFinalReturns.trans hMidReturns

/-! ### Rotation of the preserved prefix

`Ctx.cleanupManyPreserving?` drops each local with a bare `SWAP temps; POP`
instead of paying `swapRestoreUpTo?` after every discard. That is cheaper by
`temps - 1` instructions per discard, but it leaves the preserved prefix
**rotated left by one** rather than restored, so the induction below cannot fix
`values`: it has to be generalised over rotations.

`rotN` is that rotation. Everything rests on `rotN_length_append`, which says
rotating `xs ++ ys` by `xs.length` yields `ys ++ xs`; periodicity, the
single-step law, and the right-rotation performed by `rotateRestore?` are all
instances of it. -/

private def rot1 {α : Type} : List α → List α
  | [] => []
  | x :: xs => xs ++ [x]

private def rotN {α : Type} : Nat → List α → List α
  | 0, xs => xs
  | k + 1, xs => rotN k (rot1 xs)

private theorem rot1_length {α : Type} (xs : List α) :
    (rot1 xs).length = xs.length := by
  cases xs <;> simp [rot1]

private theorem rotN_length {α : Type} (k : Nat) (xs : List α) :
    (rotN k xs).length = xs.length := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih => simp [rotN, ih, rot1_length]

private theorem rotN_add {α : Type} (a b : Nat) (xs : List α) :
    rotN a (rotN b xs) = rotN (b + a) xs := by
  induction b generalizing xs with
  | zero => simp [rotN]
  | succ b ih =>
      show rotN a (rotN b (rot1 xs)) = rotN (b + 1 + a) xs
      rw [ih]
      have hIdx : b + 1 + a = (b + a) + 1 := by omega
      rw [hIdx]
      rfl

/-- Rotating `xs ++ ys` left by `xs.length` brings `ys` to the front. -/
private theorem rotN_length_append {α : Type} (xs ys : List α) :
    rotN xs.length (xs ++ ys) = ys ++ xs := by
  induction xs generalizing ys with
  | nil => simp [rotN]
  | cons x xs ih =>
      simp only [List.length_cons, List.cons_append]
      have hStep :
          rotN (xs.length + 1) (x :: (xs ++ ys)) =
            rotN xs.length (xs ++ (ys ++ [x])) := by
        show rotN xs.length (rot1 (x :: (xs ++ ys))) = _
        simp [rot1, List.append_assoc]
      rw [hStep, ih (ys ++ [x])]
      simp

private theorem rotN_self {α : Type} (xs : List α) :
    rotN xs.length xs = xs := by
  simpa using rotN_length_append xs []

private theorem rotN_mul_self {α : Type} (m : Nat) (xs : List α) :
    rotN (m * xs.length) xs = xs := by
  induction m with
  | zero => simp [rotN]
  | succ m ih =>
      have hEq : (m + 1) * xs.length = xs.length + m * xs.length := by
        rw [Nat.succ_mul, Nat.add_comm]
      rw [hEq, ← rotN_add (m * xs.length) xs.length xs, rotN_self]
      exact ih

/-- The rotations left behind by `count` discards are undone by rotating right
`count % (preserve + 1)` times, each right-rotation being `preserve` left ones. -/
private theorem rotN_cleanup {values : List Word} {count preserve : Nat}
    (hLength : values.length = preserve + 1) :
    rotN (count + (count % (preserve + 1)) * preserve) values = values := by
  have hEq :
      count + (count % (preserve + 1)) * preserve =
        (count / (preserve + 1) + count % (preserve + 1)) * (preserve + 1) := by
    have hDiv :
        (preserve + 1) * (count / (preserve + 1)) + count % (preserve + 1) =
          count := Nat.div_add_mod count (preserve + 1)
    have hSplit :
        (count % (preserve + 1)) * (preserve + 1) =
          (count % (preserve + 1)) * preserve + count % (preserve + 1) :=
      Nat.mul_succ _ _
    have hComm :
        (preserve + 1) * (count / (preserve + 1)) =
          (count / (preserve + 1)) * (preserve + 1) :=
      Nat.mul_comm _ _
    rw [Nat.add_mul]
    omega
  rw [hEq]
  have hRot :=
    rotN_mul_self (count / (preserve + 1) + count % (preserve + 1)) values
  rw [hLength] at hRot
  exact hRot

/-- `count` bare `SWAP (preserve+1); POP` discards drop `count` values from
under the preserved prefix and leave that prefix rotated left by `count`. -/
private theorem openRun_discardManyRotating?
    {count preserve : Nat} {code : Structured.Code}
    {values discarded suffix : List Word}
    {target : Structured.RunState}
    (hCode :
      Locals.Ctx.discardManyRotating? count (preserve + 1) = some code)
    (hValuesLength : values.length = preserve + 1)
    (hDiscardedLength : discarded.length = count)
    (hStack : target.evm.stack = values ++ discarded ++ suffix) :
    ∃ final,
      Structured.InteractionSemantics.Code.openRun code target =
          .done (.ok final) ∧
        final.evm.stack = rotN count values ++ suffix ∧
        final.evm.toSharedState = target.evm.toSharedState ∧
        final.returns = target.returns := by
  induction count generalizing code values discarded target with
  | zero =>
      simp [Locals.Ctx.discardManyRotating?] at hCode
      subst code
      have hDiscarded : discarded = [] :=
        List.eq_nil_of_length_eq_zero hDiscardedLength
      subst discarded
      exact ⟨target, rfl, by simpa [rotN] using hStack, rfl, rfl⟩
  | succ count ih =>
      simp only [Locals.Ctx.discardManyRotating?] at hCode
      cases hOp : Locals.StackOp.swap? (preserve + 1) with
      | none => simp [hOp] at hCode
      | some op =>
          cases hRest :
              Locals.Ctx.discardManyRotating? count (preserve + 1) with
          | none => simp [hOp, hRest] at hCode
          | some restCode =>
              simp [hOp, hRest] at hCode
              subst code
              cases values with
              | nil => simp at hValuesLength
              | cons value vs =>
                  have hVsLength : vs.length = preserve := by
                    simpa using Nat.succ.inj hValuesLength
                  cases discarded with
                  | nil => simp at hDiscardedLength
                  | cons discardedHead discardedTail =>
                      have hTailLength : discardedTail.length = count := by
                        simpa using Nat.succ.inj hDiscardedLength
                      have hGet :
                          (vs ++ discardedHead :: (discardedTail ++ suffix))[preserve]? =
                            some discardedHead := by
                        simp [hVsLength]
                      obtain
                          ⟨mid, hHeadRun, hMidStack, hMidShared, hMidReturns⟩ :=
                        InteractionPreservation.Code.openRun_swap_pop hOp hGet
                          (by simpa [List.append_assoc] using hStack)
                      have hMidStack' :
                          mid.evm.stack =
                            rot1 (value :: vs) ++ discardedTail ++ suffix := by
                        rw [hMidStack, ← hVsLength, set_append_head]
                        simp [rot1, List.append_assoc]
                      have hRotLength :
                          (rot1 (value :: vs)).length = preserve + 1 := by
                        simp [rot1, hVsLength]
                      obtain
                          ⟨final, hTailRun, hFinalStack,
                            hFinalShared, hFinalReturns⟩ :=
                        ih hRest hRotLength hTailLength hMidStack'
                      refine ⟨final, ?_, ?_, ?_, ?_⟩
                      · change
                          Structured.InteractionSemantics.Code.openRun
                              ([.op op, .op .pop] ++ restCode) target =
                            .done (.ok final)
                        rw [Structured.InteractionSemantics.Code.openRun_append,
                          hHeadRun]
                        exact hTailRun
                      · exact hFinalStack
                      · exact hFinalShared.trans hMidShared
                      · exact hFinalReturns.trans hMidReturns

/-- `rotateRestore? k (preserve+1)` rotates the preserved prefix right `k`
times; a right-rotation of `preserve + 1` values is `preserve` left ones. -/
private theorem openRun_rotateRestore?
    {k preserve : Nat} {code : Structured.Code}
    {values suffix : List Word} {target : Structured.RunState}
    (hCode : Locals.Ctx.rotateRestore? k (preserve + 1) = some code)
    (hValuesLength : values.length = preserve + 1)
    (hStack : target.evm.stack = values ++ suffix) :
    ∃ final,
      Structured.InteractionSemantics.Code.openRun code target =
          .done (.ok final) ∧
        final.evm.stack = rotN (k * preserve) values ++ suffix ∧
        final.evm.toSharedState = target.evm.toSharedState ∧
        final.returns = target.returns := by
  induction k generalizing code values target with
  | zero =>
      simp [Locals.Ctx.rotateRestore?] at hCode
      subst code
      exact ⟨target, rfl, by simpa [rotN] using hStack, rfl, rfl⟩
  | succ k ih =>
      simp only [Locals.Ctx.rotateRestore?, Nat.add_sub_cancel] at hCode
      cases hOne : Locals.Ctx.swapRestoreUpTo? preserve with
      | none => simp [hOne] at hCode
      | some oneCode =>
          cases hRest : Locals.Ctx.rotateRestore? k (preserve + 1) with
          | none => simp [hOne, hRest] at hCode
          | some restCode =>
              simp [hOne, hRest] at hCode
              subst code
              have hNonempty : values ≠ [] := by
                intro hEmpty
                simp [hEmpty] at hValuesLength
              let last := values.getLast hNonempty
              let init := values.dropLast
              have hValuesEq : init ++ [last] = values :=
                List.dropLast_append_getLast hNonempty
              have hInitLength : init.length = preserve := by
                have hLengths := congrArg List.length hValuesEq
                simp only [List.length_append, List.length_singleton]
                  at hLengths
                simp only [init] at hLengths ⊢
                omega
              have hStackInit :
                  target.evm.stack = init ++ last :: suffix := by
                rw [← hValuesEq] at hStack
                simpa [List.append_assoc] using hStack
              obtain ⟨mid, hOneRun, hMidStack, hMidShared, hMidReturns⟩ :=
                openRun_swapRestoreUpTo? hOne hInitLength hStackInit
              have hRotated : last :: init = rotN preserve values := by
                rw [← hValuesEq, ← hInitLength]
                simpa using (rotN_length_append init [last]).symm
              have hMidStack' :
                  mid.evm.stack = rotN preserve values ++ suffix := by
                rw [hMidStack, ← hRotated]
              have hMidLength :
                  (rotN preserve values).length = preserve + 1 := by
                rw [rotN_length]; exact hValuesLength
              obtain
                  ⟨final, hRestRun, hFinalStack,
                    hFinalShared, hFinalReturns⟩ :=
                ih hRest hMidLength hMidStack'
              refine ⟨final, ?_, ?_, ?_, ?_⟩
              · rw [Structured.InteractionSemantics.Code.openRun_append,
                  hOneRun]
                exact hRestRun
              · rw [hFinalStack, rotN_add]
                have hIdx : preserve + k * preserve = (k + 1) * preserve := by
                  rw [Nat.succ_mul, Nat.add_comm]
                rw [hIdx]
              · exact hFinalShared.trans hMidShared
              · exact hFinalReturns.trans hMidReturns

/-- Repeated preserving cleanup removes a contiguous list below the prefix. -/
theorem openRun_cleanupManyPreservingRot?
    {count preserve : Nat} {code : Structured.Code}
    {values discarded suffix : List Word}
    {target : Structured.RunState}
    (hCode :
      Locals.Ctx.cleanupManyPreservingRot? count preserve = some code)
    (hValuesLength : values.length = preserve)
    (hDiscardedLength : discarded.length = count)
    (hStack : target.evm.stack = values ++ discarded ++ suffix) :
    ∃ final,
      Structured.InteractionSemantics.Code.openRun code target =
          .done (.ok final) ∧
        final.evm.stack = values ++ suffix ∧
        final.evm.toSharedState = target.evm.toSharedState ∧
        final.returns = target.returns := by
  cases preserve with
  | zero =>
      rw [Locals.Ctx.cleanupManyPreservingRot?_zero] at hCode
      have hCodeEq :
          List.replicate count (Structured.BasicInstr.op .pop) = code :=
        Option.some.inj hCode
      subst hCodeEq
      have hValues : values = [] :=
        List.eq_nil_of_length_eq_zero hValuesLength
      subst values
      have hDrop : (discarded ++ suffix).drop count = suffix := by
        rw [← hDiscardedLength]
        exact List.drop_left
      have hBound : count ≤ target.evm.stack.length := by
        rw [hStack]
        simp [hDiscardedLength]
      obtain ⟨final, hRun, hFinalStack, hFinalShared, hFinalReturns⟩ :=
        InteractionPreservation.Code.openRun_replicate_pop count hBound
      refine ⟨final, hRun, ?_, hFinalShared, hFinalReturns⟩
      rw [hFinalStack, hStack]
      simpa using hDrop
  | succ preserve =>
      simp only [Locals.Ctx.cleanupManyPreservingRot?] at hCode
      cases hBody :
          Locals.Ctx.discardManyRotating? count (preserve + 1) with
      | none => simp [hBody] at hCode
      | some body =>
          cases hFixup :
              Locals.Ctx.rotateRestore?
                (count % (preserve + 1)) (preserve + 1) with
          | none => simp [hBody, hFixup] at hCode
          | some fixup =>
              simp [hBody, hFixup] at hCode
              subst code
              obtain
                  ⟨mid, hBodyRun, hMidStack, hMidShared, hMidReturns⟩ :=
                openRun_discardManyRotating? hBody hValuesLength
                  hDiscardedLength hStack
              have hMidLength :
                  (rotN count values).length = preserve + 1 := by
                rw [rotN_length]; exact hValuesLength
              obtain
                  ⟨final, hFixupRun, hFinalStack,
                    hFinalShared, hFinalReturns⟩ :=
                openRun_rotateRestore? hFixup hMidLength hMidStack
              refine ⟨final, ?_, ?_, ?_, ?_⟩
              · rw [Structured.InteractionSemantics.Code.openRun_append,
                  hBodyRun]
                exact hFixupRun
              · rw [hFinalStack, rotN_add, rotN_cleanup hValuesLength]
              · exact hFinalShared.trans hMidShared
              · exact hFinalReturns.trans hMidReturns

/-- **Bulk teardown under one preserved value.**

`SWAP count ; POP^count` applied to `[p] ++ discarded ++ suffix` (with
`discarded.length = count`) sinks `p` past the whole discard window and then
clears it, leaving `[p] ++ suffix`. -/
theorem openRun_bulkDiscardUnderOne?
    {count : Nat} {code : Structured.Code}
    {values discarded suffix : List Word}
    {target : Structured.RunState}
    (hCode : Locals.Ctx.bulkDiscardUnderOne? count = some code)
    (hValuesLength : values.length = 1)
    (hDiscardedLength : discarded.length = count)
    (hStack : target.evm.stack = values ++ discarded ++ suffix) :
    ∃ final,
      Structured.InteractionSemantics.Code.openRun code target =
          .done (.ok final) ∧
        final.evm.stack = values ++ suffix ∧
        final.evm.toSharedState = target.evm.toSharedState ∧
        final.returns = target.returns := by
  obtain ⟨p, rfl⟩ := List.length_eq_one_iff.mp hValuesLength
  cases count with
  | zero =>
      simp [Locals.Ctx.bulkDiscardUnderOne?, StackOp.swap?] at hCode
  | succ d =>
      unfold Locals.Ctx.bulkDiscardUnderOne? at hCode
      cases hOp : StackOp.swap? (d + 1) with
      | none => simp [hOp] at hCode
      | some op =>
          rw [hOp] at hCode
          simp at hCode
          subst hCode
          have hd : d < discarded.length := by omega
          have hGet : (discarded ++ suffix)[d]? = some discarded[d] := by
            rw [List.getElem?_append_left hd]
            exact List.getElem?_eq_getElem hd
          have hStack' : target.evm.stack = p :: (discarded ++ suffix) := by
            simpa using hStack
          let afterSwap :=
            target.withEVM
              (target.evm.replaceStackAndIncrPC
                (discarded[d] :: (discarded ++ suffix).set d p))
          have hAfterStack :
              afterSwap.evm.stack =
                discarded[d] :: (discarded ++ suffix).set d p := by
            simp [afterSwap, EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
          have hBound : d + 1 ≤ afterSwap.evm.stack.length := by
            rw [hAfterStack]
            simp
            omega
          obtain ⟨final, hPopRun, hFinalStack, hFinalShared, hFinalReturns⟩ :=
            InteractionPreservation.Code.openRun_replicate_pop
              (target := afterSwap) (d + 1) hBound
          have hTail : ((discarded ++ suffix).set d p).drop d = p :: suffix := by
            rw [List.set_append_left d p hd]
            rw [List.drop_append_of_le_length (by simp; omega)]
            have hLen : (discarded.set d p).length = d + 1 := by
              simp [hDiscardedLength]
            have hdSet : d < (discarded.set d p).length := by omega
            rw [List.drop_eq_getElem_cons hdSet,
              List.drop_eq_nil_of_le (by omega), List.getElem_set_self]
            simp
          refine ⟨final, ?_, ?_, ?_, ?_⟩
          · change
              Structured.InteractionSemantics.Code.openRun
                  ([Structured.BasicInstr.op op] ++
                    List.replicate (d + 1)
                      (Structured.BasicInstr.op .pop)) target =
                .done (.ok final)
            rw [Structured.InteractionSemantics.Code.openRun_append,
              InteractionPreservation.Code.openRun_swap hOp hGet hStack']
            exact hPopRun
          · rw [hFinalStack, hAfterStack, List.drop_succ_cons, hTail]
            simp
          · exact hFinalShared.trans (by
              simp [afterSwap, EvmYul.EVM.State.replaceStackAndIncrPC,
                EvmYul.EVM.State.incrPC])
          · exact hFinalReturns.trans (by simp [afterSwap])

/-- Preserving cleanup: the rotating schedule, or the bulk shortcut at
`preserve = 1`. -/
theorem openRun_cleanupManyPreserving?
    {count preserve : Nat} {code : Structured.Code}
    {values discarded suffix : List Word}
    {target : Structured.RunState}
    (hCode :
      Locals.Ctx.cleanupManyPreserving? count preserve = some code)
    (hValuesLength : values.length = preserve)
    (hDiscardedLength : discarded.length = count)
    (hStack : target.evm.stack = values ++ discarded ++ suffix) :
    ∃ final,
      Structured.InteractionSemantics.Code.openRun code target =
          .done (.ok final) ∧
        final.evm.stack = values ++ suffix ∧
        final.evm.toSharedState = target.evm.toSharedState ∧
        final.returns = target.returns := by
  match preserve with
  | 0 =>
      rw [Locals.Ctx.cleanupManyPreserving?_zero_eq] at hCode
      exact openRun_cleanupManyPreservingRot? hCode hValuesLength
        hDiscardedLength hStack
  | 1 =>
      rw [Locals.Ctx.cleanupManyPreserving?_one] at hCode
      cases hBulk : Locals.Ctx.bulkDiscardUnderOne? count with
      | none =>
          rw [hBulk] at hCode
          exact openRun_cleanupManyPreservingRot? hCode hValuesLength
            hDiscardedLength hStack
      | some bulk =>
          rw [hBulk] at hCode
          cases hCode
          exact openRun_bulkDiscardUnderOne? hBulk hValuesLength
            hDiscardedLength hStack
  | _ + 2 =>
      rw [Locals.Ctx.cleanupManyPreserving?_succ_succ_eq] at hCode
      exact openRun_cleanupManyPreservingRot? hCode hValuesLength
        hDiscardedLength hStack

/-- The zero-byte return-value retag emitted at the end of a preserving cleanup
runs to the identity: `bindLocals` is a type-level marker whose Structured
semantics is `.ok state`. -/
@[simp] theorem openRun_retagPreservedWords (preserve : Nat)
    (target : Structured.RunState) :
    Structured.InteractionSemantics.Code.openRun
        (Ctx.retagPreservedWords preserve) target =
      .done (.ok target) := by
  cases preserve with
  | zero => rfl
  | succ count =>
      rw [Ctx.retagPreservedWords,
        Structured.InteractionSemantics.Code.openRun_single]
      unfold Structured.InteractionSemantics.BasicInstr.openStep
        Structured.InteractionSemantics.BasicInstr.openStepEVM
      simp [Structured.BasicInstr.step, Simulation.Interaction.map,
        Simulation.Interaction.pure, Structured.RunState.withEVM]

/-- **Preserving cleanup, including the trailing zero-byte return-value retag.**

This is the form the procedure-exit call sites consume: `cleanupToPreserving?`
emits the value-preserving `SWAP`/`POP` schedule followed by a `bindLocals`
marker that reclassifies the kept return values as anonymous words.  The marker
lowers to no bytes and steps to the identity, so the runtime conclusion is
exactly that of `openRun_cleanupManyPreserving?`. -/
theorem openRun_cleanupToPreserving?
    {ctx : Ctx} {preserve targetDepth : Nat} {code : Structured.Code}
    {values discarded suffix : List Word}
    {target : Structured.RunState}
    (hCode : ctx.cleanupToPreserving? preserve targetDepth = some code)
    (hValuesLength : values.length = preserve)
    (hDiscardedLength : discarded.length = ctx.layout.length - targetDepth)
    (hStack : target.evm.stack = values ++ discarded ++ suffix) :
    ∃ final,
      Structured.InteractionSemantics.Code.openRun code target =
          .done (.ok final) ∧
        final.evm.stack = values ++ suffix ∧
        final.evm.toSharedState = target.evm.toSharedState ∧
        final.returns = target.returns := by
  unfold Ctx.cleanupToPreserving? at hCode
  split at hCode
  · rcases Option.map_eq_some_iff.mp hCode with ⟨many, hMany, hManyCode⟩
    subst hManyCode
    obtain ⟨final, hRun, hFinalStack, hFinalShared, hFinalReturns⟩ :=
      openRun_cleanupManyPreserving? hMany hValuesLength hDiscardedLength
        hStack
    refine ⟨final, ?_, hFinalStack, hFinalShared, hFinalReturns⟩
    rw [Structured.InteractionSemantics.Code.openRun_append, hRun]
    simpa using openRun_retagPreservedWords preserve final
  · simp at hCode

end InteractionCleanupPreservation
end Locals
end EvmCompiler
