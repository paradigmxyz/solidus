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

/-- Repeated preserving cleanup removes a contiguous list below the prefix. -/
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
  induction count generalizing code discarded target with
  | zero =>
      simp [Locals.Ctx.cleanupManyPreserving?] at hCode
      subst code
      have hDiscarded : discarded = [] :=
        List.eq_nil_of_length_eq_zero hDiscardedLength
      subst discarded
      exact ⟨target, rfl, by simpa using hStack, rfl, rfl⟩
  | succ count ih =>
      simp only [Locals.Ctx.cleanupManyPreserving?] at hCode
      cases hHead : Locals.Ctx.cleanupOnePreserving? preserve with
      | none => simp [hHead] at hCode
      | some headCode =>
          cases hTail : Locals.Ctx.cleanupManyPreserving? count preserve with
          | none => simp [hHead, hTail] at hCode
          | some tailCode =>
              simp [hHead, hTail] at hCode
              subst code
              cases discarded with
              | nil => simp at hDiscardedLength
              | cons discardedHead discardedTail =>
                  have hTailLength : discardedTail.length = count := by
                    simpa using Nat.succ.inj hDiscardedLength
                  obtain
                      ⟨mid, hHeadRun, hMidStack, hMidShared, hMidReturns⟩ :=
                    openRun_cleanupOnePreserving? hHead hValuesLength
                      (by simpa [List.append_assoc] using hStack)
                  obtain
                      ⟨final, hTailRun, hFinalStack,
                        hFinalShared, hFinalReturns⟩ :=
                    ih hTail hTailLength
                      (by simpa [List.append_assoc] using hMidStack)
                  refine ⟨final, ?_, hFinalStack, ?_, ?_⟩
                  · rw [Structured.InteractionSemantics.Code.openRun_append,
                      hHeadRun]
                    exact hTailRun
                  · exact hFinalShared.trans hMidShared
                  · exact hFinalReturns.trans hMidReturns

end InteractionCleanupPreservation
end Locals
end EvmCompiler
