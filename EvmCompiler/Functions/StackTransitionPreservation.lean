import EvmCompiler.Functions.StackRelation
import EvmCompiler.Locals.InteractionCleanupPreservation

/-!
Open-semantics preservation for one checked symbolic-stack promotion.
-/

namespace EvmCompiler
namespace Functions
namespace StackTransitionPreservation

open AllocationLayout
open StackRelation

theorem Discard.openRun
    {ctx : Locals.Ctx} {discard : Discard}
    {discarded : Locals.Layout} {code : Structured.Code}
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hApply : discard.apply? ctx.layout = some discarded)
    (hCode :
      ctx.discardNameStackOnly? discard.name = some (code, discarded))
    (hRel : StateRel ctx.layout suffix returns source target) :
    ∃ final,
      Structured.InteractionSemantics.Code.openRun code target =
          .done (.ok final) ∧
        StateRel discarded suffix returns source final := by
  unfold Discard.apply? at hApply
  cases hDepth : Locals.Layout.lookupDepth? discard.name ctx.layout with
  | none => simp [hDepth] at hApply
  | some depth =>
      by_cases hAllowed : depth = discard.depth ∧ depth ≤ 17
      · simp [hDepth, hAllowed] at hApply
        have hDiscarded := hApply.2
        subst discarded
        have hMem : discard.name ∈ ctx.layout :=
          Locals.Layout.mem_of_lookupDepth?_eq_some hDepth
        obtain ⟨index, hDepthIndex⟩ :=
          Locals.Layout.exists_lookupDepth?_eq_some_of_mem hMem
        have hDepthEq : depth = index + 1 := by
          rw [hDepth] at hDepthIndex
          exact Option.some.inj hDepthIndex
        have hIndex : discard.depth - 1 = index := by omega
        have hAt : ctx.layout[index]? = some discard.name :=
          Locals.Layout.getElem?_eq_some_of_lookupDepth?_eq_some hDepthIndex
        have hValueAt := values_getElem?_eq_some
          (source := source) hAt
        have hIndexBound : index < (values source ctx.layout).length :=
          (List.getElem?_eq_some_iff.mp hValueAt).1
        have hTargetAt :
            target.evm.stack[index]? =
              some ((source.vars discard.name).getD
                (EvmYul.UInt256.ofNat 0)) := by
          rw [hRel.stack, List.getElem?_append_left hIndexBound]
          exact hValueAt
        obtain ⟨final, hRun, hDiscardedLayout, hFinalStack,
            hShared, hReturns⟩ :=
          Locals.InteractionCleanupPreservation.openRun_discardNameStackOnly?_exact
            hDepthIndex hCode hTargetAt
        refine ⟨final, hRun, ?_⟩
        rw [hIndex]
        constructor
        · exact hShared.trans hRel.shared
        · exact hReturns.trans hRel.returns
        · rw [hFinalStack, hRel.stack,
            Locals.StackList.swapPopAt_append_of_lt
              index (values source ctx.layout) suffix hIndexBound,
            ← values_discardAt]
        · intro candidate hCandidate
          apply hRel.defined
          exact Locals.StackList.mem_of_mem_swapPopAt hCandidate
      · simp [hDepth, hAllowed] at hApply

theorem Discard.openRunWithBind
    {ctx : Locals.Ctx} {discard : Discard}
    {discarded : Locals.Layout} {code : Structured.Code}
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hApply : discard.apply? ctx.layout = some discarded)
    (hCode :
      ctx.discardNameStackOnly? discard.name = some (code, discarded))
    (hRel : StateRel ctx.layout suffix returns source target) :
    ∃ final,
      Structured.InteractionSemantics.Code.openRun
          (code ++ Locals.bindLocals 0 discarded) target =
        .done (.ok final) ∧
      StateRel discarded suffix returns source final := by
  obtain ⟨final, hRun, hFinal⟩ := Discard.openRun hApply hCode hRel
  refine ⟨final, ?_, hFinal⟩
  rw [Structured.InteractionSemantics.Code.openRun_append, hRun,
    Simulation.Interaction.bind_done_ok]
  simpa [Locals.bindLocals] using
    Locals.InteractionPreservation.Code.openRun_bindLocals 0 discarded final

inductive DiscardCodes :
    Locals.Ctx → List Discard → List Structured.Code → Locals.Ctx → Prop where
  | nil (ctx : Locals.Ctx) : DiscardCodes ctx [] [] ctx
  | cons
      {ctx discardedCtx finalCtx : Locals.Ctx}
      {discarded : Locals.Layout}
      {discard : Discard} {rest : List Discard}
      {raw head : Structured.Code} {tail : List Structured.Code}
      (apply : discard.apply? ctx.layout = some discarded)
      (code :
        ctx.discardNameStackOnly? discard.name = some (raw, discarded))
      (discardedCtxEq : discardedCtx = ctx.withLayout discarded)
      (headEq : head = raw ++ Locals.bindLocals 0 discarded)
      (tailCodes : DiscardCodes discardedCtx rest tail finalCtx) :
      DiscardCodes ctx (discard :: rest) (head :: tail) finalCtx

namespace DiscardCodes

theorem code_length
    {ctx finalCtx : Locals.Ctx} {discards : List Discard}
    {codes : List Structured.Code}
    (hCodes : DiscardCodes ctx discards codes finalCtx) :
    codes.length = discards.length := by
  induction hCodes with
  | nil => rfl
  | cons _ _ _ _ hTail ih => simp [ih]

theorem openRun
    {ctx finalCtx : Locals.Ctx} {discards : List Discard}
    {codes : List Structured.Code}
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hCodes : DiscardCodes ctx discards codes finalCtx)
    (hRel : StateRel ctx.layout suffix returns source target) :
    ∃ final,
      Structured.InteractionSemantics.Code.openRun codes.flatten target =
          .done (.ok final) ∧
        StateRel finalCtx.layout suffix returns source final := by
  induction hCodes generalizing target with
  | nil ctx => exact ⟨target, rfl, hRel⟩
  | @cons ctx discardedCtx finalCtx discarded discard rest raw head tail
      hApply hCode hDiscardedCtx hHead hTail ih =>
      obtain ⟨middle, hHeadRun, hMiddleRel⟩ :=
        Discard.openRunWithBind hApply hCode hRel
      subst discardedCtx
      obtain ⟨final, hTailRun, hFinalRel⟩ := ih hMiddleRel
      refine ⟨final, ?_, hFinalRel⟩
      rw [hHead]
      change
        Structured.InteractionSemantics.Code.openRun
            ((raw ++ Locals.bindLocals 0 discarded) ++ tail.flatten) target =
          .done (.ok final)
      rw [Structured.InteractionSemantics.Code.openRun_append, hHeadRun]
      exact hTailRun

end DiscardCodes

theorem Promotion.openRun
    {promotion : Promotion} {layout promoted : Locals.Layout}
    {code : Structured.Code} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hApply : promotion.apply? layout = some promoted)
    (hCode :
      Locals.Ctx.swapRestoreUpTo? (promotion.depth - 1) = some code)
    (hRel : StateRel layout suffix returns source target) :
    ∃ final,
      Structured.InteractionSemantics.Code.openRun code target =
          .done (.ok final) ∧
        StateRel promoted suffix returns source final := by
  unfold Promotion.apply? at hApply
  cases hDepth : Locals.Layout.lookupDepth? promotion.name layout with
  | none => simp [hDepth] at hApply
  | some depth =>
      by_cases hAllowed : depth = promotion.depth ∧ depth ≤ 17
      · simp [hDepth, hAllowed] at hApply
        have hPromoted := hApply.2
        subst promoted
        have hMem : promotion.name ∈ layout :=
          Locals.Layout.mem_of_lookupDepth?_eq_some hDepth
        obtain ⟨index, hDepthIndex⟩ :=
          Locals.Layout.exists_lookupDepth?_eq_some_of_mem hMem
        have hIndex : promotion.depth - 1 = index := by
          rw [hDepth] at hDepthIndex
          have := Option.some.inj hDepthIndex.symm
          omega
        have hAt : layout[index]? = some promotion.name :=
          Locals.Layout.getElem?_eq_some_of_lookupDepth?_eq_some hDepthIndex
        have hValueAt := values_getElem?_eq_some
          (source := source) hAt
        have hValuesSplit :=
          list_eq_take_cons_drop_of_getElem?_eq_some hValueAt
        have hTargetStack :
            target.evm.stack =
              (values source layout).take index ++
                (source.vars promotion.name).getD
                    (EvmYul.UInt256.ofNat 0) ::
                  ((values source layout).drop (index + 1) ++ suffix) := by
          calc
            target.evm.stack = values source layout ++ suffix := hRel.stack
            _ =
                ((values source layout).take index ++
                    (source.vars promotion.name).getD
                        (EvmYul.UInt256.ofNat 0) ::
                      (values source layout).drop (index + 1)) ++ suffix :=
              congrArg (fun values => values ++ suffix) hValuesSplit
            _ = _ := by simp [List.append_assoc]
        have hIndexBound : index < (values source layout).length :=
          (List.getElem?_eq_some_iff.mp hValueAt).1
        have hTakeLength :
            ((values source layout).take index).length = index := by
          rw [List.length_take]
          omega
        obtain ⟨final, hRun, hFinalStack, hShared, hReturns⟩ :=
          Locals.InteractionCleanupPreservation.openRun_swapRestoreUpTo?
            (by simpa [hIndex] using hCode)
            hTakeLength hTargetStack
        refine ⟨final, hRun, ?_⟩
        rw [hIndex]
        constructor
        · exact hShared.trans hRel.shared
        · exact hReturns.trans hRel.returns
        · rw [hFinalStack, values_promoteAt hAt]
          simp [List.append_assoc]
        · intro candidate hCandidate
          exact hRel.defined (mem_of_mem_promoteAt hAt hCandidate)
      · simp [hDepth, hAllowed] at hApply

theorem Promotion.openRunWithBind
    {promotion : Promotion} {layout promoted : Locals.Layout}
    {shuffle : Structured.Code} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hApply : promotion.apply? layout = some promoted)
    (hCode :
      Locals.Ctx.swapRestoreUpTo? (promotion.depth - 1) = some shuffle)
    (hRel : StateRel layout suffix returns source target) :
    ∃ final,
      Structured.InteractionSemantics.Code.openRun
          (shuffle ++ Locals.bindLocals 0 promoted) target =
        .done (.ok final) ∧
      StateRel promoted suffix returns source final := by
  obtain ⟨final, hRun, hFinal⟩ := Promotion.openRun hApply hCode hRel
  refine ⟨final, ?_, hFinal⟩
  rw [Structured.InteractionSemantics.Code.openRun_append, hRun,
    Simulation.Interaction.bind_done_ok]
  simpa [Locals.bindLocals] using
    Locals.InteractionPreservation.Code.openRun_bindLocals 0 promoted final

theorem Cleanup.openRun
    {promoted targetLayout : Locals.Layout}
    {ctx : Locals.Ctx} {code : Structured.Code}
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hCtx : ctx.layout = promoted)
    (hSuffix :
      targetLayout =
        promoted.drop (promoted.length - targetLayout.length))
    (hCode : ctx.cleanupTo? targetLayout.length = some code)
    (hRel : StateRel promoted suffix returns source target) :
    ∃ final,
      Structured.InteractionSemantics.Code.openRun code target =
          .done (.ok final) ∧
        StateRel targetLayout suffix returns source final := by
  have hTargetLength : targetLayout.length ≤ promoted.length := by
    have hLengths := congrArg List.length hSuffix
    simp only [List.length_drop] at hLengths
    omega
  let count := promoted.length - targetLayout.length
  have hPromotedSplit :
      promoted = promoted.take count ++ targetLayout := by
    calc
      promoted = promoted.take count ++ promoted.drop count :=
        (List.take_append_drop count promoted).symm
      _ = promoted.take count ++ targetLayout := by rw [← hSuffix]
  have hValuesSplit :
      values source promoted =
        values source (promoted.take count) ++
          values source targetLayout := by
    calc
      values source promoted =
          values source (promoted.take count ++ targetLayout) :=
        congrArg (values source) hPromotedSplit
      _ = _ := by simp [values]
  have hCountLe : count ≤ promoted.length := by
    simp [count]
  have hCountLength : (promoted.take count).length = count := by
    rw [List.length_take]
    omega
  have hPrefixLength :
      (values source (promoted.take count)).length = count := by
    unfold values
    rw [List.length_map, hCountLength]
  have hTargetStack :
      target.evm.stack =
        values source (promoted.take count) ++
          (values source targetLayout ++ suffix) := by
    rw [hRel.stack, hValuesSplit]
    simp [List.append_assoc]
  have hBound : count ≤ target.evm.stack.length := by
    rw [hTargetStack, List.length_append, hPrefixLength]
    omega
  unfold Locals.Ctx.cleanupTo? at hCode
  rw [if_pos (by simpa [hCtx] using hTargetLength)] at hCode
  have hCodeEq :
      code = List.replicate count (Structured.BasicInstr.op .pop) := by
    simpa [hCtx, count] using (Option.some.inj hCode).symm
  subst code
  obtain ⟨final, hRun, hFinalStack, hShared, hReturns⟩ :=
    Locals.InteractionPreservation.Code.openRun_replicate_pop count hBound
  refine ⟨final, hRun, ?_⟩
  constructor
  · exact hShared.trans hRel.shared
  · exact hReturns.trans hRel.returns
  · rw [hFinalStack, hTargetStack]
    calc
      (values source (promoted.take count) ++
          (values source targetLayout ++ suffix)).drop count =
          (values source (promoted.take count) ++
            (values source targetLayout ++ suffix)).drop
              (values source (promoted.take count)).length := by
        rw [hPrefixLength]
      _ = values source targetLayout ++ suffix := List.drop_left
  · intro name hName
    apply hRel.defined
    rw [hPromotedSplit]
    exact List.mem_append_right _ hName

inductive PromotionCodes :
    Locals.Layout → List Promotion → List Structured.Code →
      Locals.Layout → Prop where
  | nil (layout : Locals.Layout) : PromotionCodes layout [] [] layout
  | cons
      {layout promoted final : Locals.Layout}
      {promotion : Promotion} {rest : List Promotion}
      {shuffle head : Structured.Code} {tail : List Structured.Code}
      (apply : promotion.apply? layout = some promoted)
      (code :
        Locals.Ctx.swapRestoreUpTo? (promotion.depth - 1) = some shuffle)
      (headEq : head = shuffle ++ Locals.bindLocals 0 promoted)
      (tailCodes : PromotionCodes promoted rest tail final) :
      PromotionCodes layout (promotion :: rest) (head :: tail) final

namespace PromotionCodes

theorem code_length
    {layout finalLayout : Locals.Layout}
    {promotions : List Promotion} {codes : List Structured.Code}
    (hCodes : PromotionCodes layout promotions codes finalLayout) :
    codes.length = promotions.length := by
  induction hCodes with
  | nil => rfl
  | cons _ _ _ hTail ih => simp [ih]

theorem openRun
    {layout finalLayout : Locals.Layout}
    {promotions : List Promotion} {codes : List Structured.Code}
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hCodes : PromotionCodes layout promotions codes finalLayout)
    (hRel : StateRel layout suffix returns source target) :
    ∃ final,
      Structured.InteractionSemantics.Code.openRun codes.flatten target =
          .done (.ok final) ∧
        StateRel finalLayout suffix returns source final := by
  induction hCodes generalizing target with
  | nil layout => exact ⟨target, rfl, hRel⟩
  | @cons layout promoted finalLayout promotion rest shuffle head tail
      hApply hCode hHead hTail ih =>
      obtain ⟨middle, hHeadRun, hMiddleRel⟩ :=
        Promotion.openRunWithBind hApply hCode hRel
      obtain ⟨final, hTailRun, hFinalRel⟩ := ih hMiddleRel
      refine ⟨final, ?_, hFinalRel⟩
      rw [hHead]
      change
        Structured.InteractionSemantics.Code.openRun
            ((shuffle ++ Locals.bindLocals 0 promoted) ++ tail.flatten)
              target = .done (.ok final)
      rw [Structured.InteractionSemantics.Code.openRun_append, hHeadRun]
      exact hTailRun

end PromotionCodes

theorem Ordering.openRun
    {ordering : AllocationLayout.Ordering} {codes : List Structured.Code}
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hCodes :
      PromotionCodes ordering.source ordering.promotions codes ordering.target)
    (hRel : StateRel ordering.source suffix returns source target) :
    ∃ final,
      Structured.InteractionSemantics.Code.openRun codes.flatten target =
          .done (.ok final) ∧
        StateRel ordering.target suffix returns source final := by
  exact PromotionCodes.openRun hCodes hRel

theorem Schedule.openRun
    {layout : Locals.Layout} {schedule : Schedule}
    {codes : List Structured.Code} {cleanup : Structured.Code}
    {cleanupCtx : Locals.Ctx}
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hSuffix :
      schedule.target =
        schedule.promoted.drop
          (schedule.promoted.length - schedule.target.length))
    (hCodes :
      PromotionCodes layout schedule.promotions codes schedule.promoted)
    (hCleanupCtx : cleanupCtx.layout = schedule.promoted)
    (hCleanup :
      cleanupCtx.cleanupTo? schedule.target.length = some cleanup)
    (hRel : StateRel layout suffix returns source target) :
    ∃ final,
      Structured.InteractionSemantics.Code.openRun
          (codes.flatten ++ cleanup) target = .done (.ok final) ∧
        StateRel schedule.target suffix returns source final := by
  obtain ⟨middle, hPromotionsRun, hMiddleRel⟩ :=
    PromotionCodes.openRun hCodes hRel
  obtain ⟨final, hCleanupRun, hFinalRel⟩ :=
    Cleanup.openRun hCleanupCtx hSuffix hCleanup hMiddleRel
  refine ⟨final, ?_, hFinalRel⟩
  rw [Structured.InteractionSemantics.Code.openRun_append, hPromotionsRun]
  exact hCleanupRun

end StackTransitionPreservation
end Functions
end EvmCompiler
