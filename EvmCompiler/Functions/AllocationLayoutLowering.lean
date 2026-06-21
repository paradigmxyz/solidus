import EvmCompiler.Functions.AllocationLayout
import EvmCompiler.Locals.Compiler

/-!
Adjacent compiler bridge for checked allocation layout schedules.

`AllocationLayout` owns symbolic transitions.  This module proves that the
ordinary Locals compiler realizes those transitions; it contains no source
liveness analysis and no higher- or lower-pass compiler reasoning.
-/

namespace EvmCompiler
namespace Functions
namespace AllocationLayoutLowering

open AllocationLayout

theorem Promotion.compile
    {ctx : Locals.Ctx} {promotion : Promotion}
    {promoted : Locals.Layout}
    (hApply : promotion.apply? ctx.layout = some promoted) :
    ∃ code,
      Locals.Stmt.compile ctx (.promoteName promotion.name) =
        some (code, ctx.withLayout promoted) := by
  unfold Promotion.apply? at hApply
  cases hDepth :
      Locals.Layout.lookupDepth? promotion.name ctx.layout with
  | none => simp [hDepth] at hApply
  | some depth =>
      by_cases hAllowed :
          depth = promotion.depth ∧ depth ≤ 17
      · simp [hDepth, hAllowed] at hApply
        have hPromoted := hApply.2
        subst promoted
        have hIndex : promotion.depth - 1 ≤ 16 := by omega
        have hPromotionBound : promotion.depth ≤ 17 := by omega
        obtain ⟨shuffle, hShuffle⟩ :=
          Locals.Ctx.exists_swapRestoreUpTo?_of_le hIndex
        have hPromote :
            ctx.promoteNameStackOnly? promotion.name =
              some
                (shuffle,
                  Locals.Layout.promoteAt
                    (promotion.depth - 1) ctx.layout) := by
          unfold Locals.Ctx.promoteNameStackOnly?
          simp [hDepth, hAllowed.1, hIndex, hPromotionBound, hShuffle]
        exact
          ⟨Locals.codeStmt shuffle,
            by simp [Locals.Stmt.compile, hPromote]⟩
      · simp [hDepth, hAllowed] at hApply

theorem compilePromotions
    {ctx : Locals.Ctx} {promotions : List Promotion}
    {finalLayout : Locals.Layout}
    (hRun : run ctx.layout promotions = some finalLayout) :
    ∃ code finalCtx,
      Locals.Block.compileOpen ctx
          { stmts := promotions.map fun promotion =>
              Locals.Stmt.promoteName promotion.name } =
        some (code, finalCtx) ∧
      finalCtx = ctx.withLayout finalLayout := by
  induction promotions generalizing ctx with
  | nil =>
      simp [run] at hRun
      subst finalLayout
      refine ⟨[], ctx, by simp [Locals.Block.compileOpen], ?_⟩
      cases ctx
      rfl
  | cons promotion rest ih =>
      unfold run at hRun
      cases hApply : promotion.apply? ctx.layout with
      | none => simp [hApply] at hRun
      | some promoted =>
          have hRestRun : run promoted rest = some finalLayout := by
            simpa [hApply] using hRun
          obtain ⟨headCode, hHead⟩ := Promotion.compile hApply
          obtain ⟨tailCode, tailCtx, hTail, hTailCtx⟩ :=
            ih (ctx := ctx.withLayout promoted) hRestRun
          have hFinalCtx :
              tailCtx = ctx.withLayout finalLayout := by
            rw [hTailCtx]
            cases ctx
            rfl
          refine
            ⟨headCode ++ tailCode, tailCtx, ?_, hFinalCtx⟩
          · simp [Locals.Block.compileOpen, hHead, hTail]

theorem Ordering.compile
    {ctx : Locals.Ctx} (ordering : AllocationLayout.Ordering)
    (hSource : ctx.layout = ordering.source) :
    ∃ code finalCtx,
      Locals.Block.compileOpen ctx
          { stmts := ordering.statements } = some (code, finalCtx) ∧
      finalCtx = ctx.withLayout ordering.target := by
  have hRun :
      run ctx.layout ordering.promotions = some ordering.target := by
    simpa [hSource] using ordering.valid
  simpa [Ordering.statements] using compilePromotions hRun

theorem cleanup_compile
    {ctx : Locals.Ctx} {target : Locals.Layout}
    (hSuffix :
      target =
        ctx.layout.drop (ctx.layout.length - target.length)) :
    ∃ code,
      Locals.Block.compileOpen ctx
          { stmts := [Locals.Stmt.cleanupTo target] } =
        some (code, ctx.withLayout target) := by
  have hLength : target.length ≤ ctx.layout.length := by
    have hLengths := congrArg List.length hSuffix
    simp only [List.length_drop] at hLengths
    omega
  let cleanup :=
    List.replicate (ctx.layout.length - target.length)
      (Structured.BasicInstr.op .pop)
  have hCleanup : ctx.cleanupTo? target.length = some cleanup := by
    unfold Locals.Ctx.cleanupTo?
    rw [if_pos hLength]
  have hStmt :
      Locals.Stmt.compile ctx (.cleanupTo target) =
        some (Locals.codeStmt cleanup, ctx.withLayout target) := by
    rw [Locals.Stmt.compile]
    rw [if_pos hSuffix]
    rw [hCleanup]
    rfl
  exact
    ⟨Locals.codeStmt cleanup,
      by simp [Locals.Block.compileOpen, hStmt]⟩

theorem Schedule.compile
    {ctx : Locals.Ctx} {schedule : Schedule}
    {live : AllocationLiveness.LiveSet}
    (hValid : schedule.ValidFor ctx.layout live) :
    ∃ code finalCtx,
      Locals.Block.compileOpen ctx { stmts := schedule.statements } =
        some (code, finalCtx) ∧
      finalCtx = ctx.withLayout schedule.target := by
  obtain ⟨promoteCode, promotedCtx, hPromote, hPromotedCtx⟩ :=
    compilePromotions hValid.1
  subst promotedCtx
  have hSuffix :
      schedule.target =
        (ctx.withLayout schedule.promoted).layout.drop
          ((ctx.withLayout schedule.promoted).layout.length -
            schedule.target.length) := by
    simpa using hValid.2.2
  obtain ⟨cleanupCode, hCleanup⟩ := cleanup_compile hSuffix
  refine
    ⟨promoteCode ++ cleanupCode,
      (ctx.withLayout schedule.promoted).withLayout schedule.target,
      ?_, ?_⟩
  · simpa [Schedule.statements] using
      Locals.Block.compileOpen_append hPromote hCleanup
  · cases ctx
    rfl

theorem Transition.compile
    {ctx : Locals.Ctx} (transition : Transition)
    (hSource : ctx.layout = transition.source) :
    ∃ code finalCtx,
      Locals.Block.compileOpen ctx
          { stmts := transition.schedule.statements } =
        some (code, finalCtx) ∧
      finalCtx = ctx.withLayout transition.target := by
  have hValid :
      transition.schedule.ValidFor ctx.layout transition.live := by
    simpa [hSource] using transition.valid
  simpa [Transition.target] using Schedule.compile hValid

theorem Join.compile
    {ctx : Locals.Ctx} (join : Join)
    (hSource : ctx.layout = join.source) :
    ∃ code finalCtx,
      Locals.Block.compileOpen ctx { stmts := join.statements } =
        some (code, finalCtx) ∧
      finalCtx = ctx.withLayout join.target := by
  have hRetainSource : ctx.layout = join.retain.source := by
    rw [join.retainSource, hSource]
  obtain ⟨retainCode, retainCtx, hRetain, hRetainCtx⟩ :=
    Transition.compile join.retain hRetainSource
  have hOrderSource : retainCtx.layout = join.order.source := by
    rw [hRetainCtx]
    simpa [Locals.Ctx.withLayout] using join.orderSource.symm
  obtain ⟨orderCode, orderCtx, hOrder, hOrderCtx⟩ :=
    Ordering.compile join.order hOrderSource
  refine ⟨retainCode ++ orderCode, orderCtx, ?_, ?_⟩
  · simpa [Join.statements, Schedule.statements, Ordering.statements] using
      Locals.Block.compileOpen_append hRetain hOrder
  · rw [hOrderCtx, join.orderTarget, hRetainCtx]
    cases ctx
    rfl

end AllocationLayoutLowering
end Functions
end EvmCompiler
