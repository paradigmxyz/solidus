import EvmCompiler.Functions.AllocationLayoutLowering
import EvmCompiler.Functions.StackTransitionPreservation

/-!
The ordinary Locals compiler constructs exactly the raw code relation consumed
by dynamic stack-transition preservation.
-/

namespace EvmCompiler
namespace Functions
namespace StackTransitionCompilation

open AllocationLayout
open StackTransitionPreservation

theorem Promotion.compileCode
    {ctx : Locals.Ctx} {promotion : Promotion}
    {promoted : Locals.Layout}
    (hApply : promotion.apply? ctx.layout = some promoted) :
    ∃ code,
      Locals.Ctx.swapRestoreUpTo? (promotion.depth - 1) = some code ∧
      Locals.Stmt.compile ctx (.promoteName promotion.name) =
        some (Locals.codeStmt code, ctx.withLayout promoted) := by
  unfold Promotion.apply? at hApply
  cases hDepth :
      Locals.Layout.lookupDepth? promotion.name ctx.layout with
  | none => simp [hDepth] at hApply
  | some depth =>
      by_cases hAllowed : depth = promotion.depth ∧ depth ≤ 17
      · simp [hDepth, hAllowed] at hApply
        have hPromoted := hApply.2
        subst promoted
        have hIndex : promotion.depth - 1 ≤ 16 := by omega
        have hPromotionBound : promotion.depth ≤ 17 := by omega
        obtain ⟨code, hCode⟩ :=
          Locals.Ctx.exists_swapRestoreUpTo?_of_le hIndex
        have hPromote :
            ctx.promoteNameStackOnly? promotion.name =
              some
                (code,
                  Locals.Layout.promoteAt
                    (promotion.depth - 1) ctx.layout) := by
          unfold Locals.Ctx.promoteNameStackOnly?
          simp [hDepth, hAllowed.1, hIndex, hPromotionBound, hCode]
        exact
          ⟨code, hCode,
            by simp [Locals.Stmt.compile, hPromote]⟩
      · simp [hDepth, hAllowed] at hApply

theorem compilePromotions
    {ctx : Locals.Ctx} {promotions : List Promotion}
    {finalLayout : Locals.Layout}
    (hRun : AllocationLayout.run ctx.layout promotions = some finalLayout) :
    ∃ codes finalCtx,
      PromotionCodes ctx.layout promotions codes finalLayout ∧
      Locals.Block.compileOpen ctx
          { stmts := promotions.map fun promotion =>
              Locals.Stmt.promoteName promotion.name } =
        some (codes.map Expressions.Stmt.code, finalCtx) ∧
      finalCtx = ctx.withLayout finalLayout := by
  induction promotions generalizing ctx with
  | nil =>
      simp [AllocationLayout.run] at hRun
      subst finalLayout
      refine ⟨[], ctx, .nil ctx.layout, ?_, ?_⟩
      · simp [Locals.Block.compileOpen]
      cases ctx
      rfl
  | cons promotion rest ih =>
      unfold AllocationLayout.run at hRun
      cases hApply : promotion.apply? ctx.layout with
      | none => simp [hApply] at hRun
      | some promoted =>
          have hTailRun :
              AllocationLayout.run promoted rest = some finalLayout := by
            simpa [hApply] using hRun
          obtain ⟨headCode, hHeadRaw, hHeadCompile⟩ :=
            Promotion.compileCode hApply
          obtain
              ⟨tailCodes, tailCtx, hTailCodes,
                hTailCompile, hTailCtx⟩ :=
            ih (ctx := ctx.withLayout promoted) hTailRun
          refine
            ⟨headCode :: tailCodes, tailCtx,
              .cons hApply hHeadRaw hTailCodes, ?_, ?_⟩
          · simp [Locals.Block.compileOpen, hHeadCompile, hTailCompile,
              Locals.codeStmt]
          · rw [hTailCtx]
            cases ctx
            rfl

structure Artifact (ctx : Locals.Ctx) (transition : Transition) where
  promotionCodes : List Structured.Code
  cleanup : Structured.Code
  codes :
    PromotionCodes ctx.layout transition.schedule.promotions
      promotionCodes transition.schedule.promoted
  cleanupEq :
    (ctx.withLayout transition.schedule.promoted).cleanupTo?
        transition.schedule.target.length = some cleanup
  compileEq :
    Locals.Block.compileOpen ctx
        { stmts := transition.schedule.statements } =
      some
        (promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code cleanup],
         ctx.withLayout transition.schedule.target)

theorem Transition.compileArtifact
    {ctx : Locals.Ctx} (transition : Transition)
    (hSource : ctx.layout = transition.source) :
    Nonempty (Artifact ctx transition) := by
  have hValid :
      transition.schedule.ValidFor ctx.layout transition.live := by
    simpa [hSource] using transition.valid
  obtain
      ⟨promotionCodes, promotionFinal, hCodes,
        hPromotionsCompile, hPromotionFinal⟩ :=
    compilePromotions hValid.1
  subst promotionFinal
  let cleanup :=
    List.replicate
      (transition.schedule.promoted.length -
        transition.schedule.target.length)
      (Structured.BasicInstr.op .pop)
  have hTargetLength :
      transition.schedule.target.length ≤
        transition.schedule.promoted.length := by
    have hLengths := congrArg List.length hValid.2.2
    simp only [List.length_drop] at hLengths
    omega
  have hCleanup :
      (ctx.withLayout transition.schedule.promoted).cleanupTo?
          transition.schedule.target.length = some cleanup := by
    unfold Locals.Ctx.cleanupTo?
    simp [Locals.Ctx.withLayout, hTargetLength, cleanup]
  have hCleanupStmt :
      Locals.Block.compileOpen
          (ctx.withLayout transition.schedule.promoted)
          { stmts :=
              [Locals.Stmt.cleanupTo transition.schedule.target] } =
        some
          ([Expressions.Stmt.code cleanup],
            ctx.withLayout transition.schedule.target) := by
    have hStmt :
        Locals.Stmt.compile
            (ctx.withLayout transition.schedule.promoted)
            (.cleanupTo transition.schedule.target) =
          some
            ([Expressions.Stmt.code cleanup],
              ctx.withLayout transition.schedule.target) := by
      simp only [Locals.Stmt.compile]
      rw [if_pos (by
        simpa [Locals.Ctx.withLayout] using hValid.2.2)]
      rw [hCleanup]
      cases ctx
      rfl
    simpa [Locals.Block.compileOpen, hStmt]
  have hWhole :=
    Locals.Block.compileOpen_append hPromotionsCompile hCleanupStmt
  refine
    ⟨{ promotionCodes
       cleanup
       codes := hCodes
       cleanupEq := hCleanup
       compileEq := ?_ }⟩
  simpa [Schedule.statements] using hWhole

theorem Transition.compiledOpenRun
    {ctx : Locals.Ctx} (transition : Transition)
    {suffix : List StackRelation.Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hSource : ctx.layout = transition.source)
    (hRel :
      StackRelation.StateRel ctx.layout suffix returns source target) :
    ∃ artifact : Artifact ctx transition,
      ∃ final,
        Locals.Block.compileOpen ctx
            { stmts := transition.schedule.statements } =
          some
            (artifact.promotionCodes.map Expressions.Stmt.code ++
              [Expressions.Stmt.code artifact.cleanup],
             ctx.withLayout transition.schedule.target) ∧
        Structured.InteractionSemantics.Code.openRun
            (artifact.promotionCodes.flatten ++ artifact.cleanup) target =
          .done (.ok final) ∧
        StackRelation.StateRel transition.schedule.target suffix returns
          source final := by
  obtain ⟨artifact⟩ := Transition.compileArtifact transition hSource
  obtain ⟨final, hRun, hFinalRel⟩ :=
    StackTransitionPreservation.Schedule.openRun
      transition.valid.2.2 artifact.codes rfl artifact.cleanupEq hRel
  exact
    ⟨artifact, final, artifact.compileEq, hRun, hFinalRel⟩

end StackTransitionCompilation
end Functions
end EvmCompiler
