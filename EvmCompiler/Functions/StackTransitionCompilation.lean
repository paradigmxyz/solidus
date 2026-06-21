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
    ∃ shuffle code,
      Locals.Ctx.swapRestoreUpTo? (promotion.depth - 1) = some shuffle ∧
      code = shuffle ++ Locals.bindLocals 0 promoted ∧
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
          ⟨code, code ++ Locals.bindLocals 0
              (Locals.Layout.promoteAt
                (promotion.depth - 1) ctx.layout),
            hCode, rfl,
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
          obtain ⟨headShuffle, headCode, hHeadRaw, hHeadEq, hHeadCompile⟩ :=
            Promotion.compileCode hApply
          obtain
              ⟨tailCodes, tailCtx, hTailCodes,
                hTailCompile, hTailCtx⟩ :=
            ih (ctx := ctx.withLayout promoted) hTailRun
          refine
            ⟨headCode :: tailCodes, tailCtx,
              .cons hApply hHeadRaw hHeadEq hTailCodes, ?_, ?_⟩
          · simp [Locals.Block.compileOpen, hHeadCompile, hTailCompile,
              Locals.codeStmt]
          · rw [hTailCtx]
            cases ctx
            rfl

theorem Ordering.compiledOpenRun
    {ctx : Locals.Ctx} (ordering : AllocationLayout.Ordering)
    {suffix : List StackRelation.Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hSource : ctx.layout = ordering.source)
    (hRel :
      StackRelation.StateRel ctx.layout suffix returns source target) :
    ∃ codes : List Structured.Code, ∃ final,
      Locals.Block.compileOpen ctx { stmts := ordering.statements } =
          some (codes.map Expressions.Stmt.code,
            ctx.withLayout ordering.target) ∧
        Structured.InteractionSemantics.Code.openRun codes.flatten target =
          .done (.ok final) ∧
        StackRelation.StateRel ordering.target suffix returns source final := by
  have hRun :
      AllocationLayout.run ctx.layout ordering.promotions =
        some ordering.target := by
    simpa [hSource] using ordering.valid
  obtain ⟨codes, finalCtx, hCodes, hCompile, hFinalCtx⟩ :=
    compilePromotions hRun
  have hRel' :
      StackRelation.StateRel ordering.source suffix returns source target := by
    simpa [hSource] using hRel
  have hCodes' :
      PromotionCodes ordering.source ordering.promotions codes ordering.target := by
    simpa [hSource] using hCodes
  obtain ⟨final, hOpen, hFinalRel⟩ :=
    StackTransitionPreservation.Ordering.openRun hCodes' hRel'
  subst finalCtx
  exact ⟨codes, final, by simpa [Ordering.statements] using hCompile,
    hOpen, hFinalRel⟩

structure OrderingArtifact (ctx : Locals.Ctx)
    (ordering : AllocationLayout.Ordering) where
  promotionCodes : List Structured.Code
  codes :
    PromotionCodes ctx.layout ordering.promotions promotionCodes
      ordering.target
  compileEq :
    Locals.Block.compileOpen ctx { stmts := ordering.statements } =
      some (promotionCodes.map Expressions.Stmt.code,
        ctx.withLayout ordering.target)

theorem Ordering.compileArtifact
    {ctx : Locals.Ctx} (ordering : AllocationLayout.Ordering)
    (hSource : ctx.layout = ordering.source) :
    Nonempty (OrderingArtifact ctx ordering) := by
  have hRun :
      AllocationLayout.run ctx.layout ordering.promotions =
        some ordering.target := by
    simpa [hSource] using ordering.valid
  obtain ⟨codes, finalCtx, hCodes, hCompile, hFinalCtx⟩ :=
    compilePromotions hRun
  subst finalCtx
  exact ⟨{ promotionCodes := codes, codes := hCodes, compileEq := hCompile }⟩

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

theorem Join.compiledOpenRun
    {ctx : Locals.Ctx} (join : AllocationLayout.Join)
    {suffix : List StackRelation.Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hSource : ctx.layout = join.source)
    (hRel :
      StackRelation.StateRel ctx.layout suffix returns source target) :
    ∃ retainArtifact : Artifact ctx join.retain,
      ∃ orderCodes : List Structured.Code, ∃ final,
        Locals.Block.compileOpen ctx { stmts := join.statements } =
          some
            (retainArtifact.promotionCodes.map Expressions.Stmt.code ++
              [Expressions.Stmt.code retainArtifact.cleanup] ++
              orderCodes.map Expressions.Stmt.code,
             ctx.withLayout join.target) ∧
        Structured.InteractionSemantics.Code.openRun
            (retainArtifact.promotionCodes.flatten ++
              retainArtifact.cleanup ++ orderCodes.flatten) target =
          .done (.ok final) ∧
        StackRelation.StateRel join.target suffix returns source final := by
  have hRetainSource : ctx.layout = join.retain.source := by
    rw [join.retainSource, hSource]
  obtain ⟨retainArtifact, middle, hRetainCompile,
      hRetainRun, hMiddleRel⟩ :=
    Transition.compiledOpenRun join.retain hRetainSource hRel
  let orderCtx := ctx.withLayout join.retain.target
  have hOrderSource : orderCtx.layout = join.order.source := by
    simpa [orderCtx, Locals.Ctx.withLayout] using join.orderSource.symm
  obtain ⟨orderCodes, final, hOrderCompile, hOrderRun, hFinalRel⟩ :=
    Ordering.compiledOpenRun (ctx := orderCtx) join.order
      hOrderSource hMiddleRel
  refine ⟨retainArtifact, orderCodes, final, ?_, ?_, ?_⟩
  · have hAppend :=
      Locals.Block.compileOpen_append hRetainCompile hOrderCompile
    simpa [Join.statements, Schedule.statements, Ordering.statements,
      orderCtx, join.orderTarget] using hAppend
  · rw [Structured.InteractionSemantics.Code.openRun_append, hRetainRun]
    exact hOrderRun
  · simpa [join.orderTarget] using hFinalRel

structure JoinArtifact (ctx : Locals.Ctx)
    (join : AllocationLayout.Join) where
  retainArtifact : Artifact ctx join.retain
  orderArtifact :
    OrderingArtifact (ctx.withLayout join.retain.target) join.order
  compileEq :
    Locals.Block.compileOpen ctx { stmts := join.statements } =
      some
        (retainArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code retainArtifact.cleanup] ++
          orderArtifact.promotionCodes.map Expressions.Stmt.code,
         ctx.withLayout join.target)

theorem Join.compileArtifact
    {ctx : Locals.Ctx} (join : AllocationLayout.Join)
    (hSource : ctx.layout = join.source) :
    Nonempty (JoinArtifact ctx join) := by
  have hRetainSource : ctx.layout = join.retain.source := by
    rw [join.retainSource, hSource]
  obtain ⟨retainArtifact⟩ :=
    Transition.compileArtifact join.retain hRetainSource
  let orderCtx := ctx.withLayout join.retain.target
  have hOrderSource : orderCtx.layout = join.order.source := by
    simpa [orderCtx, Locals.Ctx.withLayout] using join.orderSource.symm
  obtain ⟨orderArtifact⟩ :=
    Ordering.compileArtifact (ctx := orderCtx) join.order hOrderSource
  refine ⟨{ retainArtifact, orderArtifact, compileEq := ?_ }⟩
  have hAppend :=
    Locals.Block.compileOpen_append retainArtifact.compileEq
      orderArtifact.compileEq
  simpa [Join.statements, Schedule.statements, Ordering.statements,
    orderCtx, join.orderTarget] using hAppend

theorem PromotionCodes.openBlockRun
    (program : Expressions.Program)
    {layout finalLayout : Locals.Layout}
    {promotions : List Promotion} {codes : List Structured.Code}
    {suffix : List StackRelation.Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hCodes : PromotionCodes layout promotions codes finalLayout)
    (hRel : StackRelation.StateRel layout suffix returns source target)
    (fuel : Nat) (hFuel : codes.length < fuel) :
    ∃ final,
      Expressions.InteractionSemantics.Block.openRun program
          fuel
          { stmts := codes.map Expressions.Stmt.code } target =
        .done (.ok (Structured.Outcome.regular final)) ∧
      StackRelation.StateRel finalLayout suffix returns source final := by
  induction hCodes generalizing target fuel with
  | nil layout =>
      refine ⟨target, ?_, hRel⟩
      cases fuel with
      | zero => simp at hFuel
      | succ fuel =>
          simp only [List.map_nil]
          rw [Expressions.InteractionSemantics.Block.openRun_nil]
          rfl
  | @cons layout promoted finalLayout promotion rest shuffle head tail
      hApply hCode hHead hTail ih =>
      obtain ⟨middle, hHeadRun, hMiddleRel⟩ :=
        StackTransitionPreservation.Promotion.openRunWithBind
          hApply hCode hRel
      have hHeadRun' :
          Structured.InteractionSemantics.Code.openRun head target =
            .done (.ok middle) := by
        simpa [hHead] using hHeadRun
      obtain ⟨final, hTailRun, hFinalRel⟩ :=
        ih hMiddleRel (fuel := fuel - 1) (by simp at hFuel ⊢; omega)
      refine ⟨final, ?_, hFinalRel⟩
      change
        Expressions.InteractionSemantics.Block.openRun program
            fuel
            { stmts := [.code head] ++
                tail.map Expressions.Stmt.code } target =
          .done (.ok (Structured.Outcome.regular final))
      rw [Expressions.InteractionSemantics.Block.openRun_append]
      have hHeadBlock :=
        Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code_done
          program fuel head target middle
          (by simp at hFuel; omega) hHeadRun'
      rw [hHeadBlock, Simulation.Interaction.bind_done_ok]
      simpa using hTailRun

theorem OrderingArtifact.blockOpenRun
    (program : Expressions.Program) {ctx : Locals.Ctx}
    {ordering : AllocationLayout.Ordering}
    (artifact : OrderingArtifact ctx ordering)
    {suffix : List StackRelation.Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (fuel : Nat) (hFuel : artifact.promotionCodes.length < fuel)
    (hRel :
      StackRelation.StateRel ctx.layout suffix returns source target) :
    ∃ final,
      Expressions.InteractionSemantics.Block.openRun program fuel
          { stmts :=
              artifact.promotionCodes.map Expressions.Stmt.code } target =
        .done (.ok (Structured.Outcome.regular final)) ∧
      StackRelation.StateRel ordering.target suffix returns source final := by
  exact PromotionCodes.openBlockRun program artifact.codes hRel fuel hFuel

theorem OrderingArtifact.thenBlock
    (program : Expressions.Program) {ctx : Locals.Ctx}
    {ordering : AllocationLayout.Ordering}
    (artifact : OrderingArtifact ctx ordering)
    {α : Type}
    {resultRel :
      Except EVMException α → Except EVMException Structured.Outcome → Prop}
    {sourceRun : Simulation.Interaction EVMException α}
    {body : List Expressions.Stmt}
    {suffix : List StackRelation.Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (fuel : Nat) (hFuel : artifact.promotionCodes.length < fuel)
    (hInitial :
      StackRelation.StateRel ctx.layout suffix returns source target)
    (hBody :
      ∀ {orderedTarget : Structured.RunState},
        StackRelation.StateRel ordering.target suffix returns
            source orderedTarget →
        Simulation.Interaction.Rel resultRel sourceRun
          (Expressions.InteractionSemantics.Block.openRun program
            (fuel - artifact.promotionCodes.length)
            { stmts := body } orderedTarget)) :
    Simulation.Interaction.Rel resultRel sourceRun
      (Expressions.InteractionSemantics.Block.openRun program fuel
        { stmts :=
            artifact.promotionCodes.map Expressions.Stmt.code ++ body }
        target) := by
  obtain ⟨orderedTarget, hOrderRun, hOrderedRel⟩ :=
    artifact.blockOpenRun program fuel hFuel hInitial
  rw [Expressions.InteractionSemantics.Block.openRun_append,
    hOrderRun, Simulation.Interaction.bind_done_ok]
  simpa using hBody hOrderedRel

theorem Artifact.blockOpenRun
    (program : Expressions.Program) {ctx : Locals.Ctx}
    {transition : Transition} (artifact : Artifact ctx transition)
    {suffix : List StackRelation.Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (fuel : Nat)
    (hFuel : artifact.promotionCodes.length + 1 < fuel)
    (hRel :
      StackRelation.StateRel ctx.layout suffix returns source target) :
    ∃ final,
      Expressions.InteractionSemantics.Block.openRun program
          fuel
          { stmts :=
              artifact.promotionCodes.map Expressions.Stmt.code ++
                [Expressions.Stmt.code artifact.cleanup] }
          target =
        .done (.ok (Structured.Outcome.regular final)) ∧
      StackRelation.StateRel transition.schedule.target suffix returns
        source final := by
  obtain ⟨middle, hPromotionRun, hMiddleRel⟩ :=
    PromotionCodes.openBlockRun program artifact.codes hRel
      fuel (by omega)
  obtain ⟨final, hCleanupRun, hFinalRel⟩ :=
    StackTransitionPreservation.Cleanup.openRun
      rfl transition.valid.2.2 artifact.cleanupEq hMiddleRel
  refine ⟨final, ?_, hFinalRel⟩
  rw [Expressions.InteractionSemantics.Block.openRun_append,
    hPromotionRun, Simulation.Interaction.bind_done_ok]
  have hCleanupBlock :=
    Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code_done
      program (fuel - artifact.promotionCodes.length)
        artifact.cleanup middle final (by omega) hCleanupRun
  simpa using hCleanupBlock

theorem JoinArtifact.blockOpenRun
    (program : Expressions.Program) {ctx : Locals.Ctx}
    {join : AllocationLayout.Join}
    (artifact : JoinArtifact ctx join)
    {suffix : List StackRelation.Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (fuel : Nat)
    (hFuel :
      artifact.retainArtifact.promotionCodes.length + 1 +
          artifact.orderArtifact.promotionCodes.length < fuel)
    (hRel :
      StackRelation.StateRel ctx.layout suffix returns source target) :
    ∃ final,
      Expressions.InteractionSemantics.Block.openRun program fuel
          { stmts :=
              artifact.retainArtifact.promotionCodes.map
                  Expressions.Stmt.code ++
                [Expressions.Stmt.code artifact.retainArtifact.cleanup] ++
                artifact.orderArtifact.promotionCodes.map
                  Expressions.Stmt.code }
          target =
        .done (.ok (Structured.Outcome.regular final)) ∧
      StackRelation.StateRel join.target suffix returns source final := by
  let retainLength := artifact.retainArtifact.promotionCodes.length + 1
  obtain ⟨middle, hRetainRun, hMiddleRel⟩ :=
    artifact.retainArtifact.blockOpenRun program fuel (by omega) hRel
  have hMiddleRel' :
      StackRelation.StateRel
        (ctx.withLayout join.retain.target).layout suffix returns source
        middle := by
    simpa [Locals.Ctx.withLayout] using hMiddleRel
  obtain ⟨final, hOrderRun, hFinalRel⟩ :=
    artifact.orderArtifact.blockOpenRun program (fuel - retainLength)
      (by simp [retainLength] at hFuel ⊢; omega) hMiddleRel'
  refine ⟨final, ?_, ?_⟩
  · rw [Expressions.InteractionSemantics.Block.openRun_append,
      hRetainRun, Simulation.Interaction.bind_done_ok]
    simpa [retainLength, List.length_map] using hOrderRun
  · simpa [join.orderTarget] using hFinalRel

theorem JoinArtifact.thenBlock
    (program : Expressions.Program) {ctx : Locals.Ctx}
    {join : AllocationLayout.Join}
    (artifact : JoinArtifact ctx join)
    {α : Type}
    {resultRel :
      Except EVMException α → Except EVMException Structured.Outcome → Prop}
    {sourceRun : Simulation.Interaction EVMException α}
    {body : List Expressions.Stmt}
    {suffix : List StackRelation.Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (fuel : Nat)
    (hFuel :
      artifact.retainArtifact.promotionCodes.length + 1 +
          artifact.orderArtifact.promotionCodes.length < fuel)
    (hInitial :
      StackRelation.StateRel ctx.layout suffix returns source target)
    (hBody :
      ∀ {joinedTarget : Structured.RunState},
        StackRelation.StateRel join.target suffix returns source joinedTarget →
        Simulation.Interaction.Rel resultRel sourceRun
          (Expressions.InteractionSemantics.Block.openRun program
            (fuel -
              (artifact.retainArtifact.promotionCodes.length + 1 +
                artifact.orderArtifact.promotionCodes.length))
            { stmts := body } joinedTarget)) :
    Simulation.Interaction.Rel resultRel sourceRun
      (Expressions.InteractionSemantics.Block.openRun program fuel
        { stmts :=
            artifact.retainArtifact.promotionCodes.map
                Expressions.Stmt.code ++
              [Expressions.Stmt.code artifact.retainArtifact.cleanup] ++
              artifact.orderArtifact.promotionCodes.map Expressions.Stmt.code ++
              body }
        target) := by
  let joinLength :=
    artifact.retainArtifact.promotionCodes.length + 1 +
      artifact.orderArtifact.promotionCodes.length
  obtain ⟨joinedTarget, hJoinRun, hJoinedRel⟩ :=
    artifact.blockOpenRun program fuel hFuel hInitial
  rw [show
      artifact.retainArtifact.promotionCodes.map Expressions.Stmt.code ++
            [Expressions.Stmt.code artifact.retainArtifact.cleanup] ++
            artifact.orderArtifact.promotionCodes.map Expressions.Stmt.code ++
            body =
        (artifact.retainArtifact.promotionCodes.map Expressions.Stmt.code ++
            [Expressions.Stmt.code artifact.retainArtifact.cleanup] ++
            artifact.orderArtifact.promotionCodes.map Expressions.Stmt.code) ++
          body by simp [List.append_assoc]]
  rw [Expressions.InteractionSemantics.Block.openRun_append,
    hJoinRun, Simulation.Interaction.bind_done_ok]
  have hLength :
      (artifact.retainArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code artifact.retainArtifact.cleanup] ++
          artifact.orderArtifact.promotionCodes.map Expressions.Stmt.code).length =
        joinLength := by
    simp only [List.length_append, List.length_map, List.length_singleton]
    simp [joinLength]
  rw [hLength]
  simpa [joinLength] using hBody hJoinedRel

theorem Transition.compiledBlockOpenRun
    (program : Expressions.Program) {ctx : Locals.Ctx}
    (transition : Transition)
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
        Expressions.InteractionSemantics.Block.openRun program
            (artifact.promotionCodes.length + 2)
            { stmts :=
                artifact.promotionCodes.map Expressions.Stmt.code ++
                  [Expressions.Stmt.code artifact.cleanup] }
            target =
          .done (.ok (Structured.Outcome.regular final)) ∧
        StackRelation.StateRel transition.schedule.target suffix returns
          source final := by
  obtain ⟨artifact⟩ := Transition.compileArtifact transition hSource
  obtain ⟨final, hRun, hFinalRel⟩ :=
    artifact.blockOpenRun program (artifact.promotionCodes.length + 2)
      (by omega) hRel
  exact ⟨artifact, final, artifact.compileEq, hRun, hFinalRel⟩

end StackTransitionCompilation
end Functions
end EvmCompiler
