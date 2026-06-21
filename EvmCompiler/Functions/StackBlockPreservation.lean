import EvmCompiler.Functions.StackStatementPreservation

/-!
Statement-list composition for dynamically scheduled stack layouts.

Leaf and retain-transition proofs stay in `StackStatementPreservation`; this
module owns only block sequencing and, later, structured control recursion.
-/

namespace EvmCompiler
namespace Functions
namespace StackBlockPreservation

open StackRelation
open StackStatementPreservation

def regularLeafTargetCost : List StackSchedule.Point → Nat
  | [] => 0
  | point :: points =>
      (match point.retain? with
       | some transition => transition.schedule.promotions.length + 2
       | none => 0) + regularLeafTargetCost points

theorem regularEmpty
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hSourceFuel : 1 ≤ sourceFuel)
    (hTargetFuel : 1 ≤ targetFuel)
    (hCtx : CtxCovers sourceCtx targetCtx)
    (hInitial :
      StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (RegularOutcomeRel targetCtx suffix returns)
      (Functions.InteractionSemantics.Block.openRun
        sourceProgram sourceCtx sourceFuel { stmts := [] } source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := [] } target) := by
  cases sourceFuel with
  | zero => omega
  | succ sourceFuel =>
      cases targetFuel with
      | zero => omega
      | succ targetFuel =>
          unfold Functions.InteractionSemantics.Block.openRun
            Functions.Source.Canonical.Block.runOpen
            Expressions.InteractionSemantics.Block.openRun
            Functions.InteractionSemantics.stateModel
          simp only [Functions.Source.Effectful.Control.Block.runOpen,
            Expressions.EffectSemantics.Control.Block.run]
          apply Simulation.Interaction.Rel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact
            { sourceMode := rfl
              targetMode := rfl
              context := hCtx
              state := hInitial }

theorem regularCons
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx)
    (middleCtx finalCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    (stmt : Functions.Stmt) (rest : List Functions.Stmt)
    (headCode tailCode : List Expressions.Stmt)
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hHead :
      Simulation.Interaction.Rel
        (RegularOutcomeRel middleCtx suffix returns)
      (Functions.InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx sourceFuel stmt source)
        (Expressions.InteractionSemantics.Block.openRun
          targetProgram targetFuel { stmts := headCode } target))
    (hTail :
      ∀ {sourceMid : Locals.Source.State}
        {targetMid : Structured.RunState}
        {sourceMidCtx : Functions.Source.Ctx},
        CtxCovers sourceMidCtx middleCtx →
        StateRel middleCtx.layout suffix returns sourceMid targetMid →
        Simulation.Interaction.Rel
          (RegularOutcomeRel finalCtx suffix returns)
          (Functions.InteractionSemantics.Block.openRun
            sourceProgram sourceMidCtx sourceFuel
              { stmts := rest } sourceMid)
          (Expressions.InteractionSemantics.Block.openRun
            targetProgram (targetFuel - headCode.length)
              { stmts := tailCode } targetMid)) :
    Simulation.Interaction.Rel
      (RegularOutcomeRel finalCtx suffix returns)
      (Functions.InteractionSemantics.Block.openRun
        sourceProgram sourceCtx (sourceFuel + 1)
          { stmts := stmt :: rest } source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel
          { stmts := headCode ++ tailCode } target) := by
  rw [Expressions.InteractionSemantics.Block.openRun_append]
  unfold Functions.InteractionSemantics.Block.openRun
    Functions.Source.Canonical.Block.runOpen
    Functions.InteractionSemantics.stateModel
  simp only [Functions.Source.Effectful.Control.Block.runOpen]
  apply Simulation.Interaction.Rel.bind hHead
  intro sourceResult targetResult hResult
  simp only [hResult.sourceMode, hResult.targetMode]
  exact hTail hResult.context hResult.state

theorem regularConsOfPoint
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx)
    (targetCtx finalCtx : Locals.Ctx)
    (transition : AllocationLayout.Transition)
    (sourceFuel targetFuel : Nat)
    (stmt : Functions.Stmt) (rest : List Functions.Stmt)
    (head : Expressions.Stmt) (tailCode : List Expressions.Stmt)
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hPoint :
      RegularPointPreserves targetProgram targetCtx transition
        (Functions.InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx sourceFuel stmt source)
        head targetFuel suffix returns target)
    (hTail :
      ∀ {sourceMid : Locals.Source.State}
        {targetMid : Structured.RunState}
        {sourceMidCtx : Functions.Source.Ctx},
        CtxCovers sourceMidCtx
          (targetCtx.withLayout transition.schedule.target) →
        StateRel transition.schedule.target suffix returns
          sourceMid targetMid →
        Simulation.Interaction.Rel
          (RegularOutcomeRel finalCtx suffix returns)
          (Functions.InteractionSemantics.Block.openRun
            sourceProgram sourceMidCtx sourceFuel
              { stmts := rest } sourceMid)
          (Expressions.InteractionSemantics.Block.openRun
            targetProgram
              (targetFuel - (transition.schedule.promotions.length + 2))
              { stmts := tailCode } targetMid)) :
    ∃ artifact : StackTransitionCompilation.Artifact targetCtx transition,
      Locals.Block.compileOpen targetCtx
          { stmts := transition.schedule.statements } =
        some
          (artifact.promotionCodes.map Expressions.Stmt.code ++
            [Expressions.Stmt.code artifact.cleanup],
           targetCtx.withLayout transition.schedule.target) ∧
      Simulation.Interaction.Rel
        (RegularOutcomeRel finalCtx suffix returns)
        (Functions.InteractionSemantics.Block.openRun
          sourceProgram sourceCtx (sourceFuel + 1)
            { stmts := stmt :: rest } source)
        (Expressions.InteractionSemantics.Block.openRun targetProgram
          targetFuel
          { stmts :=
              (head ::
                (artifact.promotionCodes.map Expressions.Stmt.code ++
                  [Expressions.Stmt.code artifact.cleanup])) ++ tailCode }
          target) := by
  unfold RegularPointPreserves at hPoint
  obtain ⟨artifact, hCompile, hHead⟩ := hPoint
  have hCodeLength :
      artifact.promotionCodes.length =
        transition.schedule.promotions.length :=
    artifact.codes.code_length
  refine ⟨artifact, hCompile, ?_⟩
  apply regularCons sourceProgram targetProgram sourceCtx
    (targetCtx.withLayout transition.schedule.target) finalCtx
    sourceFuel targetFuel stmt rest
    (head ::
      (artifact.promotionCodes.map Expressions.Stmt.code ++
        [Expressions.Stmt.code artifact.cleanup])) tailCode hHead
  intro sourceMid targetMid sourceMidCtx hCtx hState
  have hTail' := hTail hCtx hState
  simpa [hCodeLength] using hTail'

end StackBlockPreservation
end Functions
end EvmCompiler
