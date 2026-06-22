import EvmCompiler.Functions.StackStatementPreservation
import EvmCompiler.Functions.StackCallPreservation

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

variable (returnNames : List Name)

def regularLeafTargetCost : List StackSchedule.Point → Nat
  | [] => 0
  | point :: points =>
      (match point.order? with
       | some order => order.promotions.length
       | none => 0) +
      (match point.retain? with
       | some transition => transition.schedule.discards.length + 2
       | none => 0) + regularLeafTargetCost points

def RegularListPreserves
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targetCtx finalCtx : Locals.Ctx)
    (stmts : List Functions.Stmt)
    (points : List StackSchedule.Point)
    (finalLayout : Locals.Layout)
    (code : List Expressions.Stmt) : Prop :=
  finalCtx.layout = finalLayout ∧
    code.length = regularLeafTargetCost points ∧
    ∀ (sourceCtx : Functions.Source.Ctx)
      {suffix : List Word} {returns : List Structured.ReturnDest}
      {source : Locals.Source.State} {target : Structured.RunState},
      CtxCovers sourceCtx targetCtx →
      StateRel targetCtx.layout suffix returns source target →
      Simulation.Interaction.Rel
        (RegularOutcomeRel finalCtx suffix returns)
        (Functions.InteractionSemantics.Block.openRun
          sourceProgram sourceCtx (stmts.length + 1) { stmts } source)
        (Expressions.InteractionSemantics.Block.openRun targetProgram
          (regularLeafTargetCost points + 1) { stmts := code } target)

def OpenListPreserves
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targetCtx finalCtx : Locals.Ctx)
    (stmts : List Functions.Stmt)
    (finalLayout : Locals.Layout)
    (code : List Expressions.Stmt) : Prop :=
  finalCtx.layout = finalLayout ∧
    ∀ (sourceCtx : Functions.Source.Ctx)
      {suffix : List Word} {returns : List Structured.ReturnDest}
      {source : Locals.Source.State} {target : Structured.RunState},
      CtxCovers sourceCtx targetCtx →
      StateRel targetCtx.layout suffix returns source target →
      Simulation.Interaction.Rel
        (OpenOutcomeRel finalCtx suffix returns)
        (Functions.InteractionSemantics.Block.openRun
          sourceProgram sourceCtx (stmts.length + 1) { stmts } source)
        (Expressions.InteractionSemantics.Block.openRun targetProgram
          (code.length + 1) { stmts := code } target)

def BreakListPreserves
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targetCtx finalCtx : Locals.Ctx)
    (stmts : List Functions.Stmt)
    (targetLayout : Locals.Layout)
    (code : List Expressions.Stmt) : Prop :=
  finalCtx.layout = targetLayout ∧
    ∀ (sourceCtx : Functions.Source.Ctx)
      {suffix : List Word} {returns : List Structured.ReturnDest}
      {source : Locals.Source.State} {target : Structured.RunState},
      BreakCtxCovers sourceCtx targetCtx targetLayout →
      StateRel targetCtx.layout suffix returns source target →
      Simulation.Interaction.Rel
        (OpenOutcomeRel finalCtx suffix returns)
        (Functions.InteractionSemantics.Block.openRun
          sourceProgram sourceCtx (stmts.length + 1) { stmts } source)
        (Expressions.InteractionSemantics.Block.openRun targetProgram
          (code.length + 1) { stmts := code } target)

def ContinueListPreserves
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targetCtx finalCtx : Locals.Ctx)
    (stmts : List Functions.Stmt)
    (targetLayout : Locals.Layout)
    (code : List Expressions.Stmt) : Prop :=
  finalCtx.layout = targetLayout ∧
    ∀ (sourceCtx : Functions.Source.Ctx)
      {suffix : List Word} {returns : List Structured.ReturnDest}
      {source : Locals.Source.State} {target : Structured.RunState},
      ContinueCtxCovers sourceCtx targetCtx targetLayout →
      StateRel targetCtx.layout suffix returns source target →
      Simulation.Interaction.Rel
        (OpenOutcomeRel finalCtx suffix returns)
        (Functions.InteractionSemantics.Block.openRun
          sourceProgram sourceCtx (stmts.length + 1) { stmts } source)
        (Expressions.InteractionSemantics.Block.openRun targetProgram
          (code.length + 1) { stmts := code } target)

def ScheduledListPreserves
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (targetCtx finalCtx : Locals.Ctx)
    (stmts : List Functions.Stmt)
    (finalLayout : Locals.Layout)
    (code : List Expressions.Stmt) : Prop :=
  finalCtx.layout = finalLayout ∧
    ∀ (sourceCtx : Functions.Source.Ctx)
      {suffix : List Word} {returns : List Structured.ReturnDest}
      {source : Locals.Source.State} {target : Structured.RunState},
      ControlCtxCovers sourceCtx targetCtx targets →
      StateRel targetCtx.layout suffix returns source target →
      Simulation.Interaction.Rel
        (OpenOutcomeRel finalCtx suffix returns)
        (Functions.InteractionSemantics.Block.openRun
          sourceProgram sourceCtx (stmts.length + 1) { stmts } source)
        (Expressions.InteractionSemantics.Block.openRun targetProgram
          (code.length + 1) { stmts := code } target)

def ControlScheduledListPreserves
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (targetCtx finalCtx : Locals.Ctx)
    (stmts : List Functions.Stmt)
    (finalLayout : Locals.Layout)
    (code : List Expressions.Stmt) : Prop :=
  finalCtx.layout = finalLayout ∧
    ∀ (sourceCtx : Functions.Source.Ctx) (sourceFuel targetFuel : Nat)
      {suffix : List Word} {returns : List Structured.ReturnDest}
      {source : Locals.Source.State} {target : Structured.RunState},
      Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel code →
      RuntimeCtxCovers sourceCtx targetCtx targets returnNames returns →
      StateRel targetCtx.layout suffix returns source target →
      Simulation.Interaction.ForwardRel FuelTruncated
        (ControlOpenOutcomeRel targets returnNames finalCtx suffix returns)
        (Functions.InteractionSemantics.Block.openRun
          sourceProgram sourceCtx sourceFuel { stmts } source)
        (Expressions.InteractionSemantics.Block.openRun targetProgram
          targetFuel { stmts := code } target)

/-- Exact-source-fuel statement-list preservation. Recursive call closure uses
this interface internally; the public all-fuel theorem remains
`ControlScheduledListPreserves`. -/
def ControlScheduledListPreservesAt
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (targetCtx finalCtx : Locals.Ctx)
    (stmts : List Functions.Stmt)
    (finalLayout : Locals.Layout)
    (code : List Expressions.Stmt)
    (sourceFuel : Nat) : Prop :=
  finalCtx.layout = finalLayout ∧
    ∀ (sourceCtx : Functions.Source.Ctx) (targetFuel : Nat)
      {suffix : List Word} {returns : List Structured.ReturnDest}
      {source : Locals.Source.State} {target : Structured.RunState},
      Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel code →
      RuntimeCtxCovers sourceCtx targetCtx targets returnNames returns →
      StateRel targetCtx.layout suffix returns source target →
      Simulation.Interaction.ForwardRel FuelTruncated
        (ControlOpenOutcomeRel targets returnNames finalCtx suffix returns)
        (Functions.InteractionSemantics.Block.openRun
          sourceProgram sourceCtx sourceFuel { stmts } source)
        (Expressions.InteractionSemantics.Block.openRun targetProgram
          targetFuel { stmts := code } target)

theorem ControlScheduledListPreserves.at
    {sourceProgram : Functions.Program}
    {targetProgram : Expressions.Program}
    {targets : StackSchedule.ControlTargets}
    {returnNames : List Name}
    {targetCtx finalCtx : Locals.Ctx}
    {stmts : List Functions.Stmt}
    {finalLayout : Locals.Layout}
    {code : List Expressions.Stmt}
    (h : ControlScheduledListPreserves sourceProgram targetProgram targets
      returnNames targetCtx finalCtx stmts finalLayout code)
    (sourceFuel : Nat) :
    ControlScheduledListPreservesAt sourceProgram targetProgram targets
      returnNames targetCtx finalCtx stmts finalLayout code sourceFuel := by
  refine ⟨h.1, ?_⟩
  intro sourceCtx targetFuel suffix returns source target hFuel hCtx hInitial
  exact h.2 sourceCtx sourceFuel targetFuel hFuel hCtx hInitial

theorem ControlScheduledListPreserves.of_at
    {sourceProgram : Functions.Program}
    {targetProgram : Expressions.Program}
    {targets : StackSchedule.ControlTargets}
    {returnNames : List Name}
    {targetCtx finalCtx : Locals.Ctx}
    {stmts : List Functions.Stmt}
    {finalLayout : Locals.Layout}
    {code : List Expressions.Stmt}
    (hLayout : finalCtx.layout = finalLayout)
    (hAt : ∀ sourceFuel,
      ControlScheduledListPreservesAt sourceProgram targetProgram targets
        returnNames targetCtx finalCtx stmts finalLayout code sourceFuel) :
    ControlScheduledListPreserves sourceProgram targetProgram targets
      returnNames targetCtx finalCtx stmts finalLayout code := by
  refine ⟨hLayout, ?_⟩
  intro sourceCtx sourceFuel
  exact (hAt sourceFuel).2 sourceCtx

theorem controlOrdering
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (targetCtx finalCtx : Locals.Ctx)
    (stmt : Functions.Stmt) (bodyCode : List Expressions.Stmt)
    (order : AllocationLayout.Ordering)
    (hSource : targetCtx.layout = order.source)
    (hBody :
      ControlPointPreserves sourceProgram targetProgram targets returnNames
        (targetCtx.withLayout order.target) finalCtx stmt bodyCode) :
    ∃ artifact :
        StackTransitionCompilation.OrderingArtifact targetCtx order,
      Locals.Block.compileOpen targetCtx { stmts := order.statements } =
          some
            (artifact.promotionCodes.map Expressions.Stmt.code,
             targetCtx.withLayout order.target) ∧
        ControlPointPreserves sourceProgram targetProgram targets returnNames targetCtx
          finalCtx stmt
          (artifact.promotionCodes.map Expressions.Stmt.code ++ bodyCode) := by
  obtain ⟨artifact⟩ :=
    StackTransitionCompilation.Ordering.compileArtifact order hSource
  refine ⟨artifact, artifact.compileEq, ?_⟩
  unfold ControlPointPreserves at hBody ⊢
  intro sourceCtx sourceFuel targetFuel suffix returns source target hFuel
    hCtx hInitial
  have hLength := Expressions.TargetFuel.Covers.length_lt hFuel
  have hBodyFuel := Expressions.TargetFuel.Covers.tail_after_append hFuel
  apply artifact.thenBlockForward targetProgram targetFuel
      (by
        simp only [List.length_append, List.length_map] at hLength
        omega) hInitial
  intro orderedTarget hOrdered
  apply hBody sourceCtx sourceFuel
    (targetFuel - artifact.promotionCodes.length)
  · simpa using hBodyFuel
  · exact hCtx.afterOrdering order hSource
  · exact hOrdered

theorem controlOrderingAt
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (targetCtx finalCtx : Locals.Ctx)
    (stmt : Functions.Stmt) (bodyCode : List Expressions.Stmt)
    (order : AllocationLayout.Ordering)
    (sourceFuel : Nat)
    (hSource : targetCtx.layout = order.source)
    (hBody :
      ControlPointPreservesAt sourceProgram targetProgram targets returnNames
        (targetCtx.withLayout order.target) finalCtx stmt bodyCode
        sourceFuel) :
    ∃ artifact :
        StackTransitionCompilation.OrderingArtifact targetCtx order,
      Locals.Block.compileOpen targetCtx { stmts := order.statements } =
          some
            (artifact.promotionCodes.map Expressions.Stmt.code,
             targetCtx.withLayout order.target) ∧
        ControlPointPreservesAt sourceProgram targetProgram targets returnNames
          targetCtx finalCtx stmt
          (artifact.promotionCodes.map Expressions.Stmt.code ++ bodyCode)
          sourceFuel := by
  obtain ⟨artifact⟩ :=
    StackTransitionCompilation.Ordering.compileArtifact order hSource
  refine ⟨artifact, artifact.compileEq, ?_⟩
  intro sourceCtx targetFuel suffix returns source target hFuel hCtx hInitial
  have hLength := Expressions.TargetFuel.Covers.length_lt hFuel
  have hBodyFuel := Expressions.TargetFuel.Covers.tail_after_append hFuel
  apply artifact.thenBlockForward targetProgram targetFuel
      (by
        simp only [List.length_append, List.length_map] at hLength
        omega) hInitial
  intro orderedTarget hOrdered
  apply hBody sourceCtx (targetFuel - artifact.promotionCodes.length)
  · simpa using hBodyFuel
  · exact hCtx.afterOrdering order hSource
  · exact hOrdered

theorem controlNil
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (targetCtx : Locals.Ctx) :
    ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
      targetCtx targetCtx [] targetCtx.layout [] := by
  refine ⟨rfl, ?_⟩
  intro sourceCtx sourceFuel targetFuel suffix returns source target hFuel
    hCtx hInitial
  cases sourceFuel with
  | zero =>
      unfold Functions.InteractionSemantics.Block.openRun
        Functions.InteractionSemantics.stateModel
      simp only [Functions.Source.Effectful.Control.Block.runOpen]
      exact Simulation.Interaction.ForwardRel.truncated rfl
  | succ sourceFuel =>
      have hTargetFuel : 0 < targetFuel :=
        Expressions.TargetFuel.Covers.length_lt hFuel
      cases targetFuel with
      | zero => omega
      | succ targetFuel =>
          unfold Functions.InteractionSemantics.Block.openRun
            Functions.InteractionSemantics.stateModel
            Expressions.InteractionSemantics.Block.openRun
          simp only [Functions.Source.Effectful.Control.Block.runOpen,
            Expressions.EffectSemantics.Control.Block.run]
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact .regular hCtx hInitial

theorem controlNilAt
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (targetCtx : Locals.Ctx)
    (sourceFuel : Nat) :
    ControlScheduledListPreservesAt sourceProgram targetProgram targets
      returnNames targetCtx targetCtx [] targetCtx.layout [] sourceFuel :=
  (controlNil returnNames sourceProgram targetProgram targets targetCtx).at
    sourceFuel

theorem controlCons
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (targetCtx middleCtx finalCtx : Locals.Ctx)
    (stmt : Functions.Stmt) (rest : List Functions.Stmt)
    (headCode tailCode code : List Expressions.Stmt)
    (finalLayout : Locals.Layout)
    (hHead :
      ControlPointPreserves sourceProgram targetProgram targets returnNames targetCtx
        middleCtx stmt headCode)
    (hTail :
      ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
        middleCtx finalCtx rest finalLayout tailCode)
    (hCode : code = headCode ++ tailCode) :
    ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
      targetCtx finalCtx (stmt :: rest) finalLayout code := by
  rcases hTail with ⟨hFinal, hTailForward⟩
  subst code
  refine ⟨hFinal, ?_⟩
  intro sourceCtx sourceFuel targetFuel suffix returns source target
    hFuel hCtx hInitial
  cases sourceFuel with
  | zero =>
      unfold Functions.InteractionSemantics.Block.openRun
        Functions.InteractionSemantics.stateModel
      simp only [Functions.Source.Effectful.Control.Block.runOpen]
      exact Simulation.Interaction.ForwardRel.truncated rfl
  | succ sourceFuel =>
      have hFuel' :
          Expressions.TargetFuel.Covers targetProgram (sourceFuel + 1)
            targetFuel (headCode ++ tailCode) := by
        simpa [Nat.succ_eq_add_one] using hFuel
      have hHeadFuel :=
        Expressions.TargetFuel.Covers.head_of_succ_append hFuel'
      have hHeadRun :=
        hHead sourceCtx sourceFuel targetFuel hHeadFuel hCtx hInitial
      rw [Expressions.InteractionSemantics.Block.openRun_append]
      rw [Functions.InteractionSemantics.Block.openRun_cons]
      apply Simulation.Interaction.ForwardRel.bind hHeadRun
      intro sourceResult targetResult hResult
      cases hResult with
      | regular hMiddleCtx hMiddleState =>
          have hTailFuel :=
            Expressions.TargetFuel.Covers.tail_after_succ_append hFuel'
          exact
            hTailForward _ sourceFuel (targetFuel - headCode.length)
              hTailFuel hMiddleCtx hMiddleState
      | brk hTarget hState =>
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact .brk hTarget hState
      | cont hTarget hState =>
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact .cont hTarget hState
      | leave hState =>
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact .leave hState
      | halt hShared =>
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact .halt hShared

/-- Exact-fuel list sequencing. A block at `sourceFuel + 1` runs both its head
and regular tail at `sourceFuel`, matching the canonical Functions semantics. -/
theorem controlConsAt
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (targetCtx middleCtx finalCtx : Locals.Ctx)
    (stmt : Functions.Stmt) (rest : List Functions.Stmt)
    (headCode tailCode code : List Expressions.Stmt)
    (finalLayout : Locals.Layout)
    (sourceFuel : Nat)
    (hHead :
      ControlPointPreservesAt sourceProgram targetProgram targets returnNames
        targetCtx middleCtx stmt headCode sourceFuel)
    (hTail :
      ControlScheduledListPreservesAt sourceProgram targetProgram targets
        returnNames middleCtx finalCtx rest finalLayout tailCode sourceFuel)
    (hCode : code = headCode ++ tailCode) :
    ControlScheduledListPreservesAt sourceProgram targetProgram targets
      returnNames targetCtx finalCtx (stmt :: rest) finalLayout code
      (sourceFuel + 1) := by
  rcases hTail with ⟨hFinal, hTailForward⟩
  subst code
  refine ⟨hFinal, ?_⟩
  intro sourceCtx targetFuel suffix returns source target hFuel hCtx hInitial
  have hHeadFuel :=
    Expressions.TargetFuel.Covers.head_of_succ_append hFuel
  have hHeadRun :=
    hHead sourceCtx targetFuel hHeadFuel hCtx hInitial
  rw [Expressions.InteractionSemantics.Block.openRun_append]
  rw [Functions.InteractionSemantics.Block.openRun_cons]
  apply Simulation.Interaction.ForwardRel.bind hHeadRun
  intro sourceResult targetResult hResult
  cases hResult with
  | regular hMiddleCtx hMiddleState =>
      have hTailFuel :=
        Expressions.TargetFuel.Covers.tail_after_succ_append hFuel
      exact
        hTailForward _ (targetFuel - headCode.length) hTailFuel
          hMiddleCtx hMiddleState
  | brk hTarget hState =>
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact .brk hTarget hState
  | cont hTarget hState =>
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact .cont hTarget hState
  | leave hState =>
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact .leave hState
  | halt hShared =>
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact .halt hShared

theorem controlOrderedCons
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (targetCtx middleCtx finalCtx : Locals.Ctx)
    (stmt : Functions.Stmt) (rest : List Functions.Stmt)
    (order : AllocationLayout.Ordering)
    (orderCode pointCode tailCode code : List Expressions.Stmt)
    (finalLayout : Locals.Layout)
    (hOrderSource : targetCtx.layout = order.source)
    (hOrderCompile :
      Locals.Block.compileOpen targetCtx { stmts := order.statements } =
        some (orderCode, targetCtx.withLayout order.target))
    (hPoint :
      ControlPointPreserves sourceProgram targetProgram targets returnNames
        (targetCtx.withLayout order.target) middleCtx stmt pointCode)
    (hTail :
      ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
        middleCtx finalCtx rest finalLayout tailCode)
    (hCode : code = orderCode ++ pointCode ++ tailCode) :
    ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
      targetCtx finalCtx (stmt :: rest) finalLayout code := by
  obtain ⟨artifact, hArtifactCompile, hOrderedPoint⟩ :=
    controlOrdering returnNames sourceProgram targetProgram targets targetCtx middleCtx
      stmt pointCode order hOrderSource hPoint
  have hOrderPair :=
    Option.some.inj (hArtifactCompile.symm.trans hOrderCompile)
  have hOrderCode :
      artifact.promotionCodes.map Expressions.Stmt.code = orderCode :=
    congrArg Prod.fst hOrderPair
  apply controlCons returnNames sourceProgram targetProgram targets targetCtx middleCtx
    finalCtx stmt rest
    (artifact.promotionCodes.map Expressions.Stmt.code ++ pointCode)
    tailCode code finalLayout hOrderedPoint hTail
  rw [hCode, ← hOrderCode]

theorem controlOrderedConsAt
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (targetCtx middleCtx finalCtx : Locals.Ctx)
    (stmt : Functions.Stmt) (rest : List Functions.Stmt)
    (order : AllocationLayout.Ordering)
    (orderCode pointCode tailCode code : List Expressions.Stmt)
    (finalLayout : Locals.Layout)
    (sourceFuel : Nat)
    (hOrderSource : targetCtx.layout = order.source)
    (hOrderCompile :
      Locals.Block.compileOpen targetCtx { stmts := order.statements } =
        some (orderCode, targetCtx.withLayout order.target))
    (hPoint :
      ControlPointPreservesAt sourceProgram targetProgram targets returnNames
        (targetCtx.withLayout order.target) middleCtx stmt pointCode
        sourceFuel)
    (hTail :
      ControlScheduledListPreservesAt sourceProgram targetProgram targets
        returnNames middleCtx finalCtx rest finalLayout tailCode sourceFuel)
    (hCode : code = orderCode ++ pointCode ++ tailCode) :
    ControlScheduledListPreservesAt sourceProgram targetProgram targets
      returnNames targetCtx finalCtx (stmt :: rest) finalLayout code
      (sourceFuel + 1) := by
  obtain ⟨artifact, hArtifactCompile, hOrderedPoint⟩ :=
    controlOrderingAt returnNames sourceProgram targetProgram targets targetCtx
      middleCtx stmt pointCode order sourceFuel hOrderSource hPoint
  have hOrderPair :=
    Option.some.inj (hArtifactCompile.symm.trans hOrderCompile)
  have hOrderCode :
      artifact.promotionCodes.map Expressions.Stmt.code = orderCode :=
    congrArg Prod.fst hOrderPair
  apply controlConsAt returnNames sourceProgram targetProgram targets targetCtx
    middleCtx finalCtx stmt rest
    (artifact.promotionCodes.map Expressions.Stmt.code ++ pointCode)
    tailCode code finalLayout sourceFuel hOrderedPoint hTail
  rw [hCode, ← hOrderCode]

theorem controlScopedBodyThenJoin
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (sourceCtx : Functions.Source.Ctx)
    (bodyCtx bodyFinalCtx : Locals.Ctx)
    (source : Functions.Block) (bodyCode : List Expressions.Stmt)
    (exit : AllocationLayout.Join)
    (exitArtifact :
      StackTransitionCompilation.JoinArtifact bodyFinalCtx exit)
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {initialSource : Locals.Source.State}
    {initialTarget : Structured.RunState}
    (sourceFuel targetFuel : Nat)
    (hBody :
      ControlScheduledListPreservesAt sourceProgram targetProgram targets
        returnNames bodyCtx bodyFinalCtx source.stmts bodyFinalCtx.layout
        bodyCode sourceFuel)
    (hBodyCtx : RuntimeCtxCovers sourceCtx bodyCtx targets returnNames returns)
    (hFinalCtx :
      RuntimeCtxCovers sourceCtx
        (bodyFinalCtx.withLayout exit.target) targets returnNames returns)
    (hScopeCovers :
      ∀ {name : Name}, name ∈ exit.target → name ∈ sourceCtx.scope)
    (hFuel :
      Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel
        (bodyCode ++
          (exitArtifact.retainArtifact.promotionCodes.map
                Expressions.Stmt.code ++
            [Expressions.Stmt.code exitArtifact.retainArtifact.cleanup] ++
            exitArtifact.orderArtifact.promotionCodes.map
              Expressions.Stmt.code)))
    (hInitial :
      StateRel bodyCtx.layout suffix returns initialSource initialTarget) :
    Simulation.Interaction.ForwardRel FuelTruncated
      (ControlOpenOutcomeRel targets returnNames
        (bodyFinalCtx.withLayout exit.target) suffix returns)
      (Simulation.Interaction.bind
        (Functions.InteractionSemantics.Block.openRun sourceProgram sourceCtx
          sourceFuel source initialSource)
        (fun result =>
          match result.1.mode with
          | .regular =>
              Simulation.Interaction.pure
                (Locals.Source.Effectful.Outcome.regular
                  (result.1.state.restrictTo sourceCtx.scope), sourceCtx)
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure (result.1, sourceCtx)))
      (Expressions.InteractionSemantics.Block.openRun targetProgram targetFuel
        { stmts :=
            bodyCode ++
              (exitArtifact.retainArtifact.promotionCodes.map
                  Expressions.Stmt.code ++
                [Expressions.Stmt.code exitArtifact.retainArtifact.cleanup] ++
                exitArtifact.orderArtifact.promotionCodes.map
                  Expressions.Stmt.code) }
        initialTarget) := by
  cases source
  rcases hBody with ⟨_hBodyFinal, hBodyForward⟩
  have hBodyFuel :=
    Expressions.TargetFuel.Covers.head_of_append hFuel
  have hBodyRun :=
    hBodyForward sourceCtx targetFuel hBodyFuel hBodyCtx hInitial
  rw [Expressions.InteractionSemantics.Block.openRun_append]
  apply Simulation.Interaction.ForwardRel.bind hBodyRun
  intro sourceResult targetResult hResult
  cases hResult with
  | regular _hBodyControl hBodyState =>
      simp only [Locals.Source.Effectful.Outcome.regular,
        Structured.Outcome.regular, Structured.OutcomeT.regular]
      have hExitFuel :
          exitArtifact.retainArtifact.promotionCodes.length + 1 +
              exitArtifact.orderArtifact.promotionCodes.length <
            targetFuel - bodyCode.length := by
        have hLength := Expressions.TargetFuel.Covers.length_lt hFuel
        simp only [List.length_append, List.length_map, List.length_cons,
          List.length_nil] at hLength
        omega
      obtain ⟨finalTarget, hExitRun, hFinalState⟩ :=
        exitArtifact.blockOpenRun targetProgram
          (targetFuel - bodyCode.length) hExitFuel hBodyState
      rw [hExitRun]
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact .regular hFinalCtx (hFinalState.restrictTo hScopeCovers)
  | brk hTarget hState =>
      simp only [Locals.Source.Effectful.Outcome.brk,
        Structured.Outcome.brk, Structured.OutcomeT.brk]
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact .brk hTarget hState
  | cont hTarget hState =>
      simp only [Locals.Source.Effectful.Outcome.cont,
        Structured.Outcome.cont, Structured.OutcomeT.cont]
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact .cont hTarget hState
  | leave hState =>
      simp only [Locals.Source.Effectful.Outcome.leave,
        Structured.Outcome.leave, Structured.OutcomeT.leave]
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact .leave hState
  | halt hShared =>
      simp only [Locals.Source.Effectful.Outcome.halt,
        Structured.Outcome.halt, Structured.OutcomeT.halt]
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact .halt hShared

theorem controlScheduledRegion
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (sourceCtx : Functions.Source.Ctx)
    (targetCtx bodyFinalCtx : Locals.Ctx)
    (source : Functions.Block) (bodyCode : List Expressions.Stmt)
    (entry : AllocationLayout.Transition)
    (entryArtifact :
      StackTransitionCompilation.Artifact targetCtx entry)
    (exit : AllocationLayout.Join)
    (exitArtifact :
      StackTransitionCompilation.JoinArtifact bodyFinalCtx exit)
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {initialSource : Locals.Source.State}
    {initialTarget : Structured.RunState}
    (sourceFuel targetFuel : Nat)
    (hBody :
      ControlScheduledListPreservesAt sourceProgram targetProgram targets
        returnNames (targetCtx.withLayout entry.target) bodyFinalCtx
        source.stmts bodyFinalCtx.layout bodyCode sourceFuel)
    (hCtx : RuntimeCtxCovers sourceCtx targetCtx targets returnNames returns)
    (hEntrySource : targetCtx.layout = entry.source)
    (hFinalCtx :
      RuntimeCtxCovers sourceCtx
        (bodyFinalCtx.withLayout exit.target) targets returnNames returns)
    (hScopeCovers :
      ∀ {name : Name}, name ∈ exit.target → name ∈ sourceCtx.scope)
    (hFuel :
      Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel
        ((entryArtifact.promotionCodes.map Expressions.Stmt.code ++
            [Expressions.Stmt.code entryArtifact.cleanup]) ++
          (bodyCode ++
            (exitArtifact.retainArtifact.promotionCodes.map
                  Expressions.Stmt.code ++
              [Expressions.Stmt.code exitArtifact.retainArtifact.cleanup] ++
              exitArtifact.orderArtifact.promotionCodes.map
                Expressions.Stmt.code))))
    (hInitial :
      StateRel targetCtx.layout suffix returns initialSource initialTarget) :
    Simulation.Interaction.ForwardRel FuelTruncated
      (ControlOpenOutcomeRel targets returnNames
        (bodyFinalCtx.withLayout exit.target) suffix returns)
      (Simulation.Interaction.bind
        (Functions.InteractionSemantics.Block.openRun sourceProgram sourceCtx
          sourceFuel source initialSource)
        (fun result =>
          match result.1.mode with
          | .regular =>
              Simulation.Interaction.pure
                (Locals.Source.Effectful.Outcome.regular
                  (result.1.state.restrictTo sourceCtx.scope), sourceCtx)
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure (result.1, sourceCtx)))
      (Expressions.InteractionSemantics.Block.openRun targetProgram targetFuel
        { stmts :=
            entryArtifact.promotionCodes.map Expressions.Stmt.code ++
              [Expressions.Stmt.code entryArtifact.cleanup] ++
              bodyCode ++
              (exitArtifact.retainArtifact.promotionCodes.map
                  Expressions.Stmt.code ++
                [Expressions.Stmt.code exitArtifact.retainArtifact.cleanup] ++
                exitArtifact.orderArtifact.promotionCodes.map
                  Expressions.Stmt.code) }
        initialTarget) := by
  have hEntryFuel : entryArtifact.promotionCodes.length + 1 < targetFuel := by
    have hLength := Expressions.TargetFuel.Covers.length_lt hFuel
    simp only [List.length_append, List.length_map, List.length_cons,
      List.length_nil] at hLength
    omega
  rw [show
      entryArtifact.promotionCodes.map Expressions.Stmt.code ++
            [Expressions.Stmt.code entryArtifact.cleanup] ++
            bodyCode ++
            (exitArtifact.retainArtifact.promotionCodes.map
                Expressions.Stmt.code ++
              [Expressions.Stmt.code exitArtifact.retainArtifact.cleanup] ++
              exitArtifact.orderArtifact.promotionCodes.map
                Expressions.Stmt.code) =
        (entryArtifact.promotionCodes.map Expressions.Stmt.code ++
            [Expressions.Stmt.code entryArtifact.cleanup]) ++
          (bodyCode ++
            (exitArtifact.retainArtifact.promotionCodes.map
                Expressions.Stmt.code ++
              [Expressions.Stmt.code exitArtifact.retainArtifact.cleanup] ++
              exitArtifact.orderArtifact.promotionCodes.map
                Expressions.Stmt.code)) by
      simp [List.append_assoc]]
  apply entryArtifact.thenBlockForward targetProgram
      (body :=
        bodyCode ++
          (exitArtifact.retainArtifact.promotionCodes.map
              Expressions.Stmt.code ++
            [Expressions.Stmt.code exitArtifact.retainArtifact.cleanup] ++
            exitArtifact.orderArtifact.promotionCodes.map
              Expressions.Stmt.code))
      targetFuel hEntryFuel hInitial
  intro transitionedTarget hTransitioned
  have hBodyFuel :=
    Expressions.TargetFuel.Covers.tail_after_append hFuel
  have hBodyFuel' :
      Expressions.TargetFuel.Covers targetProgram sourceFuel
        (targetFuel - (entryArtifact.promotionCodes.length + 1))
        (bodyCode ++
          (exitArtifact.retainArtifact.promotionCodes.map
                Expressions.Stmt.code ++
            [Expressions.Stmt.code exitArtifact.retainArtifact.cleanup] ++
            exitArtifact.orderArtifact.promotionCodes.map
              Expressions.Stmt.code)) := by
    simpa only [List.length_append, List.length_map, List.length_cons,
      List.length_nil, Nat.add_zero] using hBodyFuel
  have hRun :=
    controlScopedBodyThenJoin returnNames sourceProgram targetProgram targets sourceCtx
      (targetCtx.withLayout entry.target) bodyFinalCtx source bodyCode exit
      exitArtifact sourceFuel
      (targetFuel - (entryArtifact.promotionCodes.length + 1))
      hBody (hCtx.afterTransition entry hEntrySource) hFinalCtx hScopeCovers
      hBodyFuel' hTransitioned
  simpa [List.append_assoc] using hRun

theorem controlScheduledRegionAsBlock
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (sourceCtx : Functions.Source.Ctx)
    (targetCtx bodyFinalCtx : Locals.Ctx)
    (source : Functions.Block) (bodyCode : List Expressions.Stmt)
    (entry : AllocationLayout.Transition)
    (entryArtifact :
      StackTransitionCompilation.Artifact targetCtx entry)
    (exit : AllocationLayout.Join)
    (exitArtifact :
      StackTransitionCompilation.JoinArtifact bodyFinalCtx exit)
    (targetBody : Expressions.Block)
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {initialSource : Locals.Source.State}
    {initialTarget : Structured.RunState}
    (sourceFuel targetFuel : Nat)
    (hBody :
      ControlScheduledListPreservesAt sourceProgram targetProgram targets
        returnNames (targetCtx.withLayout entry.target) bodyFinalCtx
        source.stmts bodyFinalCtx.layout bodyCode sourceFuel)
    (hCtx : RuntimeCtxCovers sourceCtx targetCtx targets returnNames returns)
    (hEntrySource : targetCtx.layout = entry.source)
    (hFinalCtx :
      RuntimeCtxCovers sourceCtx
        (bodyFinalCtx.withLayout exit.target) targets returnNames returns)
    (hScopeCovers :
      ∀ {name : Name}, name ∈ exit.target → name ∈ sourceCtx.scope)
    (hTargetBody :
      targetBody.stmts =
        ((entryArtifact.promotionCodes.map Expressions.Stmt.code ++
            [Expressions.Stmt.code entryArtifact.cleanup]) ++
          (bodyCode ++
            (exitArtifact.retainArtifact.promotionCodes.map
                  Expressions.Stmt.code ++
              [Expressions.Stmt.code exitArtifact.retainArtifact.cleanup] ++
              exitArtifact.orderArtifact.promotionCodes.map
                Expressions.Stmt.code))) ++ [.code []])
    (hFuel :
      Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel
        targetBody.stmts)
    (hInitial :
      StateRel targetCtx.layout suffix returns initialSource initialTarget) :
    Simulation.Interaction.ForwardRel FuelTruncated
      (ControlOpenOutcomeRel targets returnNames
        (bodyFinalCtx.withLayout exit.target) suffix returns)
      (Functions.InteractionSemantics.Stmt.openRun sourceProgram sourceCtx
        sourceFuel (.block source) initialSource)
      (Expressions.InteractionSemantics.Block.openRun targetProgram targetFuel
        targetBody initialTarget) := by
  rcases targetBody with ⟨targetStmts⟩
  simp only at hTargetBody
  subst targetStmts
  have hTargetLength := Expressions.TargetFuel.Covers.length_lt hFuel
  have hRegionFuel :=
    Expressions.TargetFuel.Covers.head_of_append hFuel
  have hRegionRun :=
    controlScheduledRegion returnNames sourceProgram targetProgram targets sourceCtx
      targetCtx bodyFinalCtx source bodyCode entry entryArtifact exit
      exitArtifact sourceFuel targetFuel hBody hCtx hEntrySource hFinalCtx
      hScopeCovers hRegionFuel hInitial
  have hEmptyFuel :
      ((entryArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code entryArtifact.cleanup]) ++
        (bodyCode ++
          (exitArtifact.retainArtifact.promotionCodes.map
                Expressions.Stmt.code ++
            [Expressions.Stmt.code exitArtifact.retainArtifact.cleanup] ++
            exitArtifact.orderArtifact.promotionCodes.map
              Expressions.Stmt.code))).length + 1 < targetFuel := by
    simpa only [List.length_append, List.length_cons, List.length_nil,
      Nat.add_zero] using hTargetLength
  have hWithEmpty :=
    controlAppendEmptyCodeForward targetProgram targets returnNames
      (bodyFinalCtx.withLayout exit.target) targetFuel hEmptyFuel
      (by simpa [List.append_assoc] using hRegionRun)
  rw [Functions.InteractionSemantics.Stmt.openRun_block]
  simpa [List.append_assoc] using hWithEmpty

theorem controlGrowingRegionAsBlock
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (targetCtx bodyFinalCtx : Locals.Ctx)
    (source : Functions.Block) (bodyCode : List Expressions.Stmt)
    (entry : AllocationLayout.Transition)
    (entryArtifact : StackTransitionCompilation.Artifact targetCtx entry)
    (targetBody : Expressions.Block)
    (hBody :
      ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
        (targetCtx.withLayout entry.target) bodyFinalCtx source.stmts
        bodyFinalCtx.layout bodyCode)
    (hEntrySource : targetCtx.layout = entry.source)
    (hTargetBody :
      targetBody.stmts =
        entryArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code entryArtifact.cleanup] ++ bodyCode) :
    ControlBlockPreserves sourceProgram targetProgram targets returnNames targetCtx
      bodyFinalCtx source targetBody := by
  rcases source with ⟨sourceStmts⟩
  rcases targetBody with ⟨targetStmts⟩
  simp only at hTargetBody
  subst targetStmts
  unfold ControlBlockPreserves
  intro sourceCtx sourceFuel targetFuel suffix returns initialSource
    initialTarget hFuel hCtx hInitial
  have hEntryFuel : entryArtifact.promotionCodes.length + 1 < targetFuel := by
    have hLength := hFuel.length_lt
    simp only [List.length_append, List.length_map, List.length_cons,
      List.length_nil] at hLength
    omega
  apply entryArtifact.thenBlockForward targetProgram targetFuel hEntryFuel
    hInitial
  intro transitionedTarget hTransitioned
  have hBodyFuelRaw :=
    Expressions.TargetFuel.Covers.tail_after_append hFuel
  have hBodyFuel :
      Expressions.TargetFuel.Covers targetProgram sourceFuel
        (targetFuel - (entryArtifact.promotionCodes.length + 1)) bodyCode := by
    simpa only [List.length_append, List.length_map, List.length_cons,
      List.length_nil, Nat.add_zero] using hBodyFuelRaw
  exact hBody.2 sourceCtx sourceFuel
    (targetFuel - (entryArtifact.promotionCodes.length + 1)) hBodyFuel
    (hCtx.afterTransition entry hEntrySource) hTransitioned

theorem compiledGrowingRegion_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (scheduleFuel lowerFuel : Nat)
    (body : Functions.Block)
    (bodyFacts : AllocationLivenessFacts.Region)
    (rawRegion : StackSchedule.Region)
    (targetCtx regionFinalCtx : Locals.Ctx)
    (loweredBody : Locals.Block)
    (regionCode : List Expressions.Stmt)
    (hSchedule :
      StackSchedule.scheduleBlockFuelWithTargets targets (scheduleFuel - 1)
          (StackSchedule.layoutSet targetCtx.layout) targetCtx.layout
          body bodyFacts = some rawRegion)
    (hLower :
      StackLowering.lowerBlockFuel (lowerFuel - 1) lowerCtx body rawRegion =
        some loweredBody)
    (hCompile :
      Locals.Block.compileOpen targetCtx loweredBody =
        some (regionCode, regionFinalCtx))
    (hBody :
      ∀ {bodyLowered bodyCode bodyFinalCtx},
        StackLowering.lowerStmtListFuel ((lowerFuel - 1) - 1) lowerCtx
            body.stmts rawRegion.points = some bodyLowered →
        Locals.Block.compileOpen
            (targetCtx.withLayout rawRegion.entry.target)
            { stmts := bodyLowered } = some (bodyCode, bodyFinalCtx) →
        ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
          (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx body.stmts
          rawRegion.finalLayout bodyCode) :
    ∃ bodyCode bodyFinalCtx,
      ∃ entryArtifact :
          StackTransitionCompilation.Artifact targetCtx rawRegion.entry,
        ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
            (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx body.stmts
            rawRegion.finalLayout bodyCode ∧
          regionCode =
            entryArtifact.promotionCodes.map Expressions.Stmt.code ++
              [Expressions.Stmt.code entryArtifact.cleanup] ++ bodyCode ∧
          regionFinalCtx = bodyFinalCtx ∧
          targetCtx.layout = rawRegion.entry.source ∧
          ControlBlockPreserves sourceProgram targetProgram targets returnNames
            targetCtx bodyFinalCtx body { stmts := regionCode } := by
  obtain ⟨builtEntry, _points, _finalLayout, hEntryBuild, _hPoints,
      hRawEntry, _hRawPoints, hRawExitNone, _hRawFinal⟩ :=
    StackSchedule.scheduleBlockFuelWithTargets_components hSchedule
  have hBuiltEntry : builtEntry = rawRegion.entry := hRawEntry.symm
  subst builtEntry
  obtain ⟨bodyLowered, hBodyLower, hLoweredBody⟩ :=
    StackLowering.lowerBlockFuel_components hLower
  have hLoweredBody' :
      loweredBody.stmts =
        StackLowering.entryTransitionStmts rawRegion.entry ++ bodyLowered := by
    simpa [StackLowering.exitStmts, hRawExitNone, List.append_assoc] using
      hLoweredBody
  have hLoweredBodyStruct :
      loweredBody =
        { stmts :=
            StackLowering.entryTransitionStmts rawRegion.entry ++
              bodyLowered } := by
    cases loweredBody
    simp_all
  rw [hLoweredBodyStruct] at hCompile
  obtain ⟨entryCode, entryFinalCtx, bodyCode, hEntryCompile, hBodyCompile,
      hRegionCode⟩ :=
    Locals.Block.compileOpen_append_components hCompile
  have hEntrySource : targetCtx.layout = rawRegion.entry.source :=
    (AllocationLayout.Transition.build?_sound hEntryBuild).1.symm
  obtain ⟨entryArtifact⟩ :=
    StackTransitionCompilation.Transition.compileArtifact rawRegion.entry
      hEntrySource
  have hEntryPair :=
    Option.some.inj (entryArtifact.compileEq.symm.trans hEntryCompile)
  have hEntryCode :
      entryArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code entryArtifact.cleanup] = entryCode :=
    congrArg Prod.fst hEntryPair
  have hEntryFinal :
      targetCtx.withLayout rawRegion.entry.target = entryFinalCtx :=
    congrArg Prod.snd hEntryPair
  rw [← hEntryFinal] at hBodyCompile
  have hBodyPreserves := hBody (by simpa using hBodyLower) hBodyCompile
  have hBodyPreservesSelf :
      ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
        (targetCtx.withLayout rawRegion.entry.target) regionFinalCtx body.stmts
        regionFinalCtx.layout bodyCode :=
    ⟨rfl, hBodyPreserves.2⟩
  have hCode :
      regionCode =
        entryArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code entryArtifact.cleanup] ++ bodyCode := by
    rw [hRegionCode, ← hEntryCode]
  refine ⟨bodyCode, regionFinalCtx, entryArtifact, hBodyPreserves, hCode,
    rfl, hEntrySource, ?_⟩
  exact controlGrowingRegionAsBlock returnNames sourceProgram targetProgram targets
    targetCtx regionFinalCtx body bodyCode rawRegion.entry entryArtifact
    { stmts := regionCode } hBodyPreservesSelf hEntrySource hCode

theorem controlOpenRegionAsBlock
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (targetCtx bodyFinalCtx : Locals.Ctx)
    (source : Functions.Block) (bodyCode : List Expressions.Stmt)
    (entry : AllocationLayout.Transition)
    (entryArtifact : StackTransitionCompilation.Artifact targetCtx entry)
    (exit : AllocationLayout.Join)
    (exitArtifact : StackTransitionCompilation.JoinArtifact bodyFinalCtx exit)
    (targetBody : Expressions.Block)
    (hBody :
      ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
        (targetCtx.withLayout entry.target) bodyFinalCtx source.stmts
        bodyFinalCtx.layout bodyCode)
    (hEntrySource : targetCtx.layout = entry.source)
    (hExitSource : bodyFinalCtx.layout = exit.source)
    (hTargetBody :
      targetBody.stmts =
        entryArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code entryArtifact.cleanup] ++ bodyCode ++
          (exitArtifact.retainArtifact.promotionCodes.map
                Expressions.Stmt.code ++
            [Expressions.Stmt.code exitArtifact.retainArtifact.cleanup] ++
            exitArtifact.orderArtifact.promotionCodes.map
              Expressions.Stmt.code)) :
    ControlBlockPreserves sourceProgram targetProgram targets returnNames targetCtx
      (bodyFinalCtx.withLayout exit.target) source targetBody := by
  rcases source with ⟨sourceStmts⟩
  rcases targetBody with ⟨targetStmts⟩
  simp only at hTargetBody
  subst targetStmts
  unfold ControlBlockPreserves
  intro sourceCtx sourceFuel targetFuel suffix returns initialSource
    initialTarget hFuel hCtx hInitial
  have hLength := hFuel.length_lt
  have hEntryFuel : entryArtifact.promotionCodes.length + 1 < targetFuel := by
    simp only [List.length_append, List.length_map, List.length_cons,
      List.length_nil] at hLength
    omega
  rw [show
      entryArtifact.promotionCodes.map Expressions.Stmt.code ++
              [Expressions.Stmt.code entryArtifact.cleanup] ++ bodyCode ++
            (exitArtifact.retainArtifact.promotionCodes.map
                  Expressions.Stmt.code ++
              [Expressions.Stmt.code exitArtifact.retainArtifact.cleanup] ++
              exitArtifact.orderArtifact.promotionCodes.map
                Expressions.Stmt.code) =
        (entryArtifact.promotionCodes.map Expressions.Stmt.code ++
            [Expressions.Stmt.code entryArtifact.cleanup]) ++
          (bodyCode ++
            (exitArtifact.retainArtifact.promotionCodes.map
                  Expressions.Stmt.code ++
              [Expressions.Stmt.code exitArtifact.retainArtifact.cleanup] ++
              exitArtifact.orderArtifact.promotionCodes.map
                Expressions.Stmt.code)) by
      simp [List.append_assoc]]
  apply entryArtifact.thenBlockForward targetProgram
    (body :=
      bodyCode ++
        (exitArtifact.retainArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code exitArtifact.retainArtifact.cleanup] ++
          exitArtifact.orderArtifact.promotionCodes.map Expressions.Stmt.code))
    targetFuel hEntryFuel hInitial
  intro transitionedTarget hTransitioned
  have hFuelGrouped :
      Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel
        ((entryArtifact.promotionCodes.map Expressions.Stmt.code ++
            [Expressions.Stmt.code entryArtifact.cleanup]) ++
          (bodyCode ++
            (exitArtifact.retainArtifact.promotionCodes.map
                  Expressions.Stmt.code ++
              [Expressions.Stmt.code exitArtifact.retainArtifact.cleanup] ++
              exitArtifact.orderArtifact.promotionCodes.map
                Expressions.Stmt.code))) := by
    simpa [List.append_assoc] using hFuel
  have hRestFuelRaw :=
    Expressions.TargetFuel.Covers.tail_after_append hFuelGrouped
  have hRestFuel :
      Expressions.TargetFuel.Covers targetProgram sourceFuel
        (targetFuel - (entryArtifact.promotionCodes.length + 1))
        (bodyCode ++
          (exitArtifact.retainArtifact.promotionCodes.map
                Expressions.Stmt.code ++
            [Expressions.Stmt.code exitArtifact.retainArtifact.cleanup] ++
            exitArtifact.orderArtifact.promotionCodes.map
              Expressions.Stmt.code)) := by
    simpa only [List.length_append, List.length_map, List.length_cons,
      List.length_nil, Nat.add_zero] using hRestFuelRaw
  have hBodyFuel := Expressions.TargetFuel.Covers.head_of_append hRestFuel
  have hBodyRun :=
    hBody.2 sourceCtx sourceFuel
      (targetFuel - (entryArtifact.promotionCodes.length + 1)) hBodyFuel
      (hCtx.afterTransition entry hEntrySource) hTransitioned
  rw [Expressions.InteractionSemantics.Block.openRun_append]
  apply Simulation.Interaction.ForwardRel.bind_right hBodyRun
  intro sourceDone targetDone hResult
  cases hResult with
  | error hError => exact .done (.error hError)
  | ok hResult =>
      cases hResult with
      | regular hBodyCtx hBodyState =>
          simp only [Structured.Outcome.regular,
            Structured.OutcomeT.regular]
          have hExitFuel :
              exitArtifact.retainArtifact.promotionCodes.length + 1 +
                  exitArtifact.orderArtifact.promotionCodes.length <
                targetFuel - (entryArtifact.promotionCodes.length + 1) -
                  bodyCode.length := by
            simp only [List.length_append, List.length_map, List.length_cons,
              List.length_nil] at hLength
            omega
          obtain ⟨finalTarget, hExitRun, hFinalState⟩ :=
            exitArtifact.blockOpenRun targetProgram
              (targetFuel - (entryArtifact.promotionCodes.length + 1) -
                bodyCode.length)
              hExitFuel hBodyState
          rw [hExitRun]
          exact .done (.ok
            (.regular (hBodyCtx.afterJoin exit hExitSource) hFinalState))
      | brk hTarget hState =>
          simp only [Structured.Outcome.brk, Structured.OutcomeT.brk]
          exact .done (.ok (.brk hTarget hState))
      | cont hTarget hState =>
          simp only [Structured.Outcome.cont, Structured.OutcomeT.cont]
          exact .done (.ok (.cont hTarget hState))
      | leave hState =>
          simp only [Structured.Outcome.leave, Structured.OutcomeT.leave]
          exact .done (.ok (.leave hState))
      | halt hShared =>
          simp only [Structured.Outcome.halt, Structured.OutcomeT.halt]
          exact .done (.ok (.halt hShared))

theorem compiledOpenRegion_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (scheduleFuel lowerFuel : Nat)
    (body : Functions.Block)
    (bodyFacts : AllocationLivenessFacts.Region)
    (rawRegion : StackSchedule.Region)
    (exit : AllocationLayout.Join)
    (targetCtx regionFinalCtx : Locals.Ctx)
    (loweredBody : Locals.Block)
    (regionCode : List Expressions.Stmt)
    (hSchedule :
      StackSchedule.scheduleBlockFuelWithTargets targets (scheduleFuel - 1)
          (StackSchedule.layoutSet targetCtx.layout) targetCtx.layout
          body bodyFacts = some rawRegion)
    (hExitBuild :
      AllocationLayout.Join.build? rawRegion.finalLayout exit.target =
        some exit)
    (hLower :
      StackLowering.lowerBlockFuel (lowerFuel - 1) lowerCtx body
          { rawRegion with exit? := some exit, finalLayout := exit.target } =
        some loweredBody)
    (hCompile :
      Locals.Block.compileOpen targetCtx loweredBody =
        some (regionCode, regionFinalCtx))
    (hBody :
      ∀ {bodyLowered bodyCode bodyFinalCtx},
        StackLowering.lowerStmtListFuel ((lowerFuel - 1) - 1) lowerCtx
            body.stmts rawRegion.points = some bodyLowered →
        Locals.Block.compileOpen
            (targetCtx.withLayout rawRegion.entry.target)
            { stmts := bodyLowered } = some (bodyCode, bodyFinalCtx) →
        ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
          (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx body.stmts
          rawRegion.finalLayout bodyCode) :
    ∃ (bodyCode : List Expressions.Stmt) (bodyFinalCtx : Locals.Ctx),
      ∃ entryArtifact :
          StackTransitionCompilation.Artifact targetCtx rawRegion.entry,
      ∃ exitArtifact :
          StackTransitionCompilation.JoinArtifact bodyFinalCtx exit,
        ControlBlockPreserves sourceProgram targetProgram targets returnNames targetCtx
            (bodyFinalCtx.withLayout exit.target) body
            { stmts := regionCode } ∧
          bodyFinalCtx.layout = rawRegion.finalLayout ∧
          regionFinalCtx = bodyFinalCtx.withLayout exit.target ∧
          targetCtx.layout = rawRegion.entry.source := by
  obtain ⟨builtEntry, _points, _finalLayout, hEntryBuild, _hPoints,
      hRawEntry, _hRawPoints, _hRawExitNone, _hRawFinal⟩ :=
    StackSchedule.scheduleBlockFuelWithTargets_components hSchedule
  have hBuiltEntry : builtEntry = rawRegion.entry := hRawEntry.symm
  subst builtEntry
  obtain ⟨bodyLowered, hBodyLower, hLoweredBody⟩ :=
    StackLowering.lowerBlockFuel_components hLower
  have hLoweredBody' :
      loweredBody.stmts =
        StackLowering.entryTransitionStmts rawRegion.entry ++
          (bodyLowered ++ exit.statements) := by
    simpa [StackLowering.exitStmts] using hLoweredBody
  have hLoweredBodyStruct :
      loweredBody =
        { stmts :=
            StackLowering.entryTransitionStmts rawRegion.entry ++
              (bodyLowered ++ exit.statements) } := by
    cases loweredBody
    simp_all
  rw [hLoweredBodyStruct] at hCompile
  obtain ⟨entryCode, entryFinalCtx, restCode, hEntryCompile, hRestCompile,
      hRegionCode⟩ :=
    Locals.Block.compileOpen_append_components hCompile
  have hEntrySource : targetCtx.layout = rawRegion.entry.source :=
    (AllocationLayout.Transition.build?_sound hEntryBuild).1.symm
  obtain ⟨entryArtifact⟩ :=
    StackTransitionCompilation.Transition.compileArtifact rawRegion.entry
      hEntrySource
  have hEntryPair :=
    Option.some.inj (entryArtifact.compileEq.symm.trans hEntryCompile)
  have hEntryCode :
      entryArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code entryArtifact.cleanup] = entryCode :=
    congrArg Prod.fst hEntryPair
  have hEntryFinal :
      targetCtx.withLayout rawRegion.entry.target = entryFinalCtx :=
    congrArg Prod.snd hEntryPair
  rw [← hEntryFinal] at hRestCompile
  have hRestCompile' :
      Locals.Block.compileOpen
          (targetCtx.withLayout rawRegion.entry.target)
          { stmts := bodyLowered ++ exit.statements } =
        some (restCode, regionFinalCtx) := by
    simpa [List.append_assoc] using hRestCompile
  obtain ⟨bodyCode, bodyFinalCtx, exitCode, hBodyCompile, hExitCompile,
      hRestCode⟩ :=
    Locals.Block.compileOpen_append_components hRestCompile'
  have hBodyPreserves := hBody (by simpa using hBodyLower) hBodyCompile
  have hBodyLayout : bodyFinalCtx.layout = rawRegion.finalLayout :=
    hBodyPreserves.1
  have hExitSource : bodyFinalCtx.layout = exit.source := by
    rw [hBodyLayout]
    exact (AllocationLayout.Join.build?_endpoints hExitBuild).1.symm
  obtain ⟨exitArtifact⟩ :=
    StackTransitionCompilation.Join.compileArtifact exit hExitSource
  have hExitPair :=
    Option.some.inj (exitArtifact.compileEq.symm.trans hExitCompile)
  have hExitCode :
      exitArtifact.retainArtifact.promotionCodes.map Expressions.Stmt.code ++
            [Expressions.Stmt.code exitArtifact.retainArtifact.cleanup] ++
          exitArtifact.orderArtifact.promotionCodes.map Expressions.Stmt.code =
        exitCode :=
    congrArg Prod.fst hExitPair
  have hRegionFinal :
      bodyFinalCtx.withLayout exit.target = regionFinalCtx :=
    congrArg Prod.snd hExitPair
  have hTargetBody :
      ({ stmts := regionCode } : Expressions.Block).stmts =
        entryArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code entryArtifact.cleanup] ++ bodyCode ++
          (exitArtifact.retainArtifact.promotionCodes.map
                Expressions.Stmt.code ++
            [Expressions.Stmt.code exitArtifact.retainArtifact.cleanup] ++
            exitArtifact.orderArtifact.promotionCodes.map
              Expressions.Stmt.code) := by
    simp only
    rw [hRegionCode, ← hEntryCode, hRestCode, ← hExitCode]
    simp [List.append_assoc]
  have hBodySelf :
      ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
        (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx body.stmts
        bodyFinalCtx.layout bodyCode :=
    ⟨rfl, hBodyPreserves.2⟩
  refine ⟨bodyCode, bodyFinalCtx, entryArtifact, exitArtifact, ?_,
    hBodyLayout, hRegionFinal.symm, hEntrySource⟩
  exact controlOpenRegionAsBlock returnNames sourceProgram targetProgram targets targetCtx
    bodyFinalCtx body bodyCode rawRegion.entry entryArtifact exit exitArtifact
    { stmts := regionCode } hBodySelf hEntrySource hExitSource hTargetBody

theorem compiledScheduledRegion_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (scheduleFuel lowerFuel : Nat)
    (body : Functions.Block)
    (bodyFacts : AllocationLivenessFacts.Region)
    (rawRegion : StackSchedule.Region)
    (exit : AllocationLayout.Join)
    (targetCtx regionFinalCtx : Locals.Ctx)
    (loweredBody : Locals.Block)
    (regionCode : List Expressions.Stmt)
    (hSchedule :
      StackSchedule.scheduleBlockFuelWithTargets targets (scheduleFuel - 1)
          (StackSchedule.layoutSet targetCtx.layout) targetCtx.layout
          body bodyFacts = some rawRegion)
    (hExitBuild :
      AllocationLayout.Join.build? rawRegion.finalLayout targetCtx.layout =
        some exit)
    (hLower :
      StackLowering.lowerBlockFuel (lowerFuel - 1) lowerCtx body
          { rawRegion with exit? := some exit, finalLayout := targetCtx.layout } =
        some loweredBody)
    (hCompile :
      Locals.Block.compileOpen targetCtx loweredBody =
        some (regionCode, regionFinalCtx))
    (hBody :
      ∀ {bodyLowered bodyCode bodyFinalCtx},
        StackLowering.lowerStmtListFuel ((lowerFuel - 1) - 1) lowerCtx
            body.stmts rawRegion.points = some bodyLowered →
        Locals.Block.compileOpen
            (targetCtx.withLayout rawRegion.entry.target)
            { stmts := bodyLowered } = some (bodyCode, bodyFinalCtx) →
        ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
          (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx body.stmts
          rawRegion.finalLayout bodyCode) :
    ∃ bodyCode bodyFinalCtx,
      ∃ entryArtifact :
          StackTransitionCompilation.Artifact targetCtx rawRegion.entry,
      ∃ exitArtifact :
          StackTransitionCompilation.JoinArtifact bodyFinalCtx exit,
        ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
            (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx body.stmts
            rawRegion.finalLayout bodyCode ∧
          regionCode =
            entryArtifact.promotionCodes.map Expressions.Stmt.code ++
              [Expressions.Stmt.code entryArtifact.cleanup] ++ bodyCode ++
              (exitArtifact.retainArtifact.promotionCodes.map
                    Expressions.Stmt.code ++
                [Expressions.Stmt.code exitArtifact.retainArtifact.cleanup] ++
                exitArtifact.orderArtifact.promotionCodes.map
                  Expressions.Stmt.code) ∧
          regionFinalCtx = bodyFinalCtx.withLayout exit.target ∧
          bodyFinalCtx.withLayout exit.target = targetCtx ∧
          targetCtx.layout = rawRegion.entry.source := by
  obtain ⟨builtEntry, _childPoints, _childFinalLayout, hEntryBuild,
      _hChildPoints, hRawEntry, _hRawPoints, _hRawExitNone,
      _hRawFinal⟩ :=
    StackSchedule.scheduleBlockFuelWithTargets_components hSchedule
  have hBuiltEntry : builtEntry = rawRegion.entry := hRawEntry.symm
  subst builtEntry
  obtain ⟨bodyLowered, hBodyLower, hLoweredBody⟩ :=
    StackLowering.lowerBlockFuel_components hLower
  have hLoweredBody' :
      loweredBody.stmts =
        StackLowering.entryTransitionStmts rawRegion.entry ++
          (bodyLowered ++ exit.statements) := by
    simpa [StackLowering.exitStmts] using hLoweredBody
  have hLoweredBodyStruct :
      loweredBody =
        { stmts :=
            StackLowering.entryTransitionStmts rawRegion.entry ++
              (bodyLowered ++ exit.statements) } := by
    cases loweredBody
    simp_all
  rw [hLoweredBodyStruct] at hCompile
  obtain ⟨entryCode, entryFinalCtx, restCode, hEntryCompile, hRestCompile,
      hRegionCode⟩ :=
    Locals.Block.compileOpen_append_components hCompile
  have hEntrySource : targetCtx.layout = rawRegion.entry.source :=
    (AllocationLayout.Transition.build?_sound hEntryBuild).1.symm
  obtain ⟨entryArtifact⟩ :=
    StackTransitionCompilation.Transition.compileArtifact rawRegion.entry
      hEntrySource
  have hEntryPair :=
    Option.some.inj (entryArtifact.compileEq.symm.trans hEntryCompile)
  have hEntryCode :
      entryArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code entryArtifact.cleanup] = entryCode :=
    congrArg Prod.fst hEntryPair
  have hEntryFinal :
      targetCtx.withLayout rawRegion.entry.target = entryFinalCtx :=
    congrArg Prod.snd hEntryPair
  rw [← hEntryFinal] at hRestCompile
  have hRestCompile' :
      Locals.Block.compileOpen
          (targetCtx.withLayout rawRegion.entry.target)
          { stmts := bodyLowered ++ exit.statements } =
        some (restCode, regionFinalCtx) := by
    simpa [List.append_assoc] using hRestCompile
  obtain ⟨bodyCode, bodyFinalCtx, exitCode, hBodyCompile, hExitCompile,
      hRestCode⟩ :=
    Locals.Block.compileOpen_append_components hRestCompile'
  have hBodyPreserves := hBody (by simpa using hBodyLower) hBodyCompile
  have hBodyLayout : bodyFinalCtx.layout = rawRegion.finalLayout :=
    hBodyPreserves.1
  have hExitSource : bodyFinalCtx.layout = exit.source := by
    rw [hBodyLayout]
    exact (AllocationLayout.Join.build?_endpoints hExitBuild).1.symm
  obtain ⟨exitArtifact⟩ :=
    StackTransitionCompilation.Join.compileArtifact exit hExitSource
  have hExitPair :=
    Option.some.inj (exitArtifact.compileEq.symm.trans hExitCompile)
  have hExitCode :
      exitArtifact.retainArtifact.promotionCodes.map Expressions.Stmt.code ++
            [Expressions.Stmt.code exitArtifact.retainArtifact.cleanup] ++
          exitArtifact.orderArtifact.promotionCodes.map Expressions.Stmt.code =
        exitCode :=
    congrArg Prod.fst hExitPair
  have hRegionFinal :
      bodyFinalCtx.withLayout exit.target = regionFinalCtx :=
    congrArg Prod.snd hExitPair
  have hExitTarget : exit.target = targetCtx.layout :=
    (AllocationLayout.Join.build?_endpoints hExitBuild).2
  have hControl :
      Locals.Ctx.SameControl targetCtx
        (bodyFinalCtx.withLayout exit.target) :=
    (Locals.Ctx.SameControl.withLayout targetCtx rawRegion.entry.target).trans
      ((Locals.Block.compileOpen_sameControl hBodyCompile).trans
        (Locals.Ctx.SameControl.withLayout bodyFinalCtx exit.target))
  have hRestoredCtx :
      bodyFinalCtx.withLayout exit.target = targetCtx := by
    cases targetCtx
    cases bodyFinalCtx
    simp [Locals.Ctx.withLayout] at hControl hExitTarget ⊢
    rcases hControl with ⟨hBreak, hContinue, hLeave, hRetc⟩
    simp_all
  refine ⟨bodyCode, bodyFinalCtx, entryArtifact, exitArtifact,
    hBodyPreserves, ?_, hRegionFinal.symm, hRestoredCtx, hEntrySource⟩
  rw [hRegionCode, ← hEntryCode, hRestCode, ← hExitCode]
  simp [List.append_assoc]

def ControlSwitchBranchPreserves
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (targetCtx : Locals.Ctx) (sourceBody : Functions.Block)
    (targetBody : Expressions.Block) : Prop :=
  ∀ (sourceCtx : Functions.Source.Ctx) (sourceFuel targetFuel : Nat)
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState},
    Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel
        targetBody.stmts →
      RuntimeCtxCovers sourceCtx targetCtx targets returnNames returns →
      StateRel targetCtx.layout suffix returns source target →
      Simulation.Interaction.ForwardRel FuelTruncated
        (ControlOpenOutcomeRel targets returnNames targetCtx suffix returns)
        (Functions.InteractionSemantics.Stmt.openRun sourceProgram sourceCtx
          sourceFuel (.block sourceBody) source)
        (Expressions.InteractionSemantics.Block.openRun targetProgram
          targetFuel targetBody target)

theorem ControlSwitchBranchPreserves.toPoint
    {sourceProgram : Functions.Program}
    {targetProgram : Expressions.Program}
    {targets : StackSchedule.ControlTargets}
    {targetCtx : Locals.Ctx} {sourceBody : Functions.Block}
    {targetBody : Expressions.Block}
    (hPreserves :
      ControlSwitchBranchPreserves returnNames sourceProgram targetProgram targets
        targetCtx sourceBody targetBody) :
    ControlPointPreserves sourceProgram targetProgram targets returnNames targetCtx
      targetCtx (.block sourceBody) targetBody.stmts := by
  rcases targetBody with ⟨targetStmts⟩
  exact hPreserves

inductive SwitchBranchRel
    (returnNames : List Name)
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets) (targetCtx : Locals.Ctx) :
    Option Functions.Block → Option Expressions.Block → Prop
  | none : SwitchBranchRel returnNames sourceProgram targetProgram targets targetCtx none none
  | some {sourceBody : Functions.Block} {targetBody : Expressions.Block} :
      ControlSwitchBranchPreserves returnNames sourceProgram targetProgram targets targetCtx
          sourceBody targetBody →
        SwitchBranchRel returnNames sourceProgram targetProgram targets targetCtx
          (some sourceBody) (some targetBody)

theorem compiledSwitchBranch_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (scheduleFuel lowerFuel : Nat)
    (body : Functions.Block)
    (bodyFacts : AllocationLivenessFacts.Region)
    (rawRegion : StackSchedule.Region)
    (exit : AllocationLayout.Join)
    (targetCtx regionFinalCtx : Locals.Ctx)
    (loweredBody : Locals.Block)
    (regionCode : List Expressions.Stmt)
    (targetBody : Expressions.Block)
    (hSchedule :
      StackSchedule.scheduleBlockFuelWithTargets targets (scheduleFuel - 1)
          (StackSchedule.layoutSet targetCtx.layout) targetCtx.layout
          body bodyFacts = some rawRegion)
    (hExitBuild :
      AllocationLayout.Join.build? rawRegion.finalLayout targetCtx.layout =
        some exit)
    (hLower :
      StackLowering.lowerBlockFuel (lowerFuel - 1) lowerCtx body
          { rawRegion with exit? := some exit, finalLayout := targetCtx.layout } =
        some loweredBody)
    (hCompile :
      Locals.Block.compileOpen targetCtx loweredBody =
        some (regionCode, regionFinalCtx))
    (hFinish :
      Locals.finishScoped targetCtx regionFinalCtx regionCode = some targetBody)
    (hBody :
      ∀ {bodyLowered bodyCode bodyFinalCtx},
        StackLowering.lowerStmtListFuel ((lowerFuel - 1) - 1) lowerCtx
            body.stmts rawRegion.points = some bodyLowered →
        Locals.Block.compileOpen
            (targetCtx.withLayout rawRegion.entry.target)
            { stmts := bodyLowered } = some (bodyCode, bodyFinalCtx) →
        ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
          (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx body.stmts
          rawRegion.finalLayout bodyCode) :
    ControlSwitchBranchPreserves returnNames sourceProgram targetProgram targets targetCtx
      body targetBody := by
  obtain ⟨bodyCode, bodyFinalCtx, entryArtifact, exitArtifact,
      hBodyPreserves, hRegionCode, hRegionFinal, hRestoredCtx, hEntrySource⟩ :=
    compiledScheduledRegion_of_compilers returnNames sourceProgram targetProgram lowerCtx
      targets scheduleFuel lowerFuel body bodyFacts rawRegion exit targetCtx
      regionFinalCtx loweredBody regionCode hSchedule hExitBuild hLower hCompile
      hBody
  obtain ⟨cleanup, hCleanup, hTargetBody⟩ :=
    Locals.finishScoped_components hFinish
  have hBodyPreservesSelf :
      ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
        (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx body.stmts
        bodyFinalCtx.layout bodyCode :=
    ⟨rfl, hBodyPreserves.2⟩
  have hRegionCtx : regionFinalCtx = targetCtx :=
    hRegionFinal.trans hRestoredCtx
  have hCleanupEmpty : cleanup = [] := by
    rw [hRegionCtx] at hCleanup
    simpa [Locals.Ctx.cleanupTo?] using hCleanup
  subst cleanup
  have hTargetBodyCode :
      targetBody.stmts =
        ((entryArtifact.promotionCodes.map Expressions.Stmt.code ++
            [Expressions.Stmt.code entryArtifact.cleanup]) ++
          (bodyCode ++
            (exitArtifact.retainArtifact.promotionCodes.map
                  Expressions.Stmt.code ++
              [Expressions.Stmt.code exitArtifact.retainArtifact.cleanup] ++
              exitArtifact.orderArtifact.promotionCodes.map
                Expressions.Stmt.code))) ++ [.code []] := by
    rw [hTargetBody, hRegionCode]
    simp [Locals.codeStmt, List.append_assoc]
  have hExitTarget : exit.target = targetCtx.layout :=
    (AllocationLayout.Join.build?_endpoints hExitBuild).2
  unfold ControlSwitchBranchPreserves
  intro sourceCtx sourceFuel targetFuel suffix returns source target hFuel hCtx
    hInitial
  have hFinalControl :
      RuntimeCtxCovers sourceCtx
        (bodyFinalCtx.withLayout exit.target) targets returnNames returns := by
    rw [hRestoredCtx]
    exact hCtx
  have hScopeCovers :
      ∀ {name : Name}, name ∈ exit.target → name ∈ sourceCtx.scope := by
    intro name hName
    apply hCtx.context.scope
    rwa [hExitTarget] at hName
  have hRun :=
    controlScheduledRegionAsBlock returnNames sourceProgram targetProgram targets sourceCtx
      targetCtx bodyFinalCtx body bodyCode rawRegion.entry entryArtifact exit
      exitArtifact targetBody sourceFuel targetFuel
      (hBodyPreservesSelf.at sourceFuel) hCtx
      hEntrySource hFinalControl hScopeCovers hTargetBodyCode hFuel hInitial
  rw [hRestoredCtx] at hRun
  exact hRun

theorem switchDefaultRel_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (scheduleFuel lowerFuel : Nat)
    (targetCtx : Locals.Ctx)
    (defaultBody : Option Functions.Block)
    (defaultFacts : List AllocationLivenessFacts.Region)
    (regions : List StackSchedule.Region)
    (loweredDefault : Option Locals.Block)
    (compiledDefault : Option Expressions.Block)
    (hSchedule :
      StackSchedule.scheduleDefaultRegionFuelWithTargets targets
          (scheduleFuel - 1) (StackSchedule.layoutSet targetCtx.layout)
          targetCtx.layout defaultBody defaultFacts = some regions)
    (hLower :
      StackLowering.lowerDefaultFuel (lowerFuel - 1) lowerCtx defaultBody
          regions = some loweredDefault)
    (hCompile :
      Locals.Default.compile targetCtx loweredDefault = some compiledDefault)
    (hBody :
      ∀ {body bodyFacts rawRegion bodyLowered bodyCode bodyFinalCtx},
        StackSchedule.scheduleBlockFuelWithTargets targets (scheduleFuel - 1)
            (StackSchedule.layoutSet targetCtx.layout) targetCtx.layout
            body bodyFacts = some rawRegion →
        StackLowering.lowerStmtListFuel ((lowerFuel - 1) - 1) lowerCtx
            body.stmts rawRegion.points = some bodyLowered →
        Locals.Block.compileOpen
            (targetCtx.withLayout rawRegion.entry.target)
            { stmts := bodyLowered } = some (bodyCode, bodyFinalCtx) →
        ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
          (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx body.stmts
          rawRegion.finalLayout bodyCode) :
    SwitchBranchRel returnNames sourceProgram targetProgram targets targetCtx defaultBody
      compiledDefault := by
  cases defaultBody with
  | none =>
      obtain ⟨hFacts, hRegions⟩ :=
        StackSchedule.scheduleDefaultRegionFuelWithTargets_none_shape hSchedule
      subst defaultFacts
      subst regions
      obtain ⟨_hRegions, hLowered⟩ :=
        StackLowering.lowerDefaultFuel_none_shape hLower
      subst loweredDefault
      simp [Locals.Default.compile] at hCompile
      subst compiledDefault
      exact .none
  | some body =>
      obtain ⟨bodyFacts, rawRegion, exit, region, hFacts, hRegions,
          hBodySchedule, hExitBuild, hRegion⟩ :=
        StackSchedule.scheduleDefaultRegionFuelWithTargets_some_shape hSchedule
      subst defaultFacts
      subst regions
      obtain ⟨lowerRegion, loweredBody, hLowerRegions, hLowered,
          hBodyLower⟩ :=
        StackLowering.lowerDefaultFuel_some_shape hLower
      injection hLowerRegions with hLowerRegion
      subst lowerRegion
      subst loweredDefault
      subst region
      obtain ⟨regionCode, regionFinalCtx, targetBody,
          hRegionCompile, hFinish, hCompiledDefault⟩ :=
        Locals.Default.compile_some_components hCompile
      subst compiledDefault
      apply SwitchBranchRel.some
      apply compiledSwitchBranch_of_compilers returnNames sourceProgram targetProgram
        lowerCtx targets scheduleFuel lowerFuel body bodyFacts rawRegion exit
        targetCtx regionFinalCtx loweredBody regionCode targetBody hBodySchedule
        hExitBuild hBodyLower hRegionCompile hFinish
      intro bodyLowered bodyCode bodyFinalCtx hBodyLowered hBodyCompile
      exact hBody hBodySchedule hBodyLowered hBodyCompile

theorem switchCasesRel_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (scheduleFuel lowerFuel : Nat)
    (targetCtx : Locals.Ctx)
    (cases : List (Word × Functions.Block))
    (defaultBody : Option Functions.Block)
    (facts : List AllocationLivenessFacts.Region)
    (regions : List StackSchedule.Region)
    (loweredCases : List (Word × Locals.Block))
    (compiledCases : List (Word × Expressions.Block))
    (compiledDefault : Option Expressions.Block)
    (hSchedule :
      StackSchedule.scheduleCaseRegionsFuelWithTargets targets
          (scheduleFuel - 1) (StackSchedule.layoutSet targetCtx.layout)
          targetCtx.layout cases facts = some regions)
    (hLower :
      StackLowering.lowerCasesFuel (lowerFuel - 1) lowerCtx cases regions =
        some loweredCases)
    (hCompile :
      Locals.CaseList.compile targetCtx loweredCases = some compiledCases)
    (hBody :
      ∀ {body bodyFacts rawRegion bodyLowered bodyCode bodyFinalCtx},
        StackSchedule.scheduleBlockFuelWithTargets targets (scheduleFuel - 1)
            (StackSchedule.layoutSet targetCtx.layout) targetCtx.layout
            body bodyFacts = some rawRegion →
        StackLowering.lowerStmtListFuel ((lowerFuel - 1) - 1) lowerCtx
            body.stmts rawRegion.points = some bodyLowered →
        Locals.Block.compileOpen
            (targetCtx.withLayout rawRegion.entry.target)
            { stmts := bodyLowered } = some (bodyCode, bodyFinalCtx) →
        ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
          (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx body.stmts
          rawRegion.finalLayout bodyCode)
    (hDefault :
      SwitchBranchRel returnNames sourceProgram targetProgram targets targetCtx defaultBody
        compiledDefault) :
    ∀ value,
      SwitchBranchRel returnNames sourceProgram targetProgram targets targetCtx
        (Functions.Source.Switch.select value cases defaultBody)
        (Expressions.EffectSemantics.Switch.select value compiledCases
          compiledDefault) := by
  induction cases generalizing facts regions loweredCases compiledCases with
  | nil =>
      obtain ⟨hFacts, hRegions⟩ :=
        StackSchedule.scheduleCaseRegionsFuelWithTargets_nil_shape hSchedule
      subst facts
      subst regions
      obtain ⟨_hRegions, hLowered⟩ :=
        StackLowering.lowerCasesFuel_nil_shape hLower
      subst loweredCases
      simp [Locals.CaseList.compile] at hCompile
      subst compiledCases
      intro value
      simpa [Functions.Source.Switch.select,
        Expressions.EffectSemantics.Switch.select] using hDefault
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      obtain ⟨bodyFacts, restFacts, rawRegion, exit, region, restRegions,
          hFacts, hRegions, hBodySchedule, hExitBuild, hRegion,
          hRestSchedule⟩ :=
        StackSchedule.scheduleCaseRegionsFuelWithTargets_cons_shape hSchedule
      subst facts
      subst regions
      obtain ⟨lowerRegion, lowerRestRegions, loweredBody, loweredRest,
          hLowerRegions, hLowered, hBodyLower, hRestLower⟩ :=
        StackLowering.lowerCasesFuel_cons_shape hLower
      injection hLowerRegions with hLowerRegion hLowerRestRegions
      subst lowerRegion
      subst lowerRestRegions
      subst loweredCases
      subst region
      obtain ⟨regionCode, regionFinalCtx, targetBody, compiledRest,
          hRegionCompile, hFinish, hRestCompile, hCompiledCases⟩ :=
        Locals.CaseList.compile_cons_components hCompile
      subst compiledCases
      have hHead :
          SwitchBranchRel returnNames sourceProgram targetProgram targets targetCtx
            (some body) (some targetBody) := by
        apply SwitchBranchRel.some
        apply compiledSwitchBranch_of_compilers returnNames sourceProgram targetProgram
          lowerCtx targets scheduleFuel lowerFuel body bodyFacts rawRegion exit
          targetCtx regionFinalCtx loweredBody regionCode targetBody
          hBodySchedule hExitBuild hBodyLower hRegionCompile hFinish
        intro bodyLowered bodyCode bodyFinalCtx hBodyLowered hBodyCompile
        exact hBody hBodySchedule hBodyLowered hBodyCompile
      intro value
      have hTail :=
        ih restFacts restRegions loweredRest compiledRest hRestSchedule
          hRestLower hRestCompile value
      by_cases hMatch : caseValue = value
      · simpa [Functions.Source.Switch.select,
          Expressions.EffectSemantics.Switch.select, hMatch] using hHead
      · simpa [Functions.Source.Switch.select,
          Expressions.EffectSemantics.Switch.select, hMatch] using hTail

theorem switchBranchRelToPreserve
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    (scrutinee : Functions.Expr 1)
    (cases : List (Word × Functions.Block))
    (defaultBody : Option Functions.Block)
    (scrutineeCode : Structured.Code)
    (compiledCases : List (Word × Expressions.Block))
    (compiledDefault : Option Expressions.Block)
    (rest : List Expressions.Stmt)
    {suffix : List Word} {returns : List Structured.ReturnDest}
    (hFuel :
      Expressions.TargetFuel.Covers targetProgram (sourceFuel + 1) targetFuel
        (.switch (.code scrutineeCode) compiledCases compiledDefault :: rest))
    (hCtx : RuntimeCtxCovers sourceCtx targetCtx targets returnNames returns)
    (hBranches :
      ∀ value,
        SwitchBranchRel returnNames sourceProgram targetProgram targets targetCtx
          (Functions.Source.Switch.select value cases defaultBody)
          (Expressions.EffectSemantics.Switch.select value compiledCases
            compiledDefault)) :
    SwitchBranchesPreserve sourceProgram targetProgram targets sourceCtx
      targetCtx sourceFuel (targetFuel - 2) cases defaultBody compiledCases
      compiledDefault returnNames suffix returns := by
  intro value
  have hBranch := hBranches value
  cases hSourceSelect :
      Functions.Source.Switch.select value cases defaultBody with
  | none =>
      cases hTargetSelect :
          Expressions.EffectSemantics.Switch.select value compiledCases
            compiledDefault with
      | none => trivial
      | some targetBody =>
          rw [hSourceSelect, hTargetSelect] at hBranch
          cases hBranch
  | some sourceBody =>
      cases hTargetSelect :
          Expressions.EffectSemantics.Switch.select value compiledCases
            compiledDefault with
      | none =>
          rw [hSourceSelect, hTargetSelect] at hBranch
          cases hBranch
      | some targetBody =>
          rw [hSourceSelect, hTargetSelect] at hBranch
          cases hBranch with
          | some hPreserves =>
              intro sourceAfter targetAfter hAfter
              apply hPreserves sourceCtx sourceFuel (targetFuel - 2)
              · exact
                  Expressions.TargetFuel.Covers.switch_selected_after_two
                    hFuel hTargetSelect
              · exact hCtx
              · exact hAfter

theorem blockPoint_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel : Nat)
    (body : Functions.Block)
    (fact : AllocationLivenessFacts.Point)
    (rawPoint point : StackSchedule.Point)
    (retain : AllocationLayout.RegularTransition)
    (targetCtx finalCtx : Locals.Ctx)
    (lowered : List Locals.Stmt) (code : List Expressions.Stmt)
    (hSchedule :
      StackSchedule.scheduleStmtFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout (.block body) fact = some rawPoint)
    (hPointRegions : point.regions = rawPoint.regions)
    (hPointRetain : point.retain? = some retain)
    (hRetainSource : targetCtx.layout = retain.source)
    (hLower :
      StackLowering.lowerPointFuel lowerFuel lowerCtx (.block body) point =
        some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx))
    (hBody :
      ∀ {bodyFacts rawRegion bodyLowered bodyCode bodyFinalCtx},
        StackSchedule.scheduleBlockFuelWithTargets targets (scheduleFuel - 1)
            (StackSchedule.layoutSet targetCtx.layout) targetCtx.layout
            body bodyFacts = some rawRegion →
        StackLowering.lowerStmtListFuel ((lowerFuel - 1) - 1) lowerCtx
            body.stmts rawRegion.points = some bodyLowered →
        Locals.Block.compileOpen
            (targetCtx.withLayout rawRegion.entry.target)
            { stmts := bodyLowered } = some (bodyCode, bodyFinalCtx) →
        ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
          (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx body.stmts
          rawRegion.finalLayout bodyCode) :
    CompiledControlPoint sourceProgram targetProgram targets returnNames targetCtx finalCtx
      (.block body) code retain.schedule.target := by
  obtain ⟨bodyFacts, rawRegion, exit, hFacts, hChildSchedule, hExitBuild,
      _hBefore, hStatement, _hRawExit, _hRawRetain, hRawRegions,
      _hFalls⟩ :=
    StackSchedule.scheduleStmtFuelWithTargets_block_components hSchedule
  obtain ⟨builtEntry, childPoints, childFinalLayout, hEntryBuild,
      _hChildPoints, hRawEntry, _hRawPoints, _hRawExitNone,
      _hRawFinal⟩ :=
    StackSchedule.scheduleBlockFuelWithTargets_components hChildSchedule
  have hBuiltEntry : builtEntry = rawRegion.entry := hRawEntry.symm
  subst builtEntry
  obtain ⟨region, loweredBody, lowerRetain, _hAccess, _hLowerFalls,
      hLowerRegions, hLowerBody, hLowerRetain, hLowered⟩ :=
    StackLowering.lowerPointFuel_block_components hLower
  have hRegionList :
      [region] =
        [{ rawRegion with exit? := some exit, finalLayout := targetCtx.layout }] :=
    hLowerRegions.symm.trans (hPointRegions.trans hRawRegions)
  injection hRegionList with hRegion
  subst region
  have hRetainEq : lowerRetain = retain :=
    Option.some.inj (hLowerRetain.symm.trans hPointRetain)
  subst lowerRetain
  obtain ⟨bodyLowered, hBodyLower, hLoweredBody⟩ :=
    StackLowering.lowerBlockFuel_components hLowerBody
  have hLoweredBody' :
      loweredBody.stmts =
        StackLowering.entryTransitionStmts rawRegion.entry ++
          (bodyLowered ++ exit.statements) := by
    simpa [StackLowering.exitStmts] using hLoweredBody
  rw [hLowered] at hCompile
  obtain ⟨blockCode, blockFinalCtx, retainCode, hBlockCompile,
      hRetainCompile, hCode⟩ :=
    Locals.Block.compileOpen_append_components hCompile
  have hBlockStmtCompile :=
    Locals.Block.compileOpen_single_components hBlockCompile
  obtain ⟨regionCode, regionFinalCtx, targetBlock, hRegionCompile, hFinish,
      hBlockCode, hBlockFinal⟩ :=
    Locals.Stmt.compile_block_components hBlockStmtCompile
  subst blockFinalCtx
  have hLoweredBodyStruct :
      loweredBody =
        { stmts :=
            StackLowering.entryTransitionStmts rawRegion.entry ++
              (bodyLowered ++ exit.statements) } := by
    cases loweredBody
    simp_all
  rw [hLoweredBodyStruct] at hRegionCompile
  obtain ⟨entryCode, entryFinalCtx, restCode, hEntryCompile, hRestCompile,
      hRegionCode⟩ :=
    Locals.Block.compileOpen_append_components hRegionCompile
  have hEntrySource : targetCtx.layout = rawRegion.entry.source := by
    exact (AllocationLayout.Transition.build?_sound hEntryBuild).1.symm
  obtain ⟨entryArtifact⟩ :=
    StackTransitionCompilation.Transition.compileArtifact rawRegion.entry
      hEntrySource
  have hEntryPair :=
    Option.some.inj (entryArtifact.compileEq.symm.trans hEntryCompile)
  have hEntryCode :
      entryArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code entryArtifact.cleanup] = entryCode :=
    congrArg Prod.fst hEntryPair
  have hEntryFinal :
      targetCtx.withLayout rawRegion.entry.target = entryFinalCtx :=
    congrArg Prod.snd hEntryPair
  rw [← hEntryFinal] at hRestCompile
  have hRestCompile' :
      Locals.Block.compileOpen
          (targetCtx.withLayout rawRegion.entry.target)
          { stmts := bodyLowered ++ exit.statements } =
        some (restCode, regionFinalCtx) := by
    simpa [List.append_assoc] using hRestCompile
  obtain ⟨bodyCode, bodyFinalCtx, exitCode, hBodyCompile, hExitCompile,
      hRestCode⟩ :=
    Locals.Block.compileOpen_append_components hRestCompile'
  have hBodyPreserves :=
    hBody hChildSchedule (by simpa using hBodyLower) hBodyCompile
  have hBodyLayout : bodyFinalCtx.layout = rawRegion.finalLayout :=
    hBodyPreserves.1
  have hBodyPreservesSelf :
      ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
        (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx body.stmts
        bodyFinalCtx.layout bodyCode :=
    ⟨rfl, hBodyPreserves.2⟩
  have hExitSource : bodyFinalCtx.layout = exit.source := by
    rw [hBodyLayout]
    exact (AllocationLayout.Join.build?_endpoints hExitBuild).1.symm
  obtain ⟨exitArtifact⟩ :=
    StackTransitionCompilation.Join.compileArtifact exit hExitSource
  have hExitPair :=
    Option.some.inj (exitArtifact.compileEq.symm.trans hExitCompile)
  have hExitCode :
      exitArtifact.retainArtifact.promotionCodes.map Expressions.Stmt.code ++
            [Expressions.Stmt.code exitArtifact.retainArtifact.cleanup] ++
          exitArtifact.orderArtifact.promotionCodes.map Expressions.Stmt.code =
        exitCode :=
    congrArg Prod.fst hExitPair
  have hRegionFinal :
      bodyFinalCtx.withLayout exit.target = regionFinalCtx :=
    congrArg Prod.snd hExitPair
  obtain ⟨cleanup, hCleanup, hTargetBlock⟩ :=
    Locals.finishScoped_components hFinish
  have hExitTarget : exit.target = targetCtx.layout :=
    (AllocationLayout.Join.build?_endpoints hExitBuild).2
  have hCleanupEmpty : cleanup = [] := by
    rw [← hRegionFinal, hExitTarget] at hCleanup
    simpa [Locals.Ctx.cleanupTo?, Locals.Ctx.withLayout] using hCleanup
  subst cleanup
  have hCoreCode :
      targetBlock.stmts =
        entryArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code entryArtifact.cleanup] ++ bodyCode ++
          (exitArtifact.retainArtifact.promotionCodes.map Expressions.Stmt.code ++
            [Expressions.Stmt.code exitArtifact.retainArtifact.cleanup] ++
            exitArtifact.orderArtifact.promotionCodes.map Expressions.Stmt.code) ++
          [.code []] := by
    rw [hTargetBlock, hRegionCode, ← hEntryCode, hRestCode, ← hExitCode]
    simp [Locals.codeStmt, List.append_assoc]
  have hControl :
      Locals.Ctx.SameControl targetCtx
        (bodyFinalCtx.withLayout exit.target) :=
    (Locals.Ctx.SameControl.withLayout targetCtx rawRegion.entry.target).trans
      ((Locals.Block.compileOpen_sameControl hBodyCompile).trans
        (Locals.Ctx.SameControl.withLayout bodyFinalCtx exit.target))
  have hRestoredLayout :
      (bodyFinalCtx.withLayout exit.target).layout = targetCtx.layout := by
    simp [Locals.Ctx.withLayout, hExitTarget]
  have hRestoredCtx :
      bodyFinalCtx.withLayout exit.target = targetCtx := by
    cases targetCtx
    cases bodyFinalCtx
    simp [Locals.Ctx.withLayout] at hControl hExitTarget ⊢
    rcases hControl with ⟨hBreak, hContinue, hLeave, hRetc⟩
    simp_all
  obtain ⟨compiledRetainArtifact⟩ :=
    StackTransitionCompilation.RegularTransition.compileArtifact retain hRetainSource
  have hCompiledRetainPair :=
    Option.some.inj
      (compiledRetainArtifact.compileEq.symm.trans hRetainCompile)
  have hCompiledRetainCode :
      compiledRetainArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code compiledRetainArtifact.cleanup] = retainCode :=
    congrArg Prod.fst hCompiledRetainPair
  have hCompiledFinalCtx :
      targetCtx.withLayout retain.schedule.target = finalCtx :=
    congrArg Prod.snd hCompiledRetainPair
  refine ⟨?_, ?_⟩
  · rw [← hCompiledFinalCtx]
    rfl
  unfold ControlPointPreserves
  intro sourceCtx sourceFuel targetFuel suffix returns source target hFuel
    hCtx hInitial
  have hCodeLength := Expressions.TargetFuel.Covers.length_lt hFuel
  have hFinalControl :
      RuntimeCtxCovers sourceCtx
        (bodyFinalCtx.withLayout exit.target) targets returnNames returns :=
    hCtx.ofSameControlLayout hControl hRestoredLayout
  have hScopeCovers :
      ∀ {name : Name}, name ∈ exit.target → name ∈ sourceCtx.scope := by
    intro name hName
    apply hCtx.context.scope
    rwa [hExitTarget] at hName
  have hBlockFuel :
      Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel
        targetBlock.stmts := by
    have h := hFuel
    rw [hCode, hBlockCode] at h
    exact Expressions.TargetFuel.Covers.head_of_append h
  have hRegionWithEmptyFuel := hBlockFuel
  rw [hCoreCode] at hRegionWithEmptyFuel
  have hRegionFuel :=
    Expressions.TargetFuel.Covers.head_of_append hRegionWithEmptyFuel
  have hRegionRun :=
    controlScheduledRegion returnNames sourceProgram targetProgram targets sourceCtx
      targetCtx bodyFinalCtx body bodyCode rawRegion.entry entryArtifact exit
      exitArtifact sourceFuel targetFuel (hBodyPreservesSelf.at sourceFuel)
      hCtx hEntrySource
      hFinalControl hScopeCovers
      (by simpa [List.append_assoc] using hRegionFuel) hInitial
  have hRegionEmptyFuel :
      (entryArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code entryArtifact.cleanup] ++ bodyCode ++
          (exitArtifact.retainArtifact.promotionCodes.map Expressions.Stmt.code ++
            [Expressions.Stmt.code exitArtifact.retainArtifact.cleanup] ++
            exitArtifact.orderArtifact.promotionCodes.map Expressions.Stmt.code)).length +
        1 < targetFuel := by
    have hLength :=
      Expressions.TargetFuel.Covers.length_lt hRegionWithEmptyFuel
    simpa only [List.length_append, List.length_map, List.length_cons,
      List.length_nil, Nat.add_zero, Nat.add_assoc] using hLength
  have hWithEmpty :=
    controlAppendEmptyCodeForward targetProgram targets returnNames
      (bodyFinalCtx.withLayout exit.target) targetFuel hRegionEmptyFuel hRegionRun
  rw [hRestoredCtx] at hWithEmpty
  have hWholeFuel :
      targetBlock.stmts.length + retain.schedule.discards.length + 1 <
        targetFuel := by
    rw [hCode, hBlockCode, ← hCompiledRetainCode] at hCodeLength
    simp only [List.length_append, List.length_map, List.length_cons,
      List.length_nil] at hCodeLength
    rw [compiledRetainArtifact.codes.code_length] at hCodeLength
    omega
  obtain ⟨retainArtifact, hWholeRun⟩ :=
    controlThenTransitionForward targetProgram targets returnNames
      targetCtx retain targetFuel hRetainSource
      hWholeFuel (by simpa [hCoreCode, List.append_assoc] using hWithEmpty)
  have hRetainPair :=
    Option.some.inj (retainArtifact.compileEq.symm.trans hRetainCompile)
  have hRetainCode :
      retainArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code retainArtifact.cleanup] = retainCode :=
    congrArg Prod.fst hRetainPair
  have hFinalCtx :
      targetCtx.withLayout retain.schedule.target = finalCtx :=
    congrArg Prod.snd hRetainPair
  rw [← hFinalCtx]
  rw [Functions.InteractionSemantics.Stmt.openRun_block]
  simpa [hCode, hBlockCode, hCoreCode, hRetainCode, List.append_assoc] using
    hWholeRun

theorem ifPoint_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel : Nat)
    (cond : Functions.Expr 1) (body : Functions.Block)
    (fact : AllocationLivenessFacts.Point)
    (rawPoint point : StackSchedule.Point)
    (retain : AllocationLayout.RegularTransition)
    (targetCtx finalCtx : Locals.Ctx)
    (lowered : List Locals.Stmt) (code : List Expressions.Stmt)
    {sourceEnv : List Name}
    (hScoped : Functions.Scope.ExprScoped sourceEnv cond)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported cond)
    (hSchedule :
      StackSchedule.scheduleStmtFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout (.if_ cond body) fact = some rawPoint)
    (hPointBefore : point.beforeLayout = targetCtx.layout)
    (hPointRegions : point.regions = rawPoint.regions)
    (hPointRetain : point.retain? = some retain)
    (hRetainSource : targetCtx.layout = retain.source)
    (hLower :
      StackLowering.lowerPointFuel lowerFuel lowerCtx (.if_ cond body) point =
        some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx))
    (hBody :
      ∀ {bodyFacts rawRegion bodyLowered bodyCode bodyFinalCtx},
        StackSchedule.scheduleBlockFuelWithTargets targets (scheduleFuel - 1)
            (StackSchedule.layoutSet targetCtx.layout) targetCtx.layout
            body bodyFacts = some rawRegion →
        StackLowering.lowerStmtListFuel ((lowerFuel - 1) - 1) lowerCtx
            body.stmts rawRegion.points = some bodyLowered →
        Locals.Block.compileOpen
            (targetCtx.withLayout rawRegion.entry.target)
            { stmts := bodyLowered } = some (bodyCode, bodyFinalCtx) →
        ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
          (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx body.stmts
          rawRegion.finalLayout bodyCode) :
    CompiledControlPoint sourceProgram targetProgram targets returnNames targetCtx finalCtx
      (.if_ cond body) code retain.schedule.target := by
  obtain ⟨bodyFacts, rawRegion, closedRegion, _hFacts, hChildSchedule, hClose,
      _hBefore, _hStatement, _hRawExit, _hRawRetain, hRawRegions,
      _hFalls⟩ :=
    StackSchedule.scheduleStmtFuelWithTargets_if_components hSchedule
  obtain ⟨region, loweredBody, lowerRetain, hAccess, _hLowerFalls,
      hLowerRegions, hLowerBody, hLowerRetain, hLowered⟩ :=
    StackLowering.lowerPointFuel_if_components hLower
  have hRegionList :
      [region] = [closedRegion] :=
    hLowerRegions.symm.trans (hPointRegions.trans hRawRegions)
  injection hRegionList with hRegion
  subst region
  have hRetainEq : lowerRetain = retain :=
    Option.some.inj (hLowerRetain.symm.trans hPointRetain)
  subst lowerRetain
  have hCondAccess :
      StackAccess.Expr.check? targetCtx.layout 0 cond = some () := by
    simpa [StackLowering.pointAccess?, hPointBefore] using hAccess
  have hCondScoped :=
    StackAccess.Expr.scoped_of_check hCondAccess hScoped
  rw [hLowered] at hCompile
  obtain ⟨ifCode, ifFinalCtx, retainCode, hIfCompile,
      hRetainCompile, hCode⟩ :=
    Locals.Block.compileOpen_append_components hCompile
  have hIfStmtCompile :=
    Locals.Block.compileOpen_single_components hIfCompile
  obtain ⟨condCode, regionCode, regionFinalCtx, targetBody,
      hCondCompile, hRegionCompile, hFinish, hIfCode, hIfFinal⟩ :=
    Locals.Stmt.compile_if_components hIfStmtCompile
  subst ifFinalCtx
  have hTargetBodyPreserves :
      ControlLexicalBlockPreserves sourceProgram targetProgram targets returnNames
        targetCtx targetCtx body targetBody := by
    rcases StackSchedule.Region.close?_components hClose with hNormal | hAbrupt
    · rcases hNormal with ⟨_hRawFalls, exit, hExitBuild, hClosed⟩
      subst closedRegion
      obtain ⟨bodyCode, bodyFinalCtx, entryArtifact, exitArtifact,
          hBodyPreserves, hRegionCode, hRegionFinal, hRestoredCtx,
          hEntrySource⟩ :=
        compiledScheduledRegion_of_compilers returnNames sourceProgram
          targetProgram lowerCtx targets scheduleFuel lowerFuel body bodyFacts
          rawRegion exit targetCtx regionFinalCtx loweredBody regionCode
          hChildSchedule hExitBuild hLowerBody hRegionCompile
          (fun hBodyLower hBodyCompile =>
            hBody hChildSchedule hBodyLower hBodyCompile)
      have hBodyPreservesSelf :
          ControlScheduledListPreserves sourceProgram targetProgram targets
            returnNames (targetCtx.withLayout rawRegion.entry.target)
            bodyFinalCtx body.stmts bodyFinalCtx.layout bodyCode :=
        ⟨rfl, hBodyPreserves.2⟩
      have hRegionCtx : regionFinalCtx = targetCtx :=
        hRegionFinal.trans hRestoredCtx
      have hTargetBodyFinished :
          Locals.finishScoped targetCtx regionFinalCtx regionCode =
            some targetBody := by
        rcases Locals.finishScopedOrAbrupt_components hFinish with
          hFinished | hFallback
        · exact hFinished
        · rw [hRegionCtx] at hFallback
          simp [Locals.finishScoped, Locals.Ctx.cleanupTo?] at hFallback
      obtain ⟨cleanup, hCleanup, hTargetBody⟩ :=
        Locals.finishScoped_components hTargetBodyFinished
      have hCleanupEmpty : cleanup = [] := by
        rw [hRegionCtx] at hCleanup
        simpa [Locals.Ctx.cleanupTo?] using hCleanup
      subst cleanup
      have hTargetBodyCode :
          targetBody.stmts =
            ((entryArtifact.promotionCodes.map Expressions.Stmt.code ++
                [Expressions.Stmt.code entryArtifact.cleanup]) ++
              (bodyCode ++
                (exitArtifact.retainArtifact.promotionCodes.map
                      Expressions.Stmt.code ++
                  [Expressions.Stmt.code exitArtifact.retainArtifact.cleanup] ++
                  exitArtifact.orderArtifact.promotionCodes.map
                    Expressions.Stmt.code))) ++ [.code []] := by
        rw [hTargetBody, hRegionCode]
        simp [Locals.codeStmt, List.append_assoc]
      have hExitTarget : exit.target = targetCtx.layout := by
        have h := congrArg Locals.Ctx.layout hRestoredCtx
        simpa [Locals.Ctx.withLayout] using h
      intro sourceCtx sourceFuel targetFuel suffix returns source target hFuel
        hCtx hInitial
      have hFinalControl :
          RuntimeCtxCovers sourceCtx
            (bodyFinalCtx.withLayout exit.target) targets returnNames returns := by
        rw [hRestoredCtx]
        exact hCtx
      have hScopeCovers :
          ∀ {name : Name}, name ∈ exit.target → name ∈ sourceCtx.scope := by
        intro name hName
        apply hCtx.context.scope
        rwa [hExitTarget] at hName
      have hRun :=
        controlScheduledRegionAsBlock returnNames sourceProgram targetProgram
          targets sourceCtx targetCtx bodyFinalCtx body bodyCode rawRegion.entry
          entryArtifact exit exitArtifact targetBody sourceFuel targetFuel
          (hBodyPreservesSelf.at sourceFuel) hCtx hEntrySource hFinalControl
          hScopeCovers hTargetBodyCode hFuel hInitial
      rwa [hRestoredCtx] at hRun
    · rcases hAbrupt with ⟨hRawFalls, hClosed⟩
      subst closedRegion
      obtain ⟨bodyCode, bodyFinalCtx, entryArtifact, _hBodyPreserves,
          hRegionCode, hRegionFinal, _hEntrySource, hGrowing⟩ :=
        compiledGrowingRegion_of_compilers returnNames sourceProgram
          targetProgram lowerCtx targets scheduleFuel lowerFuel body bodyFacts
          rawRegion targetCtx regionFinalCtx loweredBody regionCode
          hChildSchedule hLowerBody hRegionCompile
          (fun hBodyLower hBodyCompile =>
            hBody hChildSchedule hBodyLower hBodyCompile)
      have hHasExit : Functions.StmtList.hasDirectExit body.stmts = true :=
        StackSchedule.scheduleBlockFuelWithTargets_hasDirectExit_of_not_fallsThrough
          hChildSchedule hRawFalls
      have hGrowingRebased :
          ControlBlockPreserves sourceProgram targetProgram targets returnNames
            targetCtx targetCtx body { stmts := regionCode } :=
        hGrowing.rebase_of_hasDirectExit hHasExit
      intro sourceCtx sourceFuel targetFuel suffix returns source target hFuel
        hCtx hInitial
      have hNonregular :=
        Functions.InteractionSemantics.Abrupt.block_allDone_of_hasDirectExit
          sourceProgram sourceCtx sourceFuel body source hHasExit
      rcases Locals.finishScopedOrAbrupt_components hFinish with
        hFinished | hFallback
      · obtain ⟨cleanup, _hCleanup, hTargetBody⟩ :=
          Locals.finishScoped_components hFinished
        have hTargetBodyStmts :
            targetBody.stmts = regionCode ++ Locals.codeStmt cleanup := by
          simpa using congrArg Expressions.Block.stmts hTargetBody
        have hFuel' := hFuel
        rw [hTargetBodyStmts] at hFuel'
        have hPrefixFuel := Expressions.TargetFuel.Covers.head_of_append hFuel'
        have hPrefixRun :=
          hGrowingRebased sourceCtx sourceFuel targetFuel hPrefixFuel hCtx hInitial
        rw [hTargetBody]
        have hAppended :=
          controlAppendUnreachableForward
            (suffixCode := Locals.codeStmt cleanup) targetProgram targets
            returnNames targetCtx targetFuel hPrefixRun hNonregular
        exact controlOpenBlockAsStmt_of_nonregular hAppended hNonregular
      · have hTargetBody : targetBody = { stmts := regionCode } :=
          hFallback.2.2
        subst targetBody
        have hPrefixRun :=
          hGrowingRebased sourceCtx sourceFuel targetFuel hFuel hCtx hInitial
        exact controlOpenBlockAsStmt_of_nonregular hPrefixRun hNonregular
  obtain ⟨compiledRetainArtifact⟩ :=
    StackTransitionCompilation.RegularTransition.compileArtifact retain hRetainSource
  have hCompiledRetainPair :=
    Option.some.inj
      (compiledRetainArtifact.compileEq.symm.trans hRetainCompile)
  have hCompiledRetainCode :
      compiledRetainArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code compiledRetainArtifact.cleanup] = retainCode :=
    congrArg Prod.fst hCompiledRetainPair
  have hCompiledFinalCtx :
      targetCtx.withLayout retain.schedule.target = finalCtx :=
    congrArg Prod.snd hCompiledRetainPair
  refine ⟨?_, ?_⟩
  · rw [← hCompiledFinalCtx]
    rfl
  unfold ControlPointPreserves
  intro sourceCtx sourceFuel targetFuel suffix returns source target hFuel
    hCtx hInitial
  cases sourceFuel with
  | zero =>
      unfold Functions.InteractionSemantics.Stmt.openRun
        Functions.InteractionSemantics.stateModel
      simp only [Functions.Source.Effectful.Control.Stmt.run]
      exact Simulation.Interaction.ForwardRel.truncated rfl
  | succ sourceFuel =>
      have hFuel' :
          Expressions.TargetFuel.Covers targetProgram (sourceFuel + 1)
            targetFuel (.if_ (.code condCode) targetBody :: retainCode) := by
        have h := hFuel
        rw [hCode, hIfCode] at h
        simpa [Nat.succ_eq_add_one] using h
      have hTargetFuel : 2 ≤ targetFuel := by
        have hLength := Expressions.TargetFuel.Covers.length_lt hFuel'
        simp only [List.length_cons] at hLength
        omega
      have hTargetBodyFuel :=
        Expressions.TargetFuel.Covers.if_body_after_two hFuel'
      have hIfRun :=
        controlIf sourceProgram targetProgram targets returnNames sourceCtx targetCtx
          sourceFuel targetFuel cond body condCode targetBody hTargetFuel hCtx
          hCondScoped hSupported hCondCompile hInitial (by
            intro sourceAfter targetAfter hAfter
            exact hTargetBodyPreserves sourceCtx sourceFuel (targetFuel - 2)
              hTargetBodyFuel hCtx hAfter)
      have hCodeLength := Expressions.TargetFuel.Covers.length_lt hFuel'
      have hWholeFuel :
          [Expressions.Stmt.if_ (.code condCode) targetBody].length +
              retain.schedule.discards.length + 1 < targetFuel := by
        rw [← hCompiledRetainCode] at hCodeLength
        simp only [List.length_cons, List.length_append, List.length_map,
          List.length_nil] at hCodeLength ⊢
        rw [compiledRetainArtifact.codes.code_length] at hCodeLength
        omega
      obtain ⟨retainArtifact, hWholeRun⟩ :=
        controlThenTransitionForward targetProgram targets returnNames targetCtx retain
          targetFuel hRetainSource hWholeFuel hIfRun
      have hRetainPair :=
        Option.some.inj (retainArtifact.compileEq.symm.trans hRetainCompile)
      have hRetainCode :
          retainArtifact.promotionCodes.map Expressions.Stmt.code ++
              [Expressions.Stmt.code retainArtifact.cleanup] = retainCode :=
        congrArg Prod.fst hRetainPair
      have hFinalCtx :
          targetCtx.withLayout retain.schedule.target = finalCtx :=
        congrArg Prod.snd hRetainPair
      rw [← hFinalCtx]
      simpa [hCode, hIfCode, hRetainCode] using hWholeRun

theorem switchPoint_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel : Nat)
    (scrutinee : Functions.Expr 1)
    (cases : List (Word × Functions.Block))
    (defaultBody : Option Functions.Block)
    (fact : AllocationLivenessFacts.Point)
    (rawPoint point : StackSchedule.Point)
    (retain : AllocationLayout.RegularTransition)
    (targetCtx finalCtx : Locals.Ctx)
    (lowered : List Locals.Stmt) (code : List Expressions.Stmt)
    {sourceEnv : List Name}
    (hScoped : Functions.Scope.ExprScoped sourceEnv scrutinee)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported scrutinee)
    (hSchedule :
      StackSchedule.scheduleStmtFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout (.switch scrutinee cases defaultBody) fact =
        some rawPoint)
    (hPointBefore : point.beforeLayout = targetCtx.layout)
    (hPointRegions : point.regions = rawPoint.regions)
    (hPointRetain : point.retain? = some retain)
    (hRetainSource : targetCtx.layout = retain.source)
    (hLower :
      StackLowering.lowerPointFuel lowerFuel lowerCtx
          (.switch scrutinee cases defaultBody) point = some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx))
    (hBody :
      ∀ {body bodyFacts rawRegion bodyLowered bodyCode bodyFinalCtx},
        StackSchedule.scheduleBlockFuelWithTargets targets (scheduleFuel - 1)
            (StackSchedule.layoutSet targetCtx.layout) targetCtx.layout
            body bodyFacts = some rawRegion →
        StackLowering.lowerStmtListFuel ((lowerFuel - 1) - 1) lowerCtx
            body.stmts rawRegion.points = some bodyLowered →
        Locals.Block.compileOpen
            (targetCtx.withLayout rawRegion.entry.target)
            { stmts := bodyLowered } = some (bodyCode, bodyFinalCtx) →
        ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
          (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx body.stmts
          rawRegion.finalLayout bodyCode) :
    CompiledControlPoint sourceProgram targetProgram targets returnNames targetCtx finalCtx
      (.switch scrutinee cases defaultBody) code retain.schedule.target := by
  obtain ⟨caseRegions, defaultRegions, hCaseSchedule, hDefaultSchedule,
      _hRawBefore, _hRawStatement, _hRawRetain, hRawRegions, _hRawFalls⟩ :=
    StackSchedule.scheduleStmtFuelWithTargets_switch_components hSchedule
  obtain ⟨loweredCases, loweredDefault, lowerRetain, hAccess, _hLowerFalls,
      hCaseLower, hDefaultLower, hLowerRetain, hLowered⟩ :=
    StackLowering.lowerPointFuel_switch_components hLower
  have hRetainEq : lowerRetain = retain :=
    Option.some.inj (hLowerRetain.symm.trans hPointRetain)
  subst lowerRetain
  have hCaseRegionLength : caseRegions.length = cases.length :=
    StackSchedule.scheduleCaseRegionsFuelWithTargets_length hCaseSchedule
  have hPointRegionEq : point.regions = caseRegions ++ defaultRegions :=
    hPointRegions.trans hRawRegions
  have hCaseTake : point.regions.take cases.length = caseRegions := by
    rw [hPointRegionEq, ← hCaseRegionLength]
    simp
  have hDefaultDrop : point.regions.drop cases.length = defaultRegions := by
    rw [hPointRegionEq, ← hCaseRegionLength]
    simp
  rw [hCaseTake] at hCaseLower
  rw [hDefaultDrop] at hDefaultLower
  have hScrutineeAccess :
      StackAccess.Expr.check? targetCtx.layout 0 scrutinee = some () := by
    simpa [StackLowering.pointAccess?, hPointBefore] using hAccess
  have hScrutineeScoped :=
    StackAccess.Expr.scoped_of_check hScrutineeAccess hScoped
  rw [hLowered] at hCompile
  obtain ⟨switchCode, switchFinalCtx, retainCode, hSwitchCompile,
      hRetainCompile, hCode⟩ :=
    Locals.Block.compileOpen_append_components hCompile
  have hSwitchStmtCompile :=
    Locals.Block.compileOpen_single_components hSwitchCompile
  obtain ⟨scrutineeCode, compiledCases, compiledDefault,
      hScrutineeCompile, hCasesCompile, hDefaultCompile, hSwitchCode,
      hSwitchFinal⟩ :=
    Locals.Stmt.compile_switch_components hSwitchStmtCompile
  subst switchFinalCtx
  have hDefaultRel :=
    switchDefaultRel_of_compilers returnNames sourceProgram targetProgram lowerCtx targets
      scheduleFuel lowerFuel targetCtx defaultBody
      (fact.regions.drop cases.length) defaultRegions loweredDefault
      compiledDefault hDefaultSchedule hDefaultLower hDefaultCompile
      (fun hChildSchedule hChildLower hChildCompile =>
        hBody hChildSchedule hChildLower hChildCompile)
  have hBranches :=
    switchCasesRel_of_compilers returnNames sourceProgram targetProgram lowerCtx targets
      scheduleFuel lowerFuel targetCtx cases defaultBody
      (fact.regions.take cases.length) caseRegions loweredCases compiledCases
      compiledDefault hCaseSchedule hCaseLower hCasesCompile
      (fun hChildSchedule hChildLower hChildCompile =>
        hBody hChildSchedule hChildLower hChildCompile)
      hDefaultRel
  obtain ⟨compiledRetainArtifact⟩ :=
    StackTransitionCompilation.RegularTransition.compileArtifact retain hRetainSource
  have hCompiledRetainPair :=
    Option.some.inj
      (compiledRetainArtifact.compileEq.symm.trans hRetainCompile)
  have hCompiledRetainCode :
      compiledRetainArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code compiledRetainArtifact.cleanup] = retainCode :=
    congrArg Prod.fst hCompiledRetainPair
  have hCompiledFinalCtx :
      targetCtx.withLayout retain.schedule.target = finalCtx :=
    congrArg Prod.snd hCompiledRetainPair
  refine ⟨?_, ?_⟩
  · rw [← hCompiledFinalCtx]
    rfl
  unfold ControlPointPreserves
  intro sourceCtx sourceFuel targetFuel suffix returns source target hFuel hCtx
    hInitial
  cases sourceFuel with
  | zero =>
      unfold Functions.InteractionSemantics.Stmt.openRun
        Functions.InteractionSemantics.stateModel
      simp only [Functions.Source.Effectful.Control.Stmt.run]
      exact Simulation.Interaction.ForwardRel.truncated rfl
  | succ sourceFuel =>
      have hFuel' :
          Expressions.TargetFuel.Covers targetProgram (sourceFuel + 1)
            targetFuel
            (.switch (.code scrutineeCode) compiledCases compiledDefault ::
              retainCode) := by
        have h := hFuel
        rw [hCode, hSwitchCode] at h
        simpa [Nat.succ_eq_add_one] using h
      have hTargetFuel : 2 ≤ targetFuel := by
        have hLength := Expressions.TargetFuel.Covers.length_lt hFuel'
        simp only [List.length_cons] at hLength
        omega
      have hBranchPreserves :=
        switchBranchRelToPreserve returnNames sourceProgram targetProgram targets sourceCtx
          targetCtx sourceFuel targetFuel scrutinee cases defaultBody
          scrutineeCode compiledCases compiledDefault retainCode
          (suffix := suffix) (returns := returns) hFuel' hCtx hBranches
      have hSwitchRun :=
        controlSwitch sourceProgram targetProgram targets returnNames sourceCtx targetCtx
          sourceFuel targetFuel scrutinee cases defaultBody scrutineeCode
          compiledCases compiledDefault hTargetFuel hCtx hScrutineeScoped
          hSupported hScrutineeCompile hInitial hBranchPreserves
      have hCodeLength := Expressions.TargetFuel.Covers.length_lt hFuel'
      have hWholeFuel :
          [Expressions.Stmt.switch (.code scrutineeCode) compiledCases
              compiledDefault].length +
              retain.schedule.discards.length + 1 < targetFuel := by
        rw [← hCompiledRetainCode] at hCodeLength
        simp only [List.length_cons, List.length_append, List.length_map,
          List.length_nil] at hCodeLength ⊢
        rw [compiledRetainArtifact.codes.code_length] at hCodeLength
        omega
      obtain ⟨retainArtifact, hWholeRun⟩ :=
        controlThenTransitionForward targetProgram targets returnNames targetCtx retain
          targetFuel hRetainSource hWholeFuel hSwitchRun
      have hRetainPair :=
        Option.some.inj (retainArtifact.compileEq.symm.trans hRetainCompile)
      have hRetainCode :
          retainArtifact.promotionCodes.map Expressions.Stmt.code ++
              [Expressions.Stmt.code retainArtifact.cleanup] = retainCode :=
        congrArg Prod.fst hRetainPair
      have hFinalCtx :
          targetCtx.withLayout retain.schedule.target = finalCtx :=
        congrArg Prod.snd hRetainPair
      rw [← hFinalCtx]
      simpa [hCode, hSwitchCode, hRetainCode] using hWholeRun

theorem forPoint_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel : Nat)
    (init : Functions.Block) (cond : Functions.Expr 1)
    (post body : Functions.Block)
    (fact : AllocationLivenessFacts.Point)
    (rawPoint point : StackSchedule.Point)
    (retain : AllocationLayout.RegularTransition)
    (targetCtx finalCtx : Locals.Ctx)
    (lowered : List Locals.Stmt) (code : List Expressions.Stmt)
    {sourceEnv : List Name}
    (hScoped : Functions.Scope.ExprScoped sourceEnv cond)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported cond)
    (hSchedule :
      StackSchedule.scheduleStmtFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout (.for_ init cond post body) fact = some rawPoint)
    (hPointBefore : point.beforeLayout = targetCtx.layout)
    (hPointRegions : point.regions = rawPoint.regions)
    (hPointRetain : point.retain? = some retain)
    (hRetainSource : targetCtx.layout = retain.source)
    (hLower :
      StackLowering.lowerPointFuel lowerFuel lowerCtx
          (.for_ init cond post body) point = some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx))
    (hChild :
      ∀ {childTargets : StackSchedule.ControlTargets}
        {child : Functions.Block} {childCtx : Locals.Ctx}
        {childFacts rawRegion childLowered childCode childFinalCtx},
        StackSchedule.scheduleBlockFuelWithTargets childTargets
            (scheduleFuel - 1) (StackSchedule.layoutSet childCtx.layout)
            childCtx.layout child childFacts = some rawRegion →
        StackLowering.lowerStmtListFuel ((lowerFuel - 1) - 1) lowerCtx
            child.stmts rawRegion.points = some childLowered →
        Locals.Block.compileOpen
            (childCtx.withLayout rawRegion.entry.target)
            { stmts := childLowered } = some (childCode, childFinalCtx) →
        ControlScheduledListPreserves sourceProgram targetProgram childTargets
          returnNames
          (childCtx.withLayout rawRegion.entry.target) childFinalCtx child.stmts
          rawRegion.finalLayout childCode) :
    CompiledControlPoint sourceProgram targetProgram targets returnNames targetCtx finalCtx
      (.for_ init cond post body) code retain.schedule.target := by
  obtain ⟨initFacts, postFacts, bodyFacts, _loopFacts, rawInitRegion,
      rawPostRegion, rawBodyRegion, initExit, postExit, bodyExit, _hFacts,
      _hLoop, hInitSchedule, hInitExit, hPostSchedule, hBodySchedule,
      hPostExit, hBodyExit, _hRawBefore, _hRawStatement, _hRawRetain,
      hRawRegions, _hRawFalls⟩ :=
    StackSchedule.scheduleStmtFuelWithTargets_for_components hSchedule
  obtain ⟨initRegion, postRegion, bodyRegion, loweredInit, loweredPost,
      loweredBody, lowerRetain, hAccess, _hLowerFalls, hLowerRegions,
      hLowerInit, hLowerPost, hLowerBody, hLowerRetain, hLowered⟩ :=
    StackLowering.lowerPointFuel_for_components hLower
  have hRegionList :
      [initRegion, postRegion, bodyRegion] =
        [{ rawInitRegion with
            exit? := some initExit,
            finalLayout := StackSchedule.loopBaseline targetCtx.layout
              rawInitRegion.finalLayout },
         { rawPostRegion with
            exit? := some postExit,
            finalLayout := StackSchedule.loopBaseline targetCtx.layout
              rawInitRegion.finalLayout },
         { rawBodyRegion with
            exit? := some bodyExit,
            finalLayout := StackSchedule.loopBaseline targetCtx.layout
              rawInitRegion.finalLayout }] :=
    hLowerRegions.symm.trans (hPointRegions.trans hRawRegions)
  simp only [List.cons.injEq, and_true] at hRegionList
  rcases hRegionList with ⟨hInitRegion, hPostRegion, hBodyRegion⟩
  subst initRegion
  subst postRegion
  subst bodyRegion
  have hRetainEq : lowerRetain = retain :=
    Option.some.inj (hLowerRetain.symm.trans hPointRetain)
  subst lowerRetain
  rw [hLowered] at hCompile
  obtain ⟨forCode, forFinalCtx, retainCode, hForCompile, hRetainCompile,
      hCode⟩ :=
    Locals.Block.compileOpen_append_components hCompile
  have hForStmtCompile :=
    Locals.Block.compileOpen_single_components hForCompile
  obtain ⟨initCode, initCtx, condCode, postCode, postCtx, compiledPost,
      bodyCode, bodyCtx, compiledBody, outerCleanup, hInitCompile,
      hCondCompile, hPostCompile, hFinishPost, hBodyCompile, hFinishBody,
      hOuterCleanup, hForCode, hForFinal⟩ :=
    Locals.Stmt.compile_for_components hForStmtCompile
  subst forFinalCtx
  have hInitExitTarget :
      initExit.target =
        StackSchedule.loopBaseline targetCtx.layout
          rawInitRegion.finalLayout :=
    (AllocationLayout.Join.build?_endpoints hInitExit).2
  have hInitExit' :
      AllocationLayout.Join.build? rawInitRegion.finalLayout
          initExit.target = some initExit := by
    rw [hInitExitTarget]
    exact hInitExit
  obtain ⟨_initBodyCode, initBodyFinalCtx, _initEntryArtifact,
      _initExitArtifact, hInitPreserves, _hInitBodyLayout, hInitFinal,
      _hInitEntrySource⟩ :=
    compiledOpenRegion_of_compilers returnNames sourceProgram targetProgram lowerCtx {}
      scheduleFuel lowerFuel init initFacts rawInitRegion initExit
      targetCtx.withoutLoopControl initCtx loweredInit initCode
      (by simpa [Locals.Ctx.withoutLoopControl] using hInitSchedule)
      hInitExit' (by simpa [hInitExitTarget] using hLowerInit) hInitCompile
      (fun hChildLower hChildCompile =>
        hChild (childTargets := {}) (childCtx := targetCtx.withoutLoopControl)
          (by simpa [Locals.Ctx.withoutLoopControl] using hInitSchedule)
          hChildLower hChildCompile)
  rw [← hInitFinal] at hInitPreserves
  have hInitLayout :
      initCtx.layout =
        StackSchedule.loopBaseline targetCtx.layout
          rawInitRegion.finalLayout := by
    rw [hInitFinal]
    simp [Locals.Ctx.withLayout, hInitExitTarget]
  have hCondAccess :
      StackAccess.Expr.check?
          (StackSchedule.loopBaseline targetCtx.layout
            rawInitRegion.finalLayout) 0 cond = some () := by
    simpa [StackLowering.pointAccess?, hLowerRegions] using hAccess
  have hCondAccess' :
      StackAccess.Expr.check? initCtx.layout 0 cond = some () := by
    rw [hInitLayout]
    exact hCondAccess
  have hCondScoped :=
    StackAccess.Expr.scoped_of_check hCondAccess' hScoped
  have hPostSchedule' :
      StackSchedule.scheduleBlockFuelWithTargets {} (scheduleFuel - 1)
          (StackSchedule.layoutSet initCtx.withoutLoopControl.layout)
          initCtx.withoutLoopControl.layout post postFacts =
        some rawPostRegion := by
    simpa [Locals.Ctx.withoutLoopControl, hInitLayout] using hPostSchedule
  have hPostBranch :=
    compiledSwitchBranch_of_compilers returnNames sourceProgram targetProgram lowerCtx {}
      scheduleFuel lowerFuel post postFacts rawPostRegion postExit
      initCtx.withoutLoopControl postCtx loweredPost postCode compiledPost
      hPostSchedule'
      (by simpa [Locals.Ctx.withoutLoopControl, hInitLayout] using hPostExit)
      (by simpa [Locals.Ctx.withoutLoopControl, hInitLayout] using hLowerPost)
      hPostCompile hFinishPost
      (fun hChildLower hChildCompile =>
        hChild (childTargets := {}) (childCtx := initCtx.withoutLoopControl)
          hPostSchedule' hChildLower hChildCompile)
  have hPostPoint := hPostBranch.toPoint
  have hBodySchedule' :
      StackSchedule.scheduleBlockFuelWithTargets
          { brk? := some initCtx.layout, cont? := some initCtx.layout }
          (scheduleFuel - 1)
          (StackSchedule.layoutSet
            (initCtx.withLoopControl initCtx.layout.length).layout)
          (initCtx.withLoopControl initCtx.layout.length).layout body
          bodyFacts = some rawBodyRegion := by
    simpa [Locals.Ctx.withLoopControl, hInitLayout] using hBodySchedule
  have hBodyExit' :
      AllocationLayout.Join.build? rawBodyRegion.finalLayout initCtx.layout =
        some bodyExit := by
    rw [hInitLayout]
    exact hBodyExit
  have hBodyBranch :=
    compiledSwitchBranch_of_compilers returnNames sourceProgram targetProgram lowerCtx
      { brk? := some initCtx.layout, cont? := some initCtx.layout }
      scheduleFuel lowerFuel body bodyFacts rawBodyRegion bodyExit
      (initCtx.withLoopControl initCtx.layout.length) bodyCtx loweredBody
      bodyCode compiledBody hBodySchedule' hBodyExit'
      (by simpa [Locals.Ctx.withLoopControl, hInitLayout] using hLowerBody)
      hBodyCompile
      hFinishBody
      (fun hChildLower hChildCompile =>
        hChild
          (childTargets :=
            { brk? := some initCtx.layout, cont? := some initCtx.layout })
          (childCtx := initCtx.withLoopControl initCtx.layout.length)
          hBodySchedule' hChildLower hChildCompile)
  have hBodyPoint := hBodyBranch.toPoint
  have hOuterLayout : ∃ pre, initCtx.layout = pre ++ targetCtx.layout := by
    rw [hInitLayout]
    exact StackSchedule.loopBaseline_suffix _ _
  have hForPreserves :=
    controlFor sourceProgram targetProgram targets returnNames targetCtx initCtx init cond
      condCode post body { stmts := initCode } compiledPost compiledBody
      outerCleanup hOuterLayout hOuterCleanup hCondScoped hSupported
      hCondCompile hInitPreserves hBodyPoint hPostPoint
  obtain ⟨compiledRetainArtifact⟩ :=
    StackTransitionCompilation.RegularTransition.compileArtifact retain hRetainSource
  have hCompiledRetainPair :=
    Option.some.inj
      (compiledRetainArtifact.compileEq.symm.trans hRetainCompile)
  have hCompiledRetainCode :
      compiledRetainArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code compiledRetainArtifact.cleanup] = retainCode :=
    congrArg Prod.fst hCompiledRetainPair
  have hCompiledFinalCtx :
      targetCtx.withLayout retain.schedule.target = finalCtx :=
    congrArg Prod.snd hCompiledRetainPair
  refine ⟨?_, ?_⟩
  · rw [← hCompiledFinalCtx]
    rfl
  unfold ControlPointPreserves
  intro sourceCtx sourceFuel targetFuel suffix returns source target hFuel hCtx
    hInitial
  have hFuel' :
      Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel
        (forCode ++ retainCode) := by
    rw [← hCode]
    exact hFuel
  have hForFuel := Expressions.TargetFuel.Covers.head_of_append hFuel'
  have hForRun := hForPreserves sourceCtx sourceFuel targetFuel
    (by simpa [hForCode] using hForFuel) hCtx hInitial
  have hForRun' :
      Simulation.Interaction.ForwardRel FuelTruncated
        (ControlOpenOutcomeRel targets returnNames targetCtx suffix returns)
        (Functions.InteractionSemantics.Stmt.openRun sourceProgram sourceCtx
          sourceFuel (.for_ init cond post body) source)
        (Expressions.InteractionSemantics.Block.openRun targetProgram
          targetFuel { stmts := forCode } target) := by
    simpa [hForCode] using hForRun
  have hLength := hFuel'.length_lt
  have hWholeFuel :
      forCode.length + retain.schedule.discards.length + 1 < targetFuel := by
    rw [← hCompiledRetainCode] at hLength
    simp only [List.length_append, List.length_map, List.length_cons,
      List.length_nil] at hLength
    rw [compiledRetainArtifact.codes.code_length] at hLength
    omega
  obtain ⟨retainArtifact, hWholeRun⟩ :=
    controlThenTransitionForward targetProgram targets returnNames targetCtx retain
      targetFuel hRetainSource hWholeFuel hForRun'
  have hRetainPair :=
    Option.some.inj (retainArtifact.compileEq.symm.trans hRetainCompile)
  have hRetainCode :
      retainArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code retainArtifact.cleanup] = retainCode :=
    congrArg Prod.fst hRetainPair
  have hFinalCtx :
      targetCtx.withLayout retain.schedule.target = finalCtx :=
    congrArg Prod.snd hRetainPair
  rw [← hFinalCtx]
  simpa [hCode, hForCode, hRetainCode] using hWholeRun

theorem controlFallthroughCons_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel : Nat)
    (stmt : Functions.Stmt) (rest : List Functions.Stmt)
    (fact : AllocationLivenessFacts.Point)
    (restFacts : List AllocationLivenessFacts.Point)
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    (hSchedule :
      StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout (stmt :: rest) (fact :: restFacts) =
        some (point :: points, finalLayout))
    (hLower :
      StackLowering.lowerStmtListFuel lowerFuel lowerCtx
          (stmt :: rest) (point :: points) = some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx))
    (hFalls :
      ∀ {before rawPoint},
        StackSchedule.scheduleStmtFuelWithTargets targets scheduleFuel pinned
            before stmt fact = some rawPoint →
          rawPoint.fallsThrough = true)
    (hPoint :
      ∀ {order rawPoint retain pointLowered pointCode middleCtx},
        AllocationLayout.Ordering.build? targetCtx.layout
            (StackSchedule.orderPriority targetCtx.layout stmt fact) =
          some order →
        StackSchedule.scheduleStmtFuelWithTargets targets scheduleFuel pinned
            order.target stmt fact = some rawPoint →
        AllocationLayout.RegularTransition.build? rawPoint.statementLayout
            (StackSchedule.required pinned
              (StackSchedule.nextLive fact.liveAfter rest restFacts)) =
          some retain →
        StackLowering.lowerPointFuel lowerFuel lowerCtx stmt
            { rawPoint with order? := some order, retain? := some retain } =
          some pointLowered →
        Locals.Block.compileOpen (targetCtx.withLayout order.target)
            { stmts := pointLowered } = some (pointCode, middleCtx) →
        CompiledControlPoint sourceProgram targetProgram targets returnNames
          (targetCtx.withLayout order.target) middleCtx stmt pointCode
          retain.schedule.target)
    (hTail :
      ∀ {tailLayout : Locals.Layout} {tailFinal : Locals.Layout}
        {tailLowered : List Locals.Stmt} {middleCtx tailFinalCtx : Locals.Ctx}
        {tailCode : List Expressions.Stmt},
        middleCtx.layout = tailLayout →
        StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
            tailLayout rest restFacts = some (points, tailFinal) →
        StackLowering.lowerStmtListFuel lowerFuel lowerCtx rest points =
          some tailLowered →
        Locals.Block.compileOpen middleCtx { stmts := tailLowered } =
          some (tailCode, tailFinalCtx) →
        ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
          middleCtx tailFinalCtx rest tailFinal tailCode) :
    ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
      targetCtx finalCtx (stmt :: rest) finalLayout code := by
  obtain ⟨order, rawPoint, retain, tailFinal, hOrderBuild, hRawSchedule,
      hRawFalls, hRetainBuild, hPointEq, hTailSchedule, hFinalLayout⟩ :=
    StackSchedule.scheduleStmtListFuelWithTargets_cons_fallsThrough_components
      hSchedule hFalls
  subst point
  have hPointFalls :
      ({ rawPoint with order? := some order, retain? := some retain } :
        StackSchedule.Point).fallsThrough = true := by
    simpa using hRawFalls
  obtain ⟨lowerOrder, pointLowered, tailLowered, hLowerOrder, hPointLower,
      hTailLower, hLowered⟩ :=
    StackLowering.lowerStmtListFuel_cons_fallsThrough_components hLower
      hPointFalls
  have hOrderEq : lowerOrder = order :=
    Option.some.inj (hLowerOrder.symm.trans rfl)
  subst lowerOrder
  have hLowered' :
      lowered = order.statements ++ (pointLowered ++ tailLowered) := by
    simpa [List.append_assoc] using hLowered
  rw [hLowered'] at hCompile
  obtain ⟨orderCode, orderedCtx, restCode, hOrderCompile, hRestCompile,
      hWholeCode⟩ :=
    Locals.Block.compileOpen_append_components hCompile
  have hOrderSource : targetCtx.layout = order.source :=
    (AllocationLayout.Ordering.build?_source hOrderBuild).symm
  obtain ⟨orderArtifact⟩ :=
    StackTransitionCompilation.Ordering.compileArtifact order hOrderSource
  have hOrderPair :=
    Option.some.inj (orderArtifact.compileEq.symm.trans hOrderCompile)
  have hOrderedCtx : targetCtx.withLayout order.target = orderedCtx :=
    congrArg Prod.snd hOrderPair
  have hOrderCompile' :
      Locals.Block.compileOpen targetCtx { stmts := order.statements } =
        some (orderCode, targetCtx.withLayout order.target) := by
    rw [hOrderedCtx]
    exact hOrderCompile
  rw [← hOrderedCtx] at hRestCompile
  obtain ⟨pointCode, middleCtx, tailCode, hPointCompile, hTailCompile,
      hRestCode⟩ :=
    Locals.Block.compileOpen_append_components hRestCompile
  have hPointCompiled :=
    hPoint hOrderBuild hRawSchedule hRetainBuild hPointLower hPointCompile
  have hTailPreserves :=
    hTail hPointCompiled.layout hTailSchedule hTailLower hTailCompile
  have hTailPreserves' :
      ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
        middleCtx finalCtx rest finalLayout tailCode := by
    rw [hFinalLayout]
    exact hTailPreserves
  have hCode : code = orderCode ++ pointCode ++ tailCode := by
    rw [hWholeCode, hRestCode]
    simp [List.append_assoc]
  exact
    controlOrderedCons returnNames sourceProgram targetProgram targets targetCtx middleCtx
      finalCtx stmt rest order orderCode pointCode tailCode code finalLayout
      hOrderSource hOrderCompile' hPointCompiled.preserves hTailPreserves' hCode

theorem controlFallthroughConsAt_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel sourceFuel : Nat)
    (stmt : Functions.Stmt) (rest : List Functions.Stmt)
    (fact : AllocationLivenessFacts.Point)
    (restFacts : List AllocationLivenessFacts.Point)
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    (hSchedule :
      StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout (stmt :: rest) (fact :: restFacts) =
        some (point :: points, finalLayout))
    (hLower :
      StackLowering.lowerStmtListFuel lowerFuel lowerCtx
          (stmt :: rest) (point :: points) = some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx))
    (hFalls :
      ∀ {before rawPoint},
        StackSchedule.scheduleStmtFuelWithTargets targets scheduleFuel pinned
            before stmt fact = some rawPoint →
          rawPoint.fallsThrough = true)
    (hPoint :
      ∀ {order rawPoint retain pointLowered pointCode middleCtx},
        AllocationLayout.Ordering.build? targetCtx.layout
            (StackSchedule.orderPriority targetCtx.layout stmt fact) =
          some order →
        StackSchedule.scheduleStmtFuelWithTargets targets scheduleFuel pinned
            order.target stmt fact = some rawPoint →
        AllocationLayout.RegularTransition.build? rawPoint.statementLayout
            (StackSchedule.required pinned
              (StackSchedule.nextLive fact.liveAfter rest restFacts)) =
          some retain →
        StackLowering.lowerPointFuel lowerFuel lowerCtx stmt
            { rawPoint with order? := some order, retain? := some retain } =
          some pointLowered →
        Locals.Block.compileOpen (targetCtx.withLayout order.target)
            { stmts := pointLowered } = some (pointCode, middleCtx) →
        CompiledControlPointAt sourceProgram targetProgram targets returnNames
            (targetCtx.withLayout order.target) middleCtx stmt pointCode
            retain.schedule.target sourceFuel ∧
          middleCtx.layout.Nodup)
    (hTail :
      ∀ {tailLayout : Locals.Layout} {tailFinal : Locals.Layout}
        {tailLowered : List Locals.Stmt} {middleCtx tailFinalCtx : Locals.Ctx}
        {tailCode : List Expressions.Stmt},
        middleCtx.layout = tailLayout →
        middleCtx.layout.Nodup →
        Locals.Ctx.SameControl targetCtx middleCtx →
        StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
            tailLayout rest restFacts = some (points, tailFinal) →
        StackLowering.lowerStmtListFuel lowerFuel lowerCtx rest points =
          some tailLowered →
        Locals.Block.compileOpen middleCtx { stmts := tailLowered } =
          some (tailCode, tailFinalCtx) →
        ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames middleCtx tailFinalCtx rest tailFinal tailCode
          sourceFuel ∧
        tailFinalCtx.layout.Nodup) :
    ControlScheduledListPreservesAt sourceProgram targetProgram targets
      returnNames targetCtx finalCtx (stmt :: rest) finalLayout code
      (sourceFuel + 1) ∧
    finalCtx.layout.Nodup := by
  obtain ⟨order, rawPoint, retain, tailFinal, hOrderBuild, hRawSchedule,
      hRawFalls, hRetainBuild, hPointEq, hTailSchedule, hFinalLayout⟩ :=
    StackSchedule.scheduleStmtListFuelWithTargets_cons_fallsThrough_components
      hSchedule hFalls
  subst point
  have hPointFalls :
      ({ rawPoint with order? := some order, retain? := some retain } :
        StackSchedule.Point).fallsThrough = true := by
    simpa using hRawFalls
  obtain ⟨lowerOrder, pointLowered, tailLowered, hLowerOrder, hPointLower,
      hTailLower, hLowered⟩ :=
    StackLowering.lowerStmtListFuel_cons_fallsThrough_components hLower
      hPointFalls
  have hOrderEq : lowerOrder = order :=
    Option.some.inj (hLowerOrder.symm.trans rfl)
  subst lowerOrder
  have hLowered' :
      lowered = order.statements ++ (pointLowered ++ tailLowered) := by
    simpa [List.append_assoc] using hLowered
  rw [hLowered'] at hCompile
  obtain ⟨orderCode, orderedCtx, restCode, hOrderCompile, hRestCompile,
      hWholeCode⟩ :=
    Locals.Block.compileOpen_append_components hCompile
  have hOrderSource : targetCtx.layout = order.source :=
    (AllocationLayout.Ordering.build?_source hOrderBuild).symm
  obtain ⟨orderArtifact⟩ :=
    StackTransitionCompilation.Ordering.compileArtifact order hOrderSource
  have hOrderPair :=
    Option.some.inj (orderArtifact.compileEq.symm.trans hOrderCompile)
  have hOrderedCtx : targetCtx.withLayout order.target = orderedCtx :=
    congrArg Prod.snd hOrderPair
  have hOrderCompile' :
      Locals.Block.compileOpen targetCtx { stmts := order.statements } =
        some (orderCode, targetCtx.withLayout order.target) := by
    rw [hOrderedCtx]
    exact hOrderCompile
  rw [← hOrderedCtx] at hRestCompile
  obtain ⟨pointCode, middleCtx, tailCode, hPointCompile, hTailCompile,
      hRestCode⟩ :=
    Locals.Block.compileOpen_append_components hRestCompile
  obtain ⟨hPointCompiled, hMiddleNodup⟩ :=
    hPoint hOrderBuild hRawSchedule hRetainBuild hPointLower hPointCompile
  have hMiddleControl : Locals.Ctx.SameControl targetCtx middleCtx :=
    (Locals.Ctx.SameControl.withLayout targetCtx order.target).trans
      (Locals.Block.compileOpen_sameControl hPointCompile)
  have hTailResult :=
    hTail hPointCompiled.layout hMiddleNodup hMiddleControl hTailSchedule hTailLower
      hTailCompile
  have hTailPreserves := hTailResult.1
  have hTailPreserves' :
      ControlScheduledListPreservesAt sourceProgram targetProgram targets
        returnNames middleCtx finalCtx rest finalLayout tailCode sourceFuel := by
    rw [hFinalLayout]
    exact hTailPreserves
  have hCode : code = orderCode ++ pointCode ++ tailCode := by
    rw [hWholeCode, hRestCode]
    simp [List.append_assoc]
  refine ⟨?_, hTailResult.2⟩
  exact
    controlOrderedConsAt returnNames sourceProgram targetProgram targets
      targetCtx middleCtx finalCtx stmt rest order orderCode pointCode tailCode
      code finalLayout sourceFuel hOrderSource hOrderCompile'
      hPointCompiled.preserves hTailPreserves' hCode

theorem compiledNonfallPoint_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel : Nat)
    (stmt : Functions.Stmt) (rest : List Functions.Stmt)
    (fact : AllocationLivenessFacts.Point)
    (restFacts : List AllocationLivenessFacts.Point)
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    (hSchedule :
      StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout (stmt :: rest) (fact :: restFacts) =
        some (point :: points, finalLayout))
    (hLower :
      StackLowering.lowerStmtListFuel lowerFuel lowerCtx
          (stmt :: rest) (point :: points) = some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx))
    (hFalls :
      ∀ {before rawPoint},
        StackSchedule.scheduleStmtFuelWithTargets targets scheduleFuel pinned
            before stmt fact = some rawPoint →
          rawPoint.fallsThrough = false)
    (hPoint :
      ∀ {order rawPoint pointLowered pointCode middleCtx},
        AllocationLayout.Ordering.build? targetCtx.layout
            (StackSchedule.orderPriority targetCtx.layout stmt fact) =
          some order →
        StackSchedule.scheduleStmtFuelWithTargets targets scheduleFuel pinned
            order.target stmt fact = some rawPoint →
        StackLowering.lowerPointFuel lowerFuel lowerCtx stmt
            { rawPoint with order? := some order, retain? := none } =
          some pointLowered →
        Locals.Block.compileOpen (targetCtx.withLayout order.target)
            { stmts := pointLowered } = some (pointCode, middleCtx) →
        CompiledControlPoint sourceProgram targetProgram targets returnNames
          (targetCtx.withLayout order.target) middleCtx stmt pointCode
          rawPoint.statementLayout) :
    CompiledControlPoint sourceProgram targetProgram targets returnNames targetCtx finalCtx
      stmt code finalLayout := by
  obtain ⟨order, rawPoint, hOrderBuild, hRawSchedule, hRawFalls, hPointEq,
      hPoints, hFinalLayout⟩ :=
    StackSchedule.scheduleStmtListFuelWithTargets_cons_nonfallthrough_components
      hSchedule hFalls
  subst point
  subst points
  have hScheduledFalls :
      ({ rawPoint with order? := some order, retain? := none } :
        StackSchedule.Point).fallsThrough = false := by
    simpa using hRawFalls
  obtain ⟨lowerOrder, pointLowered, hLowerOrder, hPointLower, hLowered⟩ :=
    StackLowering.lowerStmtListFuel_cons_nonfallthrough_components hLower
      hScheduledFalls
  have hOrderEq : lowerOrder = order :=
    Option.some.inj (hLowerOrder.symm.trans rfl)
  subst lowerOrder
  rw [hLowered] at hCompile
  obtain ⟨orderCode, orderedCtx, pointCode, hOrderCompile, hPointCompile,
      hWholeCode⟩ :=
    Locals.Block.compileOpen_append_components hCompile
  have hOrderSource : targetCtx.layout = order.source :=
    (AllocationLayout.Ordering.build?_source hOrderBuild).symm
  obtain ⟨orderArtifact⟩ :=
    StackTransitionCompilation.Ordering.compileArtifact order hOrderSource
  have hOrderPair :=
    Option.some.inj (orderArtifact.compileEq.symm.trans hOrderCompile)
  have hOrderCode :
      orderArtifact.promotionCodes.map Expressions.Stmt.code = orderCode :=
    congrArg Prod.fst hOrderPair
  have hOrderedCtx : targetCtx.withLayout order.target = orderedCtx :=
    congrArg Prod.snd hOrderPair
  rw [← hOrderedCtx] at hPointCompile
  have hPointCompiled :=
    hPoint hOrderBuild hRawSchedule hPointLower hPointCompile
  refine ⟨?_, ?_⟩
  · rw [hFinalLayout]
    exact hPointCompiled.layout
  unfold ControlPointPreserves
  intro sourceCtx sourceFuel targetFuel suffix returns source target hFuel
    hCtx hInitial
  have hFuel' := hFuel
  rw [hWholeCode, ← hOrderCode] at hFuel'
  have hPointFuel :=
    Expressions.TargetFuel.Covers.tail_after_append hFuel'
  rw [hWholeCode, ← hOrderCode]
  apply orderArtifact.thenBlockForward targetProgram targetFuel
      (by
        have hLength := Expressions.TargetFuel.Covers.length_lt hFuel'
        simp only [List.length_append, List.length_map] at hLength
        omega) hInitial
  intro orderedTarget hOrdered
  apply hPointCompiled.preserves sourceCtx sourceFuel
    (targetFuel - orderArtifact.promotionCodes.length)
  · simpa using hPointFuel
  · exact hCtx.afterOrdering order hOrderSource
  · exact hOrdered

theorem controlNonfallPointToList
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (targetCtx finalCtx : Locals.Ctx)
    (stmt : Functions.Stmt) (rest : List Functions.Stmt)
    (code : List Expressions.Stmt) (finalLayout : Locals.Layout)
    (hPoint :
      CompiledControlPoint sourceProgram targetProgram targets returnNames targetCtx finalCtx
        stmt code finalLayout)
    (hSource :
      ∀ (sourceCtx : Functions.Source.Ctx) (sourceFuel : Nat)
        (source : Locals.Source.State)
        (returns : List Structured.ReturnDest),
        RuntimeCtxCovers sourceCtx targetCtx targets returnNames returns →
        Functions.InteractionSemantics.Block.openRun sourceProgram sourceCtx
            (sourceFuel + 1) { stmts := stmt :: rest } source =
          Functions.InteractionSemantics.Stmt.openRun sourceProgram sourceCtx
            sourceFuel stmt source) :
    ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
      targetCtx finalCtx (stmt :: rest) finalLayout code := by
  refine ⟨hPoint.layout, ?_⟩
  intro sourceCtx sourceFuel targetFuel suffix returns source target hFuel
    hCtx hInitial
  cases sourceFuel with
  | zero =>
      unfold Functions.InteractionSemantics.Block.openRun
        Functions.InteractionSemantics.stateModel
      simp only [Functions.Source.Effectful.Control.Block.runOpen]
      exact Simulation.Interaction.ForwardRel.truncated rfl
  | succ sourceFuel =>
      have hPointFuel :
          Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel
            code := by
        apply Expressions.TargetFuel.Covers.head_of_succ_append
          (left := code) (right := [])
        simpa [Nat.succ_eq_add_one] using hFuel
      rw [hSource sourceCtx sourceFuel source returns hCtx]
      exact hPoint.preserves sourceCtx sourceFuel targetFuel hPointFuel hCtx
        hInitial

theorem blockCons_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel : Nat)
    (body : Functions.Block) (rest : List Functions.Stmt)
    (fact : AllocationLivenessFacts.Point)
    (restFacts : List AllocationLivenessFacts.Point)
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    (hSchedule :
      StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout (.block body :: rest) (fact :: restFacts) =
        some (point :: points, finalLayout))
    (hLower :
      StackLowering.lowerStmtListFuel lowerFuel lowerCtx
          (.block body :: rest) (point :: points) = some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx))
    (hBody :
      ∀ {childCtx : Locals.Ctx}
        {bodyFacts rawRegion bodyLowered bodyCode bodyFinalCtx},
        StackSchedule.scheduleBlockFuelWithTargets targets (scheduleFuel - 1)
            (StackSchedule.layoutSet childCtx.layout) childCtx.layout
            body bodyFacts = some rawRegion →
        StackLowering.lowerStmtListFuel ((lowerFuel - 1) - 1) lowerCtx
            body.stmts rawRegion.points = some bodyLowered →
        Locals.Block.compileOpen
            (childCtx.withLayout rawRegion.entry.target)
            { stmts := bodyLowered } = some (bodyCode, bodyFinalCtx) →
        ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
          (childCtx.withLayout rawRegion.entry.target) bodyFinalCtx body.stmts
          rawRegion.finalLayout bodyCode)
    (hTail :
      ∀ {tailLayout : Locals.Layout} {tailFinal : Locals.Layout}
        {tailLowered : List Locals.Stmt} {middleCtx tailFinalCtx : Locals.Ctx}
        {tailCode : List Expressions.Stmt},
        middleCtx.layout = tailLayout →
        StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
            tailLayout rest restFacts = some (points, tailFinal) →
        StackLowering.lowerStmtListFuel lowerFuel lowerCtx rest points =
          some tailLowered →
        Locals.Block.compileOpen middleCtx { stmts := tailLowered } =
          some (tailCode, tailFinalCtx) →
        ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
          middleCtx tailFinalCtx rest tailFinal tailCode) :
    ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
      targetCtx finalCtx (.block body :: rest) finalLayout code := by
  apply controlFallthroughCons_of_compilers returnNames sourceProgram targetProgram lowerCtx
    targets pinned scheduleFuel lowerFuel (.block body) rest fact restFacts
    hSchedule hLower hCompile
  · intro before rawPoint hRaw
    obtain ⟨_bodyFacts, _rawRegion, _exit, _hFacts, _hChild,
        _hExit, _hBefore, _hStatement, _hRawExit, _hRawRetain,
        _hRegions, hFalls⟩ :=
      StackSchedule.scheduleStmtFuelWithTargets_block_components hRaw
    exact hFalls
  · intro order rawPoint retain pointLowered pointCode middleCtx hOrderBuild
      hRawSchedule hRetainBuild hPointLower hPointCompile
    obtain ⟨_bodyFacts, _rawRegion, _exit, _hFacts, _hChild,
        _hExit, _hBefore, hRawStatement, _hRawExit, _hRawRetain,
        hRawRegions, _hFalls⟩ :=
      StackSchedule.scheduleStmtFuelWithTargets_block_components hRawSchedule
    have hRetainSource :
        (targetCtx.withLayout order.target).layout = retain.source := by
      have hBuiltSource : rawPoint.statementLayout = retain.source :=
        (AllocationLayout.RegularTransition.build?_sound hRetainBuild).1.symm
      simpa [Locals.Ctx.withLayout] using
        hRawStatement.symm.trans hBuiltSource
    exact
      blockPoint_of_compilers returnNames sourceProgram targetProgram lowerCtx targets pinned
        scheduleFuel lowerFuel body fact rawPoint
        { rawPoint with order? := some order, retain? := some retain } retain
        (targetCtx.withLayout order.target) middleCtx pointLowered pointCode
        hRawSchedule (by simpa using hRawRegions) rfl hRetainSource hPointLower
        hPointCompile (fun hChildSchedule hChildLower hChildCompile =>
          hBody hChildSchedule hChildLower hChildCompile)
  · exact hTail

theorem ifCons_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel : Nat)
    (cond : Functions.Expr 1) (body : Functions.Block)
    (rest : List Functions.Stmt)
    (fact : AllocationLivenessFacts.Point)
    (restFacts : List AllocationLivenessFacts.Point)
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    {sourceEnv : List Name}
    (hScoped : Functions.Scope.ExprScoped sourceEnv cond)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported cond)
    (hSchedule :
      StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout (.if_ cond body :: rest) (fact :: restFacts) =
        some (point :: points, finalLayout))
    (hLower :
      StackLowering.lowerStmtListFuel lowerFuel lowerCtx
          (.if_ cond body :: rest) (point :: points) = some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx))
    (hBody :
      ∀ {childCtx : Locals.Ctx}
        {bodyFacts rawRegion bodyLowered bodyCode bodyFinalCtx},
        StackSchedule.scheduleBlockFuelWithTargets targets (scheduleFuel - 1)
            (StackSchedule.layoutSet childCtx.layout) childCtx.layout
            body bodyFacts = some rawRegion →
        StackLowering.lowerStmtListFuel ((lowerFuel - 1) - 1) lowerCtx
            body.stmts rawRegion.points = some bodyLowered →
        Locals.Block.compileOpen
            (childCtx.withLayout rawRegion.entry.target)
            { stmts := bodyLowered } = some (bodyCode, bodyFinalCtx) →
        ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
          (childCtx.withLayout rawRegion.entry.target) bodyFinalCtx body.stmts
          rawRegion.finalLayout bodyCode)
    (hTail :
      ∀ {tailLayout : Locals.Layout} {tailFinal : Locals.Layout}
        {tailLowered : List Locals.Stmt} {middleCtx tailFinalCtx : Locals.Ctx}
        {tailCode : List Expressions.Stmt},
        middleCtx.layout = tailLayout →
        StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
            tailLayout rest restFacts = some (points, tailFinal) →
        StackLowering.lowerStmtListFuel lowerFuel lowerCtx rest points =
          some tailLowered →
        Locals.Block.compileOpen middleCtx { stmts := tailLowered } =
          some (tailCode, tailFinalCtx) →
        ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
          middleCtx tailFinalCtx rest tailFinal tailCode) :
    ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
      targetCtx finalCtx (.if_ cond body :: rest) finalLayout code := by
  apply controlFallthroughCons_of_compilers returnNames sourceProgram targetProgram lowerCtx
    targets pinned scheduleFuel lowerFuel (.if_ cond body) rest fact restFacts
    hSchedule hLower hCompile
  · intro before rawPoint hRaw
    obtain ⟨_bodyFacts, _rawRegion, _exit, _hFacts, _hChild,
        _hExit, _hBefore, _hStatement, _hRawExit, _hRawRetain,
        _hRegions, hFalls⟩ :=
      StackSchedule.scheduleStmtFuelWithTargets_if_components hRaw
    exact hFalls
  · intro order rawPoint retain pointLowered pointCode middleCtx hOrderBuild
      hRawSchedule hRetainBuild hPointLower hPointCompile
    obtain ⟨_bodyFacts, _rawRegion, _exit, _hFacts, _hChild,
        _hExit, hRawBefore, hRawStatement, _hRawExit, _hRawRetain,
        hRawRegions, _hFalls⟩ :=
      StackSchedule.scheduleStmtFuelWithTargets_if_components hRawSchedule
    have hRetainSource :
        (targetCtx.withLayout order.target).layout = retain.source := by
      have hBuiltSource : rawPoint.statementLayout = retain.source :=
        (AllocationLayout.RegularTransition.build?_sound hRetainBuild).1.symm
      simpa [Locals.Ctx.withLayout] using
        hRawStatement.symm.trans hBuiltSource
    exact
      ifPoint_of_compilers returnNames sourceProgram targetProgram lowerCtx targets pinned
        scheduleFuel lowerFuel cond body fact rawPoint
        { rawPoint with order? := some order, retain? := some retain } retain
        (targetCtx.withLayout order.target) middleCtx pointLowered pointCode
        hScoped hSupported hRawSchedule
        (by simpa [Locals.Ctx.withLayout] using hRawBefore)
        (by simpa using hRawRegions) rfl hRetainSource hPointLower hPointCompile
        (fun hChildSchedule hChildLower hChildCompile =>
          hBody hChildSchedule hChildLower hChildCompile)
  · exact hTail

theorem switchCons_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel : Nat)
    (scrutinee : Functions.Expr 1)
    (cases : List (Word × Functions.Block))
    (defaultBody : Option Functions.Block)
    (rest : List Functions.Stmt)
    (fact : AllocationLivenessFacts.Point)
    (restFacts : List AllocationLivenessFacts.Point)
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    {sourceEnv : List Name}
    (hScoped : Functions.Scope.ExprScoped sourceEnv scrutinee)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported scrutinee)
    (hSchedule :
      StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout
          (.switch scrutinee cases defaultBody :: rest) (fact :: restFacts) =
        some (point :: points, finalLayout))
    (hLower :
      StackLowering.lowerStmtListFuel lowerFuel lowerCtx
          (.switch scrutinee cases defaultBody :: rest) (point :: points) =
        some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx))
    (hBody :
      ∀ {body : Functions.Block} {childCtx : Locals.Ctx}
        {bodyFacts rawRegion bodyLowered bodyCode bodyFinalCtx},
        StackSchedule.scheduleBlockFuelWithTargets targets (scheduleFuel - 1)
            (StackSchedule.layoutSet childCtx.layout) childCtx.layout
            body bodyFacts = some rawRegion →
        StackLowering.lowerStmtListFuel ((lowerFuel - 1) - 1) lowerCtx
            body.stmts rawRegion.points = some bodyLowered →
        Locals.Block.compileOpen
            (childCtx.withLayout rawRegion.entry.target)
            { stmts := bodyLowered } = some (bodyCode, bodyFinalCtx) →
        ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
          (childCtx.withLayout rawRegion.entry.target) bodyFinalCtx body.stmts
          rawRegion.finalLayout bodyCode)
    (hTail :
      ∀ {tailLayout : Locals.Layout} {tailFinal : Locals.Layout}
        {tailLowered : List Locals.Stmt} {middleCtx tailFinalCtx : Locals.Ctx}
        {tailCode : List Expressions.Stmt},
        middleCtx.layout = tailLayout →
        StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
            tailLayout rest restFacts = some (points, tailFinal) →
        StackLowering.lowerStmtListFuel lowerFuel lowerCtx rest points =
          some tailLowered →
        Locals.Block.compileOpen middleCtx { stmts := tailLowered } =
          some (tailCode, tailFinalCtx) →
        ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
          middleCtx tailFinalCtx rest tailFinal tailCode) :
    ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
      targetCtx finalCtx (.switch scrutinee cases defaultBody :: rest)
      finalLayout code := by
  apply controlFallthroughCons_of_compilers returnNames sourceProgram targetProgram lowerCtx
    targets pinned scheduleFuel lowerFuel (.switch scrutinee cases defaultBody)
    rest fact restFacts hSchedule hLower hCompile
  · intro before rawPoint hRaw
    obtain ⟨_caseRegions, _defaultRegions, _hCases, _hDefault, _hBefore,
        _hStatement, _hRetain, _hRegions, hFalls⟩ :=
      StackSchedule.scheduleStmtFuelWithTargets_switch_components hRaw
    exact hFalls
  · intro order rawPoint retain pointLowered pointCode middleCtx hOrderBuild
      hRawSchedule hRetainBuild hPointLower hPointCompile
    obtain ⟨_caseRegions, _defaultRegions, _hCases, _hDefault, hRawBefore,
        hRawStatement, _hRawRetain, hRawRegions, _hFalls⟩ :=
      StackSchedule.scheduleStmtFuelWithTargets_switch_components hRawSchedule
    have hRetainSource :
        (targetCtx.withLayout order.target).layout = retain.source := by
      have hBuiltSource : rawPoint.statementLayout = retain.source :=
        (AllocationLayout.RegularTransition.build?_sound hRetainBuild).1.symm
      simpa [Locals.Ctx.withLayout] using
        hRawStatement.symm.trans hBuiltSource
    exact
      switchPoint_of_compilers returnNames sourceProgram targetProgram lowerCtx targets pinned
        scheduleFuel lowerFuel scrutinee cases defaultBody fact rawPoint
        { rawPoint with order? := some order, retain? := some retain } retain
        (targetCtx.withLayout order.target) middleCtx pointLowered pointCode
        hScoped hSupported hRawSchedule
        (by simpa [Locals.Ctx.withLayout] using hRawBefore)
        (by simpa using hRawRegions) rfl hRetainSource hPointLower hPointCompile
        (fun hChildSchedule hChildLower hChildCompile =>
          hBody hChildSchedule hChildLower hChildCompile)
  · exact hTail

theorem forCons_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel : Nat)
    (init : Functions.Block) (cond : Functions.Expr 1)
    (post body : Functions.Block)
    (rest : List Functions.Stmt)
    (fact : AllocationLivenessFacts.Point)
    (restFacts : List AllocationLivenessFacts.Point)
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    {sourceEnv : List Name}
    (hScoped : Functions.Scope.ExprScoped sourceEnv cond)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported cond)
    (hSchedule :
      StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout (.for_ init cond post body :: rest)
          (fact :: restFacts) = some (point :: points, finalLayout))
    (hLower :
      StackLowering.lowerStmtListFuel lowerFuel lowerCtx
          (.for_ init cond post body :: rest) (point :: points) = some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx))
    (hChild :
      ∀ {childTargets : StackSchedule.ControlTargets}
        {child : Functions.Block} {childCtx : Locals.Ctx}
        {childFacts rawRegion childLowered childCode childFinalCtx},
        StackSchedule.scheduleBlockFuelWithTargets childTargets
            (scheduleFuel - 1) (StackSchedule.layoutSet childCtx.layout)
            childCtx.layout child childFacts = some rawRegion →
        StackLowering.lowerStmtListFuel ((lowerFuel - 1) - 1) lowerCtx
            child.stmts rawRegion.points = some childLowered →
        Locals.Block.compileOpen
            (childCtx.withLayout rawRegion.entry.target)
            { stmts := childLowered } = some (childCode, childFinalCtx) →
        ControlScheduledListPreserves sourceProgram targetProgram childTargets
          returnNames
          (childCtx.withLayout rawRegion.entry.target) childFinalCtx child.stmts
          rawRegion.finalLayout childCode)
    (hTail :
      ∀ {tailLayout : Locals.Layout} {tailFinal : Locals.Layout}
        {tailLowered : List Locals.Stmt} {middleCtx tailFinalCtx : Locals.Ctx}
        {tailCode : List Expressions.Stmt},
        middleCtx.layout = tailLayout →
        StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
            tailLayout rest restFacts = some (points, tailFinal) →
        StackLowering.lowerStmtListFuel lowerFuel lowerCtx rest points =
          some tailLowered →
        Locals.Block.compileOpen middleCtx { stmts := tailLowered } =
          some (tailCode, tailFinalCtx) →
        ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
          middleCtx tailFinalCtx rest tailFinal tailCode) :
    ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
      targetCtx finalCtx (.for_ init cond post body :: rest) finalLayout code := by
  apply controlFallthroughCons_of_compilers returnNames sourceProgram targetProgram lowerCtx
    targets pinned scheduleFuel lowerFuel (.for_ init cond post body) rest fact
    restFacts hSchedule hLower hCompile
  · intro before rawPoint hRaw
    obtain ⟨_initFacts, _postFacts, _bodyFacts, _loopFacts, _rawInit,
        _rawPost, _rawBody, _initExit, _postExit, _bodyExit, _hFacts,
        _hLoop, _hInit, _hInitExit, _hPost, _hBody, _hPostExit,
        _hBodyExit, _hBefore, _hStatement, _hRetain, _hRegions, hFalls⟩ :=
      StackSchedule.scheduleStmtFuelWithTargets_for_components hRaw
    exact hFalls
  · intro order rawPoint retain pointLowered pointCode middleCtx hOrderBuild
      hRawSchedule hRetainBuild hPointLower hPointCompile
    obtain ⟨_initFacts, _postFacts, _bodyFacts, _loopFacts, _rawInit,
        _rawPost, _rawBody, _initExit, _postExit, _bodyExit, _hFacts,
        _hLoop, _hInit, _hInitExit, _hPost, _hBody, _hPostExit,
        _hBodyExit, hRawBefore, hRawStatement, _hRawRetain, hRawRegions,
        _hFalls⟩ :=
      StackSchedule.scheduleStmtFuelWithTargets_for_components hRawSchedule
    have hRetainSource :
        (targetCtx.withLayout order.target).layout = retain.source := by
      have hBuiltSource : rawPoint.statementLayout = retain.source :=
        (AllocationLayout.RegularTransition.build?_sound hRetainBuild).1.symm
      simpa [Locals.Ctx.withLayout] using
        hRawStatement.symm.trans hBuiltSource
    exact
      forPoint_of_compilers returnNames sourceProgram targetProgram lowerCtx targets pinned
        scheduleFuel lowerFuel init cond post body fact rawPoint
        { rawPoint with order? := some order, retain? := some retain } retain
        (targetCtx.withLayout order.target) middleCtx pointLowered pointCode
        hScoped hSupported hRawSchedule
        (by simpa [Locals.Ctx.withLayout] using hRawBefore)
        (by simpa using hRawRegions) rfl hRetainSource hPointLower
        hPointCompile
        (fun hChildSchedule hChildLower hChildCompile =>
          hChild hChildSchedule hChildLower hChildCompile)
  · exact hTail

theorem exprCons_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel : Nat)
    (expr : Functions.Expr 0) (rest : List Functions.Stmt)
    (fact : AllocationLivenessFacts.Point)
    (restFacts : List AllocationLivenessFacts.Point)
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    {sourceEnv : List Name}
    (hScoped : Functions.Scope.ExprScoped sourceEnv expr)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported expr)
    (hSchedule :
      StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout (.expr expr :: rest) (fact :: restFacts) =
        some (point :: points, finalLayout))
    (hLower :
      StackLowering.lowerStmtListFuel lowerFuel lowerCtx
          (.expr expr :: rest) (point :: points) = some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx))
    (hTail :
      ∀ {tailLayout : Locals.Layout} {tailFinal : Locals.Layout}
        {tailLowered : List Locals.Stmt} {middleCtx tailFinalCtx : Locals.Ctx}
        {tailCode : List Expressions.Stmt},
        middleCtx.layout = tailLayout →
        StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
            tailLayout rest restFacts = some (points, tailFinal) →
        StackLowering.lowerStmtListFuel lowerFuel lowerCtx rest points =
          some tailLowered →
        Locals.Block.compileOpen middleCtx { stmts := tailLowered } =
          some (tailCode, tailFinalCtx) →
        ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
          middleCtx tailFinalCtx rest tailFinal tailCode) :
    ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
      targetCtx finalCtx (.expr expr :: rest) finalLayout code := by
  apply controlFallthroughCons_of_compilers returnNames sourceProgram targetProgram lowerCtx
    targets pinned scheduleFuel lowerFuel (.expr expr) rest fact restFacts
    hSchedule hLower hCompile
  · intro before rawPoint hRaw
    exact
      (StackSchedule.scheduleStmtFuelWithTargets_expr_components hRaw).2.2.2.2
  · intro order rawPoint retain pointLowered pointCode middleCtx hOrderBuild
      hRawSchedule hRetainBuild hPointLower hPointCompile
    obtain ⟨hRawBefore, hRawStatement, _hRawRetain, _hRawRegions,
        _hRawFalls⟩ :=
      StackSchedule.scheduleStmtFuelWithTargets_expr_components hRawSchedule
    obtain ⟨lowerRetain, hAccess, _hLowerFalls, _hLowerRegions,
        hLowerRetain, hPointLowered⟩ :=
      StackLowering.lowerPointFuel_expr_components hPointLower
    have hLowerRetainEq : lowerRetain = retain :=
      Option.some.inj (hLowerRetain.symm.trans rfl)
    subst lowerRetain
    have hRetainSource :
        (targetCtx.withLayout order.target).layout = retain.source := by
      have hBuiltSource : rawPoint.statementLayout = retain.source :=
        (AllocationLayout.RegularTransition.build?_sound hRetainBuild).1.symm
      simpa [Locals.Ctx.withLayout] using
        hRawStatement.symm.trans hBuiltSource
    have hExprAccess :
        StackAccess.Expr.check?
            (targetCtx.withLayout order.target).layout 0 expr = some () := by
      simpa [StackLowering.pointAccess?, Locals.Ctx.withLayout, hRawBefore]
        using hAccess
    exact
      compiledExprControlPointOfEquations sourceProgram targetProgram targets returnNames
        (targetCtx.withLayout order.target) middleCtx expr retain pointLowered
        pointCode hRetainSource hScoped hSupported hExprAccess hPointLowered
        hPointCompile
  · exact hTail

theorem letCons_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel : Nat)
    (name : Name) (value : Functions.Expr 1)
    (rest : List Functions.Stmt)
    (fact : AllocationLivenessFacts.Point)
    (restFacts : List AllocationLivenessFacts.Point)
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    {sourceEnv : List Name}
    (hScoped : Functions.Scope.ExprScoped sourceEnv value)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported value)
    (hSchedule :
      StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout (.let_ name value :: rest) (fact :: restFacts) =
        some (point :: points, finalLayout))
    (hLower :
      StackLowering.lowerStmtListFuel lowerFuel lowerCtx
          (.let_ name value :: rest) (point :: points) = some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx))
    (hTail :
      ∀ {tailLayout : Locals.Layout} {tailFinal : Locals.Layout}
        {tailLowered : List Locals.Stmt} {middleCtx tailFinalCtx : Locals.Ctx}
        {tailCode : List Expressions.Stmt},
        middleCtx.layout = tailLayout →
        StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
            tailLayout rest restFacts = some (points, tailFinal) →
        StackLowering.lowerStmtListFuel lowerFuel lowerCtx rest points =
          some tailLowered →
        Locals.Block.compileOpen middleCtx { stmts := tailLowered } =
          some (tailCode, tailFinalCtx) →
        ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
          middleCtx tailFinalCtx rest tailFinal tailCode) :
    ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
      targetCtx finalCtx (.let_ name value :: rest) finalLayout code := by
  apply controlFallthroughCons_of_compilers returnNames sourceProgram targetProgram lowerCtx
    targets pinned scheduleFuel lowerFuel (.let_ name value) rest fact restFacts
    hSchedule hLower hCompile
  · intro before rawPoint hRaw
    exact
      (StackSchedule.scheduleStmtFuelWithTargets_let_components hRaw).2.2.2.2.2
  · intro order rawPoint retain pointLowered pointCode middleCtx hOrderBuild
      hRawSchedule hRetainBuild hPointLower hPointCompile
    obtain ⟨hFresh, hRawBefore, hRawStatement, _hRawRetain, _hRawRegions,
        _hRawFalls⟩ :=
      StackSchedule.scheduleStmtFuelWithTargets_let_components hRawSchedule
    obtain ⟨lowerRetain, hAccess, _hLowerFalls, _hLowerRegions,
        hLowerRetain, hPointLowered⟩ :=
      StackLowering.lowerPointFuel_let_components hPointLower
    have hLowerRetainEq : lowerRetain = retain :=
      Option.some.inj (hLowerRetain.symm.trans rfl)
    subst lowerRetain
    have hRetainSource :
        name :: (targetCtx.withLayout order.target).layout = retain.source := by
      have hBuiltSource : rawPoint.statementLayout = retain.source :=
        (AllocationLayout.RegularTransition.build?_sound hRetainBuild).1.symm
      simpa [Locals.Ctx.withLayout] using
        hRawStatement.symm.trans hBuiltSource
    have hValueAccess :
        StackAccess.Expr.check?
            (targetCtx.withLayout order.target).layout 0 value = some () := by
      simpa [StackLowering.pointAccess?, Locals.Ctx.withLayout, hRawBefore]
        using hAccess
    exact
      compiledLetControlPointOfEquations sourceProgram targetProgram targets returnNames
        (targetCtx.withLayout order.target) middleCtx name value retain
        pointLowered pointCode hRetainSource hFresh hScoped hSupported
        hValueAccess hPointLowered hPointCompile
  · exact hTail

theorem assignCons_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel : Nat)
    (name : Name) (value : Functions.Expr 1)
    (rest : List Functions.Stmt)
    (fact : AllocationLivenessFacts.Point)
    (restFacts : List AllocationLivenessFacts.Point)
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    {sourceEnv : List Name}
    (hNodup : targetCtx.layout.Nodup)
    (hScoped : Functions.Scope.ExprScoped sourceEnv value)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported value)
    (hSchedule :
      StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout (.assign name value :: rest) (fact :: restFacts) =
        some (point :: points, finalLayout))
    (hLower :
      StackLowering.lowerStmtListFuel lowerFuel lowerCtx
          (.assign name value :: rest) (point :: points) = some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx))
    (hTail :
      ∀ {tailLayout : Locals.Layout} {tailFinal : Locals.Layout}
        {tailLowered : List Locals.Stmt} {middleCtx tailFinalCtx : Locals.Ctx}
        {tailCode : List Expressions.Stmt},
        middleCtx.layout = tailLayout →
        StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
            tailLayout rest restFacts = some (points, tailFinal) →
        StackLowering.lowerStmtListFuel lowerFuel lowerCtx rest points =
          some tailLowered →
        Locals.Block.compileOpen middleCtx { stmts := tailLowered } =
          some (tailCode, tailFinalCtx) →
        ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
          middleCtx tailFinalCtx rest tailFinal tailCode) :
    ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
      targetCtx finalCtx (.assign name value :: rest) finalLayout code := by
  apply controlFallthroughCons_of_compilers returnNames sourceProgram targetProgram lowerCtx
    targets pinned scheduleFuel lowerFuel (.assign name value) rest fact
    restFacts hSchedule hLower hCompile
  · intro before rawPoint hRaw
    exact
      (StackSchedule.scheduleStmtFuelWithTargets_assign_components hRaw).2.2.2.2
  · intro order rawPoint retain pointLowered pointCode middleCtx hOrderBuild
      hRawSchedule hRetainBuild hPointLower hPointCompile
    obtain ⟨hRawBefore, hRawStatement, _hRawRetain, _hRawRegions,
        _hRawFalls⟩ :=
      StackSchedule.scheduleStmtFuelWithTargets_assign_components hRawSchedule
    obtain ⟨lowerRetain, hAccess, _hLowerFalls, _hLowerRegions,
        hLowerRetain, hPointLowered⟩ :=
      StackLowering.lowerPointFuel_assign_components hPointLower
    have hLowerRetainEq : lowerRetain = retain :=
      Option.some.inj (hLowerRetain.symm.trans rfl)
    subst lowerRetain
    have hRetainSource :
        (targetCtx.withLayout order.target).layout = retain.source := by
      have hBuiltSource : rawPoint.statementLayout = retain.source :=
        (AllocationLayout.RegularTransition.build?_sound hRetainBuild).1.symm
      simpa [Locals.Ctx.withLayout] using
        hRawStatement.symm.trans hBuiltSource
    have hAssignAccess :
        StackAccess.assign? (targetCtx.withLayout order.target).layout name
            value = some () := by
      simpa [StackLowering.pointAccess?, Locals.Ctx.withLayout, hRawBefore]
        using hAccess
    have hOrderSource : targetCtx.layout = order.source :=
      (AllocationLayout.Ordering.build?_source hOrderBuild).symm
    have hOrderedNodup : order.target.Nodup :=
      order.target_nodup (by rw [← hOrderSource]; exact hNodup)
    exact
      compiledAssignControlPointOfEquations sourceProgram targetProgram targets returnNames
        (targetCtx.withLayout order.target) middleCtx name value retain
        pointLowered pointCode hRetainSource
        (by simpa [Locals.Ctx.withLayout] using hOrderedNodup)
        hScoped hSupported hAssignAccess hPointLowered hPointCompile
  · exact hTail

theorem callCons_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel : Nat)
    (callTargets : List Name) (functionName : Name)
    (args : List (Functions.Expr 1))
    (rest : List Functions.Stmt)
    (fact : AllocationLivenessFacts.Point)
    (restFacts : List AllocationLivenessFacts.Point)
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    {sourceEnv : List Name}
    (hFunctions : lowerCtx.functions = sourceProgram.functions)
    (hNodup : targetCtx.layout.Nodup)
    (hArgsScoped :
      ∀ arg, arg ∈ args → Functions.Scope.ExprScoped sourceEnv arg)
    (hArgsSupported :
      Functions.InteractionSemantics.ArgList.OpenSupported args)
    (hSchedule :
      StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout (.call callTargets functionName args :: rest)
          (fact :: restFacts) =
        some (point :: points, finalLayout))
    (hLower :
      StackLowering.lowerStmtListFuel lowerFuel lowerCtx
          (.call callTargets functionName args :: rest) (point :: points) =
        some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx))
    (hCallee :
      ∀ (callCtx : Locals.Ctx) (fn : Functions.FunDef),
        Functions.Source.FunList.find? functionName sourceProgram.functions =
            some fn →
        ∀ (sourceFuel targetFuel : Nat)
          {suffix : List Word} {returns : List Structured.ReturnDest}
          {source sourceAfterArgs : Locals.Source.State}
          {target targetAfterArgs : Structured.RunState}
          {argValues : List Word},
          StateRel callCtx.layout suffix returns source target →
          Locals.InteractionPreservation.Expr.ResultRel args.length
              source target (sourceAfterArgs, argValues) targetAfterArgs →
          (∀ {proc : Expressions.Proc},
            Expressions.EffectSemantics.ProcList.lookup? functionName
                targetProgram.procs = some proc →
            Expressions.TargetFuel.Covers targetProgram sourceFuel
              (targetFuel - 1) proc.body.stmts) →
          Simulation.Interaction.ForwardRel
            FuelTruncated
            (StackCallPreservation.OpenAttachedCallResultRel fn.returns.length
              target.evm.stack returns)
            (Functions.InteractionSemantics.FunDef.openRunBody sourceProgram
              fn argValues sourceFuel sourceAfterArgs)
            (Expressions.InteractionSemantics.Stmt.openRun targetProgram
              targetFuel (.call functionName) targetAfterArgs))
    (hTail :
      ∀ {tailLayout : Locals.Layout} {tailFinal : Locals.Layout}
        {tailLowered : List Locals.Stmt} {middleCtx tailFinalCtx : Locals.Ctx}
        {tailCode : List Expressions.Stmt},
        middleCtx.layout = tailLayout →
        StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
            tailLayout rest restFacts = some (points, tailFinal) →
        StackLowering.lowerStmtListFuel lowerFuel lowerCtx rest points =
          some tailLowered →
        Locals.Block.compileOpen middleCtx { stmts := tailLowered } =
          some (tailCode, tailFinalCtx) →
        ControlScheduledListPreserves sourceProgram targetProgram targets
          returnNames middleCtx tailFinalCtx rest tailFinal tailCode) :
    ControlScheduledListPreserves sourceProgram targetProgram targets
      returnNames targetCtx finalCtx
      (.call callTargets functionName args :: rest) finalLayout code := by
  apply controlFallthroughCons_of_compilers returnNames sourceProgram
    targetProgram lowerCtx targets pinned scheduleFuel lowerFuel
    (.call callTargets functionName args) rest fact restFacts hSchedule hLower
    hCompile
  · intro before rawPoint hRaw
    exact
      (StackSchedule.scheduleStmtFuelWithTargets_call_components hRaw).2.2.2.2
  · intro order rawPoint retain pointLowered pointCode middleCtx hOrderBuild
      hRawSchedule hRetainBuild hPointLower hPointCompile
    obtain ⟨hRawBefore, hRawStatement, _hRawRetain, _hRawRegions,
        _hRawFalls⟩ :=
      StackSchedule.scheduleStmtFuelWithTargets_call_components hRawSchedule
    obtain ⟨_fn, lowerRetain, _hFind, _hArgsLength, _hTargetsLength,
        _hTargetsNodup, hAccess, _hFalls, _hRegions, hLowerRetain,
        _hPointLowered⟩ :=
      StackLowering.lowerPointFuel_call_components hPointLower
    have hLowerRetainEq : lowerRetain = retain :=
      Option.some.inj (hLowerRetain.symm.trans rfl)
    subst lowerRetain
    have hRetainSource :
        (targetCtx.withLayout order.target).layout = retain.source := by
      have hBuiltSource : rawPoint.statementLayout = retain.source :=
        (AllocationLayout.RegularTransition.build?_sound hRetainBuild).1.symm
      simpa [Locals.Ctx.withLayout] using
        hRawStatement.symm.trans hBuiltSource
    have hOrderSource : targetCtx.layout = order.source :=
      (AllocationLayout.Ordering.build?_source hOrderBuild).symm
    have hOrderedNodup : order.target.Nodup :=
      order.target_nodup (by rw [← hOrderSource]; exact hNodup)
    have hCallAccess :
        StackAccess.call? order.target callTargets args = some () := by
      simpa [StackLowering.pointAccess?, hRawBefore] using hAccess
    unfold StackAccess.call? at hCallAccess
    obtain ⟨_unit, hArgAccess, _hReturnedAccess⟩ :=
      Option.bind_eq_some_iff.mp hCallAccess
    have hArgScoped :
        Locals.Scope.ExprSeqScoped order.target (Lower.argExprs args) :=
      StackCallPreservation.argExprs_localsScoped_of_check hArgAccess
        hArgsScoped
    have hOrderedTargets :
        ∀ name, name ∈ callTargets → name ∈ order.target := by
      exact StackAccess.call_targets_mem hCallAccess
    obtain ⟨compiledRetain, hCompiledRetain, hCompiled⟩ :=
      StackCallPreservation.CallPoint.compiledOfCompilers sourceProgram
        targetProgram lowerCtx targets returnNames callTargets functionName
        args { rawPoint with order? := some order, retain? := some retain }
        pointLowered (targetCtx.withLayout order.target) middleCtx pointCode
        lowerFuel hFunctions (by simpa [Locals.Ctx.withLayout] using
          hOrderedNodup) hOrderedTargets hArgScoped hArgsSupported
        (by
          intro candidate hCandidate
          have hCandidateEq : candidate = retain :=
            Option.some.inj (hCandidate.symm.trans rfl)
          subst candidate
          exact hRetainSource)
        hPointLower hPointCompile (hCallee (targetCtx.withLayout order.target))
    have hCompiledRetainEq : compiledRetain = retain :=
      Option.some.inj (hCompiledRetain.symm.trans rfl)
    subst compiledRetain
    exact hCompiled
  · exact hTail

theorem callConsAtSucc_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel sourceFuel : Nat)
    (callTargets : List Name) (functionName : Name)
    (args : List (Functions.Expr 1))
    (rest : List Functions.Stmt)
    (fact : AllocationLivenessFacts.Point)
    (restFacts : List AllocationLivenessFacts.Point)
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    {sourceEnv : List Name}
    (hFunctions : lowerCtx.functions = sourceProgram.functions)
    (hNodup : targetCtx.layout.Nodup)
    (hArgsScoped :
      ∀ arg, arg ∈ args → Functions.Scope.ExprScoped sourceEnv arg)
    (hArgsSupported :
      Functions.InteractionSemantics.ArgList.OpenSupported args)
    (hSchedule :
      StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout (.call callTargets functionName args :: rest)
          (fact :: restFacts) =
        some (point :: points, finalLayout))
    (hLower :
      StackLowering.lowerStmtListFuel lowerFuel lowerCtx
          (.call callTargets functionName args :: rest) (point :: points) =
        some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx))
    (hCallee :
      ∀ (callCtx : Locals.Ctx) (fn : Functions.FunDef),
        Functions.Source.FunList.find? functionName sourceProgram.functions =
            some fn →
        ∀ (targetFuel : Nat)
          {suffix : List Word} {returns : List Structured.ReturnDest}
          {source sourceAfterArgs : Locals.Source.State}
          {target targetAfterArgs : Structured.RunState}
          {argValues : List Word},
          StateRel callCtx.layout suffix returns source target →
          Locals.InteractionPreservation.Expr.ResultRel args.length
              source target (sourceAfterArgs, argValues) targetAfterArgs →
          (∀ {proc : Expressions.Proc},
            Expressions.EffectSemantics.ProcList.lookup? functionName
                targetProgram.procs = some proc →
            Expressions.TargetFuel.Covers targetProgram sourceFuel
              (targetFuel - 1) proc.body.stmts) →
          Simulation.Interaction.ForwardRel
            FuelTruncated
            (StackCallPreservation.OpenAttachedCallResultRel
              fn.returns.length target.evm.stack returns)
            (Functions.InteractionSemantics.FunDef.openRunBody sourceProgram
              fn argValues sourceFuel sourceAfterArgs)
            (Expressions.InteractionSemantics.Stmt.openRun targetProgram
              targetFuel (.call functionName) targetAfterArgs))
    (hTail :
      ∀ {tailLayout : Locals.Layout} {tailFinal : Locals.Layout}
        {tailLowered : List Locals.Stmt} {middleCtx tailFinalCtx : Locals.Ctx}
        {tailCode : List Expressions.Stmt},
        middleCtx.layout = tailLayout →
        middleCtx.layout.Nodup →
        Locals.Ctx.SameControl targetCtx middleCtx →
        StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
            tailLayout rest restFacts = some (points, tailFinal) →
        StackLowering.lowerStmtListFuel lowerFuel lowerCtx rest points =
          some tailLowered →
        Locals.Block.compileOpen middleCtx { stmts := tailLowered } =
          some (tailCode, tailFinalCtx) →
        ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames middleCtx tailFinalCtx rest tailFinal tailCode
          (sourceFuel + 1) ∧
        tailFinalCtx.layout.Nodup) :
    ControlScheduledListPreservesAt sourceProgram targetProgram targets
      returnNames targetCtx finalCtx
      (.call callTargets functionName args :: rest) finalLayout code
      ((sourceFuel + 1) + 1) ∧
    finalCtx.layout.Nodup := by
  apply controlFallthroughConsAt_of_compilers returnNames sourceProgram
    targetProgram lowerCtx targets pinned scheduleFuel lowerFuel
    (sourceFuel + 1)
    (.call callTargets functionName args) rest fact restFacts hSchedule hLower
    hCompile
  · intro before rawPoint hRaw
    exact
      (StackSchedule.scheduleStmtFuelWithTargets_call_components hRaw).2.2.2.2
  · intro order rawPoint retain pointLowered pointCode middleCtx hOrderBuild
      hRawSchedule hRetainBuild hPointLower hPointCompile
    obtain ⟨hRawBefore, hRawStatement, _hRawRetain, _hRawRegions,
        _hRawFalls⟩ :=
      StackSchedule.scheduleStmtFuelWithTargets_call_components hRawSchedule
    obtain ⟨_fn, lowerRetain, _hFind, _hArgsLength, _hTargetsLength,
        _hTargetsNodup, hAccess, _hFalls, _hRegions, hLowerRetain,
        _hPointLowered⟩ :=
      StackLowering.lowerPointFuel_call_components hPointLower
    have hLowerRetainEq : lowerRetain = retain :=
      Option.some.inj (hLowerRetain.symm.trans rfl)
    subst lowerRetain
    have hRetainSource :
        (targetCtx.withLayout order.target).layout = retain.source := by
      have hBuiltSource : rawPoint.statementLayout = retain.source :=
        (AllocationLayout.RegularTransition.build?_sound hRetainBuild).1.symm
      simpa [Locals.Ctx.withLayout] using
        hRawStatement.symm.trans hBuiltSource
    have hOrderSource : targetCtx.layout = order.source :=
      (AllocationLayout.Ordering.build?_source hOrderBuild).symm
    have hOrderedNodup : order.target.Nodup :=
      order.target_nodup (by rw [← hOrderSource]; exact hNodup)
    have hCallAccess :
        StackAccess.call? order.target callTargets args = some () := by
      simpa [StackLowering.pointAccess?, hRawBefore] using hAccess
    unfold StackAccess.call? at hCallAccess
    obtain ⟨_unit, hArgAccess, _hReturnedAccess⟩ :=
      Option.bind_eq_some_iff.mp hCallAccess
    have hArgScoped :
        Locals.Scope.ExprSeqScoped order.target (Lower.argExprs args) :=
      StackCallPreservation.argExprs_localsScoped_of_check hArgAccess
        hArgsScoped
    have hOrderedTargets :
        ∀ name, name ∈ callTargets → name ∈ order.target := by
      exact StackAccess.call_targets_mem hCallAccess
    obtain ⟨compiledRetain, hCompiledRetain, hCompiled⟩ :=
      StackCallPreservation.CallPoint.compiledOfCompilersAtSucc sourceProgram
        targetProgram lowerCtx targets returnNames sourceFuel callTargets
        functionName args
        { rawPoint with order? := some order, retain? := some retain }
        pointLowered (targetCtx.withLayout order.target) middleCtx pointCode
        lowerFuel hFunctions (by simpa [Locals.Ctx.withLayout] using
          hOrderedNodup) hOrderedTargets hArgScoped hArgsSupported
        (by
          intro candidate hCandidate
          have hCandidateEq : candidate = retain :=
            Option.some.inj (hCandidate.symm.trans rfl)
          subst candidate
          exact hRetainSource)
        hPointLower hPointCompile
        (hCallee (targetCtx.withLayout order.target))
    have hCompiledRetainEq : compiledRetain = retain :=
      Option.some.inj (hCompiledRetain.symm.trans rfl)
    subst compiledRetain
    refine ⟨hCompiled, ?_⟩
    rw [hCompiled.layout]
    exact retain.target_nodup
  · exact hTail

theorem callConsAtOne_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel : Nat)
    (callTargets : List Name) (functionName : Name)
    (args : List (Functions.Expr 1))
    (rest : List Functions.Stmt)
    (fact : AllocationLivenessFacts.Point)
    (restFacts : List AllocationLivenessFacts.Point)
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    (hNodup : targetCtx.layout.Nodup)
    (hSchedule :
      StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout (.call callTargets functionName args :: rest)
          (fact :: restFacts) =
        some (point :: points, finalLayout))
    (hLower :
      StackLowering.lowerStmtListFuel lowerFuel lowerCtx
          (.call callTargets functionName args :: rest) (point :: points) =
        some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx))
    (hTail :
      ∀ {tailLayout : Locals.Layout} {tailFinal : Locals.Layout}
        {tailLowered : List Locals.Stmt} {middleCtx tailFinalCtx : Locals.Ctx}
        {tailCode : List Expressions.Stmt},
        middleCtx.layout = tailLayout →
        middleCtx.layout.Nodup →
        Locals.Ctx.SameControl targetCtx middleCtx →
        StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
            tailLayout rest restFacts = some (points, tailFinal) →
        StackLowering.lowerStmtListFuel lowerFuel lowerCtx rest points =
          some tailLowered →
        Locals.Block.compileOpen middleCtx { stmts := tailLowered } =
          some (tailCode, tailFinalCtx) →
        ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames middleCtx tailFinalCtx rest tailFinal tailCode 0 ∧
        tailFinalCtx.layout.Nodup) :
    ControlScheduledListPreservesAt sourceProgram targetProgram targets
      returnNames targetCtx finalCtx
      (.call callTargets functionName args :: rest) finalLayout code 1 ∧
    finalCtx.layout.Nodup := by
  apply controlFallthroughConsAt_of_compilers returnNames sourceProgram
    targetProgram lowerCtx targets pinned scheduleFuel lowerFuel 0
    (.call callTargets functionName args) rest fact restFacts hSchedule hLower
    hCompile
  · intro before rawPoint hRaw
    exact
      (StackSchedule.scheduleStmtFuelWithTargets_call_components hRaw).2.2.2.2
  · intro order rawPoint retain pointLowered pointCode middleCtx hOrderBuild
      hRawSchedule hRetainBuild hPointLower hPointCompile
    obtain ⟨_hRawBefore, hRawStatement, _hRawRetain, _hRawRegions,
        _hRawFalls⟩ :=
      StackSchedule.scheduleStmtFuelWithTargets_call_components hRawSchedule
    obtain ⟨_fn, lowerRetain, _hFind, _hArgsLength, _hTargetsLength,
        _hTargetsNodup, _hAccess, _hFalls, _hRegions, hLowerRetain,
        _hPointLowered⟩ :=
      StackLowering.lowerPointFuel_call_components hPointLower
    have hLowerRetainEq : lowerRetain = retain :=
      Option.some.inj (hLowerRetain.symm.trans rfl)
    subst lowerRetain
    have hRetainSource :
        (targetCtx.withLayout order.target).layout = retain.source := by
      have hBuiltSource : rawPoint.statementLayout = retain.source :=
        (AllocationLayout.RegularTransition.build?_sound hRetainBuild).1.symm
      simpa [Locals.Ctx.withLayout] using
        hRawStatement.symm.trans hBuiltSource
    have hOrderSource : targetCtx.layout = order.source :=
      (AllocationLayout.Ordering.build?_source hOrderBuild).symm
    have hOrderedNodup : order.target.Nodup :=
      order.target_nodup (by rw [← hOrderSource]; exact hNodup)
    obtain ⟨compiledRetain, hCompiledRetain, hCompiled⟩ :=
      StackCallPreservation.CallPoint.compiledOfCompilersAtZero sourceProgram
        targetProgram lowerCtx targets returnNames callTargets functionName
        args { rawPoint with order? := some order, retain? := some retain }
        pointLowered (targetCtx.withLayout order.target) middleCtx pointCode
        lowerFuel
        (by
          intro candidate hCandidate
          have hCandidateEq : candidate = retain :=
            Option.some.inj (hCandidate.symm.trans rfl)
          subst candidate
          exact hRetainSource)
        hPointLower hPointCompile
    have hCompiledRetainEq : compiledRetain = retain :=
      Option.some.inj (hCompiledRetain.symm.trans rfl)
    subst compiledRetain
    refine ⟨hCompiled, ?_⟩
    rw [hCompiled.layout]
    exact retain.target_nodup
  · exact hTail

theorem brkControlList_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel : Nat)
    (rest : List Functions.Stmt)
    (fact : AllocationLivenessFacts.Point)
    (restFacts : List AllocationLivenessFacts.Point)
    {targetLayout : Locals.Layout}
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    (hTarget : targets.brk? = some targetLayout)
    (hTargetDepth : targetCtx.breakDepth? = some targetLayout.length)
    (hSchedule :
      StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout (.brk :: rest) (fact :: restFacts) =
        some (point :: points, finalLayout))
    (hLower :
      StackLowering.lowerStmtListFuel lowerFuel lowerCtx
          (.brk :: rest) (point :: points) = some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx)) :
    ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
      targetCtx finalCtx (.brk :: rest) finalLayout code := by
  have hCompiled :
      CompiledControlPoint sourceProgram targetProgram targets returnNames targetCtx
        finalCtx .brk code finalLayout := by
    apply compiledNonfallPoint_of_compilers returnNames sourceProgram targetProgram lowerCtx
      targets pinned scheduleFuel lowerFuel .brk rest fact restFacts hSchedule
      hLower hCompile
    · intro before rawPoint hRaw
      obtain ⟨_exit, _hExit, _hBefore, _hStatement, _hPointExit,
          _hRetain, _hRegions, hFalls⟩ :=
        StackSchedule.scheduleStmtFuelWithTargets_brk_components hTarget hRaw
      exact hFalls
    · intro order rawPoint pointLowered pointCode middleCtx hOrderBuild
        hRawSchedule hPointLower hPointCompile
      obtain ⟨exit, hExitBuild, _hRawBefore, hRawStatement, hRawExit,
          _hRawRetain, _hRawRegions, _hRawFalls⟩ :=
        StackSchedule.scheduleStmtFuelWithTargets_brk_components hTarget
          hRawSchedule
      obtain ⟨_hAccess, _hLowerFalls, _hLowerRegions, _hLowerRetain,
          hPointLowered⟩ :=
        StackLowering.lowerPointFuel_brk_components hPointLower
      have hExitSource : order.target = exit.source :=
        (AllocationLayout.Join.build?_endpoints hExitBuild).1.symm
      have hExitTarget : exit.target = targetLayout :=
        (AllocationLayout.Join.build?_endpoints hExitBuild).2
      have hTarget' : targets.brk? = some exit.target := by
        rw [hExitTarget]
        exact hTarget
      have hDepth :
          (targetCtx.withLayout order.target).breakDepth? =
            some exit.target.length := by
        rw [hExitTarget]
        simpa [Locals.Ctx.withLayout] using hTargetDepth
      have hPointLowered' :
          pointLowered = exit.statements ++ [.brk] := by
        simpa [StackLowering.exitStmts, hRawExit] using hPointLowered
      have hPointCompiled :=
        compiledBrkControlPointOfEquations sourceProgram targetProgram targets returnNames
          (targetCtx.withLayout order.target) middleCtx exit pointLowered
          pointCode hTarget'
          (by simpa [Locals.Ctx.withLayout] using hExitSource)
          hDepth hPointLowered' hPointCompile
      simpa [hRawStatement, hExitTarget] using hPointCompiled
  apply controlNonfallPointToList returnNames sourceProgram targetProgram targets targetCtx
    finalCtx .brk rest code finalLayout hCompiled
  intro sourceCtx sourceFuel source returns hCtx
  obtain ⟨scope, hSourceScope, _hScopeCovers⟩ :=
    (hCtx.breakTarget hTarget).sourceCovers
  rw [Functions.InteractionSemantics.Block.openRun_cons]
  simp only [Functions.InteractionSemantics.Stmt.openRun,
    Functions.Source.Canonical.Stmt.run,
    Functions.Source.Effectful.Control.Stmt.run, hSourceScope]
  let result :=
    (Locals.Source.Effectful.Outcome.brk
        (Functions.InteractionSemantics.stateModel.restrictTo scope source),
      sourceCtx)
  change Simulation.Interaction.bind
      ((pure result) :
        Simulation.Interaction EVMException
          (Locals.Source.Effectful.Outcome Locals.Source.State ×
            Functions.Source.Ctx)) _ =
    ((pure result) :
      Simulation.Interaction EVMException
        (Locals.Source.Effectful.Outcome Locals.Source.State ×
          Functions.Source.Ctx))
  change Simulation.Interaction.bind
      (Simulation.Interaction.done (.ok result)) _ =
    Simulation.Interaction.done (.ok result)
  rw [Simulation.Interaction.bind_done_ok]
  simp [result]
  rfl

theorem contControlList_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel : Nat)
    (rest : List Functions.Stmt)
    (fact : AllocationLivenessFacts.Point)
    (restFacts : List AllocationLivenessFacts.Point)
    {targetLayout : Locals.Layout}
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    (hTarget : targets.cont? = some targetLayout)
    (hTargetDepth : targetCtx.continueDepth? = some targetLayout.length)
    (hSchedule :
      StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout (.cont :: rest) (fact :: restFacts) =
        some (point :: points, finalLayout))
    (hLower :
      StackLowering.lowerStmtListFuel lowerFuel lowerCtx
          (.cont :: rest) (point :: points) = some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx)) :
    ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
      targetCtx finalCtx (.cont :: rest) finalLayout code := by
  have hCompiled :
      CompiledControlPoint sourceProgram targetProgram targets returnNames targetCtx
        finalCtx .cont code finalLayout := by
    apply compiledNonfallPoint_of_compilers returnNames sourceProgram targetProgram lowerCtx
      targets pinned scheduleFuel lowerFuel .cont rest fact restFacts hSchedule
      hLower hCompile
    · intro before rawPoint hRaw
      obtain ⟨_exit, _hExit, _hBefore, _hStatement, _hPointExit,
          _hRetain, _hRegions, hFalls⟩ :=
        StackSchedule.scheduleStmtFuelWithTargets_cont_components hTarget hRaw
      exact hFalls
    · intro order rawPoint pointLowered pointCode middleCtx hOrderBuild
        hRawSchedule hPointLower hPointCompile
      obtain ⟨exit, hExitBuild, _hRawBefore, hRawStatement, hRawExit,
          _hRawRetain, _hRawRegions, _hRawFalls⟩ :=
        StackSchedule.scheduleStmtFuelWithTargets_cont_components hTarget
          hRawSchedule
      obtain ⟨_hAccess, _hLowerFalls, _hLowerRegions, _hLowerRetain,
          hPointLowered⟩ :=
        StackLowering.lowerPointFuel_cont_components hPointLower
      have hExitSource : order.target = exit.source :=
        (AllocationLayout.Join.build?_endpoints hExitBuild).1.symm
      have hExitTarget : exit.target = targetLayout :=
        (AllocationLayout.Join.build?_endpoints hExitBuild).2
      have hTarget' : targets.cont? = some exit.target := by
        rw [hExitTarget]
        exact hTarget
      have hDepth :
          (targetCtx.withLayout order.target).continueDepth? =
            some exit.target.length := by
        rw [hExitTarget]
        simpa [Locals.Ctx.withLayout] using hTargetDepth
      have hPointLowered' :
          pointLowered = exit.statements ++ [.cont] := by
        simpa [StackLowering.exitStmts, hRawExit] using hPointLowered
      have hPointCompiled :=
        compiledContControlPointOfEquations sourceProgram targetProgram targets returnNames
          (targetCtx.withLayout order.target) middleCtx exit pointLowered
          pointCode hTarget'
          (by simpa [Locals.Ctx.withLayout] using hExitSource)
          hDepth hPointLowered' hPointCompile
      simpa [hRawStatement, hExitTarget] using hPointCompiled
  apply controlNonfallPointToList returnNames sourceProgram targetProgram targets targetCtx
    finalCtx .cont rest code finalLayout hCompiled
  intro sourceCtx sourceFuel source returns hCtx
  obtain ⟨scope, hSourceScope, _hScopeCovers⟩ :=
    (hCtx.continueTarget hTarget).sourceCovers
  rw [Functions.InteractionSemantics.Block.openRun_cons]
  simp only [Functions.InteractionSemantics.Stmt.openRun,
    Functions.Source.Canonical.Stmt.run,
    Functions.Source.Effectful.Control.Stmt.run, hSourceScope]
  let result :=
    (Locals.Source.Effectful.Outcome.cont
        (Functions.InteractionSemantics.stateModel.restrictTo scope source),
      sourceCtx)
  change Simulation.Interaction.bind
      ((pure result) :
        Simulation.Interaction EVMException
          (Locals.Source.Effectful.Outcome Locals.Source.State ×
            Functions.Source.Ctx)) _ =
    ((pure result) :
      Simulation.Interaction EVMException
        (Locals.Source.Effectful.Outcome Locals.Source.State ×
          Functions.Source.Ctx))
  change Simulation.Interaction.bind
      (Simulation.Interaction.done (.ok result)) _ =
    Simulation.Interaction.done (.ok result)
  rw [Simulation.Interaction.bind_done_ok]
  simp [result]
  rfl

theorem leaveControlList_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel : Nat)
    (rest : List Functions.Stmt)
    (fact : AllocationLivenessFacts.Point)
    (restFacts : List AllocationLivenessFacts.Point)
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    (hReturns : lowerCtx.returns = returnNames)
    (hSchedule :
      StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout (.leave :: rest) (fact :: restFacts) =
        some (point :: points, finalLayout))
    (hLower :
      StackLowering.lowerStmtListFuel lowerFuel lowerCtx
          (.leave :: rest) (point :: points) = some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx)) :
    ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
      targetCtx finalCtx (.leave :: rest) finalLayout code := by
  have hCompiled :
      CompiledControlPoint sourceProgram targetProgram targets returnNames targetCtx
        finalCtx .leave code finalLayout := by
    apply compiledNonfallPoint_of_compilers returnNames sourceProgram targetProgram lowerCtx
      targets pinned scheduleFuel lowerFuel .leave rest fact restFacts
      hSchedule hLower hCompile
    · intro before rawPoint hRaw
      exact
        (StackSchedule.scheduleStmtFuelWithTargets_leave_components
          hRaw).2.2.2.2
    · intro order rawPoint pointLowered pointCode middleCtx _hOrderBuild
        hRawSchedule hPointLower hPointCompile
      obtain ⟨hRawBefore, hRawStatement, _hRawRetain, _hRawRegions,
          _hRawFalls⟩ :=
        StackSchedule.scheduleStmtFuelWithTargets_leave_components
          hRawSchedule
      obtain ⟨hAccess, _hLowerFalls, _hLowerRegions, _hLowerRetain,
          hPointLowered⟩ :=
        StackLowering.lowerPointFuel_leave_components hPointLower
      have hAccess' :
          StackAccess.ExprSeq.check? rawPoint.beforeLayout 0
              (StackLowering.returnWords lowerCtx.returns) = some () := by
        simpa [StackLowering.pointAccess?] using hAccess
      rw [hReturns] at hAccess'
      have hReturnAccess :
          StackAccess.ExprSeq.check? order.target 0
              (StackLowering.returnWords returnNames) = some () := by
        simpa [hRawBefore] using hAccess'
      have hPointLowered' :
          pointLowered =
            StackLowering.pushWordReturns returnNames ++ [.leave] := by
        simpa [hReturns] using hPointLowered
      have hPointCompiled :=
        compiledLeaveControlPointOfEquations sourceProgram targetProgram
          targets returnNames (targetCtx.withLayout order.target) middleCtx
          pointLowered pointCode
          (by simpa [Locals.Ctx.withLayout] using hReturnAccess)
          hPointLowered' hPointCompile
      simpa [hRawStatement, Locals.Ctx.withLayout] using hPointCompiled
  apply controlNonfallPointToList returnNames sourceProgram targetProgram targets targetCtx
    finalCtx .leave rest code finalLayout hCompiled
  intro sourceCtx sourceFuel source _returns _hCtx
  exact
    Functions.InteractionSemantics.Block.openRun_leave_cons sourceProgram
      sourceCtx sourceFuel rest source

theorem terminalControlList_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel : Nat)
    (kind : Assembly.HaltKind) (rest : List Functions.Stmt)
    (fact : AllocationLivenessFacts.Point)
    (restFacts : List AllocationLivenessFacts.Point)
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    (hArgCount : kind.argCount = 0)
    (hSchedule :
      StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout (.terminal kind :: rest) (fact :: restFacts) =
        some (point :: points, finalLayout))
    (hLower :
      StackLowering.lowerStmtListFuel lowerFuel lowerCtx
          (.terminal kind :: rest) (point :: points) = some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx)) :
    ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
      targetCtx finalCtx (.terminal kind :: rest) finalLayout code := by
  have hCompiled :
      CompiledControlPoint sourceProgram targetProgram targets returnNames targetCtx
        finalCtx (.terminal kind) code finalLayout := by
    apply compiledNonfallPoint_of_compilers returnNames sourceProgram targetProgram lowerCtx
      targets pinned scheduleFuel lowerFuel (.terminal kind) rest fact restFacts
      hSchedule hLower hCompile
    · intro before rawPoint hRaw
      exact
        (StackSchedule.scheduleStmtFuelWithTargets_terminal_components
          hRaw).2.2.2.2
    · intro order rawPoint pointLowered pointCode middleCtx _hOrderBuild
        hRawSchedule hPointLower hPointCompile
      obtain ⟨_hRawBefore, hRawStatement, _hRawRetain, _hRawRegions,
          _hRawFalls⟩ :=
        StackSchedule.scheduleStmtFuelWithTargets_terminal_components
          hRawSchedule
      obtain ⟨_hAccess, _hLowerFalls, _hLowerRegions, _hLowerRetain,
          hPointLowered⟩ :=
        StackLowering.lowerPointFuel_terminal_components hPointLower
      have hPointCompiled :=
        compiledTerminalControlPointOfEquations sourceProgram targetProgram
          targets returnNames (targetCtx.withLayout order.target) middleCtx kind
          pointLowered pointCode hArgCount hPointLowered hPointCompile
      simpa [hRawStatement, Locals.Ctx.withLayout] using hPointCompiled
  apply controlNonfallPointToList returnNames sourceProgram targetProgram targets targetCtx
    finalCtx (.terminal kind) rest code finalLayout hCompiled
  intro sourceCtx sourceFuel source returns _hCtx
  simpa [Functions.InteractionSemantics.Stmt.openRun] using
    Functions.InteractionSemantics.Block.openRun_terminal_cons sourceProgram
      sourceCtx sourceFuel kind rest source

theorem terminalArgsControlList_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel : Nat)
    (kind : Assembly.HaltKind) (args : Locals.ExprSeq kind.argCount)
    (rest : List Functions.Stmt)
    (fact : AllocationLivenessFacts.Point)
    (restFacts : List AllocationLivenessFacts.Point)
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    {sourceEnv : List Name}
    (hScoped : Functions.Scope.ExprSeqScoped sourceEnv args)
    (hSupported : Locals.InteractionSemantics.ExprSeq.OpenSupported args)
    (hSchedule :
      StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout (.terminalArgs kind args :: rest)
          (fact :: restFacts) = some (point :: points, finalLayout))
    (hLower :
      StackLowering.lowerStmtListFuel lowerFuel lowerCtx
          (.terminalArgs kind args :: rest) (point :: points) = some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx)) :
    ControlScheduledListPreserves sourceProgram targetProgram targets returnNames
      targetCtx finalCtx (.terminalArgs kind args :: rest) finalLayout code := by
  have hCompiled :
      CompiledControlPoint sourceProgram targetProgram targets returnNames targetCtx
        finalCtx (.terminalArgs kind args) code finalLayout := by
    apply compiledNonfallPoint_of_compilers returnNames sourceProgram targetProgram lowerCtx
      targets pinned scheduleFuel lowerFuel (.terminalArgs kind args) rest fact
      restFacts hSchedule hLower hCompile
    · intro before rawPoint hRaw
      exact
        (StackSchedule.scheduleStmtFuelWithTargets_terminalArgs_components
          hRaw).2.2.2.2
    · intro order rawPoint pointLowered pointCode middleCtx _hOrderBuild
        hRawSchedule hPointLower hPointCompile
      obtain ⟨hRawBefore, hRawStatement, _hRawRetain, _hRawRegions,
          _hRawFalls⟩ :=
        StackSchedule.scheduleStmtFuelWithTargets_terminalArgs_components
          hRawSchedule
      obtain ⟨hAccess, _hLowerFalls, _hLowerRegions, _hLowerRetain,
          hPointLowered⟩ :=
        StackLowering.lowerPointFuel_terminalArgs_components hPointLower
      have hArgsAccess :
          StackAccess.ExprSeq.check? order.target 0 args = some () := by
        simpa [StackLowering.pointAccess?, hRawBefore] using hAccess
      have hPointCompiled :=
        compiledTerminalArgsControlPointOfEquations sourceProgram
          targetProgram targets returnNames
          (targetCtx.withLayout order.target) middleCtx
          kind args pointLowered pointCode hScoped hSupported
          (by simpa [Locals.Ctx.withLayout] using hArgsAccess)
          hPointLowered hPointCompile
      simpa [hRawStatement, Locals.Ctx.withLayout] using hPointCompiled
  apply controlNonfallPointToList returnNames sourceProgram targetProgram targets targetCtx
    finalCtx (.terminalArgs kind args) rest code finalLayout hCompiled
  intro sourceCtx sourceFuel source returns _hCtx
  simpa [Functions.InteractionSemantics.Stmt.openRun] using
    Functions.InteractionSemantics.Block.openRun_terminalArgs_cons
      sourceProgram sourceCtx sourceFuel kind args rest source

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
    (transition : AllocationLayout.RegularTransition)
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
              (targetFuel - (transition.schedule.discards.length + 2))
              { stmts := tailCode } targetMid)) :
    ∃ artifact : StackTransitionCompilation.RegularArtifact targetCtx transition,
      Locals.Block.compileOpen targetCtx
          { stmts := transition.statements } =
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
        transition.schedule.discards.length :=
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

theorem regularConsResult
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targetCtx middleCtx finalCtx : Locals.Ctx)
    (stmt : Functions.Stmt) (rest : List Functions.Stmt)
    (point : StackSchedule.Point) (points : List StackSchedule.Point)
    (order : AllocationLayout.Ordering)
    (transition : AllocationLayout.RegularTransition)
    (finalLayout tailFinal : Locals.Layout)
    (headCode tailCode code : List Expressions.Stmt)
    (hOrder : point.order? = some order)
    (hRetain : point.retain? = some transition)
    (hMiddle :
      middleCtx = targetCtx.withLayout transition.schedule.target)
    (hHeadLength :
      headCode.length =
        order.promotions.length + transition.schedule.discards.length + 2)
    (hHead :
      ∀ (sourceCtx : Functions.Source.Ctx)
        (sourceFuel targetFuel : Nat)
        {suffix : List Word} {returns : List Structured.ReturnDest}
        {source : Locals.Source.State} {target : Structured.RunState},
        order.promotions.length +
            transition.schedule.discards.length + 2 < targetFuel →
        CtxCovers sourceCtx targetCtx →
        StateRel targetCtx.layout suffix returns source target →
        Simulation.Interaction.Rel
          (RegularOutcomeRel middleCtx suffix returns)
          (Functions.InteractionSemantics.Stmt.openRun
            sourceProgram sourceCtx sourceFuel stmt source)
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            targetFuel { stmts := headCode } target))
    (hTail :
      RegularListPreserves sourceProgram targetProgram middleCtx finalCtx
        rest points tailFinal tailCode)
    (hFinal : finalLayout = tailFinal)
    (hCode : code = headCode ++ tailCode) :
    RegularListPreserves sourceProgram targetProgram targetCtx finalCtx
      (stmt :: rest) (point :: points) finalLayout code := by
  rcases hTail with ⟨hTailFinal, hTailLength, hTailForward⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hFinal]
    exact hTailFinal
  · rw [hCode, List.length_append, hHeadLength, hTailLength]
    simp [regularLeafTargetCost, hOrder, hRetain]
    omega
  · intro sourceCtx suffix returns source target hCtx hInitial
    have hHeadFuel :
        order.promotions.length + transition.schedule.discards.length + 2 <
          regularLeafTargetCost (point :: points) + 1 := by
      simp [regularLeafTargetCost, hOrder, hRetain]
      omega
    have hHeadRun :=
      hHead sourceCtx (rest.length + 1)
        (regularLeafTargetCost (point :: points) + 1)
        hHeadFuel hCtx hInitial
    have hTailFuel :
        regularLeafTargetCost (point :: points) + 1 - headCode.length =
          regularLeafTargetCost points + 1 := by
      simp [regularLeafTargetCost, hOrder, hRetain, hHeadLength]
      omega
    have hComposed :=
      regularCons sourceProgram targetProgram sourceCtx middleCtx finalCtx
        (rest.length + 1)
        (regularLeafTargetCost (point :: points) + 1)
        stmt rest headCode tailCode hHeadRun
        (by
          intro sourceMid targetMid sourceMidCtx hCtxMid hStateMid
          rw [hTailFuel]
          exact hTailForward sourceMidCtx hCtxMid hStateMid)
    simpa [hCode] using hComposed

inductive RegularLeafList : List Functions.Stmt → Prop
  | nil : RegularLeafList []
  | expr {rest : List Functions.Stmt} (expr : Functions.Expr 0)
      (tail : RegularLeafList rest) :
      RegularLeafList (.expr expr :: rest)
  | let_ {rest : List Functions.Stmt} (name : Name)
      (value : Functions.Expr 1) (tail : RegularLeafList rest) :
      RegularLeafList (.let_ name value :: rest)
  | assign {rest : List Functions.Stmt} (name : Name)
      (value : Functions.Expr 1) (tail : RegularLeafList rest) :
      RegularLeafList (.assign name value :: rest)

theorem regularLeafList_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel : Nat)
    {sourceEnv : List Name} {stmts : List Functions.Stmt}
    {facts : List AllocationLivenessFacts.Point}
    {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx}
    {code : List Expressions.Stmt}
    (hLeaves : RegularLeafList stmts)
    (hScoped : Functions.Scope.StmtList.Scoped sourceEnv stmts)
    (hSupported : Functions.InteractionSemantics.StmtList.OpenSupported stmts)
    (hSchedule :
      StackSchedule.scheduleStmtListFuel scheduleFuel pinned targetCtx.layout
          stmts facts = some (points, finalLayout))
    (hLower :
      StackLowering.lowerStmtListFuel lowerFuel lowerCtx stmts points =
        some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx))
    (hNodup : targetCtx.layout.Nodup) :
    RegularListPreserves sourceProgram targetProgram targetCtx finalCtx
      stmts points finalLayout code := by
  induction hLeaves generalizing sourceEnv facts points finalLayout lowered
      targetCtx finalCtx code with
  | nil =>
      cases facts with
      | nil =>
          obtain ⟨hPoints, hFinal⟩ :=
            StackSchedule.scheduleStmtListFuel_nil_components hSchedule
          subst points
          have hLowered :=
            StackLowering.lowerStmtListFuel_nil_components hLower
          subst lowered
          simp [Locals.Block.compileOpen] at hCompile
          rcases hCompile with ⟨rfl, rfl⟩
          refine ⟨hFinal.symm, rfl, ?_⟩
          intro sourceCtx suffix returns source target hCtx hInitial
          exact
            regularEmpty sourceProgram targetProgram sourceCtx targetCtx
              1 1 (by omega) (by omega) hCtx hInitial
      | cons fact restFacts =>
          simp [StackSchedule.scheduleStmtListFuel,
            StackSchedule.scheduleStmtListFuelWithTargets] at hSchedule
  | @expr rest expr hTailLeaves ih =>
      cases facts with
      | nil =>
          simp [StackSchedule.scheduleStmtListFuel,
            StackSchedule.scheduleStmtListFuelWithTargets] at hSchedule
      | cons fact restFacts =>
          obtain ⟨point, tailPoints, hPoints⟩ :=
            StackSchedule.scheduleStmtListFuel_cons_nonempty hSchedule
          subst points
          obtain
              ⟨order, retain, tailFinal, hOrderBuild, hPointOrder,
                hBefore, _hStatement, hPointRetain, _hRegions, _hFalls,
                hBuild, hTailSchedule, hFinal⟩ :=
            StackSchedule.scheduleStmtListFuel_expr_components hSchedule
          obtain
              ⟨lowerOrder, lowerRetain, tailLowered, hLowerOrder,
                hPointAccess, hLowerRetain, hTailLower, hLowered⟩ :=
            StackLowering.lowerStmtListFuel_expr_components hLower
          have hOrderEq : lowerOrder = order :=
            Option.some.inj (hLowerOrder.symm.trans hPointOrder)
          subst lowerOrder
          have hRetainEq : lowerRetain = retain :=
            Option.some.inj (hLowerRetain.symm.trans hPointRetain)
          subst lowerRetain
          have hOrderSource : targetCtx.layout = order.source :=
            (AllocationLayout.Ordering.build?_source hOrderBuild).symm
          have hAccess :
              StackAccess.Expr.check? order.target 0 expr = some () := by
            simpa [StackLowering.pointAccess?, hBefore] using hPointAccess
          have hSource : order.target = retain.source :=
            (AllocationLayout.RegularTransition.build?_sound hBuild).1.symm
          rw [hLowered] at hCompile
          obtain
              ⟨headCode, middleCtx, tailCode,
                hHeadCompile, hTailCompile, hCode⟩ :=
            Locals.Block.compileOpen_append_components hCompile
          have hHeadCompile' :
              Locals.Block.compileOpen targetCtx
                  { stmts :=
                      order.statements ++
                        ([.expr expr] ++
                          StackLowering.transitionStmts retain) } =
                some (headCode, middleCtx) := by
            simpa [List.append_assoc] using hHeadCompile
          obtain
              ⟨orderCode, orderedCtx, bodyCode, hOrderCompile,
                hBodyCompile, hHeadCode⟩ :=
            Locals.Block.compileOpen_append_components hHeadCompile'
          obtain ⟨orderArtifact⟩ :=
            StackTransitionCompilation.Ordering.compileArtifact order
              hOrderSource
          have hOrderPair :=
            Option.some.inj
              (orderArtifact.compileEq.symm.trans hOrderCompile)
          have hOrderCode :
              orderArtifact.promotionCodes.map Expressions.Stmt.code =
                orderCode :=
            congrArg Prod.fst hOrderPair
          have hOrderedCtx :
              targetCtx.withLayout order.target = orderedCtx :=
            congrArg Prod.snd hOrderPair
          rw [← hOrderCode] at hHeadCode
          rw [← hOrderedCtx] at hBodyCompile
          obtain ⟨hMiddle, hHeadLength, hHeadForward⟩ :=
            compiledExprPointOfEquations sourceProgram targetProgram
              (targetCtx.withLayout order.target) middleCtx expr retain
              ([.expr expr] ++ StackLowering.transitionStmts retain)
              bodyCode (by simpa [Locals.Ctx.withLayout] using hSource)
              hScoped.1 hSupported.1 hAccess rfl hBodyCompile
          have hOrderLength :
              orderArtifact.promotionCodes.length = order.promotions.length :=
            orderArtifact.codes.code_length
          have hWholeLength :
              headCode.length =
                order.promotions.length +
                  retain.schedule.discards.length + 2 := by
            rw [hHeadCode, List.length_append, List.length_map,
              hHeadLength, hOrderLength]
            omega
          have hWholeForward :
              ∀ (sourceCtx : Functions.Source.Ctx)
                (sourceFuel targetFuel : Nat)
                {suffix : List Word}
                {returns : List Structured.ReturnDest}
                {source : Locals.Source.State}
                {target : Structured.RunState},
                order.promotions.length +
                    retain.schedule.discards.length + 2 < targetFuel →
                CtxCovers sourceCtx targetCtx →
                StateRel targetCtx.layout suffix returns source target →
                Simulation.Interaction.Rel
                  (RegularOutcomeRel middleCtx suffix returns)
                  (Functions.InteractionSemantics.Stmt.openRun
                    sourceProgram sourceCtx sourceFuel (.expr expr) source)
                  (Expressions.InteractionSemantics.Block.openRun
                    targetProgram targetFuel
                    { stmts := headCode } target) := by
            intro sourceCtx sourceFuel targetFuel suffix returns source target
              hFuel hCtx hInitial
            rw [hHeadCode]
            apply orderArtifact.thenBlock targetProgram targetFuel
                (by rw [hOrderLength]; omega) hInitial
            intro orderedTarget hOrderedRel
            exact
              hHeadForward sourceCtx sourceFuel
                (targetFuel - orderArtifact.promotionCodes.length)
                (by rw [hOrderLength]; omega)
                (hCtx.afterOrdering order hOrderSource) hOrderedRel
          have hRetainSourceNodup : retain.source.Nodup := by
            rw [← hSource]
            exact order.target_nodup (by simpa [hOrderSource] using hNodup)
          have hMiddleNodup : middleCtx.layout.Nodup := by
            rw [hMiddle]
            simpa [Locals.Ctx.withLayout] using
              retain.target_nodup
          have hTailSchedule' :
              StackSchedule.scheduleStmtListFuel scheduleFuel pinned
                  middleCtx.layout rest restFacts =
                some (tailPoints, tailFinal) := by
            simpa [hMiddle, Locals.Ctx.withLayout] using hTailSchedule
          have hTailResult :=
            ih (sourceEnv := sourceEnv) (facts := restFacts)
              (points := tailPoints) (finalLayout := tailFinal)
              (lowered := tailLowered) (targetCtx := middleCtx)
              (finalCtx := finalCtx) (code := tailCode)
              hScoped.2 hSupported.2 hTailSchedule' hTailLower hTailCompile
              hMiddleNodup
          exact
            regularConsResult sourceProgram targetProgram targetCtx middleCtx
              finalCtx (.expr expr) rest point tailPoints order retain
              finalLayout tailFinal headCode tailCode code hPointOrder
              hPointRetain hMiddle hWholeLength hWholeForward hTailResult
              hFinal hCode
  | @let_ rest name value hTailLeaves ih =>
      cases facts with
      | nil =>
          simp [StackSchedule.scheduleStmtListFuel,
            StackSchedule.scheduleStmtListFuelWithTargets] at hSchedule
      | cons fact restFacts =>
          obtain ⟨point, tailPoints, hPoints⟩ :=
            StackSchedule.scheduleStmtListFuel_cons_nonempty hSchedule
          subst points
          obtain
              ⟨order, retain, tailFinal, hOrderBuild, hPointOrder, hFresh,
                hBefore, _hStatement, hPointRetain, _hRegions, _hFalls,
                hBuild, hTailSchedule, hFinal⟩ :=
            StackSchedule.scheduleStmtListFuel_let_components hSchedule
          obtain
              ⟨lowerOrder, lowerRetain, tailLowered, hLowerOrder,
                hPointAccess, hLowerRetain, hTailLower, hLowered⟩ :=
            StackLowering.lowerStmtListFuel_let_components hLower
          have hOrderEq : lowerOrder = order :=
            Option.some.inj (hLowerOrder.symm.trans hPointOrder)
          subst lowerOrder
          have hRetainEq : lowerRetain = retain :=
            Option.some.inj (hLowerRetain.symm.trans hPointRetain)
          subst lowerRetain
          have hOrderSource : targetCtx.layout = order.source :=
            (AllocationLayout.Ordering.build?_source hOrderBuild).symm
          have hAccess :
              StackAccess.Expr.check? order.target 0 value = some () := by
            simpa [StackLowering.pointAccess?, hBefore] using hPointAccess
          have hSource : name :: order.target = retain.source :=
            (AllocationLayout.RegularTransition.build?_sound hBuild).1.symm
          rw [hLowered] at hCompile
          obtain
              ⟨headCode, middleCtx, tailCode,
                hHeadCompile, hTailCompile, hCode⟩ :=
            Locals.Block.compileOpen_append_components hCompile
          have hHeadCompile' :
              Locals.Block.compileOpen targetCtx
                  { stmts :=
                      order.statements ++
                        ([.let_ name value] ++
                          StackLowering.transitionStmts retain) } =
                some (headCode, middleCtx) := by
            simpa [List.append_assoc] using hHeadCompile
          obtain
              ⟨orderCode, orderedCtx, bodyCode, hOrderCompile,
                hBodyCompile, hHeadCode⟩ :=
            Locals.Block.compileOpen_append_components hHeadCompile'
          obtain ⟨orderArtifact⟩ :=
            StackTransitionCompilation.Ordering.compileArtifact order
              hOrderSource
          have hOrderPair :=
            Option.some.inj
              (orderArtifact.compileEq.symm.trans hOrderCompile)
          have hOrderCode :
              orderArtifact.promotionCodes.map Expressions.Stmt.code =
                orderCode :=
            congrArg Prod.fst hOrderPair
          have hOrderedCtx :
              targetCtx.withLayout order.target = orderedCtx :=
            congrArg Prod.snd hOrderPair
          rw [← hOrderCode] at hHeadCode
          rw [← hOrderedCtx] at hBodyCompile
          obtain ⟨hMiddle, hHeadLength, hHeadForward⟩ :=
            compiledLetPointOfEquations sourceProgram targetProgram
              (targetCtx.withLayout order.target) middleCtx name value retain
              ([.let_ name value] ++ StackLowering.transitionStmts retain)
              bodyCode (by simpa [Locals.Ctx.withLayout] using hSource)
              hFresh hScoped.1.2 hSupported.1 hAccess rfl hBodyCompile
          have hOrderLength :
              orderArtifact.promotionCodes.length = order.promotions.length :=
            orderArtifact.codes.code_length
          have hWholeLength :
              headCode.length =
                order.promotions.length +
                  retain.schedule.discards.length + 2 := by
            rw [hHeadCode, List.length_append, List.length_map,
              hHeadLength, hOrderLength]
            omega
          have hWholeForward :
              ∀ (sourceCtx : Functions.Source.Ctx)
                (sourceFuel targetFuel : Nat)
                {suffix : List Word}
                {returns : List Structured.ReturnDest}
                {source : Locals.Source.State}
                {target : Structured.RunState},
                order.promotions.length +
                    retain.schedule.discards.length + 2 < targetFuel →
                CtxCovers sourceCtx targetCtx →
                StateRel targetCtx.layout suffix returns source target →
                Simulation.Interaction.Rel
                  (RegularOutcomeRel middleCtx suffix returns)
                  (Functions.InteractionSemantics.Stmt.openRun sourceProgram
                    sourceCtx sourceFuel (.let_ name value) source)
                  (Expressions.InteractionSemantics.Block.openRun
                    targetProgram targetFuel
                    { stmts := headCode } target) := by
            intro sourceCtx sourceFuel targetFuel suffix returns source target
              hFuel hCtx hInitial
            rw [hHeadCode]
            apply orderArtifact.thenBlock targetProgram targetFuel
                (by rw [hOrderLength]; omega) hInitial
            intro orderedTarget hOrderedRel
            exact
              hHeadForward sourceCtx sourceFuel
                (targetFuel - orderArtifact.promotionCodes.length)
                (by rw [hOrderLength]; omega)
                (hCtx.afterOrdering order hOrderSource) hOrderedRel
          have hRetainSourceNodup : retain.source.Nodup := by
            rw [← hSource]
            exact List.nodup_cons.mpr
              ⟨hFresh,
                order.target_nodup (by simpa [hOrderSource] using hNodup)⟩
          have hMiddleNodup : middleCtx.layout.Nodup := by
            rw [hMiddle]
            simpa [Locals.Ctx.withLayout] using
              retain.target_nodup
          have hTailSchedule' :
              StackSchedule.scheduleStmtListFuel scheduleFuel pinned
                  middleCtx.layout rest restFacts =
                some (tailPoints, tailFinal) := by
            simpa [hMiddle, Locals.Ctx.withLayout] using hTailSchedule
          have hTailResult :=
            ih (sourceEnv := name :: sourceEnv) (facts := restFacts)
              (points := tailPoints) (finalLayout := tailFinal)
              (lowered := tailLowered) (targetCtx := middleCtx)
              (finalCtx := finalCtx) (code := tailCode)
              hScoped.2 hSupported.2 hTailSchedule' hTailLower hTailCompile
              hMiddleNodup
          exact
            regularConsResult sourceProgram targetProgram targetCtx middleCtx
              finalCtx (.let_ name value) rest point tailPoints order retain
              finalLayout tailFinal headCode tailCode code hPointOrder
              hPointRetain hMiddle hWholeLength hWholeForward hTailResult
              hFinal hCode
  | @assign rest name value hTailLeaves ih =>
      cases facts with
      | nil =>
          simp [StackSchedule.scheduleStmtListFuel,
            StackSchedule.scheduleStmtListFuelWithTargets] at hSchedule
      | cons fact restFacts =>
          obtain ⟨point, tailPoints, hPoints⟩ :=
            StackSchedule.scheduleStmtListFuel_cons_nonempty hSchedule
          subst points
          obtain
              ⟨order, retain, tailFinal, hOrderBuild, hPointOrder,
                hBefore, _hStatement, hPointRetain, _hRegions, _hFalls,
                hBuild, hTailSchedule, hFinal⟩ :=
            StackSchedule.scheduleStmtListFuel_assign_components hSchedule
          obtain
              ⟨lowerOrder, lowerRetain, tailLowered, hLowerOrder,
                hPointAccess, hLowerRetain, hTailLower, hLowered⟩ :=
            StackLowering.lowerStmtListFuel_assign_components hLower
          have hOrderEq : lowerOrder = order :=
            Option.some.inj (hLowerOrder.symm.trans hPointOrder)
          subst lowerOrder
          have hRetainEq : lowerRetain = retain :=
            Option.some.inj (hLowerRetain.symm.trans hPointRetain)
          subst lowerRetain
          have hOrderSource : targetCtx.layout = order.source :=
            (AllocationLayout.Ordering.build?_source hOrderBuild).symm
          have hAccess :
              StackAccess.assign? order.target name value = some () := by
            simpa [StackLowering.pointAccess?, hBefore] using hPointAccess
          have hSource : order.target = retain.source :=
            (AllocationLayout.RegularTransition.build?_sound hBuild).1.symm
          rw [hLowered] at hCompile
          obtain
              ⟨headCode, middleCtx, tailCode,
                hHeadCompile, hTailCompile, hCode⟩ :=
            Locals.Block.compileOpen_append_components hCompile
          have hHeadCompile' :
              Locals.Block.compileOpen targetCtx
                  { stmts :=
                      order.statements ++
                        ([.assign name value] ++
                          StackLowering.transitionStmts retain) } =
                some (headCode, middleCtx) := by
            simpa [List.append_assoc] using hHeadCompile
          obtain
              ⟨orderCode, orderedCtx, bodyCode, hOrderCompile,
                hBodyCompile, hHeadCode⟩ :=
            Locals.Block.compileOpen_append_components hHeadCompile'
          obtain ⟨orderArtifact⟩ :=
            StackTransitionCompilation.Ordering.compileArtifact order
              hOrderSource
          have hOrderPair :=
            Option.some.inj
              (orderArtifact.compileEq.symm.trans hOrderCompile)
          have hOrderCode :
              orderArtifact.promotionCodes.map Expressions.Stmt.code =
                orderCode :=
            congrArg Prod.fst hOrderPair
          have hOrderedCtx :
              targetCtx.withLayout order.target = orderedCtx :=
            congrArg Prod.snd hOrderPair
          rw [← hOrderCode] at hHeadCode
          rw [← hOrderedCtx] at hBodyCompile
          obtain ⟨hMiddle, hHeadLength, hHeadForward⟩ :=
            compiledAssignPointOfEquations sourceProgram targetProgram
              (targetCtx.withLayout order.target) middleCtx name value retain
              ([.assign name value] ++ StackLowering.transitionStmts retain)
              bodyCode (by simpa [Locals.Ctx.withLayout] using hSource)
              (order.target_nodup (by simpa [hOrderSource] using hNodup))
              hScoped.1.2 hSupported.1 hAccess rfl hBodyCompile
          have hOrderLength :
              orderArtifact.promotionCodes.length = order.promotions.length :=
            orderArtifact.codes.code_length
          have hWholeLength :
              headCode.length =
                order.promotions.length +
                  retain.schedule.discards.length + 2 := by
            rw [hHeadCode, List.length_append, List.length_map,
              hHeadLength, hOrderLength]
            omega
          have hWholeForward :
              ∀ (sourceCtx : Functions.Source.Ctx)
                (sourceFuel targetFuel : Nat)
                {suffix : List Word}
                {returns : List Structured.ReturnDest}
                {source : Locals.Source.State}
                {target : Structured.RunState},
                order.promotions.length +
                    retain.schedule.discards.length + 2 < targetFuel →
                CtxCovers sourceCtx targetCtx →
                StateRel targetCtx.layout suffix returns source target →
                Simulation.Interaction.Rel
                  (RegularOutcomeRel middleCtx suffix returns)
                  (Functions.InteractionSemantics.Stmt.openRun sourceProgram
                    sourceCtx sourceFuel (.assign name value) source)
                  (Expressions.InteractionSemantics.Block.openRun
                    targetProgram targetFuel
                    { stmts := headCode } target) := by
            intro sourceCtx sourceFuel targetFuel suffix returns source target
              hFuel hCtx hInitial
            rw [hHeadCode]
            apply orderArtifact.thenBlock targetProgram targetFuel
                (by rw [hOrderLength]; omega) hInitial
            intro orderedTarget hOrderedRel
            exact
              hHeadForward sourceCtx sourceFuel
                (targetFuel - orderArtifact.promotionCodes.length)
                (by rw [hOrderLength]; omega)
                (hCtx.afterOrdering order hOrderSource) hOrderedRel
          have hRetainSourceNodup : retain.source.Nodup := by
            rw [← hSource]
            exact order.target_nodup (by simpa [hOrderSource] using hNodup)
          have hMiddleNodup : middleCtx.layout.Nodup := by
            rw [hMiddle]
            simpa [Locals.Ctx.withLayout] using
              retain.target_nodup
          have hTailSchedule' :
              StackSchedule.scheduleStmtListFuel scheduleFuel pinned
                  middleCtx.layout rest restFacts =
                some (tailPoints, tailFinal) := by
            simpa [hMiddle, Locals.Ctx.withLayout] using hTailSchedule
          have hTailResult :=
            ih (sourceEnv := sourceEnv) (facts := restFacts)
              (points := tailPoints) (finalLayout := tailFinal)
              (lowered := tailLowered) (targetCtx := middleCtx)
              (finalCtx := finalCtx) (code := tailCode)
              hScoped.2 hSupported.2 hTailSchedule' hTailLower hTailCompile
              hMiddleNodup
          exact
            regularConsResult sourceProgram targetProgram targetCtx middleCtx
              finalCtx (.assign name value) rest point tailPoints order retain
              finalLayout tailFinal headCode tailCode code hPointOrder
              hPointRetain hMiddle hWholeLength hWholeForward hTailResult
              hFinal hCode

theorem RegularListPreserves.toOpenList
    {sourceProgram : Functions.Program}
    {targetProgram : Expressions.Program}
    {targetCtx finalCtx : Locals.Ctx}
    {stmts : List Functions.Stmt}
    {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout}
    {code : List Expressions.Stmt}
    (hPreserves :
      RegularListPreserves sourceProgram targetProgram targetCtx finalCtx
        stmts points finalLayout code) :
    OpenListPreserves sourceProgram targetProgram targetCtx finalCtx
      stmts finalLayout code := by
  rcases hPreserves with ⟨hFinal, hLength, hForward⟩
  refine ⟨hFinal, ?_⟩
  intro sourceCtx suffix returns source target hCtx hInitial
  have hRun := hForward sourceCtx hCtx hInitial
  rw [hLength]
  apply Simulation.Interaction.Rel.mono hRun
  intro sourceDone targetDone hDone
  cases hDone with
  | error _ => exact Simulation.Interaction.ExceptRel.error trivial
  | ok hResult =>
      exact Simulation.Interaction.ExceptRel.ok hResult.toOpen

theorem OpenListPreserves.toScheduledList
    {sourceProgram : Functions.Program}
    {targetProgram : Expressions.Program}
    {targets : StackSchedule.ControlTargets}
    {targetCtx finalCtx : Locals.Ctx}
    {stmts : List Functions.Stmt}
    {finalLayout : Locals.Layout}
    {code : List Expressions.Stmt}
    (hPreserves :
      OpenListPreserves sourceProgram targetProgram targetCtx finalCtx
        stmts finalLayout code) :
    ScheduledListPreserves sourceProgram targetProgram targets targetCtx
      finalCtx stmts finalLayout code := by
  rcases hPreserves with ⟨hFinal, hForward⟩
  refine ⟨hFinal, ?_⟩
  intro sourceCtx suffix returns source target hCtx hInitial
  exact hForward sourceCtx hCtx.context hInitial

theorem BreakListPreserves.toScheduledList
    {sourceProgram : Functions.Program}
    {targetProgram : Expressions.Program}
    {targets : StackSchedule.ControlTargets}
    {targetCtx finalCtx : Locals.Ctx}
    {stmts : List Functions.Stmt}
    {targetLayout : Locals.Layout}
    {code : List Expressions.Stmt}
    (hTarget : targets.brk? = some targetLayout)
    (hPreserves :
      BreakListPreserves sourceProgram targetProgram targetCtx finalCtx
        stmts targetLayout code) :
    ScheduledListPreserves sourceProgram targetProgram targets targetCtx
      finalCtx stmts targetLayout code := by
  rcases hPreserves with ⟨hFinal, hForward⟩
  refine ⟨hFinal, ?_⟩
  intro sourceCtx suffix returns source target hCtx hInitial
  exact hForward sourceCtx (hCtx.breakTarget hTarget) hInitial

theorem ContinueListPreserves.toScheduledList
    {sourceProgram : Functions.Program}
    {targetProgram : Expressions.Program}
    {targets : StackSchedule.ControlTargets}
    {targetCtx finalCtx : Locals.Ctx}
    {stmts : List Functions.Stmt}
    {targetLayout : Locals.Layout}
    {code : List Expressions.Stmt}
    (hTarget : targets.cont? = some targetLayout)
    (hPreserves :
      ContinueListPreserves sourceProgram targetProgram targetCtx finalCtx
        stmts targetLayout code) :
    ScheduledListPreserves sourceProgram targetProgram targets targetCtx
      finalCtx stmts targetLayout code := by
  rcases hPreserves with ⟨hFinal, hForward⟩
  refine ⟨hFinal, ?_⟩
  intro sourceCtx suffix returns source target hCtx hInitial
  exact hForward sourceCtx (hCtx.continueTarget hTarget) hInitial

theorem brkList_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel : Nat)
    (rest : List Functions.Stmt)
    (fact : AllocationLivenessFacts.Point)
    (restFacts : List AllocationLivenessFacts.Point)
    {targetLayout : Locals.Layout}
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    (hTarget : targets.brk? = some targetLayout)
    (hTargetDepth :
      targetCtx.breakDepth? = some targetLayout.length)
    (hSchedule :
      StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout (.brk :: rest) (fact :: restFacts) =
        some (point :: points, finalLayout))
    (hLower :
      StackLowering.lowerStmtListFuel lowerFuel lowerCtx
          (.brk :: rest) (point :: points) = some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx)) :
    BreakListPreserves sourceProgram targetProgram targetCtx finalCtx
      (.brk :: rest) targetLayout code := by
  obtain
      ⟨order, exit, hOrderBuild, hExitBuild, hPointOrder, _hBefore,
        _hStatement, hPointExit, _hRetain, _hRegions, _hFalls,
        hPoints, hFinalLayout⟩ :=
    StackSchedule.scheduleStmtListFuelWithTargets_brk_components
      hTarget hSchedule
  subst points
  obtain
      ⟨lowerOrder, hLowerOrder, _hAccess, _hLowerFalls, _hLowerRegions,
        _hLowerRetain, hLowered⟩ :=
    StackLowering.lowerStmtListFuel_brk_components hLower
  have hOrderEq : lowerOrder = order :=
    Option.some.inj (hLowerOrder.symm.trans hPointOrder)
  subst lowerOrder
  have hExitEq : point.exit? = some exit := hPointExit
  have hLowered' :
      lowered = order.statements ++ (exit.statements ++ [.brk]) := by
    simpa [StackLowering.exitStmts, hExitEq, List.append_assoc] using hLowered
  have hOrderSource : targetCtx.layout = order.source :=
    (AllocationLayout.Ordering.build?_source hOrderBuild).symm
  have hExitSource : order.target = exit.source :=
    (AllocationLayout.Join.build?_endpoints hExitBuild).1.symm
  rw [hLowered'] at hCompile
  obtain
      ⟨orderCode, orderedCtx, bodyCode, hOrderCompile, hBodyCompile,
        hWholeCode⟩ :=
    Locals.Block.compileOpen_append_components hCompile
  obtain ⟨orderArtifact⟩ :=
    StackTransitionCompilation.Ordering.compileArtifact order hOrderSource
  have hOrderPair :=
    Option.some.inj (orderArtifact.compileEq.symm.trans hOrderCompile)
  have hOrderCode :
      orderArtifact.promotionCodes.map Expressions.Stmt.code = orderCode :=
    congrArg Prod.fst hOrderPair
  have hOrderedCtx : targetCtx.withLayout order.target = orderedCtx :=
    congrArg Prod.snd hOrderPair
  rw [← hOrderCode] at hWholeCode
  rw [← hOrderedCtx] at hBodyCompile
  have hBodySource :
      (targetCtx.withLayout order.target).layout = exit.source := by
    simpa [Locals.Ctx.withLayout] using hExitSource
  obtain ⟨exitArtifact, hBodyFinal, hBodyCode, hBodyForward⟩ :=
    compiledBrkJoinPointOfEquations sourceProgram targetProgram
      (targetCtx.withLayout order.target) finalCtx exit
      (exit.statements ++ [.brk]) bodyCode hBodySource
      (by
        rw [(AllocationLayout.Join.build?_endpoints hExitBuild).2]
        simpa [Locals.Ctx.withLayout] using hTargetDepth)
      rfl hBodyCompile
  refine ⟨?_, ?_⟩
  · rw [hBodyFinal]
    simp [Locals.Ctx.withLayout,
      (AllocationLayout.Join.build?_endpoints hExitBuild).2]
  · intro sourceCtx suffix returns source target hCtx hInitial
    obtain ⟨scope, hSourceScope, hScopeCovers⟩ := hCtx.sourceCovers
    have hWholeFuel :
        orderArtifact.promotionCodes.length < code.length + 1 := by
      rw [hWholeCode, List.length_append, List.length_map]
      omega
    have hPrefixed :
        Simulation.Interaction.Rel
          (OpenOutcomeRel finalCtx suffix returns)
          (Functions.InteractionSemantics.Stmt.openRun sourceProgram
            sourceCtx (rest.length + 1) .brk source)
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            (code.length + 1)
            { stmts :=
                orderArtifact.promotionCodes.map Expressions.Stmt.code ++
                  bodyCode }
            target) := by
      apply orderArtifact.thenBlock targetProgram (code.length + 1)
          hWholeFuel hInitial
      intro orderedTarget hOrderedRel
      have hBody :=
        hBodyForward sourceCtx (rest.length + 1) (bodyCode.length + 1)
          (by omega) hSourceScope
          (by
            rw [(AllocationLayout.Join.build?_endpoints hExitBuild).2]
            exact hScopeCovers)
          hOrderedRel
      have hTailFuel :
          code.length + 1 - orderArtifact.promotionCodes.length =
            bodyCode.length + 1 := by
        rw [hWholeCode, List.length_append, List.length_map]
        omega
      rw [hTailFuel]
      exact hBody
    have hHead :
        Simulation.Interaction.Rel
          (OpenOutcomeRel finalCtx suffix returns)
          (Functions.InteractionSemantics.Stmt.openRun sourceProgram
            sourceCtx (rest.length + 1) .brk source)
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            (code.length + 1) { stmts := code } target) := by
      simpa [hWholeCode] using hPrefixed
    rw [Functions.InteractionSemantics.Block.openRun_cons]
    simpa [Functions.InteractionSemantics.Stmt.openRun,
      Functions.Source.Canonical.Stmt.run,
      Functions.Source.Effectful.Control.Stmt.run, hSourceScope] using hHead

theorem contList_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel : Nat)
    (rest : List Functions.Stmt)
    (fact : AllocationLivenessFacts.Point)
    (restFacts : List AllocationLivenessFacts.Point)
    {targetLayout : Locals.Layout}
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    (hTarget : targets.cont? = some targetLayout)
    (hTargetDepth :
      targetCtx.continueDepth? = some targetLayout.length)
    (hSchedule :
      StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout (.cont :: rest) (fact :: restFacts) =
        some (point :: points, finalLayout))
    (hLower :
      StackLowering.lowerStmtListFuel lowerFuel lowerCtx
          (.cont :: rest) (point :: points) = some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx)) :
    ContinueListPreserves sourceProgram targetProgram targetCtx finalCtx
      (.cont :: rest) targetLayout code := by
  obtain
      ⟨order, exit, hOrderBuild, hExitBuild, hPointOrder, _hBefore,
        _hStatement, hPointExit, _hRetain, _hRegions, _hFalls,
        hPoints, _hFinalLayout⟩ :=
    StackSchedule.scheduleStmtListFuelWithTargets_cont_components
      hTarget hSchedule
  subst points
  obtain
      ⟨lowerOrder, hLowerOrder, _hAccess, _hLowerFalls, _hLowerRegions,
        _hLowerRetain, hLowered⟩ :=
    StackLowering.lowerStmtListFuel_cont_components hLower
  have hOrderEq : lowerOrder = order :=
    Option.some.inj (hLowerOrder.symm.trans hPointOrder)
  subst lowerOrder
  have hExitEq : point.exit? = some exit := hPointExit
  have hLowered' :
      lowered = order.statements ++ (exit.statements ++ [.cont]) := by
    simpa [StackLowering.exitStmts, hExitEq, List.append_assoc] using hLowered
  have hOrderSource : targetCtx.layout = order.source :=
    (AllocationLayout.Ordering.build?_source hOrderBuild).symm
  have hExitSource : order.target = exit.source :=
    (AllocationLayout.Join.build?_endpoints hExitBuild).1.symm
  rw [hLowered'] at hCompile
  obtain
      ⟨orderCode, orderedCtx, bodyCode, hOrderCompile, hBodyCompile,
        hWholeCode⟩ :=
    Locals.Block.compileOpen_append_components hCompile
  obtain ⟨orderArtifact⟩ :=
    StackTransitionCompilation.Ordering.compileArtifact order hOrderSource
  have hOrderPair :=
    Option.some.inj (orderArtifact.compileEq.symm.trans hOrderCompile)
  have hOrderCode :
      orderArtifact.promotionCodes.map Expressions.Stmt.code = orderCode :=
    congrArg Prod.fst hOrderPair
  have hOrderedCtx : targetCtx.withLayout order.target = orderedCtx :=
    congrArg Prod.snd hOrderPair
  rw [← hOrderCode] at hWholeCode
  rw [← hOrderedCtx] at hBodyCompile
  have hBodySource :
      (targetCtx.withLayout order.target).layout = exit.source := by
    simpa [Locals.Ctx.withLayout] using hExitSource
  obtain ⟨exitArtifact, hBodyFinal, hBodyCode, hBodyForward⟩ :=
    compiledContJoinPointOfEquations sourceProgram targetProgram
      (targetCtx.withLayout order.target) finalCtx exit
      (exit.statements ++ [.cont]) bodyCode hBodySource
      (by
        rw [(AllocationLayout.Join.build?_endpoints hExitBuild).2]
        simpa [Locals.Ctx.withLayout] using hTargetDepth)
      rfl hBodyCompile
  refine ⟨?_, ?_⟩
  · rw [hBodyFinal]
    simp [Locals.Ctx.withLayout,
      (AllocationLayout.Join.build?_endpoints hExitBuild).2]
  · intro sourceCtx suffix returns source target hCtx hInitial
    obtain ⟨scope, hSourceScope, hScopeCovers⟩ := hCtx.sourceCovers
    have hWholeFuel :
        orderArtifact.promotionCodes.length < code.length + 1 := by
      rw [hWholeCode, List.length_append, List.length_map]
      omega
    have hPrefixed :
        Simulation.Interaction.Rel
          (OpenOutcomeRel finalCtx suffix returns)
          (Functions.InteractionSemantics.Stmt.openRun sourceProgram
            sourceCtx (rest.length + 1) .cont source)
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            (code.length + 1)
            { stmts :=
                orderArtifact.promotionCodes.map Expressions.Stmt.code ++
                  bodyCode }
            target) := by
      apply orderArtifact.thenBlock targetProgram (code.length + 1)
          hWholeFuel hInitial
      intro orderedTarget hOrderedRel
      have hBody :=
        hBodyForward sourceCtx (rest.length + 1) (bodyCode.length + 1)
          (by omega) hSourceScope
          (by
            rw [(AllocationLayout.Join.build?_endpoints hExitBuild).2]
            exact hScopeCovers)
          hOrderedRel
      have hTailFuel :
          code.length + 1 - orderArtifact.promotionCodes.length =
            bodyCode.length + 1 := by
        rw [hWholeCode, List.length_append, List.length_map]
        omega
      rw [hTailFuel]
      exact hBody
    have hHead :
        Simulation.Interaction.Rel
          (OpenOutcomeRel finalCtx suffix returns)
          (Functions.InteractionSemantics.Stmt.openRun sourceProgram
            sourceCtx (rest.length + 1) .cont source)
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            (code.length + 1) { stmts := code } target) := by
      simpa [hWholeCode] using hPrefixed
    rw [Functions.InteractionSemantics.Block.openRun_cons]
    simpa [Functions.InteractionSemantics.Stmt.openRun,
      Functions.Source.Canonical.Stmt.run,
      Functions.Source.Effectful.Control.Stmt.run, hSourceScope] using hHead

theorem terminalList_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel : Nat)
    (kind : Assembly.HaltKind) (rest : List Functions.Stmt)
    (fact : AllocationLivenessFacts.Point)
    (restFacts : List AllocationLivenessFacts.Point)
    {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    (hArgCount : kind.argCount = 0)
    (hSchedule :
      StackSchedule.scheduleStmtListFuel scheduleFuel pinned targetCtx.layout
          (.terminal kind :: rest) (fact :: restFacts) =
        some (points, finalLayout))
    (hLower :
      StackLowering.lowerStmtListFuel lowerFuel lowerCtx
          (.terminal kind :: rest) points = some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx)) :
    OpenListPreserves sourceProgram targetProgram targetCtx finalCtx
      (.terminal kind :: rest) finalLayout code := by
  obtain
      ⟨order, point, hOrderBuild, hPoints, hPointOrder, _hBefore,
        _hStatement, _hRetain, _hRegions, _hFalls, hFinalLayout⟩ :=
    StackSchedule.scheduleStmtListFuel_terminal_components hSchedule
  subst points
  obtain
      ⟨lowerOrder, hLowerOrder, _pointAccess, _hPointRetain, hLowered⟩ :=
    StackLowering.lowerStmtListFuel_terminal_components hLower
  have hOrderEq : lowerOrder = order :=
    Option.some.inj (hLowerOrder.symm.trans hPointOrder)
  subst lowerOrder
  have hOrderSource : targetCtx.layout = order.source :=
    (AllocationLayout.Ordering.build?_source hOrderBuild).symm
  rw [hLowered] at hCompile
  obtain
      ⟨orderCode, orderedCtx, bodyCode, hOrderCompile, hBodyCompile,
        hWholeCode⟩ :=
    Locals.Block.compileOpen_append_components hCompile
  obtain ⟨orderArtifact⟩ :=
    StackTransitionCompilation.Ordering.compileArtifact order hOrderSource
  have hOrderPair :=
    Option.some.inj (orderArtifact.compileEq.symm.trans hOrderCompile)
  have hOrderCode :
      orderArtifact.promotionCodes.map Expressions.Stmt.code = orderCode :=
    congrArg Prod.fst hOrderPair
  have hOrderedCtx :
      targetCtx.withLayout order.target = orderedCtx :=
    congrArg Prod.snd hOrderPair
  rw [← hOrderCode] at hWholeCode
  rw [← hOrderedCtx] at hBodyCompile
  obtain ⟨hFinalCtx, hBodyCode, hForward⟩ :=
    compiledTerminalPointOfEquations sourceProgram targetProgram
      (targetCtx.withLayout order.target) finalCtx kind [.terminal kind]
      bodyCode hArgCount rfl hBodyCompile
  refine ⟨?_, ?_⟩
  · rw [hFinalCtx, hFinalLayout]
    simp [Locals.Ctx.withLayout]
  · intro sourceCtx suffix returns source target _hCtx hInitial
    have hWholeFuel :
        orderArtifact.promotionCodes.length < code.length + 1 := by
      rw [hWholeCode, List.length_append, List.length_map]
      omega
    have hPrefixed :
        Simulation.Interaction.Rel
          (OpenOutcomeRel finalCtx suffix returns)
          (Functions.InteractionSemantics.Stmt.openRun sourceProgram
            sourceCtx (rest.length + 1) (.terminal kind) source)
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            (code.length + 1)
            { stmts :=
                orderArtifact.promotionCodes.map Expressions.Stmt.code ++
                  bodyCode }
            target) := by
      apply orderArtifact.thenBlock targetProgram (code.length + 1)
          hWholeFuel hInitial
      intro orderedTarget hOrderedRel
      have hBody :=
        hForward sourceCtx (rest.length + 1) (bodyCode.length + 1)
          (by omega) hOrderedRel
      have hTailFuel :
          code.length + 1 - orderArtifact.promotionCodes.length =
            bodyCode.length + 1 := by
        rw [hWholeCode, List.length_append, List.length_map]
        omega
      rw [hTailFuel]
      exact hBody
    have hHead :
        Simulation.Interaction.Rel
          (OpenOutcomeRel finalCtx suffix returns)
          (Functions.InteractionSemantics.Stmt.openRun sourceProgram
            sourceCtx (rest.length + 1) (.terminal kind) source)
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            (code.length + 1) { stmts := code } target) := by
      simpa [hWholeCode] using hPrefixed
    rw [Functions.InteractionSemantics.Block.openRun_terminal_cons]
    simpa [Functions.InteractionSemantics.Stmt.openRun] using hHead

theorem terminalArgsList_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel : Nat)
    (kind : Assembly.HaltKind) (args : Locals.ExprSeq kind.argCount)
    (rest : List Functions.Stmt)
    (fact : AllocationLivenessFacts.Point)
    (restFacts : List AllocationLivenessFacts.Point)
    {sourceEnv : List Name} {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    (hScoped : Functions.Scope.ExprSeqScoped sourceEnv args)
    (hSupported : Locals.InteractionSemantics.ExprSeq.OpenSupported args)
    (hSchedule :
      StackSchedule.scheduleStmtListFuel scheduleFuel pinned targetCtx.layout
          (.terminalArgs kind args :: rest) (fact :: restFacts) =
        some (points, finalLayout))
    (hLower :
      StackLowering.lowerStmtListFuel lowerFuel lowerCtx
          (.terminalArgs kind args :: rest) points = some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx)) :
    OpenListPreserves sourceProgram targetProgram targetCtx finalCtx
      (.terminalArgs kind args :: rest) finalLayout code := by
  obtain
      ⟨order, point, hOrderBuild, hPoints, hPointOrder, hBefore,
        _hStatement, _hRetain, _hRegions, _hFalls, hFinalLayout⟩ :=
    StackSchedule.scheduleStmtListFuel_terminalArgs_components hSchedule
  subst points
  obtain
      ⟨lowerOrder, hLowerOrder, hPointAccess, _hPointRetain, hLowered⟩ :=
    StackLowering.lowerStmtListFuel_terminalArgs_components hLower
  have hOrderEq : lowerOrder = order :=
    Option.some.inj (hLowerOrder.symm.trans hPointOrder)
  subst lowerOrder
  have hOrderSource : targetCtx.layout = order.source :=
    (AllocationLayout.Ordering.build?_source hOrderBuild).symm
  have hAccess :
      StackAccess.ExprSeq.check? order.target 0 args = some () := by
    simpa [StackLowering.pointAccess?, hBefore] using hPointAccess
  rw [hLowered] at hCompile
  obtain
      ⟨orderCode, orderedCtx, bodyCode, hOrderCompile, hBodyCompile,
        hWholeCode⟩ :=
    Locals.Block.compileOpen_append_components hCompile
  obtain ⟨orderArtifact⟩ :=
    StackTransitionCompilation.Ordering.compileArtifact order hOrderSource
  have hOrderPair :=
    Option.some.inj (orderArtifact.compileEq.symm.trans hOrderCompile)
  have hOrderCode :
      orderArtifact.promotionCodes.map Expressions.Stmt.code = orderCode :=
    congrArg Prod.fst hOrderPair
  have hOrderedCtx :
      targetCtx.withLayout order.target = orderedCtx :=
    congrArg Prod.snd hOrderPair
  rw [← hOrderCode] at hWholeCode
  rw [← hOrderedCtx] at hBodyCompile
  obtain ⟨hFinalCtx, argsCode, hArgsCompile, hCode, hForward⟩ :=
    compiledTerminalArgsPointOfEquations sourceProgram targetProgram
      (targetCtx.withLayout order.target) finalCtx kind args
      [.terminalArgs kind args] bodyCode hScoped hSupported hAccess rfl
      hBodyCompile
  refine ⟨?_, ?_⟩
  · rw [hFinalCtx, hFinalLayout]
    simp [Locals.Ctx.withLayout]
  · intro sourceCtx suffix returns source target _hCtx hInitial
    have hWholeFuel :
        orderArtifact.promotionCodes.length < code.length + 1 := by
      rw [hWholeCode, List.length_append, List.length_map]
      omega
    have hPrefixed :
        Simulation.Interaction.Rel
          (OpenOutcomeRel finalCtx suffix returns)
          (Functions.InteractionSemantics.Stmt.openRun sourceProgram
            sourceCtx (rest.length + 1) (.terminalArgs kind args) source)
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            (code.length + 1)
            { stmts :=
                orderArtifact.promotionCodes.map Expressions.Stmt.code ++
                  bodyCode }
            target) := by
      apply orderArtifact.thenBlock targetProgram (code.length + 1)
          hWholeFuel hInitial
      intro orderedTarget hOrderedRel
      have hBody :=
        hForward sourceCtx (rest.length + 1) (bodyCode.length + 1)
          (by omega) hOrderedRel
      have hTailFuel :
          code.length + 1 - orderArtifact.promotionCodes.length =
            bodyCode.length + 1 := by
        rw [hWholeCode, List.length_append, List.length_map]
        omega
      rw [hTailFuel]
      exact hBody
    have hHead :
        Simulation.Interaction.Rel
          (OpenOutcomeRel finalCtx suffix returns)
          (Functions.InteractionSemantics.Stmt.openRun sourceProgram
            sourceCtx (rest.length + 1) (.terminalArgs kind args) source)
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            (code.length + 1) { stmts := code } target) := by
      simpa [hWholeCode] using hPrefixed
    rw [Functions.InteractionSemantics.Block.openRun_terminalArgs_cons]
    simpa [Functions.InteractionSemantics.Stmt.openRun] using hHead

end StackBlockPreservation
end Functions
end EvmCompiler
