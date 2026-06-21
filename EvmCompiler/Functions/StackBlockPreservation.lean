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
      (match point.order? with
       | some order => order.promotions.length
       | none => 0) +
      (match point.retain? with
       | some transition => transition.schedule.promotions.length + 2
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
    (targetCtx finalCtx : Locals.Ctx)
    (stmts : List Functions.Stmt)
    (finalLayout : Locals.Layout)
    (code : List Expressions.Stmt) : Prop :=
  finalCtx.layout = finalLayout ∧
    ∀ (sourceCtx : Functions.Source.Ctx) (sourceFuel targetFuel : Nat)
      {suffix : List Word} {returns : List Structured.ReturnDest}
      {source : Locals.Source.State} {target : Structured.RunState},
      Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel code →
      ControlCtxCovers sourceCtx targetCtx targets →
      StateRel targetCtx.layout suffix returns source target →
      Simulation.Interaction.ForwardRel FuelTruncated
        (ControlOpenOutcomeRel targets finalCtx suffix returns)
        (Functions.InteractionSemantics.Block.openRun
          sourceProgram sourceCtx sourceFuel { stmts } source)
        (Expressions.InteractionSemantics.Block.openRun targetProgram
          targetFuel { stmts := code } target)

theorem controlCons
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (targetCtx middleCtx finalCtx : Locals.Ctx)
    (stmt : Functions.Stmt) (rest : List Functions.Stmt)
    (headCode tailCode code : List Expressions.Stmt)
    (finalLayout : Locals.Layout)
    (hHead :
      ControlPointPreserves sourceProgram targetProgram targets targetCtx
        middleCtx stmt headCode)
    (hTail :
      ControlScheduledListPreserves sourceProgram targetProgram targets
        middleCtx finalCtx rest finalLayout tailCode)
    (hCode : code = headCode ++ tailCode) :
    ControlScheduledListPreserves sourceProgram targetProgram targets
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
      | brk hState =>
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact .brk hState
      | cont hState =>
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact .cont hState
      | leave hState =>
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact .leave hState
      | halt hShared hReturns =>
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact .halt hShared hReturns

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
      ControlScheduledListPreserves sourceProgram targetProgram targets
        bodyCtx bodyFinalCtx source.stmts bodyFinalCtx.layout bodyCode)
    (hBodyCtx : ControlCtxCovers sourceCtx bodyCtx targets)
    (hFinalCtx :
      ControlCtxCovers sourceCtx
        (bodyFinalCtx.withLayout exit.target) targets)
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
      (ControlOpenOutcomeRel targets
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
    hBodyForward sourceCtx sourceFuel targetFuel hBodyFuel hBodyCtx hInitial
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
  | brk hState =>
      simp only [Locals.Source.Effectful.Outcome.brk,
        Structured.Outcome.brk, Structured.OutcomeT.brk]
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact .brk hState
  | cont hState =>
      simp only [Locals.Source.Effectful.Outcome.cont,
        Structured.Outcome.cont, Structured.OutcomeT.cont]
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact .cont hState
  | leave hState =>
      simp only [Locals.Source.Effectful.Outcome.leave,
        Structured.Outcome.leave, Structured.OutcomeT.leave]
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact .leave hState
  | halt hShared hReturns =>
      simp only [Locals.Source.Effectful.Outcome.halt,
        Structured.Outcome.halt, Structured.OutcomeT.halt]
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact .halt hShared hReturns

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
      ControlScheduledListPreserves sourceProgram targetProgram targets
        (targetCtx.withLayout entry.target) bodyFinalCtx source.stmts
        bodyFinalCtx.layout bodyCode)
    (hCtx : ControlCtxCovers sourceCtx targetCtx targets)
    (hEntrySource : targetCtx.layout = entry.source)
    (hFinalCtx :
      ControlCtxCovers sourceCtx
        (bodyFinalCtx.withLayout exit.target) targets)
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
      (ControlOpenOutcomeRel targets
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
    controlScopedBodyThenJoin sourceProgram targetProgram targets sourceCtx
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
      ControlScheduledListPreserves sourceProgram targetProgram targets
        (targetCtx.withLayout entry.target) bodyFinalCtx source.stmts
        bodyFinalCtx.layout bodyCode)
    (hCtx : ControlCtxCovers sourceCtx targetCtx targets)
    (hEntrySource : targetCtx.layout = entry.source)
    (hFinalCtx :
      ControlCtxCovers sourceCtx
        (bodyFinalCtx.withLayout exit.target) targets)
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
      (ControlOpenOutcomeRel targets
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
    controlScheduledRegion sourceProgram targetProgram targets sourceCtx
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
    controlAppendEmptyCodeForward targetProgram targets
      (bodyFinalCtx.withLayout exit.target) targetFuel hEmptyFuel
      (by simpa [List.append_assoc] using hRegionRun)
  rw [Functions.InteractionSemantics.Stmt.openRun_block]
  simpa [List.append_assoc] using hWithEmpty

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
        ControlScheduledListPreserves sourceProgram targetProgram targets
          (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx body.stmts
          rawRegion.finalLayout bodyCode) :
    ∃ bodyCode bodyFinalCtx,
      ∃ entryArtifact :
          StackTransitionCompilation.Artifact targetCtx rawRegion.entry,
      ∃ exitArtifact :
          StackTransitionCompilation.JoinArtifact bodyFinalCtx exit,
        ControlScheduledListPreserves sourceProgram targetProgram targets
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
        StackLowering.transitionStmts rawRegion.entry ++
          (bodyLowered ++ exit.statements) := by
    simpa [StackLowering.exitStmts] using hLoweredBody
  have hLoweredBodyStruct :
      loweredBody =
        { stmts :=
            StackLowering.transitionStmts rawRegion.entry ++
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
    (retain : AllocationLayout.Transition)
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
        ControlScheduledListPreserves sourceProgram targetProgram targets
          (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx body.stmts
          rawRegion.finalLayout bodyCode) :
    ControlPointPreserves sourceProgram targetProgram targets targetCtx finalCtx
      (.block body) code := by
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
        StackLowering.transitionStmts rawRegion.entry ++
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
            StackLowering.transitionStmts rawRegion.entry ++
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
      ControlScheduledListPreserves sourceProgram targetProgram targets
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
  unfold ControlPointPreserves
  intro sourceCtx sourceFuel targetFuel suffix returns source target hFuel
    hCtx hInitial
  have hCodeLength := Expressions.TargetFuel.Covers.length_lt hFuel
  have hFinalControl :
      ControlCtxCovers sourceCtx
        (bodyFinalCtx.withLayout exit.target) targets :=
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
    controlScheduledRegion sourceProgram targetProgram targets sourceCtx
      targetCtx bodyFinalCtx body bodyCode rawRegion.entry entryArtifact exit
      exitArtifact sourceFuel targetFuel hBodyPreservesSelf hCtx hEntrySource
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
    controlAppendEmptyCodeForward targetProgram targets
      (bodyFinalCtx.withLayout exit.target) targetFuel hRegionEmptyFuel hRegionRun
  rw [hRestoredCtx] at hWithEmpty
  obtain ⟨compiledRetainArtifact⟩ :=
    StackTransitionCompilation.Transition.compileArtifact retain hRetainSource
  have hCompiledRetainPair :=
    Option.some.inj
      (compiledRetainArtifact.compileEq.symm.trans hRetainCompile)
  have hCompiledRetainCode :
      compiledRetainArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code compiledRetainArtifact.cleanup] = retainCode :=
    congrArg Prod.fst hCompiledRetainPair
  have hWholeFuel :
      targetBlock.stmts.length + retain.schedule.promotions.length + 1 <
        targetFuel := by
    rw [hCode, hBlockCode, ← hCompiledRetainCode] at hCodeLength
    simp only [List.length_append, List.length_map, List.length_cons,
      List.length_nil] at hCodeLength
    rw [compiledRetainArtifact.codes.code_length] at hCodeLength
    omega
  obtain ⟨retainArtifact, hWholeRun⟩ :=
    controlThenTransitionForward targetProgram targets
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
    (retain : AllocationLayout.Transition)
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
        ControlScheduledListPreserves sourceProgram targetProgram targets
          (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx body.stmts
          rawRegion.finalLayout bodyCode) :
    ControlPointPreserves sourceProgram targetProgram targets targetCtx finalCtx
      (.if_ cond body) code := by
  obtain ⟨bodyFacts, rawRegion, exit, _hFacts, hChildSchedule, hExitBuild,
      _hBefore, _hStatement, _hRawExit, _hRawRetain, hRawRegions,
      _hFalls⟩ :=
    StackSchedule.scheduleStmtFuelWithTargets_if_components hSchedule
  obtain ⟨region, loweredBody, lowerRetain, hAccess, _hLowerFalls,
      hLowerRegions, hLowerBody, hLowerRetain, hLowered⟩ :=
    StackLowering.lowerPointFuel_if_components hLower
  have hRegionList :
      [region] =
        [{ rawRegion with exit? := some exit, finalLayout := targetCtx.layout }] :=
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
  obtain ⟨bodyCode, bodyFinalCtx, entryArtifact, exitArtifact,
      hBodyPreserves, hRegionCode, hRegionFinal, hRestoredCtx,
      hEntrySource⟩ :=
    compiledScheduledRegion_of_compilers sourceProgram targetProgram lowerCtx
      targets scheduleFuel lowerFuel body bodyFacts rawRegion exit targetCtx
      regionFinalCtx loweredBody regionCode hChildSchedule hExitBuild
      hLowerBody hRegionCompile
      (fun hBodyLower hBodyCompile =>
        hBody hChildSchedule hBodyLower hBodyCompile)
  obtain ⟨cleanup, hCleanup, hTargetBody⟩ :=
    Locals.finishScoped_components hFinish
  have hBodyPreservesSelf :
      ControlScheduledListPreserves sourceProgram targetProgram targets
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
  have hExitTarget : exit.target = targetCtx.layout := by
    have h := congrArg Locals.Ctx.layout hRestoredCtx
    simpa [Locals.Ctx.withLayout] using h
  obtain ⟨compiledRetainArtifact⟩ :=
    StackTransitionCompilation.Transition.compileArtifact retain hRetainSource
  have hCompiledRetainPair :=
    Option.some.inj
      (compiledRetainArtifact.compileEq.symm.trans hRetainCompile)
  have hCompiledRetainCode :
      compiledRetainArtifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code compiledRetainArtifact.cleanup] = retainCode :=
    congrArg Prod.fst hCompiledRetainPair
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
      have hFinalControl :
          ControlCtxCovers sourceCtx
            (bodyFinalCtx.withLayout exit.target) targets := by
        rw [hRestoredCtx]
        exact hCtx
      have hScopeCovers :
          ∀ {name : Name}, name ∈ exit.target → name ∈ sourceCtx.scope := by
        intro name hName
        apply hCtx.context.scope
        rwa [hExitTarget] at hName
      have hIfRun :=
        controlIf sourceProgram targetProgram targets sourceCtx targetCtx
          sourceFuel targetFuel cond body condCode targetBody hTargetFuel hCtx
          hCondScoped hSupported hCondCompile hInitial (by
            intro sourceAfter targetAfter hAfter
            have hBlockRun :=
              controlScheduledRegionAsBlock sourceProgram targetProgram targets
                sourceCtx targetCtx bodyFinalCtx body bodyCode rawRegion.entry
                entryArtifact exit exitArtifact targetBody sourceFuel
                (targetFuel - 2) hBodyPreservesSelf hCtx hEntrySource
                hFinalControl hScopeCovers hTargetBodyCode hTargetBodyFuel hAfter
            rw [hRestoredCtx] at hBlockRun
            exact hBlockRun)
      have hCodeLength := Expressions.TargetFuel.Covers.length_lt hFuel'
      have hWholeFuel :
          [Expressions.Stmt.if_ (.code condCode) targetBody].length +
              retain.schedule.promotions.length + 1 < targetFuel := by
        rw [← hCompiledRetainCode] at hCodeLength
        simp only [List.length_cons, List.length_append, List.length_map,
          List.length_nil] at hCodeLength ⊢
        rw [compiledRetainArtifact.codes.code_length] at hCodeLength
        omega
      obtain ⟨retainArtifact, hWholeRun⟩ :=
        controlThenTransitionForward targetProgram targets targetCtx retain
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

theorem regularConsResult
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targetCtx middleCtx finalCtx : Locals.Ctx)
    (stmt : Functions.Stmt) (rest : List Functions.Stmt)
    (point : StackSchedule.Point) (points : List StackSchedule.Point)
    (order : AllocationLayout.Ordering)
    (transition : AllocationLayout.Transition)
    (finalLayout tailFinal : Locals.Layout)
    (headCode tailCode code : List Expressions.Stmt)
    (hOrder : point.order? = some order)
    (hRetain : point.retain? = some transition)
    (hMiddle :
      middleCtx = targetCtx.withLayout transition.schedule.target)
    (hHeadLength :
      headCode.length =
        order.promotions.length + transition.schedule.promotions.length + 2)
    (hHead :
      ∀ (sourceCtx : Functions.Source.Ctx)
        (sourceFuel targetFuel : Nat)
        {suffix : List Word} {returns : List Structured.ReturnDest}
        {source : Locals.Source.State} {target : Structured.RunState},
        order.promotions.length +
            transition.schedule.promotions.length + 2 < targetFuel →
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
        order.promotions.length + transition.schedule.promotions.length + 2 <
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
            (AllocationLayout.Transition.build?_sound hBuild).1.symm
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
                  retain.schedule.promotions.length + 2 := by
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
                    retain.schedule.promotions.length + 2 < targetFuel →
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
              AllocationLayout.Transition.target_nodup retain
                hRetainSourceNodup
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
            (AllocationLayout.Transition.build?_sound hBuild).1.symm
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
                  retain.schedule.promotions.length + 2 := by
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
                    retain.schedule.promotions.length + 2 < targetFuel →
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
              AllocationLayout.Transition.target_nodup retain
                hRetainSourceNodup
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
            (AllocationLayout.Transition.build?_sound hBuild).1.symm
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
                  retain.schedule.promotions.length + 2 := by
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
                    retain.schedule.promotions.length + 2 < targetFuel →
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
              AllocationLayout.Transition.target_nodup retain
                hRetainSourceNodup
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
        hBodyForward sourceCtx (rest.length + 1) hSourceScope
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
        hBodyForward sourceCtx (rest.length + 1) hSourceScope
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
      have hBody := hForward sourceCtx (rest.length + 1) hOrderedRel
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
      have hBody := hForward sourceCtx (rest.length + 1) hOrderedRel
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
