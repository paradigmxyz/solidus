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
    (transition : AllocationLayout.Transition)
    (finalLayout tailFinal : Locals.Layout)
    (headCode tailCode code : List Expressions.Stmt)
    (hRetain : point.retain? = some transition)
    (hMiddle :
      middleCtx = targetCtx.withLayout transition.schedule.target)
    (hHeadLength :
      headCode.length = transition.schedule.promotions.length + 2)
    (hHead :
      ∀ (sourceCtx : Functions.Source.Ctx)
        (sourceFuel targetFuel : Nat)
        {suffix : List Word} {returns : List Structured.ReturnDest}
        {source : Locals.Source.State} {target : Structured.RunState},
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
    simp [regularLeafTargetCost, hRetain]
  · intro sourceCtx suffix returns source target hCtx hInitial
    have hHeadFuel :
        transition.schedule.promotions.length + 2 <
          regularLeafTargetCost (point :: points) + 1 := by
      simp [regularLeafTargetCost, hRetain]
      omega
    have hHeadRun :=
      hHead sourceCtx (rest.length + 1)
        (regularLeafTargetCost (point :: points) + 1)
        hHeadFuel hCtx hInitial
    have hTailFuel :
        regularLeafTargetCost (point :: points) + 1 - headCode.length =
          regularLeafTargetCost points + 1 := by
      simp [regularLeafTargetCost, hRetain, hHeadLength]
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
          simp [StackSchedule.scheduleStmtListFuel] at hSchedule
  | @expr rest expr hTailLeaves ih =>
      cases facts with
      | nil =>
          simp [StackSchedule.scheduleStmtListFuel] at hSchedule
      | cons fact restFacts =>
          obtain ⟨point, tailPoints, hPoints⟩ :=
            StackSchedule.scheduleStmtListFuel_cons_nonempty hSchedule
          subst points
          obtain
              ⟨retain, tailFinal, hBefore, _hStatement, hPointRetain,
                _hRegions, _hFalls, hBuild, hTailSchedule, hFinal⟩ :=
            StackSchedule.scheduleStmtListFuel_expr_components hSchedule
          obtain
              ⟨lowerRetain, tailLowered, hPointAccess, hLowerRetain,
                hTailLower, hLowered⟩ :=
            StackLowering.lowerStmtListFuel_expr_components hLower
          have hRetainEq : lowerRetain = retain :=
            Option.some.inj (hLowerRetain.symm.trans hPointRetain)
          subst lowerRetain
          have hAccess :
              StackAccess.Expr.check? targetCtx.layout 0 expr = some () := by
            simpa [StackLowering.pointAccess?, hBefore] using hPointAccess
          have hSource : targetCtx.layout = retain.source :=
            (AllocationLayout.Transition.build?_sound hBuild).1.symm
          rw [hLowered] at hCompile
          obtain
              ⟨headCode, middleCtx, tailCode,
                hHeadCompile, hTailCompile, hCode⟩ :=
            Locals.Block.compileOpen_append_components hCompile
          obtain ⟨hMiddle, hHeadLength, hHeadForward⟩ :=
            compiledExprPointOfEquations sourceProgram targetProgram
              targetCtx middleCtx expr retain
              ([.expr expr] ++ StackLowering.transitionStmts retain)
              headCode hSource hScoped.1 hSupported.1 hAccess rfl
              hHeadCompile
          have hRetainSourceNodup : retain.source.Nodup := by
            rw [← hSource]
            exact hNodup
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
              finalCtx (.expr expr) rest point tailPoints retain finalLayout
              tailFinal headCode tailCode code hPointRetain hMiddle
              hHeadLength hHeadForward hTailResult hFinal hCode
  | @let_ rest name value hTailLeaves ih =>
      cases facts with
      | nil =>
          simp [StackSchedule.scheduleStmtListFuel] at hSchedule
      | cons fact restFacts =>
          obtain ⟨point, tailPoints, hPoints⟩ :=
            StackSchedule.scheduleStmtListFuel_cons_nonempty hSchedule
          subst points
          obtain
              ⟨retain, tailFinal, hFresh, hBefore, _hStatement,
                hPointRetain, _hRegions, _hFalls, hBuild, hTailSchedule,
                hFinal⟩ :=
            StackSchedule.scheduleStmtListFuel_let_components hSchedule
          obtain
              ⟨lowerRetain, tailLowered, hPointAccess, hLowerRetain,
                hTailLower, hLowered⟩ :=
            StackLowering.lowerStmtListFuel_let_components hLower
          have hRetainEq : lowerRetain = retain :=
            Option.some.inj (hLowerRetain.symm.trans hPointRetain)
          subst lowerRetain
          have hAccess :
              StackAccess.Expr.check? targetCtx.layout 0 value = some () := by
            simpa [StackLowering.pointAccess?, hBefore] using hPointAccess
          have hSource : name :: targetCtx.layout = retain.source :=
            (AllocationLayout.Transition.build?_sound hBuild).1.symm
          rw [hLowered] at hCompile
          obtain
              ⟨headCode, middleCtx, tailCode,
                hHeadCompile, hTailCompile, hCode⟩ :=
            Locals.Block.compileOpen_append_components hCompile
          obtain ⟨hMiddle, hHeadLength, hHeadForward⟩ :=
            compiledLetPointOfEquations sourceProgram targetProgram
              targetCtx middleCtx name value retain
              ([.let_ name value] ++ StackLowering.transitionStmts retain)
              headCode hSource hFresh hScoped.1.2 hSupported.1 hAccess rfl
              hHeadCompile
          have hRetainSourceNodup : retain.source.Nodup := by
            rw [← hSource]
            exact List.nodup_cons.mpr ⟨hFresh, hNodup⟩
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
              finalCtx (.let_ name value) rest point tailPoints retain
              finalLayout tailFinal headCode tailCode code hPointRetain
              hMiddle hHeadLength hHeadForward hTailResult hFinal hCode
  | @assign rest name value hTailLeaves ih =>
      cases facts with
      | nil =>
          simp [StackSchedule.scheduleStmtListFuel] at hSchedule
      | cons fact restFacts =>
          obtain ⟨point, tailPoints, hPoints⟩ :=
            StackSchedule.scheduleStmtListFuel_cons_nonempty hSchedule
          subst points
          obtain
              ⟨retain, tailFinal, hBefore, _hStatement, hPointRetain,
                _hRegions, _hFalls, hBuild, hTailSchedule, hFinal⟩ :=
            StackSchedule.scheduleStmtListFuel_assign_components hSchedule
          obtain
              ⟨lowerRetain, tailLowered, hPointAccess, hLowerRetain,
                hTailLower, hLowered⟩ :=
            StackLowering.lowerStmtListFuel_assign_components hLower
          have hRetainEq : lowerRetain = retain :=
            Option.some.inj (hLowerRetain.symm.trans hPointRetain)
          subst lowerRetain
          have hAccess :
              StackAccess.assign? targetCtx.layout name value = some () := by
            simpa [StackLowering.pointAccess?, hBefore] using hPointAccess
          have hSource : targetCtx.layout = retain.source :=
            (AllocationLayout.Transition.build?_sound hBuild).1.symm
          rw [hLowered] at hCompile
          obtain
              ⟨headCode, middleCtx, tailCode,
                hHeadCompile, hTailCompile, hCode⟩ :=
            Locals.Block.compileOpen_append_components hCompile
          obtain ⟨hMiddle, hHeadLength, hHeadForward⟩ :=
            compiledAssignPointOfEquations sourceProgram targetProgram
              targetCtx middleCtx name value retain
              ([.assign name value] ++ StackLowering.transitionStmts retain)
              headCode hSource hNodup hScoped.1.2 hSupported.1 hAccess rfl
              hHeadCompile
          have hRetainSourceNodup : retain.source.Nodup := by
            rw [← hSource]
            exact hNodup
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
              finalCtx (.assign name value) rest point tailPoints retain
              finalLayout tailFinal headCode tailCode code hPointRetain
              hMiddle hHeadLength hHeadForward hTailResult hFinal hCode

end StackBlockPreservation
end Functions
end EvmCompiler
