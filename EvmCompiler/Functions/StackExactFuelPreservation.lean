import EvmCompiler.Functions.StackBlockPreservation

/-!
Exact-source-fuel composition for compiler-owned stack allocation artifacts.

This companion module owns the well-founded interface needed to close
recursive internal calls. Ordinary all-fuel statement and structured-control
preservation remains in `StackBlockPreservation`; the public allocation theorem
will quantify these exact results after source-fuel recursion is discharged.
-/

namespace EvmCompiler
namespace Functions
namespace StackExactFuelPreservation

open StackRelation
open StackStatementPreservation
open StackBlockPreservation

variable (returnNames : List Name)

theorem controlListAtZero
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (targetCtx finalCtx : Locals.Ctx)
    (stmts : List Functions.Stmt)
    (finalLayout : Locals.Layout)
    (code : List Expressions.Stmt)
    (hLayout : finalCtx.layout = finalLayout) :
    ControlScheduledListPreservesAt sourceProgram targetProgram targets
      returnNames targetCtx finalCtx stmts finalLayout code 0 := by
  refine ⟨hLayout, ?_⟩
  intro sourceCtx targetFuel suffix returns source target hFuel hRuntime
    hInitial
  unfold Functions.InteractionSemantics.Block.openRun
    Functions.InteractionSemantics.stateModel
  simp only [Functions.Source.Effectful.Control.Block.runOpen]
  exact Simulation.Interaction.ForwardRel.truncated rfl

theorem exprConsAt_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel sourceFuel : Nat)
    (expr : Functions.Expr 0) (rest : List Functions.Stmt)
    (fact : AllocationLivenessFacts.Point)
    (restFacts : List AllocationLivenessFacts.Point)
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    {sourceEnv : List Name}
    (hNodup : targetCtx.layout.Nodup)
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
        middleCtx.layout.Nodup →
        StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
            tailLayout rest restFacts = some (points, tailFinal) →
        StackLowering.lowerStmtListFuel lowerFuel lowerCtx rest points =
          some tailLowered →
        Locals.Block.compileOpen middleCtx { stmts := tailLowered } =
          some (tailCode, tailFinalCtx) →
        ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames middleCtx tailFinalCtx rest tailFinal tailCode
          sourceFuel) :
    ControlScheduledListPreservesAt sourceProgram targetProgram targets
      returnNames targetCtx finalCtx (.expr expr :: rest) finalLayout code
      (sourceFuel + 1) := by
  apply controlFallthroughConsAt_of_compilers returnNames sourceProgram
    targetProgram lowerCtx targets pinned scheduleFuel lowerFuel sourceFuel
    (.expr expr) rest fact restFacts hSchedule hLower hCompile
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
        (AllocationLayout.Transition.build?_sound hRetainBuild).1.symm
      simpa [Locals.Ctx.withLayout] using
        hRawStatement.symm.trans hBuiltSource
    have hExprAccess :
        StackAccess.Expr.check?
            (targetCtx.withLayout order.target).layout 0 expr = some () := by
      simpa [StackLowering.pointAccess?, Locals.Ctx.withLayout, hRawBefore]
        using hAccess
    have hCompiled :=
      (compiledExprControlPointOfEquations sourceProgram targetProgram targets
        returnNames (targetCtx.withLayout order.target) middleCtx expr retain
        pointLowered pointCode hRetainSource hScoped hSupported hExprAccess
        hPointLowered hPointCompile).at sourceFuel
    refine ⟨hCompiled, ?_⟩
    rw [hCompiled.layout]
    apply AllocationLayout.Transition.target_nodup retain
    rw [← hRetainSource]
    exact order.target_nodup (by
      rw [AllocationLayout.Ordering.build?_source hOrderBuild]
      exact hNodup)
  · exact hTail

theorem letConsAt_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel sourceFuel : Nat)
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
        middleCtx.layout.Nodup →
        StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
            tailLayout rest restFacts = some (points, tailFinal) →
        StackLowering.lowerStmtListFuel lowerFuel lowerCtx rest points =
          some tailLowered →
        Locals.Block.compileOpen middleCtx { stmts := tailLowered } =
          some (tailCode, tailFinalCtx) →
        ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames middleCtx tailFinalCtx rest tailFinal tailCode
          sourceFuel) :
    ControlScheduledListPreservesAt sourceProgram targetProgram targets
      returnNames targetCtx finalCtx (.let_ name value :: rest) finalLayout
      code (sourceFuel + 1) := by
  apply controlFallthroughConsAt_of_compilers returnNames sourceProgram
    targetProgram lowerCtx targets pinned scheduleFuel lowerFuel sourceFuel
    (.let_ name value) rest fact restFacts hSchedule hLower hCompile
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
        (AllocationLayout.Transition.build?_sound hRetainBuild).1.symm
      simpa [Locals.Ctx.withLayout] using
        hRawStatement.symm.trans hBuiltSource
    have hValueAccess :
        StackAccess.Expr.check?
            (targetCtx.withLayout order.target).layout 0 value = some () := by
      simpa [StackLowering.pointAccess?, Locals.Ctx.withLayout, hRawBefore]
        using hAccess
    have hCompiled :=
      (compiledLetControlPointOfEquations sourceProgram targetProgram targets
        returnNames (targetCtx.withLayout order.target) middleCtx name value
        retain pointLowered pointCode hRetainSource hFresh hScoped hSupported
        hValueAccess hPointLowered hPointCompile).at sourceFuel
    refine ⟨hCompiled, ?_⟩
    rw [hCompiled.layout]
    apply AllocationLayout.Transition.target_nodup retain
    rw [← hRetainSource]
    apply List.nodup_cons.mpr
    exact ⟨hFresh, order.target_nodup (by
      rw [AllocationLayout.Ordering.build?_source hOrderBuild]
      exact hNodup)⟩
  · exact hTail

theorem assignConsAt_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel sourceFuel : Nat)
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
        middleCtx.layout.Nodup →
        StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
            tailLayout rest restFacts = some (points, tailFinal) →
        StackLowering.lowerStmtListFuel lowerFuel lowerCtx rest points =
          some tailLowered →
        Locals.Block.compileOpen middleCtx { stmts := tailLowered } =
          some (tailCode, tailFinalCtx) →
        ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames middleCtx tailFinalCtx rest tailFinal tailCode
          sourceFuel) :
    ControlScheduledListPreservesAt sourceProgram targetProgram targets
      returnNames targetCtx finalCtx (.assign name value :: rest) finalLayout
      code (sourceFuel + 1) := by
  apply controlFallthroughConsAt_of_compilers returnNames sourceProgram
    targetProgram lowerCtx targets pinned scheduleFuel lowerFuel sourceFuel
    (.assign name value) rest fact restFacts hSchedule hLower hCompile
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
        (AllocationLayout.Transition.build?_sound hRetainBuild).1.symm
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
    have hCompiled :=
      (compiledAssignControlPointOfEquations sourceProgram targetProgram
        targets returnNames (targetCtx.withLayout order.target) middleCtx name
        value retain pointLowered pointCode hRetainSource
        (by simpa [Locals.Ctx.withLayout] using hOrderedNodup)
        hScoped hSupported hAssignAccess hPointLowered hPointCompile).at
        sourceFuel
    refine ⟨hCompiled, ?_⟩
    rw [hCompiled.layout]
    apply AllocationLayout.Transition.target_nodup retain
    rw [← hRetainSource]
    simpa [Locals.Ctx.withLayout] using hOrderedNodup
  · exact hTail

theorem compiledScheduledRegionAt_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (scheduleFuel lowerFuel sourceFuel : Nat)
    (body : Functions.Block)
    (bodyFacts : AllocationLivenessFacts.Region)
    (rawRegion : StackSchedule.Region)
    (exit : AllocationLayout.Join)
    (targetCtx regionFinalCtx : Locals.Ctx)
    (hNodup : targetCtx.layout.Nodup)
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
        (targetCtx.withLayout rawRegion.entry.target).layout.Nodup →
        ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx
          body.stmts rawRegion.finalLayout bodyCode sourceFuel) :
    ∃ bodyCode bodyFinalCtx,
      ∃ entryArtifact :
          StackTransitionCompilation.Artifact targetCtx rawRegion.entry,
      ∃ exitArtifact :
          StackTransitionCompilation.JoinArtifact bodyFinalCtx exit,
        ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx
          body.stmts rawRegion.finalLayout bodyCode sourceFuel ∧
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
  have hEntryNodup :
      (targetCtx.withLayout rawRegion.entry.target).layout.Nodup := by
    simp only [Locals.Ctx.withLayout]
    apply AllocationLayout.Transition.target_nodup rawRegion.entry
    rw [← hEntrySource]
    exact hNodup
  have hBodyPreserves :=
    hBody (by simpa using hBodyLower) hBodyCompile hEntryNodup
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

def ControlSwitchBranchPreservesAt
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets)
    (targetCtx : Locals.Ctx) (sourceBody : Functions.Block)
    (targetBody : Expressions.Block) (sourceFuel : Nat) : Prop :=
  ∀ (sourceCtx : Functions.Source.Ctx) (targetFuel : Nat)
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

inductive SwitchBranchRelAt
    (returnNames : List Name)
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targets : StackSchedule.ControlTargets) (targetCtx : Locals.Ctx)
    (sourceFuel : Nat) :
    Option Functions.Block → Option Expressions.Block → Prop
  | none :
      SwitchBranchRelAt returnNames sourceProgram targetProgram targets
        targetCtx sourceFuel none none
  | some {sourceBody : Functions.Block} {targetBody : Expressions.Block} :
      ControlSwitchBranchPreservesAt returnNames sourceProgram targetProgram
          targets targetCtx sourceBody targetBody sourceFuel →
        SwitchBranchRelAt returnNames sourceProgram targetProgram targets
          targetCtx sourceFuel (some sourceBody) (some targetBody)

theorem compiledSwitchBranchAt_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (scheduleFuel lowerFuel sourceFuel : Nat)
    (body : Functions.Block)
    (bodyFacts : AllocationLivenessFacts.Region)
    (rawRegion : StackSchedule.Region)
    (exit : AllocationLayout.Join)
    (targetCtx regionFinalCtx : Locals.Ctx)
    (hNodup : targetCtx.layout.Nodup)
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
        (targetCtx.withLayout rawRegion.entry.target).layout.Nodup →
        ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx
          body.stmts rawRegion.finalLayout bodyCode sourceFuel) :
    ControlSwitchBranchPreservesAt returnNames sourceProgram targetProgram
      targets targetCtx body targetBody sourceFuel := by
  obtain ⟨bodyCode, bodyFinalCtx, entryArtifact, exitArtifact,
      hBodyPreserves, hRegionCode, hRegionFinal, hRestoredCtx, hEntrySource⟩ :=
    compiledScheduledRegionAt_of_compilers returnNames sourceProgram
      targetProgram lowerCtx targets scheduleFuel lowerFuel sourceFuel body
      bodyFacts rawRegion exit targetCtx regionFinalCtx hNodup loweredBody
      regionCode hSchedule hExitBuild hLower hCompile hBody
  obtain ⟨cleanup, hCleanup, hTargetBody⟩ :=
    Locals.finishScoped_components hFinish
  have hBodyPreservesSelf :
      ControlScheduledListPreservesAt sourceProgram targetProgram targets
        returnNames (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx
        body.stmts bodyFinalCtx.layout bodyCode sourceFuel :=
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
  unfold ControlSwitchBranchPreservesAt
  intro sourceCtx targetFuel suffix returns source target hFuel hCtx
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
      hBodyPreservesSelf hCtx
      hEntrySource hFinalControl hScopeCovers hTargetBodyCode hFuel hInitial
  rw [hRestoredCtx] at hRun
  exact hRun

theorem switchDefaultRelAt_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (scheduleFuel lowerFuel sourceFuel : Nat)
    (targetCtx : Locals.Ctx)
    (hNodup : targetCtx.layout.Nodup)
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
        (targetCtx.withLayout rawRegion.entry.target).layout.Nodup →
        ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx
          body.stmts rawRegion.finalLayout bodyCode sourceFuel) :
    SwitchBranchRelAt returnNames sourceProgram targetProgram targets targetCtx
      sourceFuel defaultBody compiledDefault := by
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
      apply SwitchBranchRelAt.some
      apply compiledSwitchBranchAt_of_compilers returnNames sourceProgram
        targetProgram lowerCtx targets scheduleFuel lowerFuel sourceFuel body
        bodyFacts rawRegion exit targetCtx regionFinalCtx hNodup loweredBody
        regionCode targetBody hBodySchedule
        hExitBuild hBodyLower hRegionCompile hFinish
      intro bodyLowered bodyCode bodyFinalCtx hBodyLowered hBodyCompile
        hChildNodup
      exact hBody hBodySchedule hBodyLowered hBodyCompile hChildNodup


theorem switchCasesRelAt_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (scheduleFuel lowerFuel sourceFuel : Nat)
    (targetCtx : Locals.Ctx)
    (hNodup : targetCtx.layout.Nodup)
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
        (targetCtx.withLayout rawRegion.entry.target).layout.Nodup →
        ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx
          body.stmts rawRegion.finalLayout bodyCode sourceFuel)
    (hDefault :
      SwitchBranchRelAt returnNames sourceProgram targetProgram targets targetCtx
        sourceFuel defaultBody compiledDefault) :
    ∀ value,
      SwitchBranchRelAt returnNames sourceProgram targetProgram targets targetCtx
        sourceFuel
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
          SwitchBranchRelAt returnNames sourceProgram targetProgram targets
            targetCtx sourceFuel (some body) (some targetBody) := by
        apply SwitchBranchRelAt.some
        apply compiledSwitchBranchAt_of_compilers returnNames sourceProgram
          targetProgram lowerCtx targets scheduleFuel lowerFuel sourceFuel body
          bodyFacts rawRegion exit targetCtx regionFinalCtx hNodup loweredBody
          regionCode targetBody hBodySchedule hExitBuild hBodyLower
          hRegionCompile hFinish
        intro bodyLowered bodyCode bodyFinalCtx hBodyLowered hBodyCompile
          hChildNodup
        exact hBody hBodySchedule hBodyLowered hBodyCompile hChildNodup
      intro value
      have hTail :=
        ih restFacts restRegions loweredRest compiledRest hRestSchedule
          hRestLower hRestCompile value
      by_cases hMatch : caseValue = value
      · simpa [Functions.Source.Switch.select,
          Expressions.EffectSemantics.Switch.select, hMatch] using hHead
      · simpa [Functions.Source.Switch.select,
          Expressions.EffectSemantics.Switch.select, hMatch] using hTail

theorem switchBranchRelAtToPreserve
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
        SwitchBranchRelAt returnNames sourceProgram targetProgram targets
          targetCtx sourceFuel
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
              apply hPreserves sourceCtx (targetFuel - 2)
              · exact
                  Expressions.TargetFuel.Covers.switch_selected_after_two
                    hFuel hTargetSelect
              · exact hCtx
              · exact hAfter

theorem switchPointAtSucc_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel sourceFuel : Nat)
    (scrutinee : Functions.Expr 1)
    (cases : List (Word × Functions.Block))
    (defaultBody : Option Functions.Block)
    (fact : AllocationLivenessFacts.Point)
    (rawPoint point : StackSchedule.Point)
    (retain : AllocationLayout.Transition)
    (targetCtx finalCtx : Locals.Ctx)
    (hNodup : targetCtx.layout.Nodup)
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
        (targetCtx.withLayout rawRegion.entry.target).layout.Nodup →
        ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx
          body.stmts rawRegion.finalLayout bodyCode sourceFuel) :
    CompiledControlPointAt sourceProgram targetProgram targets returnNames
      targetCtx finalCtx (.switch scrutinee cases defaultBody) code
      retain.schedule.target (sourceFuel + 1) := by
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
    switchDefaultRelAt_of_compilers returnNames sourceProgram targetProgram
      lowerCtx targets scheduleFuel lowerFuel sourceFuel targetCtx hNodup defaultBody
      (fact.regions.drop cases.length) defaultRegions loweredDefault
      compiledDefault hDefaultSchedule hDefaultLower hDefaultCompile
      (fun hChildSchedule hChildLower hChildCompile hChildNodup =>
        hBody hChildSchedule hChildLower hChildCompile hChildNodup)
  have hBranches :=
    switchCasesRelAt_of_compilers returnNames sourceProgram targetProgram
      lowerCtx targets scheduleFuel lowerFuel sourceFuel targetCtx hNodup cases
      defaultBody
      (fact.regions.take cases.length) caseRegions loweredCases compiledCases
      compiledDefault hCaseSchedule hCaseLower hCasesCompile
      (fun hChildSchedule hChildLower hChildCompile hChildNodup =>
        hBody hChildSchedule hChildLower hChildCompile hChildNodup)
      hDefaultRel
  obtain ⟨compiledRetainArtifact⟩ :=
    StackTransitionCompilation.Transition.compileArtifact retain hRetainSource
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
  unfold ControlPointPreservesAt
  intro sourceCtx targetFuel suffix returns source target hFuel hCtx hInitial
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
    switchBranchRelAtToPreserve returnNames sourceProgram targetProgram targets sourceCtx
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
          retain.schedule.promotions.length + 1 < targetFuel := by
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

theorem switchPointAtZero_of_compilers
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
    (retain : AllocationLayout.Transition)
    (targetCtx finalCtx : Locals.Ctx)
    (hNodup : targetCtx.layout.Nodup)
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
        (targetCtx.withLayout rawRegion.entry.target).layout.Nodup →
        ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx
          body.stmts rawRegion.finalLayout bodyCode 0) :
    CompiledControlPointAt sourceProgram targetProgram targets returnNames
      targetCtx finalCtx (.switch scrutinee cases defaultBody) code
      retain.schedule.target 0 := by
  have hLayout :=
    switchPointAtSucc_of_compilers returnNames sourceProgram targetProgram
      lowerCtx targets pinned scheduleFuel lowerFuel 0 scrutinee cases
      defaultBody fact rawPoint point retain targetCtx finalCtx hNodup lowered
      code hScoped hSupported hSchedule hPointBefore hPointRegions
      hPointRetain hRetainSource hLower hCompile hBody
  refine ⟨hLayout.layout, ?_⟩
  intro sourceCtx targetFuel suffix returns source target hFuel hRuntime
    hInitial
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run
    Functions.Source.Effectful.Control.Stmt.run
  exact Simulation.Interaction.ForwardRel.truncated rfl

theorem switchConsAtSucc_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel sourceFuel : Nat)
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
    (hNodup : targetCtx.layout.Nodup)
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
        (childCtx.withLayout rawRegion.entry.target).layout.Nodup →
        ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames (childCtx.withLayout rawRegion.entry.target) bodyFinalCtx
          body.stmts rawRegion.finalLayout bodyCode sourceFuel)
    (hTail :
      ∀ {tailLayout : Locals.Layout} {tailFinal : Locals.Layout}
        {tailLowered : List Locals.Stmt} {middleCtx tailFinalCtx : Locals.Ctx}
        {tailCode : List Expressions.Stmt},
        middleCtx.layout = tailLayout →
        middleCtx.layout.Nodup →
        StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
            tailLayout rest restFacts = some (points, tailFinal) →
        StackLowering.lowerStmtListFuel lowerFuel lowerCtx rest points =
          some tailLowered →
        Locals.Block.compileOpen middleCtx { stmts := tailLowered } =
          some (tailCode, tailFinalCtx) →
        ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames middleCtx tailFinalCtx rest tailFinal tailCode
          (sourceFuel + 1)) :
    ControlScheduledListPreservesAt sourceProgram targetProgram targets
      returnNames targetCtx finalCtx (.switch scrutinee cases defaultBody :: rest)
      finalLayout code ((sourceFuel + 1) + 1) := by
  apply controlFallthroughConsAt_of_compilers returnNames sourceProgram
    targetProgram lowerCtx targets pinned scheduleFuel lowerFuel
    (sourceFuel + 1) (.switch scrutinee cases defaultBody) rest fact restFacts
    hSchedule hLower hCompile
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
        (AllocationLayout.Transition.build?_sound hRetainBuild).1.symm
      simpa [Locals.Ctx.withLayout] using
        hRawStatement.symm.trans hBuiltSource
    have hOrderSource : targetCtx.layout = order.source :=
      (AllocationLayout.Ordering.build?_source hOrderBuild).symm
    have hOrderedNodup : order.target.Nodup :=
      order.target_nodup (by rw [← hOrderSource]; exact hNodup)
    have hCompiled :=
      switchPointAtSucc_of_compilers returnNames sourceProgram targetProgram
        lowerCtx targets pinned scheduleFuel lowerFuel sourceFuel scrutinee cases
        defaultBody fact rawPoint
        { rawPoint with order? := some order, retain? := some retain } retain
        (targetCtx.withLayout order.target) middleCtx
        (by simpa [Locals.Ctx.withLayout] using hOrderedNodup) pointLowered
        pointCode hScoped hSupported hRawSchedule
        (by simpa [Locals.Ctx.withLayout] using hRawBefore)
        (by simpa using hRawRegions) rfl hRetainSource hPointLower hPointCompile
        (fun hChildSchedule hChildLower hChildCompile hChildNodup =>
          hBody hChildSchedule hChildLower hChildCompile hChildNodup)
    refine ⟨hCompiled, ?_⟩
    rw [hCompiled.layout]
    apply AllocationLayout.Transition.target_nodup retain
    rw [← hRetainSource]
    simpa [Locals.Ctx.withLayout] using hOrderedNodup
  · exact hTail

theorem switchConsAtOne_of_compilers
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
    (hNodup : targetCtx.layout.Nodup)
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
        (childCtx.withLayout rawRegion.entry.target).layout.Nodup →
        ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames (childCtx.withLayout rawRegion.entry.target) bodyFinalCtx
          body.stmts rawRegion.finalLayout bodyCode 0)
    (hTail :
      ∀ {tailLayout : Locals.Layout} {tailFinal : Locals.Layout}
        {tailLowered : List Locals.Stmt} {middleCtx tailFinalCtx : Locals.Ctx}
        {tailCode : List Expressions.Stmt},
        middleCtx.layout = tailLayout →
        middleCtx.layout.Nodup →
        StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
            tailLayout rest restFacts = some (points, tailFinal) →
        StackLowering.lowerStmtListFuel lowerFuel lowerCtx rest points =
          some tailLowered →
        Locals.Block.compileOpen middleCtx { stmts := tailLowered } =
          some (tailCode, tailFinalCtx) →
        ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames middleCtx tailFinalCtx rest tailFinal tailCode
          0) :
    ControlScheduledListPreservesAt sourceProgram targetProgram targets
      returnNames targetCtx finalCtx (.switch scrutinee cases defaultBody :: rest)
      finalLayout code 1 := by
  apply controlFallthroughConsAt_of_compilers returnNames sourceProgram
    targetProgram lowerCtx targets pinned scheduleFuel lowerFuel
    0 (.switch scrutinee cases defaultBody) rest fact restFacts
    hSchedule hLower hCompile
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
        (AllocationLayout.Transition.build?_sound hRetainBuild).1.symm
      simpa [Locals.Ctx.withLayout] using
        hRawStatement.symm.trans hBuiltSource
    have hOrderSource : targetCtx.layout = order.source :=
      (AllocationLayout.Ordering.build?_source hOrderBuild).symm
    have hOrderedNodup : order.target.Nodup :=
      order.target_nodup (by rw [← hOrderSource]; exact hNodup)
    have hCompiled :=
      switchPointAtZero_of_compilers returnNames sourceProgram targetProgram
        lowerCtx targets pinned scheduleFuel lowerFuel scrutinee cases
        defaultBody fact rawPoint
        { rawPoint with order? := some order, retain? := some retain } retain
        (targetCtx.withLayout order.target) middleCtx
        (by simpa [Locals.Ctx.withLayout] using hOrderedNodup) pointLowered
        pointCode hScoped hSupported hRawSchedule
        (by simpa [Locals.Ctx.withLayout] using hRawBefore)
        (by simpa using hRawRegions) rfl hRetainSource hPointLower hPointCompile
        (fun hChildSchedule hChildLower hChildCompile hChildNodup =>
          hBody hChildSchedule hChildLower hChildCompile hChildNodup)
    refine ⟨hCompiled, ?_⟩
    rw [hCompiled.layout]
    apply AllocationLayout.Transition.target_nodup retain
    rw [← hRetainSource]
    simpa [Locals.Ctx.withLayout] using hOrderedNodup
  · exact hTail

theorem ifPointAtSucc_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel sourceFuel : Nat)
    (cond : Functions.Expr 1) (body : Functions.Block)
    (fact : AllocationLivenessFacts.Point)
    (rawPoint point : StackSchedule.Point)
    (retain : AllocationLayout.Transition)
    (targetCtx finalCtx : Locals.Ctx)
    (hNodup : targetCtx.layout.Nodup)
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
        (targetCtx.withLayout rawRegion.entry.target).layout.Nodup →
        ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx
          body.stmts rawRegion.finalLayout bodyCode sourceFuel) :
    CompiledControlPointAt sourceProgram targetProgram targets returnNames
      targetCtx finalCtx (.if_ cond body) code retain.schedule.target
      (sourceFuel + 1) := by
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
    compiledScheduledRegionAt_of_compilers returnNames sourceProgram targetProgram
      lowerCtx targets scheduleFuel lowerFuel sourceFuel body bodyFacts rawRegion
      exit targetCtx regionFinalCtx hNodup loweredBody regionCode hChildSchedule
      hExitBuild hLowerBody hRegionCompile
      (fun hBodyLower hBodyCompile hChildNodup =>
        hBody hChildSchedule hBodyLower hBodyCompile hChildNodup)
  obtain ⟨cleanup, hCleanup, hTargetBody⟩ :=
    Locals.finishScoped_components hFinish
  have hBodyPreservesSelf :
      ControlScheduledListPreservesAt sourceProgram targetProgram targets
        returnNames (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx
        body.stmts bodyFinalCtx.layout bodyCode sourceFuel :=
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
  have hCompiledFinalCtx :
      targetCtx.withLayout retain.schedule.target = finalCtx :=
    congrArg Prod.snd hCompiledRetainPair
  refine ⟨?_, ?_⟩
  · rw [← hCompiledFinalCtx]
    rfl
  unfold ControlPointPreservesAt
  intro sourceCtx targetFuel suffix returns source target hFuel hCtx hInitial
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
      RuntimeCtxCovers sourceCtx
        (bodyFinalCtx.withLayout exit.target) targets returnNames returns := by
    rw [hRestoredCtx]
    exact hCtx
  have hScopeCovers :
      ∀ {name : Name}, name ∈ exit.target → name ∈ sourceCtx.scope := by
    intro name hName
    apply hCtx.context.scope
    rwa [hExitTarget] at hName
  have hIfRun :=
    controlIf sourceProgram targetProgram targets returnNames sourceCtx targetCtx
      sourceFuel targetFuel cond body condCode targetBody hTargetFuel hCtx
      hCondScoped hSupported hCondCompile hInitial (by
        intro sourceAfter targetAfter hAfter
        have hBlockRun :=
          controlScheduledRegionAsBlock returnNames sourceProgram targetProgram targets
            sourceCtx targetCtx bodyFinalCtx body bodyCode rawRegion.entry
            entryArtifact exit exitArtifact targetBody sourceFuel
            (targetFuel - 2) hBodyPreservesSelf hCtx
            hEntrySource
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

theorem ifPointAtZero_of_compilers
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
    (hNodup : targetCtx.layout.Nodup)
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
        (targetCtx.withLayout rawRegion.entry.target).layout.Nodup →
        ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx
          body.stmts rawRegion.finalLayout bodyCode 0) :
    CompiledControlPointAt sourceProgram targetProgram targets returnNames
      targetCtx finalCtx (.if_ cond body) code retain.schedule.target 0 := by
  have hLayout :=
    ifPointAtSucc_of_compilers returnNames sourceProgram targetProgram lowerCtx
      targets pinned scheduleFuel lowerFuel 0 cond body fact rawPoint point
      retain targetCtx finalCtx hNodup lowered code hScoped hSupported hSchedule
      hPointBefore hPointRegions hPointRetain hRetainSource hLower hCompile hBody
  refine ⟨hLayout.layout, ?_⟩
  intro sourceCtx targetFuel suffix returns source target hFuel hRuntime
    hInitial
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run
    Functions.Source.Effectful.Control.Stmt.run
  exact Simulation.Interaction.ForwardRel.truncated rfl

theorem ifConsAtSucc_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel sourceFuel : Nat)
    (cond : Functions.Expr 1) (body : Functions.Block)
    (rest : List Functions.Stmt)
    (fact : AllocationLivenessFacts.Point)
    (restFacts : List AllocationLivenessFacts.Point)
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    {sourceEnv : List Name}
    (hNodup : targetCtx.layout.Nodup)
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
        (childCtx.withLayout rawRegion.entry.target).layout.Nodup →
        ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames (childCtx.withLayout rawRegion.entry.target) bodyFinalCtx
          body.stmts rawRegion.finalLayout bodyCode sourceFuel)
    (hTail :
      ∀ {tailLayout : Locals.Layout} {tailFinal : Locals.Layout}
        {tailLowered : List Locals.Stmt} {middleCtx tailFinalCtx : Locals.Ctx}
        {tailCode : List Expressions.Stmt},
        middleCtx.layout = tailLayout →
        middleCtx.layout.Nodup →
        StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
            tailLayout rest restFacts = some (points, tailFinal) →
        StackLowering.lowerStmtListFuel lowerFuel lowerCtx rest points =
          some tailLowered →
        Locals.Block.compileOpen middleCtx { stmts := tailLowered } =
          some (tailCode, tailFinalCtx) →
        ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames middleCtx tailFinalCtx rest tailFinal tailCode
          (sourceFuel + 1)) :
    ControlScheduledListPreservesAt sourceProgram targetProgram targets
      returnNames targetCtx finalCtx (.if_ cond body :: rest) finalLayout code
      ((sourceFuel + 1) + 1) := by
  apply controlFallthroughConsAt_of_compilers returnNames sourceProgram
    targetProgram lowerCtx targets pinned scheduleFuel lowerFuel
    (sourceFuel + 1) (.if_ cond body) rest fact restFacts hSchedule hLower
    hCompile
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
        (AllocationLayout.Transition.build?_sound hRetainBuild).1.symm
      simpa [Locals.Ctx.withLayout] using
        hRawStatement.symm.trans hBuiltSource
    have hOrderSource : targetCtx.layout = order.source :=
      (AllocationLayout.Ordering.build?_source hOrderBuild).symm
    have hOrderedNodup : order.target.Nodup :=
      order.target_nodup (by rw [← hOrderSource]; exact hNodup)
    have hCompiled :=
      ifPointAtSucc_of_compilers returnNames sourceProgram targetProgram
        lowerCtx targets pinned scheduleFuel lowerFuel sourceFuel cond body fact
        rawPoint { rawPoint with order? := some order, retain? := some retain }
        retain (targetCtx.withLayout order.target) middleCtx
        (by simpa [Locals.Ctx.withLayout] using hOrderedNodup) pointLowered
        pointCode hScoped hSupported hRawSchedule
        (by simpa [Locals.Ctx.withLayout] using hRawBefore)
        (by simpa using hRawRegions) rfl hRetainSource hPointLower hPointCompile
        (fun hChildSchedule hChildLower hChildCompile hChildNodup =>
          hBody hChildSchedule hChildLower hChildCompile hChildNodup)
    refine ⟨hCompiled, ?_⟩
    rw [hCompiled.layout]
    apply AllocationLayout.Transition.target_nodup retain
    rw [← hRetainSource]
    simpa [Locals.Ctx.withLayout] using hOrderedNodup
  · exact hTail

theorem ifConsAtOne_of_compilers
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
    (hNodup : targetCtx.layout.Nodup)
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
        (childCtx.withLayout rawRegion.entry.target).layout.Nodup →
        ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames (childCtx.withLayout rawRegion.entry.target) bodyFinalCtx
          body.stmts rawRegion.finalLayout bodyCode 0)
    (hTail :
      ∀ {tailLayout : Locals.Layout} {tailFinal : Locals.Layout}
        {tailLowered : List Locals.Stmt} {middleCtx tailFinalCtx : Locals.Ctx}
        {tailCode : List Expressions.Stmt},
        middleCtx.layout = tailLayout →
        middleCtx.layout.Nodup →
        StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
            tailLayout rest restFacts = some (points, tailFinal) →
        StackLowering.lowerStmtListFuel lowerFuel lowerCtx rest points =
          some tailLowered →
        Locals.Block.compileOpen middleCtx { stmts := tailLowered } =
          some (tailCode, tailFinalCtx) →
        ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames middleCtx tailFinalCtx rest tailFinal tailCode
          0) :
    ControlScheduledListPreservesAt sourceProgram targetProgram targets
      returnNames targetCtx finalCtx (.if_ cond body :: rest) finalLayout code
      1 := by
  apply controlFallthroughConsAt_of_compilers returnNames sourceProgram
    targetProgram lowerCtx targets pinned scheduleFuel lowerFuel
    0 (.if_ cond body) rest fact restFacts hSchedule hLower
    hCompile
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
        (AllocationLayout.Transition.build?_sound hRetainBuild).1.symm
      simpa [Locals.Ctx.withLayout] using
        hRawStatement.symm.trans hBuiltSource
    have hOrderSource : targetCtx.layout = order.source :=
      (AllocationLayout.Ordering.build?_source hOrderBuild).symm
    have hOrderedNodup : order.target.Nodup :=
      order.target_nodup (by rw [← hOrderSource]; exact hNodup)
    have hCompiled :=
      ifPointAtZero_of_compilers returnNames sourceProgram targetProgram
        lowerCtx targets pinned scheduleFuel lowerFuel cond body fact
        rawPoint { rawPoint with order? := some order, retain? := some retain }
        retain (targetCtx.withLayout order.target) middleCtx
        (by simpa [Locals.Ctx.withLayout] using hOrderedNodup) pointLowered
        pointCode hScoped hSupported hRawSchedule
        (by simpa [Locals.Ctx.withLayout] using hRawBefore)
        (by simpa using hRawRegions) rfl hRetainSource hPointLower hPointCompile
        (fun hChildSchedule hChildLower hChildCompile hChildNodup =>
          hBody hChildSchedule hChildLower hChildCompile hChildNodup)
    refine ⟨hCompiled, ?_⟩
    rw [hCompiled.layout]
    apply AllocationLayout.Transition.target_nodup retain
    rw [← hRetainSource]
    simpa [Locals.Ctx.withLayout] using hOrderedNodup
  · exact hTail

theorem blockPointAt_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel sourceFuel : Nat)
    (body : Functions.Block)
    (fact : AllocationLivenessFacts.Point)
    (rawPoint point : StackSchedule.Point)
    (retain : AllocationLayout.Transition)
    (targetCtx finalCtx : Locals.Ctx)
    (lowered : List Locals.Stmt) (code : List Expressions.Stmt)
    (hNodup : targetCtx.layout.Nodup)
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
        (targetCtx.withLayout rawRegion.entry.target).layout.Nodup →
        ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx
          body.stmts rawRegion.finalLayout bodyCode sourceFuel) :
    CompiledControlPointAt sourceProgram targetProgram targets returnNames targetCtx
      finalCtx (.block body) code retain.schedule.target sourceFuel := by
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
  have hEntryNodup :
      (targetCtx.withLayout rawRegion.entry.target).layout.Nodup := by
    simp only [Locals.Ctx.withLayout]
    apply AllocationLayout.Transition.target_nodup rawRegion.entry
    rw [← hEntrySource]
    exact hNodup
  have hBodyPreserves :=
    hBody hChildSchedule (by simpa using hBodyLower) hBodyCompile hEntryNodup
  have hBodyLayout : bodyFinalCtx.layout = rawRegion.finalLayout :=
    hBodyPreserves.1
  have hBodyPreservesSelf :
      ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames (targetCtx.withLayout rawRegion.entry.target) bodyFinalCtx
          body.stmts bodyFinalCtx.layout bodyCode sourceFuel :=
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
    StackTransitionCompilation.Transition.compileArtifact retain hRetainSource
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
  unfold ControlPointPreservesAt
  intro sourceCtx targetFuel suffix returns source target hFuel
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
      exitArtifact sourceFuel targetFuel hBodyPreservesSelf
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
      targetBlock.stmts.length + retain.schedule.promotions.length + 1 <
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

theorem blockConsAt_of_compilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel sourceFuel : Nat)
    (body : Functions.Block) (rest : List Functions.Stmt)
    (fact : AllocationLivenessFacts.Point)
    (restFacts : List AllocationLivenessFacts.Point)
    {point : StackSchedule.Point} {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    (hNodup : targetCtx.layout.Nodup)
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
        (childCtx.withLayout rawRegion.entry.target).layout.Nodup →
        ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames (childCtx.withLayout rawRegion.entry.target)
          bodyFinalCtx body.stmts rawRegion.finalLayout bodyCode sourceFuel)
    (hTail :
      ∀ {tailLayout : Locals.Layout} {tailFinal : Locals.Layout}
        {tailLowered : List Locals.Stmt} {middleCtx tailFinalCtx : Locals.Ctx}
        {tailCode : List Expressions.Stmt},
        middleCtx.layout = tailLayout →
        middleCtx.layout.Nodup →
        StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
            tailLayout rest restFacts = some (points, tailFinal) →
        StackLowering.lowerStmtListFuel lowerFuel lowerCtx rest points =
          some tailLowered →
        Locals.Block.compileOpen middleCtx { stmts := tailLowered } =
          some (tailCode, tailFinalCtx) →
        ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames middleCtx tailFinalCtx rest tailFinal tailCode
          sourceFuel) :
    ControlScheduledListPreservesAt sourceProgram targetProgram targets
      returnNames targetCtx finalCtx (.block body :: rest) finalLayout code
      (sourceFuel + 1) := by
  apply controlFallthroughConsAt_of_compilers returnNames sourceProgram
    targetProgram lowerCtx targets pinned scheduleFuel lowerFuel sourceFuel
    (.block body) rest fact restFacts hSchedule hLower hCompile
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
        (AllocationLayout.Transition.build?_sound hRetainBuild).1.symm
      simpa [Locals.Ctx.withLayout] using
        hRawStatement.symm.trans hBuiltSource
    have hOrderSource : targetCtx.layout = order.source :=
      (AllocationLayout.Ordering.build?_source hOrderBuild).symm
    have hOrderedNodup : order.target.Nodup :=
      order.target_nodup (by rw [← hOrderSource]; exact hNodup)
    have hCompiled :=
      blockPointAt_of_compilers returnNames sourceProgram targetProgram
        lowerCtx targets pinned scheduleFuel lowerFuel sourceFuel body fact
        rawPoint { rawPoint with order? := some order, retain? := some retain }
        retain (targetCtx.withLayout order.target) middleCtx pointLowered
        pointCode (by simpa [Locals.Ctx.withLayout] using hOrderedNodup)
        hRawSchedule (by simpa using hRawRegions) rfl hRetainSource
        hPointLower hPointCompile
        (fun hChildSchedule hChildLower hChildCompile hChildNodup =>
          hBody hChildSchedule hChildLower hChildCompile hChildNodup)
    refine ⟨hCompiled, ?_⟩
    rw [hCompiled.layout]
    apply AllocationLayout.Transition.target_nodup retain
    rw [← hRetainSource]
    simpa [Locals.Ctx.withLayout] using hOrderedNodup
  · exact hTail

end StackExactFuelPreservation
end Functions
end EvmCompiler
