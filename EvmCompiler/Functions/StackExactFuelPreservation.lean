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
