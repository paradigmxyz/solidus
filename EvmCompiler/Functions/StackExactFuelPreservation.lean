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

end StackExactFuelPreservation
end Functions
end EvmCompiler
