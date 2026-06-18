import EvmCompiler.Functions.AllocationInteractionExpressionRecursive
import EvmCompiler.Locals.InteractionStatePreservation

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionStatement

open AllocationInteractionRelation

/--
Statement outcomes retain the full compiler/runtime invariant on regular
continuation and the activation-owned relation on abrupt or terminal exits.
-/
inductive BoundaryOutcomeRel
    (contract : MemoryContract.Contract)
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx)
    (plan : Plan) (live : List Locals.Name)
    (frameBase : Nat) (mode : ActivationMode) :
    Functions.InteractionSemantics.Outcome →
      Expressions.InteractionSemantics.Outcome → Prop where
  | regular {source : SourceState} {target : TargetState}
      (invariant :
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
          localsCtx plan live frameBase mode source target) :
      BoundaryOutcomeRel contract lowerCtx lowerState localsCtx plan live
        frameBase mode
        (Functions.Source.Effectful.Outcome.regular source)
        (Structured.EffectSemantics.Outcome.regular target)
  | brk {source : SourceState} {target : TargetState}
      (state :
        ActivationStateRel contract plan live 0 frameBase mode source target) :
      BoundaryOutcomeRel contract lowerCtx lowerState localsCtx plan live
        frameBase mode
        (Functions.Source.Effectful.Outcome.brk source)
        (Structured.EffectSemantics.Outcome.brk target)
  | cont {source : SourceState} {target : TargetState}
      (state :
        ActivationStateRel contract plan live 0 frameBase mode source target) :
      BoundaryOutcomeRel contract lowerCtx lowerState localsCtx plan live
        frameBase mode
        (Functions.Source.Effectful.Outcome.cont source)
        (Structured.EffectSemantics.Outcome.cont target)
  | leave {source : SourceState} {target : TargetState}
      (state : LeaveStateRel contract live source target) :
      BoundaryOutcomeRel contract lowerCtx lowerState localsCtx plan live
        frameBase mode
        (Functions.Source.Effectful.Outcome.leave source)
        (Structured.EffectSemantics.Outcome.leave target)
  | halt (kind : Assembly.HaltKind)
      {source : SourceState} {target : TargetState}
      (state : HaltStateRel contract plan source target) :
      BoundaryOutcomeRel contract lowerCtx lowerState localsCtx plan live
        frameBase mode
        (Functions.Source.Effectful.Outcome.halt kind source)
        (Structured.EffectSemantics.Outcome.halt kind target)

/-- Result relation for one allocated Functions statement. -/
def StmtResultRel
    (contract : MemoryContract.Contract)
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx) (plan : Plan)
    (live : List Locals.Name) (frameBase : Nat)
    (mode : ActivationMode)
    (expectedCtx : Functions.Source.Ctx) :
    (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx) →
      Expressions.InteractionSemantics.Outcome → Prop
  | (sourceOutcome, sourceCtx), targetOutcome =>
      sourceCtx = expectedCtx ∧
        BoundaryOutcomeRel contract lowerCtx lowerState localsCtx plan live
          frameBase mode sourceOutcome targetOutcome

abbrev OpenStmtResultRel
    (contract : MemoryContract.Contract)
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx) (plan : Plan)
    (live : List Locals.Name) (frameBase : Nat)
    (mode : ActivationMode)
    (expectedCtx : Functions.Source.Ctx) :=
  Simulation.Interaction.ExceptRel
    (fun left right : EVMException => left = right)
    (StmtResultRel contract lowerCtx lowerState localsCtx plan live
      frameBase mode expectedCtx)

/--
An expression statement is preserved by the ordinary allocation lowerer and
Locals compiler. The statement layer merely packages the recursively proved
expression result as a regular control outcome.
-/
theorem expr_of_lower_compile
    {contract : MemoryContract.Contract}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Expressions.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {expr : Functions.Expr 0}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : AllocationInteractionRelation.SourceState}
    {target : AllocationInteractionRelation.TargetState}
    (hSafe : AllocationInteractionSafety.ExprSafe contract expr source)
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState (.expr expr) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan live frameBase mode source target) :
    Simulation.Interaction.Rel
      (OpenStmtResultRel contract lowerCtx lowerFinal localsFinal plan live
        frameBase mode sourceCtx)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx 0 (.expr expr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram 2 { stmts := compiledStmts } target) := by
  cases hLowerExpr :
      AllocationLowering.lowerExpr lowerCtx lowerState expr with
  | none =>
      simp [AllocationLowering.lowerStmt, hLowerExpr] at hLower
  | some lowered =>
      simp [AllocationLowering.lowerStmt, hLowerExpr] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      cases hCode : Locals.Expr.compileCode localsCtx 0 lowered with
      | none =>
          simp [Locals.Block.compileOpen, Locals.Stmt.compile, hCode]
            at hCompile
      | some code =>
          simp [Locals.Block.compileOpen, Locals.Stmt.compile, hCode]
            at hCompile
          rcases hCompile with ⟨rfl, rfl⟩
          have hExpr :=
            AllocationInteractionExpressionRecursive.forwardExpr
              hSafe hInvariant.compiler hScoped hLowerExpr hCode
              hInvariant.state
          have hVars :=
            Locals.InteractionStatePreservation.expr_openEval_vars expr source
          have hExprStrong :=
            Simulation.Interaction.Rel.strengthen_left hExpr hVars
          simp only [Locals.codeStmt]
          rw [Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code]
          unfold Functions.InteractionSemantics.Stmt.openRun
            Functions.Source.Canonical.Stmt.run
            Expressions.InteractionSemantics.Stmt.openRun
          simp only [Functions.Source.Effectful.Control.Stmt.run,
            Expressions.EffectSemantics.Control.Stmt.run]
          apply Simulation.Interaction.Rel.bind_custom hExprStrong
          intro sourceDone targetDone hDone
          rcases hDone with ⟨hRelated, hVarsDone⟩
          cases hRelated with
          | error hError =>
              exact .done (.error hError)
          | @ok sourceResult targetFinal hResult =>
              apply Simulation.Interaction.Rel.done
              apply Simulation.Interaction.ExceptRel.ok
              refine ⟨rfl, .regular ?_⟩
              exact
                { compiler := hInvariant.compiler
                  planWF := hInvariant.planWF
                  defined := hInvariant.defined.congr_vars hVarsDone
                  state := by simpa using hResult.state
                  stackLength := by
                    have hValues : sourceResult.2 = [] :=
                      List.eq_nil_of_length_eq_zero hResult.valuesLength
                    rw [hResult.stack, hValues]
                    simpa using hInvariant.stackLength }

end AllocationInteractionStatement
end Functions
end EvmCompiler
