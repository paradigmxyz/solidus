import EvmCompiler.Functions.AllocationInteractionExpressionRecursive

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionStatement

open AllocationInteractionRelation

/-- Result relation for one allocated Functions statement. -/
def StmtResultRel
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name) (frameBase : Nat)
    (mode : ActivationMode)
    (expectedCtx : Functions.Source.Ctx) :
    (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx) →
      Expressions.InteractionSemantics.Outcome → Prop
  | (sourceOutcome, sourceCtx), targetOutcome =>
      sourceCtx = expectedCtx ∧
        ActivationOutcomeRel contract plan live 0 frameBase mode
          sourceOutcome targetOutcome

abbrev OpenStmtResultRel
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name) (frameBase : Nat)
    (mode : ActivationMode)
    (expectedCtx : Functions.Source.Ctx) :=
  Simulation.Interaction.ExceptRel
    (fun left right : EVMException => left = right)
    (StmtResultRel contract plan live frameBase mode expectedCtx)

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
    (hCtx :
      AllocationContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState (.expr expr) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hRel :
      ActivationStateRel contract plan live 0 frameBase mode source target) :
    Simulation.Interaction.Rel
      (OpenStmtResultRel contract plan live frameBase mode sourceCtx)
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
              hSafe hCtx hScoped hLowerExpr hCode hRel
          simp only [Locals.codeStmt]
          rw [Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code]
          unfold Functions.InteractionSemantics.Stmt.openRun
            Functions.Source.Canonical.Stmt.run
            Expressions.InteractionSemantics.Stmt.openRun
          simp only [Functions.Source.Effectful.Control.Stmt.run,
            Expressions.EffectSemantics.Control.Stmt.run]
          apply Simulation.Interaction.Rel.bind hExpr
          intro sourceResult targetFinal hResult
          apply Simulation.Interaction.Rel.done
          apply Simulation.Interaction.ExceptRel.ok
          refine ⟨rfl, .regular ?_⟩
          simpa using hResult.state

end AllocationInteractionStatement
end Functions
end EvmCompiler
