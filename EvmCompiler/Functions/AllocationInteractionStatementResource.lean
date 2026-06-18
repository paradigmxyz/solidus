import EvmCompiler.Functions.AllocationInteractionPrimitiveResource
import EvmCompiler.Functions.AllocationInteractionResource
import EvmCompiler.Functions.AllocationInteractionStatement

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionStatementResource

open AllocationInteractionRelation
open AllocationInteractionFrame
open AllocationInteractionResource

/--
An expression statement preserves allocator resources through the ordinary
allocation lowerer and Locals compiler.
-/
theorem expr_of_lower_compile
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth : Nat} {config : Config}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Expressions.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {sourceFuel targetExtra frameBase : Nat} {mode : ActivationMode}
    {expr : Functions.Expr 0}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : SourceState} {target : TargetState}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
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
        localsCtx plan live frameBase mode source target)
    (hReady : AllocatorReady config allocatorDepth target) :
    Simulation.Interaction.Rel
      (OpenResultRel config allocatorDepth mode target)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.expr expr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (targetExtra + 2) { stmts := compiledStmts } target) := by
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
            AllocationInteractionExpressionResource.forwardExpr
              (AllocationInteractionPrimitiveResource.canonicalPrimitiveForward
                contract)
              hConfig hSafe hInvariant.compiler hScoped hLowerExpr hCode
              hInvariant.state hReady
          simp only [Locals.codeStmt]
          rw [Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code]
          unfold Functions.InteractionSemantics.Stmt.openRun
            Functions.Source.Canonical.Stmt.run
            Expressions.InteractionSemantics.Stmt.openRun
          simp only [Functions.Source.Effectful.Control.Stmt.run,
            Expressions.EffectSemantics.Control.Stmt.run]
          apply Simulation.Interaction.Rel.bind_custom hExpr
          intro sourceDone targetDone hDone
          cases hDone with
          | error hError => exact .done (.error hError)
          | ok hResult =>
              apply Simulation.Interaction.Rel.done
              apply Simulation.Interaction.ExceptRel.ok
              exact ActivationEffect.of_allocatorEffect hResult.2

end AllocationInteractionStatementResource
end Functions
end EvmCompiler
