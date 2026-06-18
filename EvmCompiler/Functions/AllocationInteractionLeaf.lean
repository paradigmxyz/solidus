import EvmCompiler.Functions.AllocationInteractionComposition

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionLeaf

open AllocationInteractionRelation
open AllocationInteractionComposition

/-- Lift an expression statement into the recursive control relation. -/
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
    {source : SourceState} {target : TargetState}
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
      (OpenControlResultRel contract lowerCtx lowerFinal localsFinal plan
        returns live frameBase sourceCtx sourceCtx)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx 0 (.expr expr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram 2 { stmts := compiledStmts } target) := by
  exact
    lift_fixed (Functions.Source.Ctx.SameControl.refl sourceCtx)
      (AllocationInteractionStatement.expr_of_lower_compile
        hSafe hScoped hLower hCompile hInvariant)

/-- Lift assignment in either activation representation. -/
theorem assign_of_lower_compile
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
    {name : Locals.Name} {valueExpr : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : SourceState} {target : TargetState}
    (hSafe : AllocationInteractionSafety.ExprSafe contract valueExpr source)
    (hScoped : Functions.Scope.ExprScoped live valueExpr)
    (hLive : name ∈ live)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.assign name valueExpr) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan live frameBase mode source target) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract lowerCtx lowerFinal localsFinal plan
        returns live frameBase sourceCtx sourceCtx)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx 0 (.assign name valueExpr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram 2 { stmts := compiledStmts } target) := by
  exact
    lift_fixed (Functions.Source.Ctx.SameControl.refl sourceCtx)
      (AllocationInteractionAssignment.of_lower_compile
        hSafe hScoped hLive hLower hCompile hInvariant)

/-- Lift a declaration in a genuinely stack-only activation. -/
theorem stack_let_of_lower_compile
    {contract : MemoryContract.Contract}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Expressions.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name} {frameBase : Nat}
    {name : Locals.Name} {valueExpr : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : SourceState} {target : TargetState}
    (hSafe : AllocationInteractionSafety.ExprSafe contract valueExpr source)
    (hAfter :
      AllocationContext.StackExprContext lowerCtx afterState afterLocals plan
        (name :: live))
    (hScoped : Functions.Scope.ExprScoped live valueExpr)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns beforeState
          (.let_ name valueExpr) =
        some (loweredStmts, afterState))
    (hCompile :
      Locals.Block.compileOpen beforeLocals { stmts := loweredStmts } =
        some (compiledStmts, afterLocals))
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx beforeState
        beforeLocals plan live frameBase .stack source target) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract lowerCtx afterState afterLocals plan
        returns (name :: live) frameBase sourceCtx
        { sourceCtx with scope := name :: sourceCtx.scope })
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx 0 (.let_ name valueExpr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram 2 { stmts := compiledStmts } target) := by
  exact
    lift_fixed
      (Functions.Source.Ctx.SameControl.scopeUpdate sourceCtx
        (name :: sourceCtx.scope))
      (AllocationInteractionStatement.stack_let_of_lower_compile
        hSafe hAfter hScoped hLower hCompile hInvariant)

/-- Lift a declaration while a scratch-capable activation is live. -/
theorem scratch_let_of_lower_compile
    {contract : MemoryContract.Contract}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Expressions.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {plan : Plan} {beforeLive afterLive : List Locals.Name}
    {beforeFrameDepth afterFrameDepth frameBase frameWords : Nat}
    {name : Locals.Name} {valueExpr : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : SourceState} {target : TargetState}
    (hSafe : AllocationInteractionSafety.ExprSafe contract valueExpr source)
    (hAfter :
      AllocationContext.ExprContext lowerCtx afterState afterLocals plan
        afterLive afterFrameDepth)
    (hScoped : Functions.Scope.ExprScoped beforeLive valueExpr)
    (hAfterLive : afterLive = name :: beforeLive)
    (hNameFrame : name ≠ lowerCtx.frameName)
    (hScratchBound :
      ∀ slot, plan.location? name = some (.scratch slot) →
        slot < frameWords)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns beforeState
          (.let_ name valueExpr) =
        some (loweredStmts, afterState))
    (hCompile :
      Locals.Block.compileOpen beforeLocals { stmts := loweredStmts } =
        some (compiledStmts, afterLocals))
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx beforeState
        beforeLocals plan beforeLive frameBase
          (.scratch beforeFrameDepth frameWords) source target) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract lowerCtx afterState afterLocals plan
        returns afterLive frameBase sourceCtx
        { sourceCtx with scope := name :: sourceCtx.scope })
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx 0 (.let_ name valueExpr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram 2 { stmts := compiledStmts } target) := by
  exact
    lift_fixed
      (Functions.Source.Ctx.SameControl.scopeUpdate sourceCtx
        (name :: sourceCtx.scope))
      (AllocationInteractionDeclaration.of_lower_compile
        hSafe hAfter hScoped hAfterLive hNameFrame hScratchBound hLower
        hCompile hInvariant)

end AllocationInteractionLeaf
end Functions
end EvmCompiler
