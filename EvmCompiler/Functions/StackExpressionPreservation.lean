import EvmCompiler.Functions.StackRelation

/-!
Expression preservation specialized to the dynamic stack-layout relation.
The primitive/open-world proof remains owned by Locals.
-/

namespace EvmCompiler
namespace Functions
namespace StackExpressionPreservation

open StackRelation

theorem openEval_compileCode
    {results : Nat} (expr : Locals.Expr results)
    (ctx : Locals.Ctx)
    {code : Structured.Code} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hScoped : Locals.Scope.ExprScoped ctx.layout expr)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported expr)
    (hCompile : Locals.Expr.compileCode ctx 0 expr = some code)
    (hRel : StateRel ctx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (Locals.InteractionPreservation.Expr.OutcomeRel results source target)
      (Locals.InteractionSemantics.Expr.openEval expr source)
      (Structured.InteractionSemantics.Code.openRun code target) := by
  exact
    Locals.InteractionPreservation.Expr.openEval_compileCode
      expr ctx 0 hScoped hSupported hCompile hRel.expr

theorem openEvalZero_compileCode
    (expr : Locals.Expr 0) (ctx : Locals.Ctx)
    {code : Structured.Code} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hScoped : Locals.Scope.ExprScoped ctx.layout expr)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported expr)
    (hCompile : Locals.Expr.compileCode ctx 0 expr = some code)
    (hRel : StateRel ctx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (Simulation.Interaction.ExceptRel
        (fun _ _ => True)
        (fun sourceResult targetResult =>
          StateRel ctx.layout suffix returns sourceResult.1 targetResult))
      (Locals.InteractionSemantics.Expr.openEval expr source)
      (Structured.InteractionSemantics.Code.openRun code target) := by
  apply Simulation.Interaction.Rel.mono
    (openEval_compileCode expr ctx hScoped hSupported hCompile hRel)
  intro sourceResult targetResult hResult
  cases hResult with
  | error => exact .error trivial
  | ok hOk => exact .ok (hRel.ofExprResultZero hOk)

theorem openEvalOne_compileCode
    (expr : Locals.Expr 1) (ctx : Locals.Ctx)
    {code : Structured.Code} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hScoped : Locals.Scope.ExprScoped ctx.layout expr)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported expr)
    (hCompile : Locals.Expr.compileCode ctx 0 expr = some code)
    (hRel : StateRel ctx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (Locals.InteractionPreservation.Expr.OneOutcomeRel source target)
      (Locals.InteractionSemantics.Expr.openEvalOne expr source)
      (Structured.InteractionSemantics.Code.openRun code target) := by
  exact
    Locals.InteractionPreservation.Expr.openEvalOne_compileCode
      expr ctx 0 hScoped hSupported hCompile hRel.expr

theorem openEvalOne_fresh_compileCode
    (expr : Locals.Expr 1) (ctx : Locals.Ctx) (name : Name)
    {code : Structured.Code} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hFresh : name ∉ ctx.layout)
    (hScoped : Locals.Scope.ExprScoped ctx.layout expr)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported expr)
    (hCompile : Locals.Expr.compileCode ctx 0 expr = some code)
    (hRel : StateRel ctx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (Simulation.Interaction.ExceptRel
        (fun _ _ => True)
        (fun sourceResult targetResult =>
          StateRel (name :: ctx.layout) suffix returns
            (sourceResult.1.insert name sourceResult.2) targetResult))
      (Locals.InteractionSemantics.Expr.openEvalOne expr source)
      (Structured.InteractionSemantics.Code.openRun code target) := by
  apply Simulation.Interaction.Rel.mono
    (Locals.InteractionPreservation.Expr.openEvalOne_compileCode
      expr ctx 0 hScoped hSupported hCompile hRel.expr)
  intro sourceResult targetResult hResult
  cases hResult with
  | error => exact .error trivial
  | ok hOk => exact .ok (hRel.ofExprResultOneInsert hFresh hOk)

end StackExpressionPreservation
end Functions
end EvmCompiler
