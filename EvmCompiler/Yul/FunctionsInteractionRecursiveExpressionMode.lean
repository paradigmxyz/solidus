import EvmCompiler.Yul.FunctionsInteractionPreparedConditionMode

/-!
Mode-parametric recursive expression interface for the adjacent Yul-to-
Functions pass. This owner exposes only compiler-selected one-result condition
preservation; statement recursion consumes it without inspecting expression
lowering or primitive semantics.
-/

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionRecursiveExpressionMode

open FunctionsInteractionPrimitive
open FunctionsInteractionRelation
open FunctionsInteractionMode

def ConditionForwardAt (mode : Mode)
    (profile : SolcValidation.DialectProfile)
    (sourceProgram : Yul.Program) (targetProgram : Objects.Program)
    (sourceFuel targetFuel : Nat) (layout : List Functions.Name) : Prop :=
  ∀ {expr : AstExpr} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1} {before after : Fresh.State}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx},
    SolcValidation.ExprOk? profile sourceProgram.contract layout 1 expr = true →
    Expr.lower1Unchecked? before expr = some (pre, lower, after) →
    FunctionsInteractionStaticCost.programBudget sourceProgram sourceFuel +
        pre.length + 2 ≤ targetFuel →
    (∀ name, name ∈ layout → name ∈ before.used) →
    ScopedStateRel layout source target →
    TargetDomainWithin before.used target.vars →
    FunctionsInteractionControlRelation.TargetScopeWithin before.used ctx →
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionPreparedConditionMode.DoneRel
        layout after.used ctx)
      (Source.evalValues mode sourceFuel expr
        (some sourceProgram.contract) source)
      (FunctionsInteractionPreparedConditionMode.run mode
        targetProgram.toFunctions ctx targetFuel pre lower target)

end FunctionsInteractionRecursiveExpressionMode
end Yul
end EvmCompiler
