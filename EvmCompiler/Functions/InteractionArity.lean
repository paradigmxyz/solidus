import EvmCompiler.Functions.InteractionSemantics
import EvmCompiler.Locals.InteractionArity

namespace EvmCompiler
namespace Functions
namespace InteractionArity

abbrev OutputLength := Locals.InteractionArity.OutputLength

namespace Expr

theorem openEval_length {results : Nat}
    (expr : Functions.Expr results)
    (state : Functions.InteractionSemantics.State) :
    Simulation.Interaction.AllDone (OutputLength results)
      (Functions.InteractionSemantics.Expr.openEval expr state) :=
  Locals.InteractionArity.Expr.openEval_length expr state

theorem openEvalOne_iszero_eq_map
    (expr : Functions.Expr 1)
    (state : Functions.InteractionSemantics.State) :
    Functions.InteractionSemantics.Expr.openEvalOne
        (.prim .iszero (Locals.ExprSeq.cons expr .nil)) state =
      Simulation.Interaction.map
        (fun result => (result.1, EvmYul.UInt256.isZero result.2))
        (Functions.InteractionSemantics.Expr.openEvalOne expr state) :=
  Locals.InteractionArity.Expr.openEvalOne_iszero_eq_map expr state

theorem openEvalCondition_iszero_eq_map_openEvalOne
    (expr : Functions.Expr 1)
    (state : Functions.InteractionSemantics.State) :
    Functions.InteractionSemantics.Expr.openEvalCondition
        (.prim .iszero (Locals.ExprSeq.cons expr .nil)) state =
      Simulation.Interaction.map
        (fun result =>
          (result.1, result.2 == EvmYul.UInt256.ofNat 0))
        (Functions.InteractionSemantics.Expr.openEvalOne expr state) :=
  Locals.InteractionArity.Expr.openEvalCondition_iszero_eq_map_openEvalOne
    expr state

end Expr

end InteractionArity
end Functions
end EvmCompiler
