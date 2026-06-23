import EvmCompiler.Expressions.InteractionSemantics
import EvmCompiler.Expressions.TargetFuel
import EvmCompiler.Structured.InteractionFuelSafety

namespace EvmCompiler
namespace Expressions
namespace TargetFuelSafety

open Assembly.InteractionFuelSafety

mutual

theorem expressionOpenRun {results : Nat}
    (expr : Expressions.Expr results) (state : Structured.RunState) :
    Simulation.Interaction.AllDone NotOutOfFuel
      (Expressions.InteractionSemantics.Expr.openRun expr state) := by
  cases expr with
  | lit value =>
      exact Structured.InteractionFuelSafety.BasicInstr.openStep
        (.push value) state
  | code code =>
      exact Structured.InteractionFuelSafety.Code.openRun code state
  | prim op args =>
      unfold Expressions.InteractionSemantics.Expr.openRun
      simp only [Expressions.EffectSemantics.Control.Expr.run]
      exact NotOutOfFuel.bind (expressionSeqOpenRun args state)
        (fun next =>
          Structured.InteractionFuelSafety.BasicInstr.openStep (.op op) next)

theorem expressionSeqOpenRun {results : Nat}
    (exprs : Expressions.ExprSeq results) (state : Structured.RunState) :
    Simulation.Interaction.AllDone NotOutOfFuel
      (Expressions.InteractionSemantics.ExprSeq.openRun exprs state) := by
  cases exprs with
  | nil => exact .done trivial
  | cons head tail =>
      unfold Expressions.InteractionSemantics.ExprSeq.openRun
      simp only [Expressions.EffectSemantics.Control.ExprSeq.run]
      exact NotOutOfFuel.bind (expressionOpenRun head state)
        (fun next => expressionSeqOpenRun tail next)

end

end TargetFuelSafety
end Expressions
end EvmCompiler
