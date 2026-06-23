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

theorem expressionOpenRunOne (expr : Expressions.Expr 1)
    (state : Structured.RunState) :
    Simulation.Interaction.AllDone NotOutOfFuel
      (Expressions.InteractionSemantics.Expr.openRunOne expr state) := by
  unfold Expressions.InteractionSemantics.Expr.openRunOne
  apply NotOutOfFuel.bind (expressionOpenRun expr state)
  intro final
  cases final.evm.stack.pop <;> exact .done (by simp [NotOutOfFuel])

theorem expressionOpenRunCondition (expr : Expressions.Expr 1)
    (state : Structured.RunState) :
    Simulation.Interaction.AllDone NotOutOfFuel
      (Expressions.InteractionSemantics.Expr.openRunCondition expr state) := by
  unfold Expressions.InteractionSemantics.Expr.openRunCondition
    Expressions.EffectSemantics.Control.Expr.runCondition
  apply NotOutOfFuel.bind (expressionOpenRun expr state)
  intro final
  unfold Structured.EffectSemantics.Control.Code.popCondition
  simp only [Structured.EffectSemantics.Ordinary.runStateModel_evm]
  cases final.evm.stack.pop <;> exact .done (by simp [NotOutOfFuel])

end TargetFuelSafety
end Expressions
end EvmCompiler
