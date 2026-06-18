import EvmCompiler.Expressions.InteractionPreservation
import EvmCompiler.Structured.InteractionReturns

namespace EvmCompiler
namespace Expressions
namespace InteractionReturns

/-- Condition evaluation preserves the procedure-return stack. -/
theorem Expr.openRunCondition_returns
    (cond : Expressions.Expr 1) (state : Structured.RunState) :
    Simulation.Interaction.AllDone
      (Structured.InteractionSemantics.Code.ConditionReturnsEq state.returns)
      (InteractionSemantics.Expr.openRunCondition cond state) := by
  rw [InteractionPreservation.Expr.openRunCondition_compile]
  exact Structured.InteractionSemantics.Code.openRunCondition_returns
    cond.compile state

/-- One-value expression evaluation and its final pop preserve returns. -/
theorem Expr.openRunOne_returns
    (expr : Expressions.Expr 1) (state : Structured.RunState) :
    Simulation.Interaction.AllDone
      (fun outcome =>
        match outcome with
        | .error _ => True
        | .ok result => result.1.returns = state.returns)
      (InteractionSemantics.Expr.openRunOne expr state) := by
  unfold InteractionSemantics.Expr.openRunOne
  apply Simulation.Interaction.AllDone.bind
    (by
      rw [InteractionPreservation.Expr.openRun_compile]
      exact Structured.InteractionSemantics.Code.openRun_returns
        expr.compile state)
  · intro err _hError
    trivial
  · intro middle hReturns
    cases hPop : middle.evm.stack.pop with
    | none =>
        simp only [hPop, Simulation.Interaction.error]
        exact Simulation.Interaction.AllDone.done True.intro
    | some popped =>
        rcases popped with ⟨stack, value⟩
        simp only [hPop, Simulation.Interaction.pure]
        exact Simulation.Interaction.AllDone.done (by
          simpa [Structured.InteractionSemantics.ReturnsEq] using hReturns)

/-- Expressions control inherits canonical non-halting return-stack safety. -/
theorem Block.openRun_returns
    (program : Expressions.Program) (fuel : Nat)
    (block : Expressions.Block) (state : Structured.RunState) :
    Simulation.Interaction.AllDone
      (Structured.InteractionReturns.OutcomeReturnsEq state.returns)
      (InteractionSemantics.Block.openRun program fuel block state) := by
  rw [InteractionPreservation.Block.openRun_toStructured]
  exact Structured.InteractionReturns.Block.openRun_returns
    program.toStructured fuel block.toStructured state

end InteractionReturns
end Expressions
end EvmCompiler
