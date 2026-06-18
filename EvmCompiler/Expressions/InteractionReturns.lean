import EvmCompiler.Expressions.InteractionPreservation
import EvmCompiler.Structured.InteractionReturns

namespace EvmCompiler
namespace Expressions
namespace InteractionReturns

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
