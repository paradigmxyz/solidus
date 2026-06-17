import EvmCompiler.Assembly.InteractionPreservation
import EvmCompiler.Structured.InteractionSemantics

namespace EvmCompiler
namespace Structured
namespace InteractionPrimitivePreservation

namespace BasicOp

/--
One Structured primitive preserves an opaque caller-owned stack suffix.

This is the adjacent primitive interface for higher stack-free languages.
The Assembly proof remains owned below this module.
-/
theorem openStepEVM_append_stack_rel
    {op : Structured.BasicOp} {input output : Nat}
    (state : EVMState) (hidden : EvmYul.Stack Word)
    (hArity :
      op.toPrimOp.stackArity? = some (input, output))
    (hBound : input ≤ state.stack.length) :
    Simulation.Interaction.Rel
      (Assembly.InteractionPreservation.PrimOp.StackSuffixRuntimeRel
        hidden)
      (InteractionSemantics.BasicInstr.openStepEVM (.op op) state)
      (InteractionSemantics.BasicInstr.openStepEVM (.op op)
        { state with stack := state.stack ++ hidden }) := by
  exact
    Assembly.InteractionPreservation.PrimOp.openStep_append_stack_rel_of_stackArity_le
      state hidden hArity hBound

end BasicOp

end InteractionPrimitivePreservation
end Structured
end EvmCompiler
