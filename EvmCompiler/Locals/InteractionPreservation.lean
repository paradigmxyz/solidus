import EvmCompiler.Locals.InteractionSemantics
import EvmCompiler.Structured.InteractionPrimitivePreservation

namespace EvmCompiler
namespace Locals
namespace InteractionPreservation

namespace Primitive

def ResultRel (baseStack : EvmYul.Stack Word)
    (returns : List Structured.ReturnDest)
    (source : Locals.Source.State × List Word)
    (target : Structured.RunState) : Prop :=
  target.returns = returns ∧
    target.evm.toSharedState = source.1.shared ∧
      target.evm.stack = source.2.reverse ++ baseStack

abbrev OutcomeRel (baseStack : EvmYul.Stack Word)
    (returns : List Structured.ReturnDest) :
    Except EVMException (Locals.Source.State × List Word) →
      Except EVMException Structured.RunState → Prop :=
  Simulation.Interaction.ExceptRel
    (fun _sourceError _targetError => True)
    (ResultRel baseStack returns)

/--
One stack-free Locals primitive is preserved by its emitted Structured
instruction for every exact resource answer and external-world response.
-/
theorem openEval_op
    {op : Structured.BasicOp}
    {source : Locals.Source.State} {values : List Word}
    (baseStack : EvmYul.Stack Word)
    (returns : List Structured.ReturnDest)
    (hLength :
      values.length = Expressions.Structured.BasicOp.inputs op)
    (hSupports :
      InteractionSemantics.Primitive.supportsOpen op = true) :
    Simulation.Interaction.Rel (OutcomeRel baseStack returns)
      (InteractionSemantics.Primitive.openEval op source values)
      (Structured.InteractionSemantics.BasicInstr.openStep
        (.op op)
        { evm :=
            { InteractionSemantics.Primitive.isolated source values with
              stack := values.reverse ++ baseStack }
          returns := returns }) := by
  have hArity :=
    InteractionSemantics.Primitive.stackArity_of_supportsOpen
      hSupports
  have hBound :
      Expressions.Structured.BasicOp.inputs op ≤
        (InteractionSemantics.Primitive.isolated source values).stack.length := by
    simpa [InteractionSemantics.Primitive.isolated,
      List.length_reverse, hLength]
  have hRaw :=
    Structured.InteractionPrimitivePreservation.BasicOp.openStepEVM_append_stack_rel
      (InteractionSemantics.Primitive.isolated source values)
      baseStack hArity hBound
  simp only [InteractionSemantics.Primitive.openEval,
    hLength, hSupports, ↓reduceIte]
  unfold Structured.InteractionSemantics.BasicInstr.openStep
  apply Simulation.Interaction.Rel.bind hRaw
  intro sourceFinal targetFinal hSuffix
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  constructor
  · rfl
  · constructor
    · have hShared :=
        congrArg EvmYul.EVM.State.toSharedState hSuffix
      simpa [ResultRel, InteractionSemantics.Primitive.finish,
        Assembly.InteractionPreservation.PrimOp.StackSuffixStateRel,
        Assembly.SameRuntimeData, Assembly.eraseRuntimeControl] using
          hShared
    · have hStack :=
        congrArg EvmYul.EVM.State.stack hSuffix
      simpa [ResultRel, InteractionSemantics.Primitive.finish,
        InteractionSemantics.Primitive.isolated,
        Assembly.InteractionPreservation.PrimOp.StackSuffixStateRel,
        Assembly.SameRuntimeData, Assembly.eraseRuntimeControl,
        List.reverse_reverse] using hStack

end Primitive

end InteractionPreservation
end Locals
end EvmCompiler
