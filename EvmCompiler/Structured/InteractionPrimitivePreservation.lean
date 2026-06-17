import EvmCompiler.Assembly.InteractionPreservation
import EvmCompiler.Structured.InteractionSemantics

namespace EvmCompiler
namespace Structured
namespace InteractionPrimitivePreservation

namespace BasicOp

def FrameResultRel (hidden : EvmYul.Stack Word)
    (source target : EVMState) : Prop :=
  target.toSharedState = source.toSharedState ∧
    target.stack = source.stack ++ hidden

abbrev FrameOutcomeRel (hidden : EvmYul.Stack Word) :=
  Simulation.Interaction.ExceptRel
    (fun _sourceError _targetError : EVMException => True)
    (FrameResultRel hidden)

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

/--
One Structured primitive can start from an arbitrary real runtime-control
position while preserving the source-visible stack prefix and shared state.

Higher stack-free layers use this theorem instead of manufacturing a target
state with the isolated source evaluator's program counter.
-/
theorem openStepEVM_frame_rel
    {op : Structured.BasicOp} {input output : Nat}
    {source target : EVMState} (hidden : EvmYul.Stack Word)
    (hArity :
      op.toPrimOp.stackArity? = some (input, output))
    (hBound : input ≤ source.stack.length)
    (hShared :
      target.toSharedState = source.toSharedState)
    (hStack :
      target.stack = source.stack ++ hidden) :
    Simulation.Interaction.Rel (FrameOutcomeRel hidden)
      (InteractionSemantics.BasicInstr.openStepEVM (.op op) source)
      (InteractionSemantics.BasicInstr.openStepEVM (.op op) target) := by
  let extended : EVMState :=
    { source with stack := source.stack ++ hidden }
  have hSuffix :=
    openStepEVM_append_stack_rel
      source hidden hArity hBound
  have hRuntimeData :
      Assembly.SameRuntimeData target extended := by
    cases source
    cases target
    simp [extended, Assembly.SameRuntimeData,
      Assembly.eraseRuntimeControl] at hShared hStack ⊢
    exact ⟨hShared, hStack⟩
  have hNoPc : op.toPrimOp ≠ .pc := by
    cases op <;> simp [Structured.BasicOp.toPrimOp]
  have hRuntime :=
    Assembly.InteractionPreservation.PrimOp.openStep_runtimeRel
      (op := op.toPrimOp)
      ⟨(input, output), hArity⟩ hNoPc hRuntimeData
  have hTrans :=
    Simulation.Interaction.Rel.trans hSuffix hRuntime.symm
  apply Simulation.Interaction.Rel.mono hTrans
  intro sourceDone targetDone hDone
  cases sourceDone with
  | error sourceError =>
      cases targetDone with
      | error targetError =>
          exact Simulation.Interaction.ExceptRel.error True.intro
      | ok targetFinal =>
          rcases hDone with
            ⟨middleDone, hSuffixDone, hRuntimeDone⟩
          cases hSuffixDone with
          | error _ =>
              cases hRuntimeDone
  | ok sourceFinal =>
      cases targetDone with
      | error targetError =>
          rcases hDone with
            ⟨middleDone, hSuffixDone, hRuntimeDone⟩
          cases hSuffixDone with
          | ok _ =>
              cases hRuntimeDone
      | ok targetFinal =>
          rcases hDone with
            ⟨middleDone, hSuffixDone, hRuntimeDone⟩
          cases hSuffixDone with
          | ok hSuffixState =>
              cases hRuntimeDone with
              | ok hRuntimeState =>
                  apply Simulation.Interaction.ExceptRel.ok
                  change
                    Assembly.SameRuntimeData _
                      { sourceFinal with
                        stack := sourceFinal.stack ++ hidden }
                    at hSuffixState
                  have hFinal :=
                    Assembly.SameRuntimeData.trans
                      hRuntimeState hSuffixState
                  constructor
                  · simpa using
                      Assembly.SameRuntimeData.shared_eq hFinal
                  · simpa using
                      Assembly.SameRuntimeData.stack_eq hFinal

def OutputLength (output : Nat) :
    Except EVMException EVMState → Prop
  | .error _ => True
  | .ok final => final.stack.length = output

/--
With an exact source-visible operand stack, every successful branch of a
Structured primitive produces its declared number of results.
-/
theorem openStepEVM_outputLength
    {op : Structured.BasicOp} {input output : Nat}
    {state : EVMState}
    (hArity :
      op.toPrimOp.stackArity? = some (input, output))
    (hLength : state.stack.length = input) :
    Simulation.Interaction.AllDone (OutputLength output)
      (InteractionSemantics.BasicInstr.openStepEVM (.op op) state) := by
  have hRaw :=
    Assembly.InteractionPreservation.PrimOp.openStep_realizesStackArity
      (state := state) hArity
  apply Simulation.Interaction.AllDone.mono hRaw
  intro outcome hOutcome
  cases outcome with
  | error error =>
      exact True.intro
  | ok final =>
      change final.stack.length = output
      change
        final.stack.length =
          state.stack.length - input + output
        at hOutcome
      omega

end BasicOp

end InteractionPrimitivePreservation
end Structured
end EvmCompiler
