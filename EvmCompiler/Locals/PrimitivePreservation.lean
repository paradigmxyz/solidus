import EvmCompiler.Locals.SourceSemantics

namespace EvmCompiler
namespace Locals
namespace Source
namespace PrimitiveSemantics

abbrev Word := Assembly.Word
abbrev EVMState := Assembly.EVMState

/--
Every primitive admitted by the canonical stack-free Locals semantics is safe
to run above an arbitrary caller-owned stack suffix.
-/
theorem sourceContinuingStep_suffixSafe
    {op : Structured.BasicOp} {step : Assembly.PrimStep}
    (hStep :
      sourceContinuingStep? op = some step) :
    Assembly.PrimStep.SuffixSafe step := by
  cases op <;>
    simp [sourceContinuingStep?,
      Structured.BasicOp.toPrimOp, Assembly.PrimOp.continuingStep?] at hStep
  all_goals
    cases hStep
    simp [Assembly.PrimStep.SuffixSafe]

theorem sourceContinuingStep_inputArity
    {op : Structured.BasicOp} {step : Assembly.PrimStep}
    (hStep :
      sourceContinuingStep? op = some step) :
    Assembly.PrimStep.inputArity step =
      Expressions.Structured.BasicOp.inputs op := by
  cases op <;>
    simp [sourceContinuingStep?,
      Structured.BasicOp.toPrimOp, Assembly.PrimOp.continuingStep?,
      Assembly.PrimStep.inputArity,
      Expressions.Structured.BasicOp.inputs] at hStep ⊢
  all_goals
    cases hStep
    rfl

theorem sourceContinuingStep_outputArity
    {op : Structured.BasicOp} {step : Assembly.PrimStep}
    (hStep :
      sourceContinuingStep? op = some step) :
    Assembly.PrimStep.outputArity step =
      Expressions.Structured.BasicOp.outputs op := by
  cases op <;>
    simp [sourceContinuingStep?,
      Structured.BasicOp.toPrimOp, Assembly.PrimOp.continuingStep?,
      Assembly.PrimStep.outputArity,
      Expressions.Structured.BasicOp.outputs] at hStep ⊢
  all_goals
    cases hStep
    rfl

theorem sourceContinuingStep_run_suffixExists
    {op : Structured.BasicOp} {step : Assembly.PrimStep}
    {shared : EvmYul.SharedState .EVM}
    {stack baseStack : EvmYul.Stack Word}
    {isolatedFinal evm : EVMState}
    (hStep :
      sourceContinuingStep? op = some step)
    (hIsolated :
      step.run (Assembly.PrimStep.isoState shared stack) =
        .ok isolatedFinal)
    (hShared : evm.toSharedState = shared)
    (hStack : evm.stack = stack ++ baseStack) :
    ∃ evmFinal,
      step.run evm = .ok evmFinal ∧
        evmFinal.toSharedState = isolatedFinal.toSharedState ∧
          evmFinal.stack = isolatedFinal.stack ++ baseStack :=
  Assembly.PrimStep.run_suffix_exists_safe
    (sourceContinuingStep_suffixSafe hStep)
    hIsolated hShared hStack

theorem sourceContinuingStep_basicOpStep
    {op : Structured.BasicOp} {step : Assembly.PrimStep}
    (hStep :
      sourceContinuingStep? op = some step)
    (state : EVMState) :
    Structured.BasicOp.step op state = step.run state := by
  cases op <;>
    simp [sourceContinuingStep?,
      Structured.BasicOp.step, Structured.BasicOp.toPrimOp,
      Assembly.Target.stepInstr, Assembly.PrimOp.step,
      Assembly.PrimOp.continuingStep?] at hStep ⊢
  all_goals
    cases hStep
    rfl

/--
Successful canonical primitive evaluation can be replayed over an arbitrary
caller stack suffix without changing its projected shared result.
-/
theorem structured_eval_step_exists
    {op : Structured.BasicOp}
    {shared sharedFinal : EvmYul.SharedState .EVM}
    {values outputs : List Word} {evm : EVMState}
    {baseStack : EvmYul.Stack Word}
    (hEval :
      structured.eval op shared values =
        .ok (sharedFinal, outputs))
    (hShared : evm.toSharedState = shared)
    (hStack : evm.stack = values.reverse ++ baseStack) :
    ∃ evmFinal,
      Structured.BasicOp.step op evm = .ok evmFinal ∧
        evmFinal.toSharedState = sharedFinal ∧
          evmFinal.stack = outputs.reverse ++ baseStack := by
  dsimp [structured] at hEval
  by_cases hLength :
      values.length = Expressions.Structured.BasicOp.inputs op
  · cases hContinuing : sourceContinuingStep? op with
    | none =>
        simp [hLength, hContinuing] at hEval
    | some step =>
        simp [hLength, hContinuing] at hEval
        cases hIsolated :
            step.run
              (Assembly.PrimStep.isoState shared values.reverse) with
        | error err =>
            simp [hIsolated] at hEval
        | ok isolatedFinal =>
            simp [hIsolated] at hEval
            rcases
                sourceContinuingStep_run_suffixExists
                  (op := op) (step := step) (shared := shared)
                  (stack := values.reverse) (baseStack := baseStack)
                  (isolatedFinal := isolatedFinal) (evm := evm)
                  hContinuing hIsolated hShared hStack with
              ⟨evmFinal, hRun, hSharedFinal, hStackFinal⟩
            rcases hEval with ⟨rfl, rfl⟩
            refine ⟨evmFinal, ?_, hSharedFinal, ?_⟩
            · simpa [sourceContinuingStep_basicOpStep hContinuing evm]
                using hRun
            · simpa using hStackFinal
  · simp [hLength] at hEval

theorem structured_eval_length
    {op : Structured.BasicOp}
    {shared sharedFinal : EvmYul.SharedState .EVM}
    {values outputs : List Word}
    (hEval :
      structured.eval op shared values =
        .ok (sharedFinal, outputs)) :
    outputs.length = Expressions.Structured.BasicOp.outputs op := by
  dsimp [structured] at hEval
  by_cases hLength :
      values.length = Expressions.Structured.BasicOp.inputs op
  · cases hContinuing : sourceContinuingStep? op with
    | none =>
        simp [hLength, hContinuing] at hEval
    | some step =>
        simp [hLength, hContinuing] at hEval
        cases hIsolated :
            step.run
              (Assembly.PrimStep.isoState shared values.reverse) with
        | error err =>
            simp [hIsolated] at hEval
        | ok isolatedFinal =>
            simp [hIsolated] at hEval
            rcases hEval with ⟨rfl, rfl⟩
            have hStackLength :
                isolatedFinal.stack.length =
                  Assembly.PrimStep.outputArity step :=
              Assembly.PrimStep.run_isolated_length_safe
                (step := step) (shared := shared)
                (stack := values.reverse)
                (evm' := isolatedFinal)
                (sourceContinuingStep_suffixSafe hContinuing)
                (by
                  simpa [sourceContinuingStep_inputArity hContinuing,
                    List.length_reverse] using hLength)
                hIsolated
            simpa [sourceContinuingStep_outputArity hContinuing,
              List.length_reverse] using hStackLength
  · simp [hLength] at hEval

end PrimitiveSemantics
end Source
end Locals
end EvmCompiler
