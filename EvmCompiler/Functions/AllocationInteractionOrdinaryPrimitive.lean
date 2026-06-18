import EvmCompiler.Functions.AllocationInteractionPrimitive
import EvmCompiler.Locals.PrimitivePreservation

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionOrdinaryPrimitive

open AllocationInteractionRelation

abbrev Word := Assembly.Word

/-- Allocation-relevant effect of one closed ordinary primitive. -/
structure TargetEffect (contract : MemoryContract.Contract)
    (sourceFinal targetInitial targetFinal : EvmYul.SharedState .EVM) : Prop where
  shared : SharedRel contract sourceFinal targetFinal
  scratchStable :
    ∀ reservation,
      contract.scratch? = some reservation →
      ∀ address,
        reservation.containsRegion address 1 →
        address + MemoryContract.wordBytes ≤
          targetInitial.toMachineState.memory.size →
        address + MemoryContract.wordBytes ≤
          targetInitial.toMachineState.activeWords.toNat *
            MemoryContract.wordBytes →
        targetFinal.toMachineState.lookupMemory (EvmYul.UInt256.ofNat address) =
          targetInitial.toMachineState.lookupMemory
            (EvmYul.UInt256.ofNat address)
  memoryMono :
    targetInitial.toMachineState.memory.size ≤
      targetFinal.toMachineState.memory.size
  activeMono :
    targetInitial.toMachineState.activeWords.toNat ≤
      targetFinal.toMachineState.activeWords.toNat
  activeNoWrap :
    targetFinal.toMachineState.activeWords.toNat * MemoryContract.wordBytes <
      EvmYul.UInt256.size

/-- Stable capability contract for any non-resource, non-external primitive. -/
structure ClosedSpec (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) : Prop where
  sourceStep :
    ∃ step,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep? op = some step
  supportsOpen : Locals.InteractionSemantics.Primitive.supportsOpen op = true
  notGas : op.toPrimOp ≠ .gas
  notMsize : op.toPrimOp ≠ .msize
  evalExists :
    ∀ {shared : EvmYul.SharedState .EVM} {values : List Word},
      values.length = Expressions.Structured.BasicOp.inputs op →
      ∃ sharedFinal outputs,
        Locals.Source.PrimitiveSemantics.structured.eval op shared values =
          .ok (sharedFinal, outputs)
  simulate :
    ∀ {sourceShared sourceFinal targetShared : EvmYul.SharedState .EVM}
      {values outputs : List Word},
      values.length = Expressions.Structured.BasicOp.inputs op →
      SharedRel contract sourceShared targetShared →
      Simulation.MemorySafety.OpenPrimitiveMemorySafe
        contract op sourceShared.toMachineState values →
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size →
      Locals.Source.PrimitiveSemantics.structured.eval
          op sourceShared values = .ok (sourceFinal, outputs) →
      ∃ targetFinal,
        Locals.Source.PrimitiveSemantics.structured.eval
            op targetShared values = .ok (targetFinal, outputs) ∧
        TargetEffect contract sourceFinal targetShared targetFinal

/-- Closed primitive capability that preserves both success and error outcomes. -/
structure FallibleClosedSpec (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) : Prop where
  sourceStep :
    ∃ step,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep? op = some step
  supportsOpen : Locals.InteractionSemantics.Primitive.supportsOpen op = true
  notGas : op.toPrimOp ≠ .gas
  notMsize : op.toPrimOp ≠ .msize
  simulateSuccess :
    ∀ {sourceShared sourceFinal targetShared : EvmYul.SharedState .EVM}
      {values outputs : List Word},
      values.length = Expressions.Structured.BasicOp.inputs op →
      SharedRel contract sourceShared targetShared →
      Simulation.MemorySafety.OpenPrimitiveMemorySafe
        contract op sourceShared.toMachineState values →
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size →
      Locals.Source.PrimitiveSemantics.structured.eval
          op sourceShared values = .ok (sourceFinal, outputs) →
      ∃ targetFinal,
        Locals.Source.PrimitiveSemantics.structured.eval
            op targetShared values = .ok (targetFinal, outputs) ∧
        TargetEffect contract sourceFinal targetShared targetFinal
  errorSuffix :
    ∀ {step : Assembly.PrimStep}
      {sourceShared : EvmYul.SharedState .EVM}
      {target : Assembly.EVMState} {values baseStack : List Word}
      {error : EVMException},
      values.length = Expressions.Structured.BasicOp.inputs op →
      Locals.Source.PrimitiveSemantics.sourceContinuingStep? op = some step →
      SharedRel contract sourceShared target.toSharedState →
      target.stack = values.reverse ++ baseStack →
      Locals.Source.PrimitiveSemantics.structured.eval
          op sourceShared values = .error error →
      step.run target = .error error

/--
Canonical primitive families that neither inspect nor modify EVM memory.
This classifies the existing ordinary source step; it is not another primitive
interpreter.
-/
inductive SharedFamily : Structured.BasicOp → Prop where
  | bin {op : Structured.BasicOp} (f : EvmYul.Primop.Binary)
      (step :
        Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
          some (.bin f)) :
      SharedFamily op
  | un {op : Structured.BasicOp} (f : EvmYul.Primop.Unary)
      (step :
        Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
          some (.un f)) :
      SharedFamily op
  | tri {op : Structured.BasicOp} (f : EvmYul.Primop.Ternary)
      (step :
        Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
          some (.tri f)) :
      SharedFamily op
  | pop {op : Structured.BasicOp}
      (step :
        Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
          some .pop) :
      SharedFamily op
  | executionEnv {op : Structured.BasicOp}
      (f : EvmYul.ExecutionEnv .EVM → Word)
      (step :
        Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
          some (.executionEnv f)) :
      SharedFamily op
  | unaryExecutionEnv {op : Structured.BasicOp}
      (f : EvmYul.ExecutionEnv .EVM → Word → Word)
      (step :
        Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
          some (.unaryExecutionEnv f)) :
      SharedFamily op
  | state {op : Structured.BasicOp}
      (f : EvmYul.State .EVM → Word)
      (step :
        Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
          some (.state f)) :
      SharedFamily op
  | unaryState {op : Structured.BasicOp}
      (f : EvmYul.State .EVM → Word → EvmYul.State .EVM × Word)
      (step :
        Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
          some (.unaryState f)) :
      SharedFamily op
  | binaryState {op : Structured.BasicOp}
      (f : EvmYul.State .EVM → Word → Word → EvmYul.State .EVM)
      (step :
        Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
          some (.binaryState f)) :
      SharedFamily op
  | returnDataSize : SharedFamily .returndatasize

namespace SharedFamily

theorem sourceStep
    {op : Structured.BasicOp} (family : SharedFamily op) :
    ∃ step,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep? op = some step := by
  cases family with
  | bin f hStep => exact ⟨.bin f, hStep⟩
  | un f hStep => exact ⟨.un f, hStep⟩
  | tri f hStep => exact ⟨.tri f, hStep⟩
  | pop hStep => exact ⟨.pop, hStep⟩
  | executionEnv f hStep => exact ⟨.executionEnv f, hStep⟩
  | unaryExecutionEnv f hStep => exact ⟨.unaryExecutionEnv f, hStep⟩
  | state f hStep => exact ⟨.state f, hStep⟩
  | unaryState f hStep => exact ⟨.unaryState f, hStep⟩
  | binaryState f hStep => exact ⟨.binaryState f, hStep⟩
  | returnDataSize =>
      exact ⟨.machineState EvmYul.MachineState.returndatasize, rfl⟩

theorem supportsOpen
    {op : Structured.BasicOp} (family : SharedFamily op) :
    Locals.InteractionSemantics.Primitive.supportsOpen op = true := by
  cases family <;>
    first
    | rfl
    | (cases op <;>
        simp [Locals.InteractionSemantics.Primitive.supportsOpen,
          Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
          Structured.BasicOp.toPrimOp, Assembly.PrimOp.continuingStep?] at *)

private theorem primOp_ne_of_sourceStep
    {op : Structured.BasicOp} {step forbiddenStep : Assembly.PrimStep}
    {forbidden : Assembly.PrimOp}
    (hStep :
      Locals.Source.PrimitiveSemantics.sourceContinuingStep? op = some step)
    (hForbidden : forbidden.continuingStep? = some forbiddenStep)
    (hNe : step ≠ forbiddenStep) :
    op.toPrimOp ≠ forbidden := by
  intro hEq
  have hPrimitive :=
    Locals.Source.PrimitiveSemantics.sourceContinuingStep?_toPrimOp hStep
  rw [hEq, hForbidden] at hPrimitive
  exact hNe (Option.some.inj hPrimitive).symm

private theorem primOp_ne_of_sourceStep_none
    {op : Structured.BasicOp} {step : Assembly.PrimStep}
    {forbidden : Assembly.PrimOp}
    (hStep :
      Locals.Source.PrimitiveSemantics.sourceContinuingStep? op = some step)
    (hForbidden : forbidden.continuingStep? = none) :
    op.toPrimOp ≠ forbidden := by
  intro hEq
  have hPrimitive :=
    Locals.Source.PrimitiveSemantics.sourceContinuingStep?_toPrimOp hStep
  rw [hEq, hForbidden] at hPrimitive
  contradiction

theorem not_gas
    {op : Structured.BasicOp} (family : SharedFamily op) :
    op.toPrimOp ≠ .gas := by
  obtain ⟨step, hStep⟩ := family.sourceStep
  exact primOp_ne_of_sourceStep_none hStep (forbidden := .gas) rfl

theorem not_msize
    {op : Structured.BasicOp} (family : SharedFamily op) :
    op.toPrimOp ≠ .msize := by
  cases family with
  | bin f hStep =>
      exact primOp_ne_of_sourceStep hStep (forbidden := .msize) rfl (by simp)
  | un f hStep =>
      exact primOp_ne_of_sourceStep hStep (forbidden := .msize) rfl (by simp)
  | tri f hStep =>
      exact primOp_ne_of_sourceStep hStep (forbidden := .msize) rfl (by simp)
  | pop hStep =>
      exact primOp_ne_of_sourceStep hStep (forbidden := .msize) rfl (by simp)
  | executionEnv f hStep =>
      exact primOp_ne_of_sourceStep hStep (forbidden := .msize) rfl (by simp)
  | unaryExecutionEnv f hStep =>
      exact primOp_ne_of_sourceStep hStep (forbidden := .msize) rfl (by simp)
  | state f hStep =>
      exact primOp_ne_of_sourceStep hStep (forbidden := .msize) rfl (by simp)
  | unaryState f hStep =>
      exact primOp_ne_of_sourceStep hStep (forbidden := .msize) rfl (by simp)
  | binaryState f hStep =>
      exact primOp_ne_of_sourceStep hStep (forbidden := .msize) rfl (by simp)
  | returnDataSize => decide

theorem eval_exists
    {op : Structured.BasicOp} (family : SharedFamily op)
    {shared : EvmYul.SharedState .EVM} {values : List Word}
    (hLength : values.length = Expressions.Structured.BasicOp.inputs op) :
    ∃ sharedFinal outputs,
      Locals.Source.PrimitiveSemantics.structured.eval op shared values =
        .ok (sharedFinal, outputs) := by
  cases family with
  | bin f hStep =>
      have hBound : 2 ≤ values.reverse.length := by
        have hArity :=
          Locals.Source.PrimitiveSemantics.sourceContinuingStep_inputArity hStep
        rw [List.length_reverse, hLength, ← hArity]
        simp [Assembly.PrimStep.inputArity]
      obtain ⟨rest, left, right, hPop⟩ :=
        Assembly.PrimStep.Stack.exists_pop2_of_two_le hBound
      simp [Locals.Source.PrimitiveSemantics.structured, hLength, hStep,
        Assembly.PrimStep.run, EvmYul.EVM.execBinOp, hPop,
        EvmYul.Stack.push, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, Assembly.PrimStep.idRun_eq]
  | un f hStep =>
      have hBound : 1 ≤ values.reverse.length := by
        have hArity :=
          Locals.Source.PrimitiveSemantics.sourceContinuingStep_inputArity hStep
        rw [List.length_reverse, hLength, ← hArity]
        simp [Assembly.PrimStep.inputArity]
      obtain ⟨rest, value, hPop⟩ :=
        Assembly.PrimStep.Stack.exists_pop_of_one_le hBound
      simp [Locals.Source.PrimitiveSemantics.structured, hLength, hStep,
        Assembly.PrimStep.run, EvmYul.EVM.execUnOp, hPop,
        EvmYul.Stack.push, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, Assembly.PrimStep.idRun_eq]
  | tri f hStep =>
      have hBound : 3 ≤ values.reverse.length := by
        have hArity :=
          Locals.Source.PrimitiveSemantics.sourceContinuingStep_inputArity hStep
        rw [List.length_reverse, hLength, ← hArity]
        simp [Assembly.PrimStep.inputArity]
      obtain ⟨rest, left, middle, right, hPop⟩ :=
        Assembly.PrimStep.Stack.exists_pop3_of_three_le hBound
      simp [Locals.Source.PrimitiveSemantics.structured, hLength, hStep,
        Assembly.PrimStep.run, EvmYul.EVM.execTriOp, hPop,
        EvmYul.Stack.push, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, Assembly.PrimStep.idRun_eq]
  | pop hStep =>
      have hBound : 1 ≤ values.reverse.length := by
        have hArity :=
          Locals.Source.PrimitiveSemantics.sourceContinuingStep_inputArity hStep
        rw [List.length_reverse, hLength, ← hArity]
        simp [Assembly.PrimStep.inputArity]
      obtain ⟨rest, value, hPop⟩ :=
        Assembly.PrimStep.Stack.exists_pop_of_one_le hBound
      simp [Locals.Source.PrimitiveSemantics.structured, hLength, hStep,
        Assembly.PrimStep.run, hPop,
        EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]
  | executionEnv f hStep =>
      simp [Locals.Source.PrimitiveSemantics.structured, hLength, hStep,
        Assembly.PrimStep.run, EvmYul.EVM.executionEnvOp,
        EvmYul.Stack.push, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, Assembly.PrimStep.idRun_eq]
  | unaryExecutionEnv f hStep =>
      have hBound : 1 ≤ values.reverse.length := by
        have hArity :=
          Locals.Source.PrimitiveSemantics.sourceContinuingStep_inputArity hStep
        rw [List.length_reverse, hLength, ← hArity]
        simp [Assembly.PrimStep.inputArity]
      obtain ⟨rest, value, hPop⟩ :=
        Assembly.PrimStep.Stack.exists_pop_of_one_le hBound
      simp [Locals.Source.PrimitiveSemantics.structured, hLength, hStep,
        Assembly.PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp, hPop,
        EvmYul.Stack.push, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, Assembly.PrimStep.idRun_eq]
  | state f hStep =>
      simp [Locals.Source.PrimitiveSemantics.structured, hLength, hStep,
        Assembly.PrimStep.run, EvmYul.EVM.stateOp,
        EvmYul.Stack.push, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, Assembly.PrimStep.idRun_eq]
  | unaryState f hStep =>
      have hBound : 1 ≤ values.reverse.length := by
        have hArity :=
          Locals.Source.PrimitiveSemantics.sourceContinuingStep_inputArity hStep
        rw [List.length_reverse, hLength, ← hArity]
        simp [Assembly.PrimStep.inputArity]
      obtain ⟨rest, value, hPop⟩ :=
        Assembly.PrimStep.Stack.exists_pop_of_one_le hBound
      simp [Locals.Source.PrimitiveSemantics.structured, hLength, hStep,
        Assembly.PrimStep.run, EvmYul.EVM.unaryStateOp, hPop,
        EvmYul.Stack.push, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, Assembly.PrimStep.idRun_eq]
  | binaryState f hStep =>
      have hBound : 2 ≤ values.reverse.length := by
        have hArity :=
          Locals.Source.PrimitiveSemantics.sourceContinuingStep_inputArity hStep
        rw [List.length_reverse, hLength, ← hArity]
        simp [Assembly.PrimStep.inputArity]
      obtain ⟨rest, left, right, hPop⟩ :=
        Assembly.PrimStep.Stack.exists_pop2_of_two_le hBound
      simp [Locals.Source.PrimitiveSemantics.structured, hLength, hStep,
        Assembly.PrimStep.run, EvmYul.EVM.binaryStateOp, hPop,
        EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC,
        Assembly.PrimStep.idRun_eq]
  | returnDataSize =>
      simp [Locals.Source.PrimitiveSemantics.structured,
        Locals.Source.PrimitiveSemantics.sourceContinuingStep?, hLength,
        Structured.BasicOp.toPrimOp, Assembly.PrimOp.continuingStep?,
        Assembly.PrimStep.run, EvmYul.EVM.machineStateOp,
        EvmYul.Stack.push, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, Assembly.PrimStep.idRun_eq]

theorem simulate
    {contract : MemoryContract.Contract} {op : Structured.BasicOp}
    {sourceShared sourceFinal targetShared : EvmYul.SharedState .EVM}
    {values outputs : List Word}
    (family : SharedFamily op)
    (hRel : SharedRel contract sourceShared targetShared)
    (hEval :
      Locals.Source.PrimitiveSemantics.structured.eval
          op sourceShared values =
        .ok (sourceFinal, outputs)) :
    ∃ targetFinal,
      Locals.Source.PrimitiveSemantics.structured.eval
          op targetShared values =
        .ok (targetFinal, outputs) ∧
      SharedRel contract sourceFinal targetFinal ∧
      targetFinal.toMachineState = targetShared.toMachineState := by
  cases family with
  | bin f hStep =>
      dsimp [Locals.Source.PrimitiveSemantics.structured] at hEval ⊢
      by_cases hLength :
          values.length = Expressions.Structured.BasicOp.inputs op
      · simp [hLength, hStep, Assembly.PrimStep.run,
          EvmYul.EVM.execBinOp] at hEval ⊢
        cases hPop : EvmYul.Stack.pop2 values.reverse with
        | none => simp [hPop] at hEval
        | some popped =>
            rcases popped with ⟨rest, left, right⟩
            simp [hPop, EvmYul.Stack.push,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC] at hEval ⊢
            rcases hEval with ⟨rfl, rfl⟩
            exact ⟨targetShared, rfl, hRel, rfl⟩
      · simp [hLength] at hEval
  | un f hStep =>
      dsimp [Locals.Source.PrimitiveSemantics.structured] at hEval ⊢
      by_cases hLength :
          values.length = Expressions.Structured.BasicOp.inputs op
      · simp [hLength, hStep, Assembly.PrimStep.run,
          EvmYul.EVM.execUnOp] at hEval ⊢
        cases hPop : EvmYul.Stack.pop values.reverse with
        | none => simp [hPop] at hEval
        | some popped =>
            rcases popped with ⟨rest, value⟩
            simp [hPop, EvmYul.Stack.push,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC] at hEval ⊢
            rcases hEval with ⟨rfl, rfl⟩
            exact ⟨targetShared, rfl, hRel, rfl⟩
      · simp [hLength] at hEval
  | tri f hStep =>
      dsimp [Locals.Source.PrimitiveSemantics.structured] at hEval ⊢
      by_cases hLength :
          values.length = Expressions.Structured.BasicOp.inputs op
      · simp [hLength, hStep, Assembly.PrimStep.run,
          EvmYul.EVM.execTriOp] at hEval ⊢
        cases hPop : EvmYul.Stack.pop3 values.reverse with
        | none => simp [hPop] at hEval
        | some popped =>
            rcases popped with ⟨rest, left, middle, right⟩
            simp [hPop, EvmYul.Stack.push,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC] at hEval ⊢
            rcases hEval with ⟨rfl, rfl⟩
            exact ⟨targetShared, rfl, hRel, rfl⟩
      · simp [hLength] at hEval
  | pop hStep =>
      dsimp [Locals.Source.PrimitiveSemantics.structured] at hEval ⊢
      by_cases hLength :
          values.length = Expressions.Structured.BasicOp.inputs op
      · simp [hLength, hStep, Assembly.PrimStep.run] at hEval ⊢
        cases hPop : EvmYul.Stack.pop values.reverse with
        | none => simp [hPop] at hEval
        | some popped =>
            rcases popped with ⟨rest, value⟩
            simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC] at hEval ⊢
            rcases hEval with ⟨rfl, rfl⟩
            exact And.intro rfl hRel
      · simp [hLength] at hEval
  | executionEnv f hStep =>
      dsimp [Locals.Source.PrimitiveSemantics.structured] at hEval ⊢
      by_cases hLength :
          values.length = Expressions.Structured.BasicOp.inputs op
      · simp [hLength, hStep, Assembly.PrimStep.run,
          EvmYul.EVM.executionEnvOp, EvmYul.Stack.push,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, hRel.executionEnv_eq] at hEval ⊢
        rcases hEval with ⟨rfl, rfl⟩
        exact ⟨targetShared, rfl, hRel, rfl⟩
      · simp [hLength] at hEval
  | unaryExecutionEnv f hStep =>
      dsimp [Locals.Source.PrimitiveSemantics.structured] at hEval ⊢
      by_cases hLength :
          values.length = Expressions.Structured.BasicOp.inputs op
      · simp [hLength, hStep, Assembly.PrimStep.run,
          EvmYul.EVM.unaryExecutionEnvOp] at hEval ⊢
        cases hPop : EvmYul.Stack.pop values.reverse with
        | none => simp [hPop] at hEval
        | some popped =>
            rcases popped with ⟨rest, value⟩
            simp [hPop, EvmYul.Stack.push,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC,
              hRel.executionEnv_eq] at hEval ⊢
            rcases hEval with ⟨rfl, rfl⟩
            exact ⟨targetShared, rfl, hRel, rfl⟩
      · simp [hLength] at hEval
  | state f hStep =>
      have hWorld : targetShared.toState = sourceShared.toState :=
        hRel.world.symm
      dsimp [Locals.Source.PrimitiveSemantics.structured] at hEval ⊢
      by_cases hLength :
          values.length = Expressions.Structured.BasicOp.inputs op
      · simp [hLength, hStep, Assembly.PrimStep.run,
          EvmYul.EVM.stateOp, EvmYul.Stack.push,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, hWorld] at hEval ⊢
        rcases hEval with ⟨rfl, rfl⟩
        exact ⟨targetShared, rfl, hRel, rfl⟩
      · simp [hLength] at hEval
  | unaryState f hStep =>
      have hWorld : targetShared.toState = sourceShared.toState :=
        hRel.world.symm
      dsimp [Locals.Source.PrimitiveSemantics.structured] at hEval ⊢
      by_cases hLength :
          values.length = Expressions.Structured.BasicOp.inputs op
      · simp [hLength, hStep, Assembly.PrimStep.run,
          EvmYul.EVM.unaryStateOp] at hEval ⊢
        cases hPop : EvmYul.Stack.pop values.reverse with
        | none => simp [hPop] at hEval
        | some popped =>
            rcases popped with ⟨rest, value⟩
            simp [hPop, EvmYul.Stack.push,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC, hWorld] at hEval ⊢
            rcases hEval with ⟨rfl, rfl⟩
            exact
              ⟨_, rfl,
                hRel.replaceToState_same
                  (f sourceShared.toState value).1,
                rfl⟩
      · simp [hLength] at hEval
  | binaryState f hStep =>
      have hWorld : targetShared.toState = sourceShared.toState :=
        hRel.world.symm
      dsimp [Locals.Source.PrimitiveSemantics.structured] at hEval ⊢
      by_cases hLength :
          values.length = Expressions.Structured.BasicOp.inputs op
      · simp [hLength, hStep, Assembly.PrimStep.run,
          EvmYul.EVM.binaryStateOp] at hEval ⊢
        cases hPop : EvmYul.Stack.pop2 values.reverse with
        | none => simp [hPop] at hEval
        | some popped =>
            rcases popped with ⟨rest, left, right⟩
            simp [hPop, EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC, hWorld] at hEval ⊢
            rcases hEval with ⟨rfl, rfl⟩
            exact
              ⟨_, rfl,
                hRel.replaceToState_same
                  (f sourceShared.toState left right),
                rfl⟩
      · simp [hLength] at hEval
  | returnDataSize =>
      have hValue :
          targetShared.toMachineState.returndatasize =
            sourceShared.toMachineState.returndatasize := by
        simp [EvmYul.MachineState.returndatasize, hRel.machine.returnData]
      dsimp [Locals.Source.PrimitiveSemantics.structured] at hEval ⊢
      by_cases hLength :
          values.length =
            Expressions.Structured.BasicOp.inputs .returndatasize
      · simp [hLength,
          Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
          Structured.BasicOp.toPrimOp, Assembly.PrimOp.continuingStep?,
          Assembly.PrimStep.run, EvmYul.EVM.machineStateOp,
          EvmYul.Stack.push, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, hValue] at hEval ⊢
        rcases hEval with ⟨rfl, rfl⟩
        exact ⟨targetShared, rfl, hRel, rfl⟩
      · simp [hLength] at hEval

end SharedFamily

namespace ClosedSpec

/-- Every checked closed primitive spec implements the canonical open capability. -/
theorem openForward
    {contract : MemoryContract.Contract} {op : Structured.BasicOp}
    (spec : ClosedSpec contract op) :
    AllocationInteractionPrimitive.OpenForward contract op where
  preserve := by
    intro plan live stackOffset frameBase mode source initialTarget target
      values hLength hRel hStack hSafe
    obtain ⟨step, hSourceStep⟩ := spec.sourceStep
    obtain ⟨sourceSharedFinal, outputs, hSourceEval⟩ :=
      spec.evalExists hLength
    have hPrimitiveStep :=
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?_toPrimOp
        hSourceStep
    have hExternal :=
      Assembly.InteractionSemantics.PrimOp.externalKind_none_of_continuingStep
        hPrimitiveStep
    have hOpenSafe :
        Simulation.MemorySafety.OpenPrimitiveMemorySafe
          contract op source.shared.toMachineState values := by
      simpa [AllocationInteractionPrimitive.PrimitiveSafe, hExternal] using hSafe
    obtain ⟨targetSharedFinal, hTargetEval, hEffect⟩ :=
      spec.simulate hLength hRel.shared hOpenSafe hRel.activeNoWrap hSourceEval
    obtain ⟨sourceEVMFinal, hSourceBasicStep, hSourceShared, hSourceStack⟩ :=
      Locals.Source.PrimitiveSemantics.structured_eval_step_exists
        (evm := Locals.InteractionSemantics.Primitive.isolated source values)
        (baseStack := []) hSourceEval rfl (by
          simp [Locals.InteractionSemantics.Primitive.isolated])
    obtain ⟨targetEVMFinal, hTargetBasicStep, hTargetShared, hTargetStack⟩ :=
      Locals.Source.PrimitiveSemantics.structured_eval_step_exists
        hTargetEval rfl hStack
    have hSourceStepRun :
        step.run (Locals.InteractionSemantics.Primitive.isolated source values) =
          .ok sourceEVMFinal := by
      rw [← Locals.Source.PrimitiveSemantics.sourceContinuingStep_basicOpStep
        hSourceStep]
      exact hSourceBasicStep
    have hTargetStepRun : step.run target.evm = .ok targetEVMFinal := by
      rw [← Locals.Source.PrimitiveSemantics.sourceContinuingStep_basicOpStep
        hSourceStep]
      exact hTargetBasicStep
    let sourceFinal := source.withShared sourceSharedFinal
    let targetFinal := target.withEVM targetEVMFinal
    have hSourceOpen :
        Locals.InteractionSemantics.Primitive.openEval op source values =
          .done (.ok (sourceFinal, outputs)) := by
      rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
        hLength spec.supportsOpen hSourceStep spec.notGas spec.notMsize]
      rw [hSourceStepRun]
      simp [Simulation.Interaction.map,
        Simulation.Interaction.pure,
        Locals.InteractionSemantics.Primitive.finish,
        sourceFinal, hSourceShared, hSourceStack]
    have hTargetOpen :
        Structured.InteractionSemantics.BasicInstr.openStep (.op op) target =
          .done (.ok targetFinal) := by
      unfold Structured.InteractionSemantics.BasicInstr.openStep
        Structured.InteractionSemantics.BasicInstr.openStepEVM
      change
        Simulation.Interaction.map target.withEVM
            (Assembly.InteractionSemantics.PrimOp.openStep
              op.toPrimOp target.evm) =
          .done (.ok targetFinal)
      rw [Assembly.InteractionSemantics.PrimOp.openStep_of_continuingStep
        hPrimitiveStep
        spec.notGas spec.notMsize]
      rw [hTargetStepRun]
      simp [Simulation.Interaction.map, Simulation.Interaction.pure,
        targetFinal]
    have hSharedEVM :
        SharedRel contract sourceSharedFinal targetEVMFinal.toSharedState := by
      rw [hTargetShared]
      exact hEffect.shared
    have hOldRel :
        ActivationStateRel contract plan live
          (stackOffset + values.reverse.length) frameBase mode source target := by
      simpa [List.length_reverse, hLength] using hRel
    have hScratchStable :
        ∀ name slot,
          name ∈ live →
          plan.location? name = some (.scratch slot) →
          targetFinal.evm.toMachineState.lookupMemory
              (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) =
            target.evm.toMachineState.lookupMemory
              (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) := by
      intro name slot hLive hLocation
      cases hOldRel with
      | stack liveStackOnly _activeNoWrap _state =>
          exact False.elim (liveStackOnly name slot hLive hLocation)
      | scratch state =>
          obtain ⟨reservation, hReservation, _hFrame⟩ := state.frameReserved
          change
            targetEVMFinal.toMachineState.lookupMemory
                (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) =
              target.evm.toMachineState.lookupMemory
                (EvmYul.UInt256.ofNat (scratchAddress frameBase slot))
          rw [hTargetShared]
          exact hEffect.scratchStable reservation hReservation
            (scratchAddress frameBase slot)
            (state.scratchAddress_reserved hLive hLocation hReservation)
            (state.scratchAddress_end_le_memory hLive hLocation)
            (state.scratchAddress_end_le_active hLive hLocation)
    have hMemoryMono :
        target.evm.toMachineState.memory.size ≤
          targetFinal.evm.toMachineState.memory.size := by
      change
        target.evm.toMachineState.memory.size ≤
          targetEVMFinal.toMachineState.memory.size
      rw [hTargetShared]
      exact hEffect.memoryMono
    have hActiveMono :
        target.evm.activeWords.toNat ≤ targetFinal.evm.activeWords.toNat := by
      change
        target.evm.activeWords.toNat ≤ targetEVMFinal.activeWords.toNat
      rw [hTargetShared]
      exact hEffect.activeMono
    have hFinalNoWrap :
        targetFinal.evm.activeWords.toNat * MemoryContract.wordBytes <
          EvmYul.UInt256.size := by
      change
        targetEVMFinal.activeWords.toNat * MemoryContract.wordBytes <
          EvmYul.UInt256.size
      rw [hTargetShared]
      exact hEffect.activeNoWrap
    have hRebased :=
      hOldRel.rebase_prefix
        (sourceFinal := sourceFinal) (targetFinal := targetFinal)
        (oldPrefix := values.reverse) (newPrefix := outputs.reverse)
        (baseStack := initialTarget.evm.stack)
        (by simpa [sourceFinal, targetFinal] using hSharedEVM)
        hStack (by simpa [targetFinal] using hTargetStack)
        hScratchStable
        (by rfl)
        hMemoryMono hActiveMono hFinalNoWrap
    have hOutputsLength :
        outputs.length = Expressions.Structured.BasicOp.outputs op :=
      Locals.Source.PrimitiveSemantics.structured_eval_length hSourceEval
    have hFinalState :
        ActivationStateRel contract plan live
          (stackOffset + Expressions.Structured.BasicOp.outputs op)
          frameBase mode sourceFinal targetFinal := by
      simpa [List.length_reverse, hOutputsLength] using hRebased
    rw [hSourceOpen, hTargetOpen]
    apply Simulation.Interaction.Rel.done
    apply Simulation.Interaction.ExceptRel.ok
    exact
      ⟨hFinalState, hOutputsLength,
        by simpa [targetFinal] using hTargetStack⟩

end ClosedSpec

namespace FallibleClosedSpec

/-- Every checked fallible closed spec implements the canonical open capability. -/
theorem openForward
    {contract : MemoryContract.Contract} {op : Structured.BasicOp}
    (spec : FallibleClosedSpec contract op) :
    AllocationInteractionPrimitive.OpenForward contract op where
  preserve := by
    intro plan live stackOffset frameBase mode source initialTarget target
      values hLength hRel hStack hSafe
    obtain ⟨step, hSourceStep⟩ := spec.sourceStep
    have hPrimitiveStep :=
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?_toPrimOp
        hSourceStep
    have hExternal :=
      Assembly.InteractionSemantics.PrimOp.externalKind_none_of_continuingStep
        hPrimitiveStep
    have hOpenSafe :
        Simulation.MemorySafety.OpenPrimitiveMemorySafe
          contract op source.shared.toMachineState values := by
      simpa [AllocationInteractionPrimitive.PrimitiveSafe, hExternal] using hSafe
    cases hSourceEval :
        Locals.Source.PrimitiveSemantics.structured.eval
          op source.shared values with
    | error error =>
        have hSourceStepRun :
            step.run (Locals.InteractionSemantics.Primitive.isolated source values) =
              .error error := by
          simpa [Locals.InteractionSemantics.Primitive.isolated,
            Assembly.PrimStep.isoState] using
            (Locals.Source.PrimitiveSemantics.structured_eval_error_run
              hLength hSourceStep hSourceEval)
        have hTargetStepRun : step.run target.evm = .error error :=
          spec.errorSuffix hLength hSourceStep hRel.shared hStack hSourceEval
        have hSourceOpen :
            Locals.InteractionSemantics.Primitive.openEval op source values =
              .done (.error error) := by
          rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
            hLength spec.supportsOpen hSourceStep spec.notGas spec.notMsize]
          rw [hSourceStepRun]
          simp [Simulation.Interaction.map]
        have hTargetOpen :
            Structured.InteractionSemantics.BasicInstr.openStep (.op op) target =
              .done (.error error) := by
          unfold Structured.InteractionSemantics.BasicInstr.openStep
            Structured.InteractionSemantics.BasicInstr.openStepEVM
          change
            Simulation.Interaction.map target.withEVM
                (Assembly.InteractionSemantics.PrimOp.openStep
                  op.toPrimOp target.evm) =
              .done (.error error)
          rw [Assembly.InteractionSemantics.PrimOp.openStep_of_continuingStep
            hPrimitiveStep spec.notGas spec.notMsize]
          rw [hTargetStepRun]
          simp [Simulation.Interaction.map]
        rw [hSourceOpen, hTargetOpen]
        exact Simulation.Interaction.Rel.done
          (Simulation.Interaction.ExceptRel.error rfl)
    | ok result =>
        rcases result with ⟨sourceSharedFinal, outputs⟩
        obtain ⟨targetSharedFinal, hTargetEval, hEffect⟩ :=
          spec.simulateSuccess hLength hRel.shared hOpenSafe hRel.activeNoWrap
            hSourceEval
        obtain ⟨sourceEVMFinal, hSourceBasicStep, hSourceShared, hSourceStack⟩ :=
          Locals.Source.PrimitiveSemantics.structured_eval_step_exists
            (evm := Locals.InteractionSemantics.Primitive.isolated source values)
            (baseStack := []) hSourceEval rfl (by
              simp [Locals.InteractionSemantics.Primitive.isolated])
        obtain ⟨targetEVMFinal, hTargetBasicStep, hTargetShared, hTargetStack⟩ :=
          Locals.Source.PrimitiveSemantics.structured_eval_step_exists
            hTargetEval rfl hStack
        have hSourceStepRun :
            step.run (Locals.InteractionSemantics.Primitive.isolated source values) =
              .ok sourceEVMFinal := by
          rw [← Locals.Source.PrimitiveSemantics.sourceContinuingStep_basicOpStep
            hSourceStep]
          exact hSourceBasicStep
        have hTargetStepRun : step.run target.evm = .ok targetEVMFinal := by
          rw [← Locals.Source.PrimitiveSemantics.sourceContinuingStep_basicOpStep
            hSourceStep]
          exact hTargetBasicStep
        let sourceFinal := source.withShared sourceSharedFinal
        let targetFinal := target.withEVM targetEVMFinal
        have hSourceOpen :
            Locals.InteractionSemantics.Primitive.openEval op source values =
              .done (.ok (sourceFinal, outputs)) := by
          rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
            hLength spec.supportsOpen hSourceStep spec.notGas spec.notMsize]
          rw [hSourceStepRun]
          simp [Simulation.Interaction.map,
            Simulation.Interaction.pure,
            Locals.InteractionSemantics.Primitive.finish,
            sourceFinal, hSourceShared, hSourceStack]
        have hTargetOpen :
            Structured.InteractionSemantics.BasicInstr.openStep (.op op) target =
              .done (.ok targetFinal) := by
          unfold Structured.InteractionSemantics.BasicInstr.openStep
            Structured.InteractionSemantics.BasicInstr.openStepEVM
          change
            Simulation.Interaction.map target.withEVM
                (Assembly.InteractionSemantics.PrimOp.openStep
                  op.toPrimOp target.evm) =
              .done (.ok targetFinal)
          rw [Assembly.InteractionSemantics.PrimOp.openStep_of_continuingStep
            hPrimitiveStep spec.notGas spec.notMsize]
          rw [hTargetStepRun]
          simp [Simulation.Interaction.map, Simulation.Interaction.pure,
            targetFinal]
        have hSharedEVM :
            SharedRel contract sourceSharedFinal targetEVMFinal.toSharedState := by
          rw [hTargetShared]
          exact hEffect.shared
        have hOldRel :
            ActivationStateRel contract plan live
              (stackOffset + values.reverse.length) frameBase mode source target := by
          simpa [List.length_reverse, hLength] using hRel
        have hScratchStable :
            ∀ name slot,
              name ∈ live →
              plan.location? name = some (.scratch slot) →
              targetFinal.evm.toMachineState.lookupMemory
                  (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) =
                target.evm.toMachineState.lookupMemory
                  (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) := by
          intro name slot hLive hLocation
          cases hOldRel with
          | stack liveStackOnly _activeNoWrap _state =>
              exact False.elim (liveStackOnly name slot hLive hLocation)
          | scratch state =>
              obtain ⟨reservation, hReservation, _hFrame⟩ := state.frameReserved
              change
                targetEVMFinal.toMachineState.lookupMemory
                    (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) =
                  target.evm.toMachineState.lookupMemory
                    (EvmYul.UInt256.ofNat (scratchAddress frameBase slot))
              rw [hTargetShared]
              exact hEffect.scratchStable reservation hReservation
                (scratchAddress frameBase slot)
                (state.scratchAddress_reserved hLive hLocation hReservation)
                (state.scratchAddress_end_le_memory hLive hLocation)
                (state.scratchAddress_end_le_active hLive hLocation)
        have hMemoryMono :
            target.evm.toMachineState.memory.size ≤
              targetFinal.evm.toMachineState.memory.size := by
          change
            target.evm.toMachineState.memory.size ≤
              targetEVMFinal.toMachineState.memory.size
          rw [hTargetShared]
          exact hEffect.memoryMono
        have hActiveMono :
            target.evm.activeWords.toNat ≤ targetFinal.evm.activeWords.toNat := by
          change target.evm.activeWords.toNat ≤ targetEVMFinal.activeWords.toNat
          rw [hTargetShared]
          exact hEffect.activeMono
        have hFinalNoWrap :
            targetFinal.evm.activeWords.toNat * MemoryContract.wordBytes <
              EvmYul.UInt256.size := by
          change
            targetEVMFinal.activeWords.toNat * MemoryContract.wordBytes <
              EvmYul.UInt256.size
          rw [hTargetShared]
          exact hEffect.activeNoWrap
        have hRebased :=
          hOldRel.rebase_prefix
            (sourceFinal := sourceFinal) (targetFinal := targetFinal)
            (oldPrefix := values.reverse) (newPrefix := outputs.reverse)
            (baseStack := initialTarget.evm.stack)
            (by simpa [sourceFinal, targetFinal] using hSharedEVM)
            hStack (by simpa [targetFinal] using hTargetStack)
            hScratchStable (by rfl) hMemoryMono hActiveMono hFinalNoWrap
        have hOutputsLength :
            outputs.length = Expressions.Structured.BasicOp.outputs op :=
          Locals.Source.PrimitiveSemantics.structured_eval_length hSourceEval
        have hFinalState :
            ActivationStateRel contract plan live
              (stackOffset + Expressions.Structured.BasicOp.outputs op)
              frameBase mode sourceFinal targetFinal := by
          simpa [List.length_reverse, hOutputsLength] using hRebased
        rw [hSourceOpen, hTargetOpen]
        apply Simulation.Interaction.Rel.done
        apply Simulation.Interaction.ExceptRel.ok
        exact
          ⟨hFinalState, hOutputsLength,
            by simpa [targetFinal] using hTargetStack⟩

end FallibleClosedSpec

namespace SharedFamily

def toClosedSpec
    {op : Structured.BasicOp} (family : SharedFamily op)
    (contract : MemoryContract.Contract) : ClosedSpec contract op where
  sourceStep := family.sourceStep
  supportsOpen := family.supportsOpen
  notGas := family.not_gas
  notMsize := family.not_msize
  evalExists := family.eval_exists
  simulate := by
    intro sourceShared sourceFinal targetShared values outputs _hLength hRel
      _hSafe hTargetNoWrap hEval
    obtain ⟨targetFinal, hTargetEval, hShared, hMachine⟩ :=
      family.simulate hRel hEval
    refine ⟨targetFinal, hTargetEval, ?_⟩
    refine ⟨hShared, ?_, ?_, ?_, ?_⟩
    · intro reservation hReservation address hRegion hMemory hActive
      simp [hMachine]
    · simp [hMachine]
    · simp [hMachine]
    · simpa [hMachine] using hTargetNoWrap

/-- Memory-neutral ordinary primitives implement the canonical open capability. -/
theorem openForward
    {op : Structured.BasicOp}
    (family : SharedFamily op) (contract : MemoryContract.Contract) :
    AllocationInteractionPrimitive.OpenForward contract op :=
  (family.toClosedSpec contract).openForward

end SharedFamily

inductive ResourceFamily : Structured.BasicOp → Simulation.ResourceQuery → Prop where
  | gas : ResourceFamily .gas .gas
  | msize : ResourceFamily .msize .msize

namespace ResourceFamily

/-- Resource primitives expose one identical query and preserve every answer. -/
theorem openForward
    {op : Structured.BasicOp} {kind : Simulation.ResourceQuery}
    (family : ResourceFamily op kind) (contract : MemoryContract.Contract) :
    AllocationInteractionPrimitive.OpenForward contract op where
  preserve := by
    intro plan live stackOffset frameBase mode source initialTarget target
      values hLength hRel hStack _hSafe
    have hValues : values = [] := by
      apply List.eq_nil_of_length_eq_zero
      cases family <;> simpa [Expressions.Structured.BasicOp.inputs] using hLength
    subst values
    cases family with
    | gas =>
        rw [Locals.InteractionSemantics.Primitive.openEval_gas,
          Structured.InteractionSemantics.BasicInstr.openStep_gas]
        apply Simulation.Interaction.Rel.request
        intro value
        apply Simulation.Interaction.Rel.done
        apply Simulation.Interaction.ExceptRel.ok
        refine ⟨?_, rfl, ?_⟩
        · simpa [Locals.InteractionSemantics.Primitive.finish,
            Locals.InteractionSemantics.Primitive.isolated,
            Assembly.InteractionSemantics.PrimOp.resourceStep,
            Simulation.Interaction.map, StateRel.pushTarget,
            StateRel.pushTargetBy] using hRel.push_target_by 1 value
        · simp [Assembly.InteractionSemantics.PrimOp.resourceStep,
            Locals.InteractionSemantics.Primitive.finish,
            Locals.InteractionSemantics.Primitive.isolated,
            StateRel.pushTarget, StateRel.pushTargetBy, hStack,
            EvmYul.Stack.push, EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
    | msize =>
        rw [Locals.InteractionSemantics.Primitive.openEval_msize,
          Structured.InteractionSemantics.BasicInstr.openStep_msize]
        apply Simulation.Interaction.Rel.request
        intro value
        apply Simulation.Interaction.Rel.done
        apply Simulation.Interaction.ExceptRel.ok
        refine ⟨?_, rfl, ?_⟩
        · simpa [Locals.InteractionSemantics.Primitive.finish,
            Locals.InteractionSemantics.Primitive.isolated,
            Assembly.InteractionSemantics.PrimOp.resourceStep,
            Simulation.Interaction.map, StateRel.pushTarget,
            StateRel.pushTargetBy] using hRel.push_target_by 1 value
        · simp [Assembly.InteractionSemantics.PrimOp.resourceStep,
            Locals.InteractionSemantics.Primitive.finish,
            Locals.InteractionSemantics.Primitive.isolated,
            StateRel.pushTarget, StateRel.pushTargetBy, hStack,
            EvmYul.Stack.push, EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]

end ResourceFamily

namespace MemoryFamily

theorem targetEffect_of_memory_eq
    {contract : MemoryContract.Contract}
    {sourceFinal targetInitial targetFinal : EvmYul.SharedState .EVM}
    (hShared : SharedRel contract sourceFinal targetFinal)
    (hMemory :
      targetFinal.toMachineState.memory = targetInitial.toMachineState.memory)
    (hActive :
      targetInitial.toMachineState.activeWords.toNat ≤
        targetFinal.toMachineState.activeWords.toNat)
    (hInitialNoWrap :
      targetInitial.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size)
    (hFinalNoWrap :
      targetFinal.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size) :
    TargetEffect contract sourceFinal targetInitial targetFinal := by
  refine ⟨hShared, ?_, ?_, hActive, hFinalNoWrap⟩
  · intro reservation hReservation query hReserved hReadMemory hReadActive
    have hQueryLt : query < EvmYul.UInt256.size :=
      lt_of_le_of_lt
        (Nat.le_add_right query MemoryContract.wordBytes)
        (hReadActive.trans_lt hInitialNoWrap)
    exact
      Compiler.MemoryRelation.MachineRel.lookupMemory_eq_of_memory_eq_active_growth
        query (EvmYul.UInt256.toNat_ofNat_of_lt hQueryLt)
        hMemory hActive hInitialNoWrap hFinalNoWrap hReadMemory hReadActive
  · simp [hMemory]

theorem mload_simulate
    {contract : MemoryContract.Contract}
    {sourceShared sourceFinal targetShared : EvmYul.SharedState .EVM}
    {address : Word} {outputs : List Word}
    (hRel : SharedRel contract sourceShared targetShared)
    (hConsistent :
      Compiler.MemoryRelation.MemoryConsistent sourceShared.toMachineState)
    (hAllowed : Simulation.MemorySafety.RegionAllowed contract
      address.toNat MemoryContract.wordBytes)
    (hExpansion : Compiler.MemoryRelation.ExpansionNoWrap
      address.toNat MemoryContract.wordBytes)
    (hTargetNoWrap :
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size)
    (hEval :
      Locals.Source.PrimitiveSemantics.structured.eval
          .mload sourceShared [address] = .ok (sourceFinal, outputs)) :
    ∃ targetFinal,
      Locals.Source.PrimitiveSemantics.structured.eval
          .mload targetShared [address] = .ok (targetFinal, outputs) ∧
      SharedRel contract sourceFinal targetFinal ∧
      targetFinal.toMachineState.memory = targetShared.toMachineState.memory ∧
      targetShared.toMachineState.activeWords.toNat ≤
        targetFinal.toMachineState.activeWords.toNat ∧
      targetFinal.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size := by
  have hAllowed' :
      match contract.scratch? with
      | none => True
      | some reservation =>
          reservation.sourceAccessAllowed
            address.toNat MemoryContract.wordBytes := by
    simpa [Simulation.MemorySafety.RegionAllowed] using hAllowed
  obtain ⟨hValue, hMachineRel, hFinalNoWrap, hActiveMono⟩ :=
    Compiler.MemoryRelation.MachineRel.mload_of_allowed
      hRel.machine hConsistent hTargetNoWrap address hAllowed' hExpansion
  have hSourceResult :
      sourceFinal =
          { sourceShared with
            toMachineState := (sourceShared.toMachineState.mload address).2 } ∧
        outputs = [(sourceShared.toMachineState.mload address).1] := by
    simpa [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp, Assembly.PrimOp.continuingStep?,
      Assembly.PrimStep.run, Expressions.Structured.BasicOp.inputs,
      EvmYul.Stack.pop, EvmYul.Stack.push,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hEval.symm
  rcases hSourceResult with ⟨rfl, rfl⟩
  let targetFinal : EvmYul.SharedState .EVM :=
    { targetShared with
      toMachineState := (targetShared.toMachineState.mload address).2 }
  refine ⟨targetFinal, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp, Assembly.PrimOp.continuingStep?,
      Assembly.PrimStep.run, Expressions.Structured.BasicOp.inputs,
      EvmYul.Stack.pop, EvmYul.Stack.push,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, targetFinal, hValue]
  · exact ⟨hMachineRel, hRel.world⟩
  · simp [targetFinal, EvmYul.MachineState.mload]
  · simpa [targetFinal] using hActiveMono
  · simpa [targetFinal] using hFinalNoWrap

def mloadClosedSpec (contract : MemoryContract.Contract) :
    ClosedSpec contract .mload where
  sourceStep := ⟨.mload, rfl⟩
  supportsOpen := rfl
  notGas := by decide
  notMsize := by decide
  evalExists := by
    intro shared values hLength
    have hOne : values.length = 1 := by simpa using hLength
    obtain ⟨address, rfl⟩ := List.length_eq_one_iff.mp hOne
    simp [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp, Assembly.PrimOp.continuingStep?,
      Assembly.PrimStep.run, Expressions.Structured.BasicOp.inputs,
      EvmYul.Stack.pop, EvmYul.Stack.push,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  simulate := by
    intro sourceShared sourceFinal targetShared values outputs hLength hRel
      hSafe hTargetNoWrap hEval
    have hOne : values.length = 1 := by simpa using hLength
    obtain ⟨address, rfl⟩ := List.length_eq_one_iff.mp hOne
    have hSafety :
        Compiler.MemoryRelation.MemoryConsistent sourceShared.toMachineState ∧
          Simulation.MemorySafety.RegionAllowed contract
            address.toNat MemoryContract.wordBytes ∧
          Compiler.MemoryRelation.ExpansionNoWrap
            address.toNat MemoryContract.wordBytes := by
      simpa [Simulation.MemorySafety.OpenPrimitiveMemorySafe,
        Simulation.MemorySafety.PrimitiveMemorySafe,
        Simulation.MemorySafety.PrimitiveExpansionSafe] using hSafe
    obtain ⟨targetFinal, hTargetEval, hShared, hMemory,
        hActive, hFinalNoWrap⟩ :=
      mload_simulate hRel hSafety.1 hSafety.2.1 hSafety.2.2
        hTargetNoWrap hEval
    exact ⟨targetFinal, hTargetEval,
      targetEffect_of_memory_eq hShared hMemory hActive
        hTargetNoWrap hFinalNoWrap⟩

theorem mload_openForward (contract : MemoryContract.Contract) :
    AllocationInteractionPrimitive.OpenForward contract .mload :=
  (mloadClosedSpec contract).openForward

theorem mstore_simulate
    {contract : MemoryContract.Contract}
    {sourceShared sourceFinal targetShared : EvmYul.SharedState .EVM}
    {address value : Word} {outputs : List Word}
    (hRel : SharedRel contract sourceShared targetShared)
    (hExpansion :
      Compiler.MemoryRelation.ExpansionNoWrap
        address.toNat MemoryContract.wordBytes)
    (hHost : address.toNat + MemoryContract.wordBytes < USize.size)
    (hTargetNoWrap :
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size)
    (hEval :
      Locals.Source.PrimitiveSemantics.structured.eval
          .mstore sourceShared [value, address] =
        .ok (sourceFinal, outputs)) :
    ∃ targetFinal,
      Locals.Source.PrimitiveSemantics.structured.eval
          .mstore targetShared [value, address] =
        .ok (targetFinal, outputs) ∧
      SharedRel contract sourceFinal targetFinal ∧
      targetFinal.toMachineState =
        targetShared.toMachineState.mstore address value ∧
      targetShared.toMachineState.memory.size ≤
        targetFinal.toMachineState.memory.size ∧
      targetShared.toMachineState.activeWords.toNat ≤
        targetFinal.toMachineState.activeWords.toNat ∧
      targetFinal.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size := by
  obtain ⟨hMachineRel, hFinalNoWrap, hActiveMono, hMemoryMono⟩ :=
    Compiler.MemoryRelation.MachineRel.mstore_both
      hRel.machine hTargetNoWrap address value hExpansion hHost
  have hSourceResult :
      sourceFinal =
          { sourceShared with
            toMachineState :=
              sourceShared.toMachineState.mstore address value } ∧
        outputs = [] := by
    simpa [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      Expressions.Structured.BasicOp.inputs,
      EvmYul.EVM.binaryMachineStateOp, EvmYul.Stack.pop2,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run] using hEval.symm
  rcases hSourceResult with ⟨rfl, rfl⟩
  let targetFinal : EvmYul.SharedState .EVM :=
    { targetShared with
      toMachineState := targetShared.toMachineState.mstore address value }
  refine ⟨targetFinal, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · simp [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      Expressions.Structured.BasicOp.inputs,
      EvmYul.EVM.binaryMachineStateOp, EvmYul.Stack.pop2,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run, targetFinal]
  · exact ⟨hMachineRel, hRel.world⟩
  · simpa [targetFinal] using hMemoryMono
  · simpa [targetFinal] using hActiveMono
  · simpa [targetFinal] using hFinalNoWrap

def mstoreClosedSpec (contract : MemoryContract.Contract) :
    ClosedSpec contract .mstore where
  sourceStep := ⟨.binaryMachineState EvmYul.MachineState.mstore, rfl⟩
  supportsOpen := rfl
  notGas := by decide
  notMsize := by decide
  evalExists := by
    intro shared values hLength
    have hTwo : values.length = 2 := by simpa using hLength
    obtain ⟨value, address, rfl⟩ := List.length_eq_two.mp hTwo
    simp [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp, Assembly.PrimOp.continuingStep?,
      Assembly.PrimStep.run, Expressions.Structured.BasicOp.inputs,
      EvmYul.EVM.binaryMachineStateOp, EvmYul.Stack.pop2,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run]
  simulate := by
    intro sourceShared sourceFinal targetShared values outputs hLength hRel
      hSafe hTargetNoWrap hEval
    have hTwo : values.length = 2 := by simpa using hLength
    obtain ⟨value, address, rfl⟩ := List.length_eq_two.mp hTwo
    have hSafety :
        Compiler.MemoryRelation.MemoryConsistent sourceShared.toMachineState ∧
          Simulation.MemorySafety.RegionAllowed contract
            address.toNat MemoryContract.wordBytes ∧
          Compiler.MemoryRelation.ExpansionNoWrap
            address.toNat MemoryContract.wordBytes ∧
          address.toNat + MemoryContract.wordBytes < USize.size := by
      simpa [Simulation.MemorySafety.OpenPrimitiveMemorySafe,
        Simulation.MemorySafety.PrimitiveMemorySafe,
        Simulation.MemorySafety.PrimitiveExpansionSafe,
        Simulation.MemorySafety.PrimitiveHostSafe] using hSafe
    obtain ⟨targetFinal, hTargetEval, hShared, hMachine, hMemoryMono,
        hActiveMono, hFinalNoWrap⟩ :=
      mstore_simulate hRel hSafety.2.2.1 hSafety.2.2.2
        hTargetNoWrap hEval
    refine ⟨targetFinal, hTargetEval, hShared, ?_, hMemoryMono,
      hActiveMono, hFinalNoWrap⟩
    intro reservation hReservation query hReserved hReadMemory hReadActive
    have hQueryLt : query < EvmYul.UInt256.size :=
      lt_of_le_of_lt (Nat.le_add_right query MemoryContract.wordBytes)
        (hReadActive.trans_lt hTargetNoWrap)
    have hDisjoint :=
      Simulation.MemorySafety.reservedWord_disjoint_of_regionAllowed
        hReservation hSafety.2.1 hReserved
    have hStable :=
      Compiler.MemoryRelation.lookupMemory_mstore_disjoint_growing
        targetShared.toMachineState address.toNat query value
        (by simp) (EvmYul.UInt256.toNat_ofNat_of_lt hQueryLt)
        (by simpa [MemoryContract.wordBytes] using hSafety.2.2.2)
        (by simpa [MemoryContract.wordBytes] using hReadMemory)
        (by simpa [MemoryContract.wordBytes] using hReadActive)
        (by simpa [MemoryContract.wordBytes] using hTargetNoWrap)
        (by simpa [MemoryContract.wordBytes] using hDisjoint)
    rw [hMachine, ← EvmYul.UInt256.ofNat_toNat address]
    exact hStable

theorem mstore_openForward (contract : MemoryContract.Contract) :
    AllocationInteractionPrimitive.OpenForward contract .mstore :=
  (mstoreClosedSpec contract).openForward

theorem mstore8_simulate
    {contract : MemoryContract.Contract}
    {sourceShared sourceFinal targetShared : EvmYul.SharedState .EVM}
    {address value : Word} {outputs : List Word}
    (hRel : SharedRel contract sourceShared targetShared)
    (hExpansion : Compiler.MemoryRelation.ExpansionNoWrap address.toNat 1)
    (hHost : address.toNat + 1 < USize.size)
    (hTargetNoWrap :
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size)
    (hEval :
      Locals.Source.PrimitiveSemantics.structured.eval
          .mstore8 sourceShared [value, address] =
        .ok (sourceFinal, outputs)) :
    ∃ targetFinal,
      Locals.Source.PrimitiveSemantics.structured.eval
          .mstore8 targetShared [value, address] =
        .ok (targetFinal, outputs) ∧
      SharedRel contract sourceFinal targetFinal ∧
      targetFinal.toMachineState =
        targetShared.toMachineState.mstore8 address value ∧
      targetShared.toMachineState.memory.size ≤
        targetFinal.toMachineState.memory.size ∧
      targetShared.toMachineState.activeWords.toNat ≤
        targetFinal.toMachineState.activeWords.toNat ∧
      targetFinal.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size := by
  obtain ⟨hMachineRel, hFinalNoWrap, hActiveMono, hMemoryMono⟩ :=
    Compiler.MemoryRelation.MachineRel.mstore8_both
      hRel.machine hTargetNoWrap address value hExpansion hHost
  have hSourceResult :
      sourceFinal =
          { sourceShared with
            toMachineState :=
              sourceShared.toMachineState.mstore8 address value } ∧
        outputs = [] := by
    simpa [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      Expressions.Structured.BasicOp.inputs,
      EvmYul.EVM.binaryMachineStateOp, EvmYul.Stack.pop2,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run] using hEval.symm
  rcases hSourceResult with ⟨rfl, rfl⟩
  let targetFinal : EvmYul.SharedState .EVM :=
    { targetShared with
      toMachineState := targetShared.toMachineState.mstore8 address value }
  refine ⟨targetFinal, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · simp [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      Expressions.Structured.BasicOp.inputs,
      EvmYul.EVM.binaryMachineStateOp, EvmYul.Stack.pop2,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run, targetFinal]
  · exact ⟨hMachineRel, hRel.world⟩
  · simpa [targetFinal] using hMemoryMono
  · simpa [targetFinal] using hActiveMono
  · simpa [targetFinal] using hFinalNoWrap

def mstore8ClosedSpec (contract : MemoryContract.Contract) :
    ClosedSpec contract .mstore8 where
  sourceStep := ⟨.binaryMachineState EvmYul.MachineState.mstore8, rfl⟩
  supportsOpen := rfl
  notGas := by decide
  notMsize := by decide
  evalExists := by
    intro shared values hLength
    have hTwo : values.length = 2 := by simpa using hLength
    obtain ⟨value, address, rfl⟩ := List.length_eq_two.mp hTwo
    simp [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp, Assembly.PrimOp.continuingStep?,
      Assembly.PrimStep.run, Expressions.Structured.BasicOp.inputs,
      EvmYul.EVM.binaryMachineStateOp, EvmYul.Stack.pop2,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run]
  simulate := by
    intro sourceShared sourceFinal targetShared values outputs hLength hRel
      hSafe hTargetNoWrap hEval
    have hTwo : values.length = 2 := by simpa using hLength
    obtain ⟨value, address, rfl⟩ := List.length_eq_two.mp hTwo
    have hSafety :
        Compiler.MemoryRelation.MemoryConsistent sourceShared.toMachineState ∧
          Simulation.MemorySafety.RegionAllowed contract address.toNat 1 ∧
          Compiler.MemoryRelation.ExpansionNoWrap address.toNat 1 ∧
          address.toNat + 1 < USize.size := by
      simpa [Simulation.MemorySafety.OpenPrimitiveMemorySafe,
        Simulation.MemorySafety.PrimitiveMemorySafe,
        Simulation.MemorySafety.PrimitiveExpansionSafe,
        Simulation.MemorySafety.PrimitiveHostSafe] using hSafe
    obtain ⟨targetFinal, hTargetEval, hShared, hMachine, hMemoryMono,
        hActiveMono, hFinalNoWrap⟩ :=
      mstore8_simulate hRel hSafety.2.2.1 hSafety.2.2.2
        hTargetNoWrap hEval
    refine ⟨targetFinal, hTargetEval, hShared, ?_, hMemoryMono,
      hActiveMono, hFinalNoWrap⟩
    intro reservation hReservation query hReserved hReadMemory hReadActive
    have hQueryLt : query < EvmYul.UInt256.size :=
      lt_of_le_of_lt (Nat.le_add_right query MemoryContract.wordBytes)
        (hReadActive.trans_lt hTargetNoWrap)
    let bytes : ByteArray := ⟨#[UInt8.ofNat value.toNat]⟩
    have hWrittenMemory :
        targetFinal.toMachineState.memory =
          (EvmYul.writeBytes bytes 0 targetShared.toMachineState
            address.toNat 1).memory := by
      rw [hMachine]
      rfl
    have hDisjoint :=
      Simulation.MemorySafety.reservedWord_disjoint_of_regionAllowed
        hReservation hSafety.2.1 hReserved
    exact
      Compiler.MemoryRelation.lookupMemory_eq_of_writeBytes_disjoint_growing
        bytes targetShared.toMachineState targetFinal.toMachineState
        address.toNat 1 query rfl (by decide) hSafety.2.2.2
        hWrittenMemory (EvmYul.UInt256.toNat_ofNat_of_lt hQueryLt)
        hReadMemory hReadActive hTargetNoWrap hActiveMono hFinalNoWrap hDisjoint

theorem mstore8_openForward (contract : MemoryContract.Contract) :
    AllocationInteractionPrimitive.OpenForward contract .mstore8 :=
  (mstore8ClosedSpec contract).openForward

/-- Decoded destination and exact target write for one total copy primitive. -/
structure CopyInvocation (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) (values : List Word) where
  sourceOffset : Word
  destination : Word
  size : Word
  writeSafe :
    ∀ {sourceMachine : EvmYul.MachineState},
      Simulation.MemorySafety.OpenPrimitiveMemorySafe
          contract op sourceMachine values →
        Simulation.MemorySafety.RegionAllowed contract
            destination.toNat size.toNat ∧
          destination.toNat + size.toNat < USize.size
  simulate :
    ∀ {sourceShared sourceFinal targetShared : EvmYul.SharedState .EVM}
      {outputs : List Word},
      SharedRel contract sourceShared targetShared →
      Simulation.MemorySafety.OpenPrimitiveMemorySafe
          contract op sourceShared.toMachineState values →
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size →
      Locals.Source.PrimitiveSemantics.structured.eval
          op sourceShared values = .ok (sourceFinal, outputs) →
      ∃ (targetFinal : EvmYul.SharedState .EVM) (copied : ByteArray),
        Locals.Source.PrimitiveSemantics.structured.eval
            op targetShared values = .ok (targetFinal, outputs) ∧
          SharedRel contract sourceFinal targetFinal ∧
          targetFinal.toMachineState.memory =
            copied.write sourceOffset.toNat
              targetShared.toMachineState.memory
              destination.toNat size.toNat ∧
          targetShared.toMachineState.memory.size ≤
            targetFinal.toMachineState.memory.size ∧
          targetShared.toMachineState.activeWords.toNat ≤
            targetFinal.toMachineState.activeWords.toNat ∧
          targetFinal.toMachineState.activeWords.toNat *
              MemoryContract.wordBytes < EvmYul.UInt256.size

/-- Pass-owned capability for a source-total canonical byte-copy operation. -/
structure CopySpec (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) where
  sourceStep :
    ∃ step,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep? op = some step
  supportsOpen : Locals.InteractionSemantics.Primitive.supportsOpen op = true
  notGas : op.toPrimOp ≠ .gas
  notMsize : op.toPrimOp ≠ .msize
  evalExists :
    ∀ {shared : EvmYul.SharedState .EVM} {values : List Word},
      values.length = Expressions.Structured.BasicOp.inputs op →
      ∃ sharedFinal outputs,
        Locals.Source.PrimitiveSemantics.structured.eval op shared values =
          .ok (sharedFinal, outputs)
  decode :
    ∀ values,
      values.length = Expressions.Structured.BasicOp.inputs op →
      CopyInvocation contract op values

theorem targetEffect_of_copy
    {contract : MemoryContract.Contract}
    {sourceFinal targetInitial targetFinal : EvmYul.SharedState .EVM}
    {copied : ByteArray} {sourceOffset destination size : Nat}
    (hShared : SharedRel contract sourceFinal targetFinal)
    (hMemory :
      targetFinal.toMachineState.memory =
        copied.write sourceOffset targetInitial.toMachineState.memory
          destination size)
    (hAllowed :
      Simulation.MemorySafety.RegionAllowed contract destination size)
    (hHost : destination + size < USize.size)
    (hMemoryMono :
      targetInitial.toMachineState.memory.size ≤
        targetFinal.toMachineState.memory.size)
    (hActiveMono :
      targetInitial.toMachineState.activeWords.toNat ≤
        targetFinal.toMachineState.activeWords.toNat)
    (hInitialNoWrap :
      targetInitial.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size)
    (hFinalNoWrap :
      targetFinal.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size) :
    TargetEffect contract sourceFinal targetInitial targetFinal := by
  refine ⟨hShared, ?_, hMemoryMono, hActiveMono, hFinalNoWrap⟩
  intro reservation hReservation query hReserved hReadMemory hReadActive
  have hQueryLt : query < EvmYul.UInt256.size :=
    lt_of_le_of_lt (Nat.le_add_right query MemoryContract.wordBytes)
      (hReadActive.trans_lt hInitialNoWrap)
  have hDisjoint :=
    Simulation.MemorySafety.reservedWord_disjoint_of_regionAllowed
      hReservation hAllowed hReserved
  exact
    Compiler.MemoryRelation.lookupMemory_eq_of_write_disjoint_growing
      copied targetInitial.toMachineState targetFinal.toMachineState
      sourceOffset destination size query hHost hMemory
      (EvmYul.UInt256.toNat_ofNat_of_lt hQueryLt)
      hReadMemory hReadActive hInitialNoWrap hActiveMono hFinalNoWrap hDisjoint

namespace CopySpec

def toClosedSpec
    {contract : MemoryContract.Contract} {op : Structured.BasicOp}
    (spec : CopySpec contract op) : ClosedSpec contract op where
  sourceStep := spec.sourceStep
  supportsOpen := spec.supportsOpen
  notGas := spec.notGas
  notMsize := spec.notMsize
  evalExists := spec.evalExists
  simulate := by
    intro sourceShared sourceFinal targetShared values outputs hLength hRel
      hSafe hTargetNoWrap hEval
    let invocation := spec.decode values hLength
    obtain ⟨hAllowed, hHost⟩ := invocation.writeSafe hSafe
    obtain ⟨targetFinal, copied, hTargetEval, hShared, hMemory,
        hMemoryMono, hActiveMono, hFinalNoWrap⟩ :=
      invocation.simulate hRel hSafe hTargetNoWrap hEval
    exact ⟨targetFinal, hTargetEval,
      targetEffect_of_copy hShared hMemory hAllowed hHost hMemoryMono
        hActiveMono hTargetNoWrap hFinalNoWrap⟩

theorem openForward
    {contract : MemoryContract.Contract} {op : Structured.BasicOp}
    (spec : CopySpec contract op) :
    AllocationInteractionPrimitive.OpenForward contract op :=
  spec.toClosedSpec.openForward

end CopySpec

theorem calldatacopy_simulate
    {contract : MemoryContract.Contract}
    {sourceShared sourceFinal targetShared : EvmYul.SharedState .EVM}
    {destination sourceOffset size : Word} {outputs : List Word}
    (hRel : SharedRel contract sourceShared targetShared)
    (hExpansion :
      Compiler.MemoryRelation.ExpansionNoWrap
        destination.toNat size.toNat)
    (hHost : destination.toNat + size.toNat < USize.size)
    (hTargetNoWrap :
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size)
    (hEval :
      Locals.Source.PrimitiveSemantics.structured.eval
          .calldatacopy sourceShared [size, sourceOffset, destination] =
        .ok (sourceFinal, outputs)) :
    ∃ targetFinal,
      Locals.Source.PrimitiveSemantics.structured.eval
          .calldatacopy targetShared [size, sourceOffset, destination] =
        .ok (targetFinal, outputs) ∧
      SharedRel contract sourceFinal targetFinal ∧
      targetFinal.toMachineState.memory =
        targetShared.executionEnv.calldata.write sourceOffset.toNat
          targetShared.toMachineState.memory destination.toNat size.toNat ∧
      targetShared.toMachineState.memory.size ≤
        targetFinal.toMachineState.memory.size ∧
      targetShared.toMachineState.activeWords.toNat ≤
        targetFinal.toMachineState.activeWords.toNat ∧
      targetFinal.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size := by
  have hCalldata :
      sourceShared.executionEnv.calldata = targetShared.executionEnv.calldata :=
    congrArg EvmYul.ExecutionEnv.calldata hRel.executionEnv_eq
  have hMachine :=
    Compiler.MemoryRelation.MachineRel.copy_both
      hRel.machine hTargetNoWrap sourceShared.executionEnv.calldata
      sourceOffset.toNat destination.toNat size.toNat hExpansion hHost
  have hSourceResult :
      sourceFinal = sourceShared.calldatacopy destination sourceOffset size ∧
        outputs = [] := by
    simpa [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      Expressions.Structured.BasicOp.inputs,
      EvmYul.EVM.ternaryCopyOp, EvmYul.Stack.pop3,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run] using hEval.symm
  rcases hSourceResult with ⟨rfl, rfl⟩
  let targetFinal := targetShared.calldatacopy destination sourceOffset size
  have hShared :
      SharedRel contract
        (sourceShared.calldatacopy destination sourceOffset size)
        targetFinal := by
    refine ⟨?_, ?_⟩
    · simpa [EvmYul.SharedState.calldatacopy, targetFinal, hCalldata] using
        hMachine.1
    · simpa [EvmYul.SharedState.calldatacopy, targetFinal] using hRel.world
  refine ⟨targetFinal, ?_, hShared, ?_, ?_, ?_, ?_⟩
  · simp [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      Expressions.Structured.BasicOp.inputs,
      EvmYul.EVM.ternaryCopyOp, EvmYul.Stack.pop3,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run, targetFinal]
  · simp [EvmYul.SharedState.calldatacopy, targetFinal]
  · simpa [EvmYul.SharedState.calldatacopy, targetFinal, hCalldata] using
      hMachine.2.2.2
  · simpa [EvmYul.SharedState.calldatacopy, targetFinal] using hMachine.2.2.1
  · simpa [EvmYul.SharedState.calldatacopy, targetFinal] using hMachine.2.1

def calldatacopySpec (contract : MemoryContract.Contract) :
    CopySpec contract .calldatacopy where
  sourceStep := ⟨.ternaryCopy EvmYul.SharedState.calldatacopy, rfl⟩
  supportsOpen := rfl
  notGas := by decide
  notMsize := by decide
  evalExists := by
    intro shared values hLength
    obtain ⟨size, sourceOffset, destination, rfl⟩ :=
      List.length_eq_three.mp (by simpa using hLength)
    simp [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp, Assembly.PrimOp.continuingStep?,
      Assembly.PrimStep.run, Expressions.Structured.BasicOp.inputs,
      EvmYul.EVM.ternaryCopyOp, EvmYul.Stack.pop3,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run]
  decode := by
    intro values hLength
    have hLength3 : values.length = 3 := by simpa using hLength
    cases values with
    | nil => simp at hLength3
    | cons size rest =>
        cases rest with
        | nil => simp at hLength3
        | cons sourceOffset tail =>
            cases tail with
            | nil => simp at hLength3
            | cons destination extra =>
                have hExtra : extra = [] := by simpa using hLength3
                subst extra
                refine
                  { sourceOffset := sourceOffset
                    destination := destination
                    size := size
                    writeSafe := ?_
                    simulate := ?_ }
                · intro sourceMachine hSafe
                  have hFacts :
                      Compiler.MemoryRelation.MemoryConsistent sourceMachine ∧
                        Simulation.MemorySafety.RegionAllowed contract
                          destination.toNat size.toNat ∧
                        Compiler.MemoryRelation.ExpansionNoWrap
                          destination.toNat size.toNat ∧
                        destination.toNat + size.toNat < USize.size := by
                    simpa [Simulation.MemorySafety.OpenPrimitiveMemorySafe,
                      Simulation.MemorySafety.PrimitiveMemorySafe,
                      Simulation.MemorySafety.PrimitiveExpansionSafe,
                      Simulation.MemorySafety.PrimitiveHostSafe] using hSafe
                  exact ⟨hFacts.2.1, hFacts.2.2.2⟩
                · intro sourceShared sourceFinal targetShared outputs hRel hSafe
                    hTargetNoWrap hEval
                  have hFacts :
                      Compiler.MemoryRelation.MemoryConsistent
                          sourceShared.toMachineState ∧
                        Simulation.MemorySafety.RegionAllowed contract
                          destination.toNat size.toNat ∧
                        Compiler.MemoryRelation.ExpansionNoWrap
                          destination.toNat size.toNat ∧
                        destination.toNat + size.toNat < USize.size := by
                    simpa [Simulation.MemorySafety.OpenPrimitiveMemorySafe,
                      Simulation.MemorySafety.PrimitiveMemorySafe,
                      Simulation.MemorySafety.PrimitiveExpansionSafe,
                      Simulation.MemorySafety.PrimitiveHostSafe] using hSafe
                  obtain ⟨targetFinal, hTargetEval, hShared, hMemory,
                      hMemoryMono, hActiveMono, hFinalNoWrap⟩ :=
                    calldatacopy_simulate hRel hFacts.2.2.1 hFacts.2.2.2
                      hTargetNoWrap hEval
                  exact
                    ⟨targetFinal, targetShared.executionEnv.calldata,
                      hTargetEval, hShared, hMemory, hMemoryMono, hActiveMono,
                      hFinalNoWrap⟩

theorem calldatacopy_openForward (contract : MemoryContract.Contract) :
    AllocationInteractionPrimitive.OpenForward contract .calldatacopy :=
  (calldatacopySpec contract).openForward

theorem codecopy_simulate
    {contract : MemoryContract.Contract}
    {sourceShared sourceFinal targetShared : EvmYul.SharedState .EVM}
    {destination sourceOffset size : Word} {outputs : List Word}
    (hRel : SharedRel contract sourceShared targetShared)
    (hExpansion :
      Compiler.MemoryRelation.ExpansionNoWrap
        destination.toNat size.toNat)
    (hHost : destination.toNat + size.toNat < USize.size)
    (hTargetNoWrap :
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size)
    (hEval :
      Locals.Source.PrimitiveSemantics.structured.eval
          .codecopy sourceShared [size, sourceOffset, destination] =
        .ok (sourceFinal, outputs)) :
    ∃ targetFinal,
      Locals.Source.PrimitiveSemantics.structured.eval
          .codecopy targetShared [size, sourceOffset, destination] =
        .ok (targetFinal, outputs) ∧
      SharedRel contract sourceFinal targetFinal ∧
      targetFinal.toMachineState.memory =
        targetShared.executionEnv.code.write sourceOffset.toNat
          targetShared.toMachineState.memory destination.toNat size.toNat ∧
      targetShared.toMachineState.memory.size ≤
        targetFinal.toMachineState.memory.size ∧
      targetShared.toMachineState.activeWords.toNat ≤
        targetFinal.toMachineState.activeWords.toNat ∧
      targetFinal.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size := by
  have hCode : sourceShared.executionEnv.code = targetShared.executionEnv.code :=
    congrArg EvmYul.ExecutionEnv.code hRel.executionEnv_eq
  have hMachine :=
    Compiler.MemoryRelation.MachineRel.copy_both
      hRel.machine hTargetNoWrap sourceShared.executionEnv.code
      sourceOffset.toNat destination.toNat size.toNat hExpansion hHost
  have hSourceResult :
      sourceFinal = sourceShared.codeCopy destination sourceOffset size ∧
        outputs = [] := by
    simpa [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      Expressions.Structured.BasicOp.inputs,
      EvmYul.EVM.ternaryCopyOp, EvmYul.Stack.pop3,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run] using hEval.symm
  rcases hSourceResult with ⟨rfl, rfl⟩
  let targetFinal := targetShared.codeCopy destination sourceOffset size
  have hShared :
      SharedRel contract
        (sourceShared.codeCopy destination sourceOffset size) targetFinal := by
    refine ⟨?_, ?_⟩
    · simpa [EvmYul.SharedState.codeCopy, targetFinal, hCode] using hMachine.1
    · simpa [EvmYul.SharedState.codeCopy, targetFinal] using hRel.world
  refine ⟨targetFinal, ?_, hShared, ?_, ?_, ?_, ?_⟩
  · simp [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      Expressions.Structured.BasicOp.inputs,
      EvmYul.EVM.ternaryCopyOp, EvmYul.Stack.pop3,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run, targetFinal]
  · simp [EvmYul.SharedState.codeCopy, targetFinal]
  · simpa [EvmYul.SharedState.codeCopy, targetFinal, hCode] using
      hMachine.2.2.2
  · simpa [EvmYul.SharedState.codeCopy, targetFinal] using hMachine.2.2.1
  · simpa [EvmYul.SharedState.codeCopy, targetFinal] using hMachine.2.1

def codecopySpec (contract : MemoryContract.Contract) :
    CopySpec contract .codecopy where
  sourceStep := ⟨.ternaryCopy EvmYul.SharedState.codeCopy, rfl⟩
  supportsOpen := rfl
  notGas := by decide
  notMsize := by decide
  evalExists := by
    intro shared values hLength
    obtain ⟨size, sourceOffset, destination, rfl⟩ :=
      List.length_eq_three.mp (by simpa using hLength)
    simp [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp, Assembly.PrimOp.continuingStep?,
      Assembly.PrimStep.run, Expressions.Structured.BasicOp.inputs,
      EvmYul.EVM.ternaryCopyOp, EvmYul.Stack.pop3,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run]
  decode := by
    intro values hLength
    have hLength3 : values.length = 3 := by simpa using hLength
    cases values with
    | nil => simp at hLength3
    | cons size rest =>
        cases rest with
        | nil => simp at hLength3
        | cons sourceOffset tail =>
            cases tail with
            | nil => simp at hLength3
            | cons destination extra =>
                have hExtra : extra = [] := by simpa using hLength3
                subst extra
                refine
                  { sourceOffset := sourceOffset
                    destination := destination
                    size := size
                    writeSafe := ?_
                    simulate := ?_ }
                · intro sourceMachine hSafe
                  have hFacts :
                      Compiler.MemoryRelation.MemoryConsistent sourceMachine ∧
                        Simulation.MemorySafety.RegionAllowed contract
                          destination.toNat size.toNat ∧
                        Compiler.MemoryRelation.ExpansionNoWrap
                          destination.toNat size.toNat ∧
                        destination.toNat + size.toNat < USize.size := by
                    simpa [Simulation.MemorySafety.OpenPrimitiveMemorySafe,
                      Simulation.MemorySafety.PrimitiveMemorySafe,
                      Simulation.MemorySafety.PrimitiveExpansionSafe,
                      Simulation.MemorySafety.PrimitiveHostSafe] using hSafe
                  exact ⟨hFacts.2.1, hFacts.2.2.2⟩
                · intro sourceShared sourceFinal targetShared outputs hRel hSafe
                    hTargetNoWrap hEval
                  have hFacts :
                      Compiler.MemoryRelation.MemoryConsistent
                          sourceShared.toMachineState ∧
                        Simulation.MemorySafety.RegionAllowed contract
                          destination.toNat size.toNat ∧
                        Compiler.MemoryRelation.ExpansionNoWrap
                          destination.toNat size.toNat ∧
                        destination.toNat + size.toNat < USize.size := by
                    simpa [Simulation.MemorySafety.OpenPrimitiveMemorySafe,
                      Simulation.MemorySafety.PrimitiveMemorySafe,
                      Simulation.MemorySafety.PrimitiveExpansionSafe,
                      Simulation.MemorySafety.PrimitiveHostSafe] using hSafe
                  obtain ⟨targetFinal, hTargetEval, hShared, hMemory,
                      hMemoryMono, hActiveMono, hFinalNoWrap⟩ :=
                    codecopy_simulate hRel hFacts.2.2.1 hFacts.2.2.2
                      hTargetNoWrap hEval
                  exact
                    ⟨targetFinal, targetShared.executionEnv.code,
                      hTargetEval, hShared, hMemory, hMemoryMono, hActiveMono,
                      hFinalNoWrap⟩

theorem codecopy_openForward (contract : MemoryContract.Contract) :
    AllocationInteractionPrimitive.OpenForward contract .codecopy :=
  (codecopySpec contract).openForward

theorem returndatacopy_simulate
    {contract : MemoryContract.Contract}
    {sourceShared sourceFinal targetShared : EvmYul.SharedState .EVM}
    {destination sourceOffset size : Word} {outputs : List Word}
    (hRel : SharedRel contract sourceShared targetShared)
    (hExpansion :
      Compiler.MemoryRelation.ExpansionNoWrap destination.toNat size.toNat)
    (hHost : destination.toNat + size.toNat < USize.size)
    (hTargetNoWrap :
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size)
    (hEval :
      Locals.Source.PrimitiveSemantics.structured.eval
          .returndatacopy sourceShared [size, sourceOffset, destination] =
        .ok (sourceFinal, outputs)) :
    ∃ targetFinal,
      Locals.Source.PrimitiveSemantics.structured.eval
          .returndatacopy targetShared [size, sourceOffset, destination] =
        .ok (targetFinal, outputs) ∧
      SharedRel contract sourceFinal targetFinal ∧
      targetFinal.toMachineState.memory =
        targetShared.toMachineState.returnData.write sourceOffset.toNat
          targetShared.toMachineState.memory destination.toNat size.toNat ∧
      targetShared.toMachineState.memory.size ≤
        targetFinal.toMachineState.memory.size ∧
      targetShared.toMachineState.activeWords.toNat ≤
        targetFinal.toMachineState.activeWords.toNat ∧
      targetFinal.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size := by
  have hReturnData :
      sourceShared.toMachineState.returnData =
        targetShared.toMachineState.returnData :=
    hRel.machine.returnData
  have hBound :
      ¬ sourceShared.toMachineState.returnData.size <
          sourceOffset.toNat + size.toNat := by
    intro hPast
    simp [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      Expressions.Structured.BasicOp.inputs,
      EvmYul.Stack.pop3, hPast] at hEval
  have hTargetBound :
      ¬ targetShared.toMachineState.returnData.size <
          sourceOffset.toNat + size.toNat := by
    simpa [← hReturnData] using hBound
  have hMachine :=
    Compiler.MemoryRelation.MachineRel.copy_both
      hRel.machine hTargetNoWrap sourceShared.toMachineState.returnData
      sourceOffset.toNat destination.toNat size.toNat hExpansion hHost
  have hSourceResult :
      sourceFinal =
          { sourceShared with
            toMachineState :=
              sourceShared.toMachineState.returndatacopy
                destination sourceOffset size } ∧
        outputs = [] := by
    simpa [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      Expressions.Structured.BasicOp.inputs,
      EvmYul.Stack.pop3, hBound,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run] using hEval.symm
  rcases hSourceResult with ⟨rfl, rfl⟩
  let targetFinal : EvmYul.SharedState .EVM :=
    { targetShared with
      toMachineState :=
        targetShared.toMachineState.returndatacopy
          destination sourceOffset size }
  have hShared :
      SharedRel contract
        { sourceShared with
          toMachineState :=
            sourceShared.toMachineState.returndatacopy
              destination sourceOffset size }
        targetFinal := by
    refine ⟨?_, ?_⟩
    · simpa [EvmYul.MachineState.returndatacopy, EvmYul.writeBytes,
        targetFinal, hReturnData] using hMachine.1
    · simpa [EvmYul.MachineState.returndatacopy, targetFinal] using hRel.world
  refine ⟨targetFinal, ?_, hShared, ?_, ?_, ?_, ?_⟩
  · simp [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      Expressions.Structured.BasicOp.inputs,
      EvmYul.Stack.pop3, hTargetBound,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run, targetFinal]
  · simp [EvmYul.MachineState.returndatacopy, EvmYul.writeBytes, targetFinal]
  · simpa [EvmYul.MachineState.returndatacopy, EvmYul.writeBytes,
      targetFinal, hReturnData] using hMachine.2.2.2
  · simpa [EvmYul.MachineState.returndatacopy, EvmYul.writeBytes,
      targetFinal] using hMachine.2.2.1
  · simpa [EvmYul.MachineState.returndatacopy, EvmYul.writeBytes,
      targetFinal] using hMachine.2.1

def returndatacopySpec (contract : MemoryContract.Contract) :
    FallibleClosedSpec contract .returndatacopy where
  sourceStep := ⟨.returndatacopy, rfl⟩
  supportsOpen := rfl
  notGas := by decide
  notMsize := by decide
  simulateSuccess := by
    intro sourceShared sourceFinal targetShared values outputs hLength hRel
      hSafe hTargetNoWrap hEval
    obtain ⟨size, sourceOffset, destination, rfl⟩ :=
      List.length_eq_three.mp (by simpa using hLength)
    have hFacts :
        Compiler.MemoryRelation.MemoryConsistent sourceShared.toMachineState ∧
          Simulation.MemorySafety.RegionAllowed contract
            destination.toNat size.toNat ∧
          Compiler.MemoryRelation.ExpansionNoWrap
            destination.toNat size.toNat ∧
          destination.toNat + size.toNat < USize.size := by
      simpa [Simulation.MemorySafety.OpenPrimitiveMemorySafe,
        Simulation.MemorySafety.PrimitiveMemorySafe,
        Simulation.MemorySafety.PrimitiveExpansionSafe,
        Simulation.MemorySafety.PrimitiveHostSafe] using hSafe
    obtain ⟨targetFinal, hTargetEval, hShared, hMemory,
        hMemoryMono, hActiveMono, hFinalNoWrap⟩ :=
      returndatacopy_simulate hRel hFacts.2.2.1 hFacts.2.2.2
        hTargetNoWrap hEval
    exact ⟨targetFinal, hTargetEval,
      targetEffect_of_copy hShared hMemory hFacts.2.1 hFacts.2.2.2
        hMemoryMono hActiveMono hTargetNoWrap hFinalNoWrap⟩
  errorSuffix := by
    intro step sourceShared target values baseStack error hLength hStep hRel
      hStack hEval
    have hStepEq : step = .returndatacopy := by
      simpa [Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
        Structured.BasicOp.toPrimOp,
        Assembly.PrimOp.continuingStep?] using (Option.some.inj hStep).symm
    subst step
    obtain ⟨size, sourceOffset, destination, rfl⟩ :=
      List.length_eq_three.mp (by simpa using hLength)
    have hBound :
        sourceShared.toMachineState.returnData.size <
          sourceOffset.toNat + size.toNat := by
      by_contra hBound
      simp [Locals.Source.PrimitiveSemantics.structured,
        Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
        Structured.BasicOp.toPrimOp,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        Expressions.Structured.BasicOp.inputs,
        EvmYul.Stack.pop3, hBound,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, Id.run] at hEval
    have hError : error = .InvalidMemoryAccess := by
      simpa [Locals.Source.PrimitiveSemantics.structured,
        Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
        Structured.BasicOp.toPrimOp,
        Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
        Expressions.Structured.BasicOp.inputs,
        EvmYul.Stack.pop3, hBound] using hEval.symm
    have hTargetBound :
        target.returnData.size < sourceOffset.toNat + size.toNat := by
      simpa [← hRel.machine.returnData] using hBound
    have hTargetStack :
        target.stack = [destination, sourceOffset, size] ++ baseStack := by
      simpa using hStack
    have hPrefixPop :
        EvmYul.Stack.pop3 [destination, sourceOffset, size] =
          some ([], destination, sourceOffset, size) := by
      rfl
    have hTargetPop :=
      Assembly.PrimStep.Stack.pop3_append_of_some
        (tail := baseStack) hPrefixPop
    have hTargetPop' :
        EvmYul.Stack.pop3
            (destination :: sourceOffset :: size :: baseStack) =
          some (baseStack, destination, sourceOffset, size) := by
      simpa using hTargetPop
    rw [hError]
    simp [Assembly.PrimStep.run, hTargetStack, hTargetPop', hTargetBound]

theorem returndatacopy_openForward (contract : MemoryContract.Contract) :
    AllocationInteractionPrimitive.OpenForward contract .returndatacopy :=
  (returndatacopySpec contract).openForward

theorem extcodecopy_simulate
    {contract : MemoryContract.Contract}
    {sourceShared sourceFinal targetShared : EvmYul.SharedState .EVM}
    {account destination sourceOffset size : Word} {outputs : List Word}
    (hRel : SharedRel contract sourceShared targetShared)
    (hExpansion :
      Compiler.MemoryRelation.ExpansionNoWrap
        destination.toNat size.toNat)
    (hHost : destination.toNat + size.toNat < USize.size)
    (hTargetNoWrap :
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size)
    (hEval :
      Locals.Source.PrimitiveSemantics.structured.eval
          .extcodecopy sourceShared
          [size, sourceOffset, destination, account] =
        .ok (sourceFinal, outputs)) :
    ∃ (targetFinal : EvmYul.SharedState .EVM) (copied : ByteArray),
      Locals.Source.PrimitiveSemantics.structured.eval
          .extcodecopy targetShared
          [size, sourceOffset, destination, account] =
        .ok (targetFinal, outputs) ∧
      SharedRel contract sourceFinal targetFinal ∧
      targetFinal.toMachineState.memory =
        copied.write sourceOffset.toNat targetShared.toMachineState.memory
          destination.toNat size.toNat ∧
      targetShared.toMachineState.memory.size ≤
        targetFinal.toMachineState.memory.size ∧
      targetShared.toMachineState.activeWords.toNat ≤
        targetFinal.toMachineState.activeWords.toNat ∧
      targetFinal.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size := by
  let address := EvmYul.AccountAddress.ofUInt256 account
  let copied : ByteArray :=
    sourceShared.toState.lookupAccount address |>.option
      .empty EvmYul.State.accountCodeImage
  have hWorld : sourceShared.toState = targetShared.toState := hRel.world
  have hMachine :=
    Compiler.MemoryRelation.MachineRel.copy_both
      hRel.machine hTargetNoWrap copied sourceOffset.toNat
      destination.toNat size.toNat hExpansion hHost
  have hSourceResult :
      sourceFinal =
          sourceShared.extCodeCopy' account destination sourceOffset size ∧
        outputs = [] := by
    simpa [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      Expressions.Structured.BasicOp.inputs,
      EvmYul.EVM.quaternaryCopyOp, EvmYul.Stack.pop4,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run] using hEval.symm
  rcases hSourceResult with ⟨rfl, rfl⟩
  let targetFinal :=
    targetShared.extCodeCopy' account destination sourceOffset size
  have hShared :
      SharedRel contract
        (sourceShared.extCodeCopy' account destination sourceOffset size)
        targetFinal := by
    refine ⟨?_, ?_⟩
    · simpa [EvmYul.SharedState.extCodeCopy', address, copied,
        targetFinal, hWorld] using hMachine.1
    · simpa [EvmYul.SharedState.extCodeCopy', address, targetFinal,
        hWorld] using hRel.world
  refine
    ⟨targetFinal,
      targetShared.toState.lookupAccount address |>.option
        .empty EvmYul.State.accountCodeImage,
      ?_, hShared, ?_, ?_, ?_, ?_⟩
  · simp [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      Expressions.Structured.BasicOp.inputs,
      EvmYul.EVM.quaternaryCopyOp, EvmYul.Stack.pop4,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run, targetFinal]
  · simp [EvmYul.SharedState.extCodeCopy', address, targetFinal]
  · simpa [EvmYul.SharedState.extCodeCopy', address, copied,
      targetFinal, hWorld] using hMachine.2.2.2
  · simpa [EvmYul.SharedState.extCodeCopy', address, targetFinal] using
      hMachine.2.2.1
  · simpa [EvmYul.SharedState.extCodeCopy', address, targetFinal] using
      hMachine.2.1

def extcodecopySpec (contract : MemoryContract.Contract) :
    CopySpec contract .extcodecopy where
  sourceStep := ⟨.quaternaryCopy EvmYul.SharedState.extCodeCopy', rfl⟩
  supportsOpen := rfl
  notGas := by decide
  notMsize := by decide
  evalExists := by
    intro shared values hLength
    obtain ⟨size, sourceOffset, destination, account, rfl⟩ :=
      List.length_eq_four.mp (by simpa using hLength)
    simp [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp, Assembly.PrimOp.continuingStep?,
      Assembly.PrimStep.run, Expressions.Structured.BasicOp.inputs,
      EvmYul.EVM.quaternaryCopyOp, EvmYul.Stack.pop4,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run]
  decode := by
    intro values hLength
    have hLength4 : values.length = 4 := by simpa using hLength
    cases values with
    | nil => simp at hLength4
    | cons size rest =>
        cases rest with
        | nil => simp at hLength4
        | cons sourceOffset tail =>
            cases tail with
            | nil => simp at hLength4
            | cons destination tail =>
                cases tail with
                | nil => simp at hLength4
                | cons account extra =>
                    have hExtra : extra = [] := by simpa using hLength4
                    subst extra
                    refine
                      { sourceOffset := sourceOffset
                        destination := destination
                        size := size
                        writeSafe := ?_
                        simulate := ?_ }
                    · intro sourceMachine hSafe
                      have hFacts :
                          Compiler.MemoryRelation.MemoryConsistent sourceMachine ∧
                            Simulation.MemorySafety.RegionAllowed contract
                              destination.toNat size.toNat ∧
                            Compiler.MemoryRelation.ExpansionNoWrap
                              destination.toNat size.toNat ∧
                            destination.toNat + size.toNat < USize.size := by
                        simpa [Simulation.MemorySafety.OpenPrimitiveMemorySafe,
                          Simulation.MemorySafety.PrimitiveMemorySafe,
                          Simulation.MemorySafety.PrimitiveExpansionSafe,
                          Simulation.MemorySafety.PrimitiveHostSafe] using hSafe
                      exact ⟨hFacts.2.1, hFacts.2.2.2⟩
                    · intro sourceShared sourceFinal targetShared outputs hRel
                        hSafe hTargetNoWrap hEval
                      have hFacts :
                          Compiler.MemoryRelation.MemoryConsistent
                              sourceShared.toMachineState ∧
                            Simulation.MemorySafety.RegionAllowed contract
                              destination.toNat size.toNat ∧
                            Compiler.MemoryRelation.ExpansionNoWrap
                              destination.toNat size.toNat ∧
                            destination.toNat + size.toNat < USize.size := by
                        simpa [Simulation.MemorySafety.OpenPrimitiveMemorySafe,
                          Simulation.MemorySafety.PrimitiveMemorySafe,
                          Simulation.MemorySafety.PrimitiveExpansionSafe,
                          Simulation.MemorySafety.PrimitiveHostSafe] using hSafe
                      exact
                        extcodecopy_simulate hRel hFacts.2.2.1 hFacts.2.2.2
                          hTargetNoWrap hEval

theorem extcodecopy_openForward (contract : MemoryContract.Contract) :
    AllocationInteractionPrimitive.OpenForward contract .extcodecopy :=
  (extcodecopySpec contract).openForward

theorem mcopy_simulate
    {contract : MemoryContract.Contract}
    {sourceShared sourceFinal targetShared : EvmYul.SharedState .EVM}
    {destination sourceOffset size : Word} {outputs : List Word}
    (hRel : SharedRel contract sourceShared targetShared)
    (hSourceAllowed :
      Simulation.MemorySafety.RegionAllowed contract
        sourceOffset.toNat size.toNat)
    (hExpansion :
      Compiler.MemoryRelation.ExpansionNoWrap
        (max destination.toNat sourceOffset.toNat) size.toNat)
    (hHost : destination.toNat + size.toNat < USize.size)
    (hTargetNoWrap :
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size)
    (hEval :
      Locals.Source.PrimitiveSemantics.structured.eval
          .mcopy sourceShared [size, sourceOffset, destination] =
        .ok (sourceFinal, outputs)) :
    ∃ targetFinal,
      Locals.Source.PrimitiveSemantics.structured.eval
          .mcopy targetShared [size, sourceOffset, destination] =
        .ok (targetFinal, outputs) ∧
      SharedRel contract sourceFinal targetFinal ∧
      targetFinal.toMachineState.memory =
        targetShared.toMachineState.memory.write sourceOffset.toNat
          targetShared.toMachineState.memory destination.toNat size.toNat ∧
      targetShared.toMachineState.memory.size ≤
        targetFinal.toMachineState.memory.size ∧
      targetShared.toMachineState.activeWords.toNat ≤
        targetFinal.toMachineState.activeWords.toNat ∧
      targetFinal.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size := by
  obtain ⟨hMachineRel, hFinalNoWrap, hActiveMono, hMemoryMono⟩ :=
    Compiler.MemoryRelation.MachineRel.mcopy_both
      hRel.machine hTargetNoWrap sourceOffset.toNat destination.toNat
      size.toNat hSourceAllowed hExpansion hHost
  have hSourceResult :
      sourceFinal =
          { sourceShared with
            toMachineState :=
              sourceShared.toMachineState.mcopy
                destination sourceOffset size } ∧
        outputs = [] := by
    simpa [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      Expressions.Structured.BasicOp.inputs,
      EvmYul.EVM.ternaryMachineStateOp, EvmYul.Stack.pop3,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run] using hEval.symm
  rcases hSourceResult with ⟨rfl, rfl⟩
  let targetFinal : EvmYul.SharedState .EVM :=
    { targetShared with
      toMachineState :=
        targetShared.toMachineState.mcopy destination sourceOffset size }
  refine ⟨targetFinal, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      Expressions.Structured.BasicOp.inputs,
      EvmYul.EVM.ternaryMachineStateOp, EvmYul.Stack.pop3,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run, targetFinal]
  · refine ⟨?_, ?_⟩
    · simpa [EvmYul.MachineState.mcopy, EvmYul.writeBytes,
        targetFinal] using hMachineRel
    · simpa [EvmYul.MachineState.mcopy, targetFinal] using hRel.world
  · simp [EvmYul.MachineState.mcopy, EvmYul.writeBytes, targetFinal]
  · simpa [EvmYul.MachineState.mcopy, EvmYul.writeBytes,
      targetFinal] using hMemoryMono
  · simpa [EvmYul.MachineState.mcopy, targetFinal] using hActiveMono
  · simpa [EvmYul.MachineState.mcopy, targetFinal] using hFinalNoWrap

def mcopySpec (contract : MemoryContract.Contract) : CopySpec contract .mcopy where
  sourceStep := ⟨.ternaryMachineState EvmYul.MachineState.mcopy, rfl⟩
  supportsOpen := rfl
  notGas := by decide
  notMsize := by decide
  evalExists := by
    intro shared values hLength
    obtain ⟨size, sourceOffset, destination, rfl⟩ :=
      List.length_eq_three.mp (by simpa using hLength)
    simp [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp, Assembly.PrimOp.continuingStep?,
      Assembly.PrimStep.run, Expressions.Structured.BasicOp.inputs,
      EvmYul.EVM.ternaryMachineStateOp, EvmYul.Stack.pop3,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run]
  decode := by
    intro values hLength
    have hLength3 : values.length = 3 := by simpa using hLength
    cases values with
    | nil => simp at hLength3
    | cons size rest =>
        cases rest with
        | nil => simp at hLength3
        | cons sourceOffset tail =>
            cases tail with
            | nil => simp at hLength3
            | cons destination extra =>
                have hExtra : extra = [] := by simpa using hLength3
                subst extra
                refine
                  { sourceOffset := sourceOffset
                    destination := destination
                    size := size
                    writeSafe := ?_
                    simulate := ?_ }
                · intro sourceMachine hSafe
                  have hFacts :
                      Compiler.MemoryRelation.MemoryConsistent sourceMachine ∧
                        Simulation.MemorySafety.RegionAllowed contract
                          destination.toNat size.toNat ∧
                        Simulation.MemorySafety.RegionAllowed contract
                          sourceOffset.toNat size.toNat ∧
                        Compiler.MemoryRelation.ExpansionNoWrap
                          (max destination.toNat sourceOffset.toNat) size.toNat ∧
                        (destination.toNat + size.toNat < USize.size ∧
                          sourceOffset.toNat + size.toNat < USize.size) := by
                    simpa [Simulation.MemorySafety.OpenPrimitiveMemorySafe,
                      Simulation.MemorySafety.PrimitiveMemorySafe,
                      Simulation.MemorySafety.PrimitiveExpansionSafe,
                      Simulation.MemorySafety.PrimitiveHostSafe] using hSafe
                  exact ⟨hFacts.2.1, hFacts.2.2.2.2.1⟩
                · intro sourceShared sourceFinal targetShared outputs hRel hSafe
                    hTargetNoWrap hEval
                  have hFacts :
                      Compiler.MemoryRelation.MemoryConsistent
                          sourceShared.toMachineState ∧
                        Simulation.MemorySafety.RegionAllowed contract
                          destination.toNat size.toNat ∧
                        Simulation.MemorySafety.RegionAllowed contract
                          sourceOffset.toNat size.toNat ∧
                        Compiler.MemoryRelation.ExpansionNoWrap
                          (max destination.toNat sourceOffset.toNat) size.toNat ∧
                        (destination.toNat + size.toNat < USize.size ∧
                          sourceOffset.toNat + size.toNat < USize.size) := by
                    simpa [Simulation.MemorySafety.OpenPrimitiveMemorySafe,
                      Simulation.MemorySafety.PrimitiveMemorySafe,
                      Simulation.MemorySafety.PrimitiveExpansionSafe,
                      Simulation.MemorySafety.PrimitiveHostSafe] using hSafe
                  obtain ⟨targetFinal, hTargetEval, hShared, hMemory,
                      hMemoryMono, hActiveMono, hFinalNoWrap⟩ :=
                    mcopy_simulate hRel hFacts.2.2.1 hFacts.2.2.2.1
                      hFacts.2.2.2.2.1 hTargetNoWrap hEval
                  exact ⟨targetFinal, targetShared.toMachineState.memory,
                    hTargetEval, hShared, hMemory, hMemoryMono, hActiveMono,
                    hFinalNoWrap⟩

theorem mcopy_openForward (contract : MemoryContract.Contract) :
    AllocationInteractionPrimitive.OpenForward contract .mcopy :=
  (mcopySpec contract).openForward

theorem keccak256_simulate
    {contract : MemoryContract.Contract}
    {sourceShared sourceFinal targetShared : EvmYul.SharedState .EVM}
    {address size : Word} {outputs : List Word}
    (hRel : SharedRel contract sourceShared targetShared)
    (hAllowed :
      Simulation.MemorySafety.RegionAllowed contract address.toNat size.toNat)
    (hExpansion :
      Compiler.MemoryRelation.ExpansionNoWrap address.toNat size.toNat)
    (hHost : address.toNat + size.toNat < USize.size)
    (hTargetNoWrap :
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size)
    (hEval :
      Locals.Source.PrimitiveSemantics.structured.eval
          .keccak256 sourceShared [size, address] =
        .ok (sourceFinal, outputs)) :
    ∃ targetFinal,
      Locals.Source.PrimitiveSemantics.structured.eval
          .keccak256 targetShared [size, address] =
        .ok (targetFinal, outputs) ∧
      SharedRel contract sourceFinal targetFinal ∧
      targetFinal.toMachineState.memory = targetShared.toMachineState.memory ∧
      targetShared.toMachineState.activeWords.toNat ≤
        targetFinal.toMachineState.activeWords.toNat ∧
      targetFinal.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size := by
  obtain ⟨hRead, hMachineRel, hFinalNoWrap, hActiveMono⟩ :=
    Compiler.MemoryRelation.MachineRel.readRange_both
      hRel.machine hTargetNoWrap address.toNat size.toNat hAllowed
      hExpansion hHost
  have hValue :
      (sourceShared.toMachineState.keccak256 address size).1 =
        (targetShared.toMachineState.keccak256 address size).1 := by
    simp [EvmYul.MachineState.keccak256, hRead]
  have hSourceResult :
      sourceFinal =
          { sourceShared with
            toMachineState :=
              (sourceShared.toMachineState.keccak256 address size).2 } ∧
        outputs =
          [(sourceShared.toMachineState.keccak256 address size).1] := by
    simpa [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp, Assembly.PrimOp.continuingStep?,
      Assembly.PrimStep.run, Expressions.Structured.BasicOp.inputs,
      EvmYul.EVM.binaryMachineStateOp', EvmYul.Stack.pop2,
      EvmYul.Stack.push, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run] using hEval.symm
  rcases hSourceResult with ⟨rfl, rfl⟩
  let targetFinal : EvmYul.SharedState .EVM :=
    { targetShared with
      toMachineState :=
        (targetShared.toMachineState.keccak256 address size).2 }
  refine ⟨targetFinal, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp, Assembly.PrimOp.continuingStep?,
      Assembly.PrimStep.run, Expressions.Structured.BasicOp.inputs,
      EvmYul.EVM.binaryMachineStateOp', EvmYul.Stack.pop2,
      EvmYul.Stack.push, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run, targetFinal, hValue]
  · refine ⟨?_, ?_⟩
    · simpa [EvmYul.MachineState.keccak256, targetFinal] using hMachineRel
    · simpa [EvmYul.MachineState.keccak256, targetFinal] using hRel.world
  · simp [EvmYul.MachineState.keccak256, targetFinal]
  · simpa [EvmYul.MachineState.keccak256, targetFinal] using hActiveMono
  · simpa [EvmYul.MachineState.keccak256, targetFinal] using hFinalNoWrap

def keccak256ClosedSpec (contract : MemoryContract.Contract) :
    ClosedSpec contract .keccak256 where
  sourceStep := ⟨.binaryMachineStateWithResult EvmYul.MachineState.keccak256,
    rfl⟩
  supportsOpen := rfl
  notGas := by decide
  notMsize := by decide
  evalExists := by
    intro shared values hLength
    have hTwo : values.length = 2 := by simpa using hLength
    obtain ⟨size, address, rfl⟩ := List.length_eq_two.mp hTwo
    simp [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp, Assembly.PrimOp.continuingStep?,
      Assembly.PrimStep.run, Expressions.Structured.BasicOp.inputs,
      EvmYul.EVM.binaryMachineStateOp', EvmYul.Stack.pop2,
      EvmYul.Stack.push, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run]
  simulate := by
    intro sourceShared sourceFinal targetShared values outputs hLength hRel
      hSafe hTargetNoWrap hEval
    have hTwo : values.length = 2 := by simpa using hLength
    obtain ⟨size, address, rfl⟩ := List.length_eq_two.mp hTwo
    have hSafety :
        Compiler.MemoryRelation.MemoryConsistent sourceShared.toMachineState ∧
          Simulation.MemorySafety.RegionAllowed contract
            address.toNat size.toNat ∧
          Compiler.MemoryRelation.ExpansionNoWrap
            address.toNat size.toNat ∧
          address.toNat + size.toNat < USize.size := by
      simpa [Simulation.MemorySafety.OpenPrimitiveMemorySafe,
        Simulation.MemorySafety.PrimitiveMemorySafe,
        Simulation.MemorySafety.PrimitiveExpansionSafe,
        Simulation.MemorySafety.PrimitiveHostSafe] using hSafe
    obtain ⟨targetFinal, hTargetEval, hShared, hMemory,
        hActive, hFinalNoWrap⟩ :=
      keccak256_simulate hRel hSafety.2.1 hSafety.2.2.1
        hSafety.2.2.2 hTargetNoWrap hEval
    exact ⟨targetFinal, hTargetEval,
      targetEffect_of_memory_eq hShared hMemory hActive
        hTargetNoWrap hFinalNoWrap⟩

theorem keccak256_openForward (contract : MemoryContract.Contract) :
    AllocationInteractionPrimitive.OpenForward contract .keccak256 :=
  (keccak256ClosedSpec contract).openForward

inductive LogInvocation :
    Structured.BasicOp → List Word → Word → Word → Array Word → Prop where
  | log0 (address size : Word) :
      LogInvocation .log0 [size, address] address size #[]
  | log1 (address size topic0 : Word) :
      LogInvocation .log1 [topic0, size, address]
        address size #[topic0]
  | log2 (address size topic0 topic1 : Word) :
      LogInvocation .log2 [topic1, topic0, size, address]
        address size #[topic0, topic1]
  | log3 (address size topic0 topic1 topic2 : Word) :
      LogInvocation .log3 [topic2, topic1, topic0, size, address]
        address size #[topic0, topic1, topic2]
  | log4 (address size topic0 topic1 topic2 topic3 : Word) :
      LogInvocation .log4
        [topic3, topic2, topic1, topic0, size, address]
        address size #[topic0, topic1, topic2, topic3]

namespace LogInvocation

theorem eval
    {op : Structured.BasicOp} {values : List Word}
    {address size : Word} {topics : Array Word}
    (invocation : LogInvocation op values address size topics)
    (shared : EvmYul.SharedState .EVM) :
    Locals.Source.PrimitiveSemantics.structured.eval op shared values =
      .ok (EvmYul.SharedState.logOp address size topics shared, []) := by
  cases invocation <;>
    simp [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp, Assembly.PrimOp.continuingStep?,
      Assembly.PrimStep.run, Expressions.Structured.BasicOp.inputs,
      EvmYul.Stack.pop2, EvmYul.Stack.pop3, EvmYul.Stack.pop4,
      EvmYul.Stack.pop5, EvmYul.Stack.pop6,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run]

theorem memorySafe
    {contract : MemoryContract.Contract}
    {op : Structured.BasicOp} {values : List Word}
    {address size : Word} {topics : Array Word}
    (invocation : LogInvocation op values address size topics)
    {machine : EvmYul.MachineState}
    (hSafe :
      Simulation.MemorySafety.OpenPrimitiveMemorySafe
        contract op machine values) :
    Compiler.MemoryRelation.MemoryConsistent machine ∧
      Simulation.MemorySafety.RegionAllowed contract
        address.toNat size.toNat ∧
      Compiler.MemoryRelation.ExpansionNoWrap
        address.toNat size.toNat ∧
      address.toNat + size.toNat < USize.size := by
  cases invocation <;>
    simpa [Simulation.MemorySafety.OpenPrimitiveMemorySafe,
      Simulation.MemorySafety.PrimitiveMemorySafe,
      Simulation.MemorySafety.PrimitiveExpansionSafe,
      Simulation.MemorySafety.PrimitiveHostSafe] using hSafe

end LogInvocation

theorem logOp_both
    {contract : MemoryContract.Contract}
    {source target : EvmYul.SharedState .EVM}
    (hRel : SharedRel contract source target)
    (address size : Word) (topics : Array Word)
    (hAllowed :
      Simulation.MemorySafety.RegionAllowed contract address.toNat size.toNat)
    (hExpansion :
      Compiler.MemoryRelation.ExpansionNoWrap address.toNat size.toNat)
    (hHost : address.toNat + size.toNat < USize.size)
    (hTargetNoWrap :
      target.toMachineState.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size) :
    SharedRel contract
        (EvmYul.SharedState.logOp address size topics source)
        (EvmYul.SharedState.logOp address size topics target) ∧
      (EvmYul.SharedState.logOp address size topics target).toMachineState.memory =
        target.toMachineState.memory ∧
      target.toMachineState.activeWords.toNat ≤
        (EvmYul.SharedState.logOp
          address size topics target).toMachineState.activeWords.toNat ∧
      (EvmYul.SharedState.logOp
          address size topics target).toMachineState.activeWords.toNat *
            MemoryContract.wordBytes < EvmYul.UInt256.size := by
  obtain ⟨hRead, hMachineRel, hFinalNoWrap, hActiveMono⟩ :=
    Compiler.MemoryRelation.MachineRel.readRange_both
      hRel.machine hTargetNoWrap address.toNat size.toNat hAllowed
      hExpansion hHost
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simpa [EvmYul.SharedState.logOp] using hMachineRel
    · change
        { source.toState with
            substate.logSeries :=
              source.toState.substate.logSeries.push
                ⟨source.executionEnv.codeOwner, topics,
                  source.memory.readWithPadding address.toNat size.toNat⟩ } =
          { target.toState with
            substate.logSeries :=
              target.toState.substate.logSeries.push
                ⟨target.executionEnv.codeOwner, topics,
                  target.memory.readWithPadding address.toNat size.toNat⟩ }
      rw [hRel.world, hRead]
  · simp [EvmYul.SharedState.logOp]
  · simpa [EvmYul.SharedState.logOp] using hActiveMono
  · simpa [EvmYul.SharedState.logOp] using hFinalNoWrap

inductive LogFamily : Structured.BasicOp → Prop where
  | log0 : LogFamily .log0
  | log1 : LogFamily .log1
  | log2 : LogFamily .log2
  | log3 : LogFamily .log3
  | log4 : LogFamily .log4

namespace LogFamily

theorem invocation_of_length
    {op : Structured.BasicOp} (family : LogFamily op)
    (values : List Word)
    (hLength : values.length = Expressions.Structured.BasicOp.inputs op) :
    ∃ address size topics, LogInvocation op values address size topics := by
  cases family with
  | log0 =>
      obtain ⟨size, address, rfl⟩ :=
        List.length_eq_two.mp (by simpa using hLength)
      exact ⟨address, size, #[], .log0 address size⟩
  | log1 =>
      obtain ⟨topic0, size, address, rfl⟩ :=
        List.length_eq_three.mp (by simpa using hLength)
      exact ⟨address, size, #[topic0], .log1 address size topic0⟩
  | log2 =>
      obtain ⟨topic1, topic0, size, address, rfl⟩ :=
        List.length_eq_four.mp (by simpa using hLength)
      exact
        ⟨address, size, #[topic0, topic1],
          .log2 address size topic0 topic1⟩
  | log3 =>
      cases values with
      | nil =>
          simp [Expressions.Structured.BasicOp.inputs] at hLength
      | cons topic2 rest =>
          have hRest : rest.length = 4 := by
            simpa [Expressions.Structured.BasicOp.inputs] using hLength
          obtain ⟨topic1, topic0, size, address, rfl⟩ :=
            List.length_eq_four.mp hRest
          exact
            ⟨address, size, #[topic0, topic1, topic2],
              .log3 address size topic0 topic1 topic2⟩
  | log4 =>
      cases values with
      | nil =>
          simp [Expressions.Structured.BasicOp.inputs] at hLength
      | cons topic3 rest =>
          cases rest with
          | nil =>
              simp [Expressions.Structured.BasicOp.inputs] at hLength
          | cons topic2 tail =>
              have hTail : tail.length = 4 := by
                simpa [Expressions.Structured.BasicOp.inputs] using hLength
              obtain ⟨topic1, topic0, size, address, rfl⟩ :=
                List.length_eq_four.mp hTail
              exact
                ⟨address, size, #[topic0, topic1, topic2, topic3],
                  .log4 address size topic0 topic1 topic2 topic3⟩

theorem sourceStep
    {op : Structured.BasicOp} (family : LogFamily op) :
    ∃ step,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep? op = some step := by
  cases family with
  | log0 => exact ⟨.log0, rfl⟩
  | log1 => exact ⟨.log1, rfl⟩
  | log2 => exact ⟨.log2, rfl⟩
  | log3 => exact ⟨.log3, rfl⟩
  | log4 => exact ⟨.log4, rfl⟩

theorem simulate
    {contract : MemoryContract.Contract} {op : Structured.BasicOp}
    (family : LogFamily op)
    {sourceShared sourceFinal targetShared : EvmYul.SharedState .EVM}
    {values outputs : List Word}
    (hLength : values.length = Expressions.Structured.BasicOp.inputs op)
    (hRel : SharedRel contract sourceShared targetShared)
    (hSafe :
      Simulation.MemorySafety.OpenPrimitiveMemorySafe
        contract op sourceShared.toMachineState values)
    (hTargetNoWrap :
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size)
    (hEval :
      Locals.Source.PrimitiveSemantics.structured.eval
          op sourceShared values = .ok (sourceFinal, outputs)) :
    ∃ targetFinal,
      Locals.Source.PrimitiveSemantics.structured.eval
          op targetShared values = .ok (targetFinal, outputs) ∧
      SharedRel contract sourceFinal targetFinal ∧
      targetFinal.toMachineState.memory = targetShared.toMachineState.memory ∧
      targetShared.toMachineState.activeWords.toNat ≤
        targetFinal.toMachineState.activeWords.toNat ∧
      targetFinal.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size := by
  obtain ⟨address, size, topics, invocation⟩ :=
    family.invocation_of_length values hLength
  obtain ⟨_hConsistent, hAllowed, hExpansion, hHost⟩ :=
    invocation.memorySafe hSafe
  have hSourceCanonical := invocation.eval sourceShared
  rw [hSourceCanonical] at hEval
  cases hEval
  obtain ⟨hShared, hMemory, hActive, hNoWrap⟩ :=
    logOp_both hRel address size topics hAllowed hExpansion hHost
      hTargetNoWrap
  exact
    ⟨EvmYul.SharedState.logOp address size topics targetShared,
      invocation.eval targetShared, hShared, hMemory, hActive, hNoWrap⟩

def closedSpec
    {op : Structured.BasicOp} (family : LogFamily op)
    (contract : MemoryContract.Contract) : ClosedSpec contract op where
  sourceStep := family.sourceStep
  supportsOpen := by cases family <;> rfl
  notGas := by cases family <;> decide
  notMsize := by cases family <;> decide
  evalExists := by
    intro shared values hLength
    obtain ⟨address, size, topics, invocation⟩ :=
      family.invocation_of_length values hLength
    exact ⟨EvmYul.SharedState.logOp address size topics shared, [],
      invocation.eval shared⟩
  simulate := by
    intro sourceShared sourceFinal targetShared values outputs hLength hRel
      hSafe hTargetNoWrap hEval
    obtain ⟨targetFinal, hTargetEval, hShared, hMemory,
        hActive, hFinalNoWrap⟩ :=
      family.simulate hLength hRel hSafe hTargetNoWrap hEval
    exact ⟨targetFinal, hTargetEval,
      targetEffect_of_memory_eq hShared hMemory hActive
        hTargetNoWrap hFinalNoWrap⟩

theorem openForward
    {op : Structured.BasicOp} (family : LogFamily op)
    (contract : MemoryContract.Contract) :
    AllocationInteractionPrimitive.OpenForward contract op :=
  (family.closedSpec contract).openForward

end LogFamily

end MemoryFamily

/-- Complete open capability for every primitive admitted by source semantics. -/
theorem canonicalOpenForward
    (contract : MemoryContract.Contract) (op : Structured.BasicOp)
    (hSupported :
      Locals.InteractionSemantics.Primitive.supportsOpen op = true) :
    AllocationInteractionPrimitive.OpenForward contract op := by
  cases op <;>
    first
    | exact ResourceFamily.gas.openForward contract
    | exact ResourceFamily.msize.openForward contract
    | exact MemoryFamily.mload_openForward contract
    | exact MemoryFamily.mstore_openForward contract
    | exact MemoryFamily.mstore8_openForward contract
    | exact MemoryFamily.calldatacopy_openForward contract
    | exact MemoryFamily.codecopy_openForward contract
    | exact MemoryFamily.returndatacopy_openForward contract
    | exact MemoryFamily.extcodecopy_openForward contract
    | exact MemoryFamily.mcopy_openForward contract
    | exact MemoryFamily.keccak256_openForward contract
    | exact MemoryFamily.LogFamily.log0.openForward contract
    | exact MemoryFamily.LogFamily.log1.openForward contract
    | exact MemoryFamily.LogFamily.log2.openForward contract
    | exact MemoryFamily.LogFamily.log3.openForward contract
    | exact MemoryFamily.LogFamily.log4.openForward contract
    | exact AllocationInteractionPrimitive.call_openForward contract .call
    | exact AllocationInteractionPrimitive.call_openForward contract .callcode
    | exact AllocationInteractionPrimitive.call_openForward contract .delegatecall
    | exact AllocationInteractionPrimitive.call_openForward contract .staticcall
    | exact AllocationInteractionPrimitive.create_openForward contract .create
    | exact AllocationInteractionPrimitive.create_openForward contract .create2
    | exact SharedFamily.openForward (.bin _ rfl) contract
    | exact SharedFamily.openForward (.un _ rfl) contract
    | exact SharedFamily.openForward (.tri _ rfl) contract
    | exact SharedFamily.openForward (.pop rfl) contract
    | exact SharedFamily.openForward (.executionEnv _ rfl) contract
    | exact SharedFamily.openForward (.unaryExecutionEnv _ rfl) contract
    | exact SharedFamily.openForward (.state _ rfl) contract
    | exact SharedFamily.openForward (.unaryState _ rfl) contract
    | exact SharedFamily.openForward (.binaryState _ rfl) contract
    | exact SharedFamily.openForward .returnDataSize contract
    | (simp [Locals.InteractionSemantics.Primitive.supportsOpen] at hSupported)

end AllocationInteractionOrdinaryPrimitive
end Functions
end EvmCompiler
