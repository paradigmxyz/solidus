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
end AllocationInteractionOrdinaryPrimitive
end Functions
end EvmCompiler
