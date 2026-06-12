import EvmCompiler.Functions.AllocationObserverExpression
import EvmCompiler.Locals.PrimitivePreservation

namespace EvmCompiler
namespace Functions
namespace AllocationObserverPrimitive

abbrev Word := Assembly.Word

open AllocationObserverRelation

/--
Proof classifier for canonical primitive families that do not inspect or modify
EVM memory. State operations may read or update the world; `returndatasize`
reads the machine state's return-data buffer, which `MachineRel` equates.

This is evidence about the existing `sourceContinuingStep?` classifier, not a
second primitive interpreter.
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
      (f : EvmYul.State .EVM → Word →
        EvmYul.State .EVM × Word)
      (step :
        Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
          some (.unaryState f)) :
      SharedFamily op
  | binaryState {op : Structured.BasicOp}
      (f : EvmYul.State .EVM → Word → Word →
        EvmYul.State .EVM)
      (step :
        Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
          some (.binaryState f)) :
      SharedFamily op
  | returnDataSize :
      SharedFamily .returndatasize

namespace SharedFamily

theorem observer_none
    {op : Structured.BasicOp}
    (family : SharedFamily op) :
    Functions.ObserverSemantics.basicOpObserver? op = none := by
  cases family
  case returnDataSize =>
    rfl
  all_goals
    cases op <;>
      simp [Functions.ObserverSemantics.basicOpObserver?,
        Locals.ObserverSemantics.basicOpObserver?,
        Structured.BasicOp.toPrimOp,
        Assembly.ResourceObserver.ofPrimOp?,
        Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
        Assembly.PrimOp.continuingStep?] at *

/--
Canonical stack-free primitive evaluation preserves the allocation shared-state
relation for every non-memory semantic family. The target machine state itself
is unchanged, preserving the active spill frame.
-/
theorem simulate
    {contract : MemoryContract.Contract}
    {op : Structured.BasicOp}
    {sourceShared sourceFinal targetShared :
      EvmYul.SharedState .EVM}
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
        | none =>
            simp [hPop] at hEval
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
        | none =>
            simp [hPop] at hEval
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
        | none =>
            simp [hPop] at hEval
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
        | none =>
            simp [hPop] at hEval
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
        | none =>
            simp [hPop] at hEval
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
      have hWorld :
          targetShared.toState = sourceShared.toState :=
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
      have hWorld :
          targetShared.toState = sourceShared.toState :=
        hRel.world.symm
      dsimp [Locals.Source.PrimitiveSemantics.structured] at hEval ⊢
      by_cases hLength :
          values.length = Expressions.Structured.BasicOp.inputs op
      · simp [hLength, hStep, Assembly.PrimStep.run,
          EvmYul.EVM.unaryStateOp] at hEval ⊢
        cases hPop : EvmYul.Stack.pop values.reverse with
        | none =>
            simp [hPop] at hEval
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
      have hWorld :
          targetShared.toState = sourceShared.toState :=
        hRel.world.symm
      dsimp [Locals.Source.PrimitiveSemantics.structured] at hEval ⊢
      by_cases hLength :
          values.length = Expressions.Structured.BasicOp.inputs op
      · simp [hLength, hStep, Assembly.PrimStep.run,
          EvmYul.EVM.binaryStateOp] at hEval ⊢
        cases hPop : EvmYul.Stack.pop2 values.reverse with
        | none =>
            simp [hPop] at hEval
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
        simp [EvmYul.MachineState.returndatasize,
          hRel.machine.returnData]
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

theorem primitiveForward
    {contract : MemoryContract.Contract}
    {op : Structured.BasicOp}
    (family : SharedFamily op) :
    AllocationObserverExpression.PrimitiveForward contract op where
  simulate := by
    intro transcript plan live stackOffset frameBase frameDepth frameWords
      sourceArgs sourceFinal targetInitial targetArgs values outputs
      hArgsRel _hMemory hPrimitive
    have hObserver := family.observer_none
    cases hSourceEval :
        Locals.Source.PrimitiveSemantics.structured.eval
          op sourceArgs.source.shared values with
    | error err =>
        simp [Functions.ObserverSemantics.primitiveSemantics,
          Locals.ObserverSemantics.primitiveSemantics,
          hObserver, hSourceEval] at hPrimitive
    | ok result =>
        rcases result with ⟨sourceSharedFinal, canonicalOutputs⟩
        have hPrimitiveResult :
            sourceArgs.withSource
                (sourceArgs.source.withShared sourceSharedFinal) =
              sourceFinal ∧
            canonicalOutputs = outputs := by
          simpa [Functions.ObserverSemantics.primitiveSemantics,
            Locals.ObserverSemantics.primitiveSemantics,
            hObserver, hSourceEval] using hPrimitive
        rcases hPrimitiveResult with ⟨rfl, rfl⟩
        obtain
            ⟨targetSharedFinal, hTargetEval, hSharedFinal,
              hTargetMachine⟩ :=
          family.simulate hArgsRel.state.base.core.shared hSourceEval
        obtain ⟨evmFinal, hStep, hEvmShared, hEvmStack⟩ :=
          Locals.Source.PrimitiveSemantics.structured_eval_step_exists
            hTargetEval rfl hArgsRel.stack
        let targetFinal :
            Structured.ObserverSemantics.State transcript :=
          targetArgs.withSource
            (targetArgs.source.withEVM evmFinal)
        have hRun :
            Structured.ObserverSemantics.Code.run [.op op] targetArgs =
              .ok targetFinal := by
          change
            Structured.ObserverSemantics.basicOpObserver? op = none
            at hObserver
          simp [Structured.ObserverSemantics.Code.run,
            Structured.EffectSemantics.Code.run,
            Structured.BasicInstr.step, hStep,
            Structured.ObserverSemantics.handler, hObserver,
            targetFinal]
        have hOutputsLength :
            canonicalOutputs.length =
              Expressions.Structured.BasicOp.outputs op :=
          Locals.Source.PrimitiveSemantics.structured_eval_length
            hSourceEval
        have hMachine :
            targetFinal.source.evm.toMachineState =
              targetArgs.source.evm.toMachineState := by
          change
            evmFinal.toMachineState =
              targetArgs.source.evm.toMachineState
          have hFinalMachine :
              evmFinal.toMachineState =
                targetSharedFinal.toMachineState :=
            congrArg EvmYul.SharedState.toMachineState hEvmShared
          exact hFinalMachine.trans hTargetMachine
        have hFinalStack :
            targetFinal.source.evm.stack =
              canonicalOutputs.reverse ++
                targetInitial.source.evm.stack := by
          simpa [targetFinal] using hEvmStack
        have hBaseRel :
            StateRel contract plan live
              (stackOffset + canonicalOutputs.length) frameBase
              (sourceArgs.withSource
                (sourceArgs.source.withShared sourceSharedFinal))
              targetFinal := by
          refine ⟨?_, ?_⟩
          · simpa [targetFinal] using hArgsRel.state.base.cursor
          · refine ⟨?_, ?_, ?_⟩
            · simpa [targetFinal, hEvmShared] using
                hSharedFinal.machine
            · simpa [targetFinal, hEvmShared] using
                hSharedFinal.world
            · have hOldStore :
                  StoreRel plan live
                    (stackOffset + values.reverse.length) frameBase
                    sourceArgs.source targetArgs.source := by
                simpa [List.length_reverse, hArgsRel.valuesLength] using
                  hArgsRel.state.base.core.store
              have hNewStore :=
                StoreRel.rebase_prefix
                  (oldPrefix := values.reverse)
                  (newPrefix := canonicalOutputs.reverse)
                  (baseStack := targetInitial.source.evm.stack)
                  hOldStore hArgsRel.stack hFinalStack hMachine rfl
              simpa [List.length_reverse] using hNewStore
        have hScratchRel :
            ScratchStateRel contract plan live
              (stackOffset + canonicalOutputs.length) frameBase
              frameDepth frameWords
              (sourceArgs.withSource
                (sourceArgs.source.withShared sourceSharedFinal))
              targetFinal := by
          have hOldScratch :
              ScratchStateRel contract plan live
                (stackOffset + values.reverse.length) frameBase
                frameDepth frameWords sourceArgs targetArgs := by
            simpa [List.length_reverse, hArgsRel.valuesLength] using
              hArgsRel.state
          have hBaseRaw :
              StateRel contract plan live
                (stackOffset + canonicalOutputs.reverse.length) frameBase
                (sourceArgs.withSource
                  (sourceArgs.source.withShared sourceSharedFinal))
                targetFinal := by
            simpa [List.length_reverse] using hBaseRel
          have hScratchRaw :=
            ScratchStateRel.rebase_prefix
              (oldPrefix := values.reverse)
              (newPrefix := canonicalOutputs.reverse)
              (baseStack := targetInitial.source.evm.stack)
              hOldScratch hBaseRaw hArgsRel.stack hFinalStack hMachine
          simpa [List.length_reverse] using hScratchRaw
        refine ⟨targetFinal, hRun, ?_, hOutputsLength, hFinalStack⟩
        simpa [hOutputsLength] using hScratchRel

end SharedFamily

/--
Shared-state simulation contract sufficient for a stack-only activation.

Scratch preservation is intentionally absent: `StackPrimitiveForward` uses the
planner fact that every live local is stack-resident. Existing semantic-family
proofs instantiate this contract by forgetting their stronger memory-growth
results.
-/
structure StackSpec (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) : Prop where
  observerNone :
    Functions.ObserverSemantics.basicOpObserver? op = none
  simulate :
    ∀ {sourceShared sourceFinal targetShared :
        EvmYul.SharedState .EVM}
      {values outputs : List Word},
      values.length = Expressions.Structured.BasicOp.inputs op →
      SharedRel contract sourceShared targetShared →
      AllocationObserverSafety.PrimitiveMemorySafe
        contract op sourceShared.toMachineState values →
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size →
      Locals.Source.PrimitiveSemantics.structured.eval
          op sourceShared values =
        .ok (sourceFinal, outputs) →
      ∃ targetFinal,
        Locals.Source.PrimitiveSemantics.structured.eval
            op targetShared values =
          .ok (targetFinal, outputs) ∧
        SharedRel contract sourceFinal targetFinal ∧
        targetFinal.toMachineState.activeWords.toNat *
            MemoryContract.wordBytes <
          EvmYul.UInt256.size

/--
One stack-only primitive theorem from a shared-state semantic-family proof.

The only local-allocation reasoning is `StoreRel.rebase_prefix_stack_only`;
individual opcodes do not know about layouts or spill slots.
-/
theorem stack_primitiveForward
    {contract : MemoryContract.Contract}
    {op : Structured.BasicOp}
    (spec : StackSpec contract op) :
    AllocationObserverExpression.StackPrimitiveForward contract op where
  simulate := by
    intro transcript plan live stackOffset frameBase
      sourceArgs sourceFinal targetInitial targetArgs values outputs
      hOnly hActiveNoWrap hArgsRel hMemory hPrimitive
    cases hSourceEval :
        Locals.Source.PrimitiveSemantics.structured.eval
          op sourceArgs.source.shared values with
    | error err =>
        simp [Functions.ObserverSemantics.primitiveSemantics,
          Locals.ObserverSemantics.primitiveSemantics,
          spec.observerNone, hSourceEval] at hPrimitive
    | ok result =>
        rcases result with ⟨sourceSharedFinal, canonicalOutputs⟩
        have hPrimitiveResult :
            sourceArgs.withSource
                (sourceArgs.source.withShared sourceSharedFinal) =
              sourceFinal ∧
            canonicalOutputs = outputs := by
          simpa [Functions.ObserverSemantics.primitiveSemantics,
            Locals.ObserverSemantics.primitiveSemantics,
            spec.observerNone, hSourceEval] using hPrimitive
        rcases hPrimitiveResult with ⟨rfl, rfl⟩
        obtain
            ⟨targetSharedFinal, hTargetEval,
              hSharedFinal, hFinalNoWrap⟩ :=
          spec.simulate hArgsRel.valuesLength
            hArgsRel.state.core.shared hMemory
            hActiveNoWrap hSourceEval
        obtain ⟨evmFinal, hStep, hEvmShared, hEvmStack⟩ :=
          Locals.Source.PrimitiveSemantics.structured_eval_step_exists
            hTargetEval rfl hArgsRel.stack
        let targetFinal :
            Structured.ObserverSemantics.State transcript :=
          targetArgs.withSource
            (targetArgs.source.withEVM evmFinal)
        have hRun :
            Structured.ObserverSemantics.Code.run [.op op] targetArgs =
              .ok targetFinal := by
          have hObserver := spec.observerNone
          change
            Structured.ObserverSemantics.basicOpObserver? op = none
            at hObserver
          simp [Structured.ObserverSemantics.Code.run,
            Structured.EffectSemantics.Code.run,
            Structured.BasicInstr.step, hStep,
            Structured.ObserverSemantics.handler,
            hObserver, targetFinal]
        have hOutputsLength :
            canonicalOutputs.length =
              Expressions.Structured.BasicOp.outputs op :=
          Locals.Source.PrimitiveSemantics.structured_eval_length
            hSourceEval
        have hFinalStack :
            targetFinal.source.evm.stack =
              canonicalOutputs.reverse ++
                targetInitial.source.evm.stack := by
          simpa [targetFinal] using hEvmStack
        have hOldStore :
            StoreRel plan live
              (stackOffset + values.reverse.length) frameBase
              sourceArgs.source targetArgs.source := by
          simpa [List.length_reverse, hArgsRel.valuesLength] using
            hArgsRel.state.core.store
        have hVars :
            (sourceArgs.withSource
                (sourceArgs.source.withShared sourceSharedFinal)).source.vars =
              sourceArgs.source.vars := by
          exact
            Locals.ObserverSemantics.primitiveSemantics_eval_vars_eq
              hPrimitive
        have hBaseRel :
            StateRel contract plan live
              (stackOffset + canonicalOutputs.reverse.length) frameBase
              (sourceArgs.withSource
                (sourceArgs.source.withShared sourceSharedFinal))
              targetFinal := by
          refine ⟨?_, ?_⟩
          · simpa [targetFinal] using hArgsRel.state.cursor
          · refine ⟨?_, ?_, ?_⟩
            · simpa [targetFinal, hEvmShared] using
                hSharedFinal.machine
            · simpa [targetFinal, hEvmShared] using
                hSharedFinal.world
            · exact
                StoreRel.rebase_prefix_stack_only
                  hOnly hOldStore hArgsRel.stack hFinalStack hVars
        refine
          ⟨targetFinal, hRun, ?_, ?_,
            hOutputsLength, hFinalStack⟩
        · simpa [targetFinal, hEvmShared] using hFinalNoWrap
        · simpa [List.length_reverse, hOutputsLength] using hBaseRel

def SharedFamily.stackSpec
    {contract : MemoryContract.Contract}
    {op : Structured.BasicOp}
    (family : SharedFamily op) :
    StackSpec contract op where
  observerNone := family.observer_none
  simulate := by
    intro sourceShared sourceFinal targetShared values outputs
      _hLength hRel _hMemory hTargetNoWrap hEval
    obtain ⟨targetFinal, hTarget, hFinal, hMachine⟩ :=
      family.simulate hRel hEval
    exact
      ⟨targetFinal, hTarget, hFinal,
        by simpa [hMachine] using hTargetNoWrap⟩

theorem SharedFamily.stackPrimitiveForward
    {contract : MemoryContract.Contract}
    {op : Structured.BasicOp}
    (family : SharedFamily op) :
    AllocationObserverExpression.StackPrimitiveForward contract op :=
  stack_primitiveForward family.stackSpec

namespace MemoryFamily

/--
Canonical `keccak256` reads the same source-approved byte range in related
machines, returns the same digest, and preserves the active spill frame.
-/
theorem keccak256_simulate
    {contract : MemoryContract.Contract}
    {sourceShared sourceFinal targetShared :
      EvmYul.SharedState .EVM}
    {address size : Word} {outputs : List Word}
    (hRel : SharedRel contract sourceShared targetShared)
    (hAllowed :
      match contract.scratch? with
      | none => True
      | some reservation =>
          reservation.sourceAccessAllowed address.toNat size.toNat)
    (hExpansion :
      Compiler.MemoryRelation.ExpansionNoWrap
        address.toNat size.toNat)
    (hHost : address.toNat + size.toNat < USize.size)
    (hTargetNoWrap :
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (hEval :
      Locals.Source.PrimitiveSemantics.structured.eval
          .keccak256 sourceShared [size, address] =
        .ok (sourceFinal, outputs)) :
    ∃ targetFinal,
      Locals.Source.PrimitiveSemantics.structured.eval
          .keccak256 targetShared [size, address] =
        .ok (targetFinal, outputs) ∧
      SharedRel contract sourceFinal targetFinal ∧
      targetFinal.toMachineState.memory =
        targetShared.toMachineState.memory ∧
      targetShared.toMachineState.activeWords.toNat ≤
        targetFinal.toMachineState.activeWords.toNat ∧
      targetFinal.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
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
      Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      Expressions.Structured.BasicOp.inputs,
      EvmYul.EVM.binaryMachineStateOp', EvmYul.Stack.pop2,
      EvmYul.Stack.push,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run] using hEval.symm
  rcases hSourceResult with ⟨rfl, rfl⟩
  let targetFinal : EvmYul.SharedState .EVM :=
    { targetShared with
      toMachineState :=
        (targetShared.toMachineState.keccak256 address size).2 }
  refine ⟨targetFinal, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      Expressions.Structured.BasicOp.inputs,
      EvmYul.EVM.binaryMachineStateOp', EvmYul.Stack.pop2,
      EvmYul.Stack.push,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run, targetFinal, hValue]
  · refine ⟨?_, ?_⟩
    · simpa [EvmYul.MachineState.keccak256, targetFinal] using hMachineRel
    · simpa [EvmYul.MachineState.keccak256, targetFinal] using hRel.world
  · simp [EvmYul.MachineState.keccak256, targetFinal]
  · simpa [EvmYul.MachineState.keccak256, targetFinal] using hActiveMono
  · simpa [EvmYul.MachineState.keccak256, targetFinal] using hFinalNoWrap

/--
The canonical Functions argument list for one logging primitive.

Functions values are reversed before the concrete EVM primitive runs, so topic
arguments appear in reverse order here while `topics` records their EVM order.
-/
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
      Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      Expressions.Structured.BasicOp.inputs,
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
      AllocationObserverSafety.PrimitiveMemorySafe
        contract op machine values) :
    Compiler.MemoryRelation.MemoryConsistent machine ∧
      AllocationObserverSafety.RegionAllowed contract
        address.toNat size.toNat ∧
      Compiler.MemoryRelation.ExpansionNoWrap
        address.toNat size.toNat ∧
      address.toNat + size.toNat < USize.size := by
  cases invocation <;>
    simpa [AllocationObserverSafety.PrimitiveMemorySafe,
      AllocationObserverSafety.PrimitiveExpansionSafe,
      AllocationObserverSafety.PrimitiveHostSafe] using hSafe

end LogInvocation

/--
Appending one log entry preserves the allocation relation when its data range
is source-approved. Both states append the same address, topics, and bytes;
only their already-related active-memory counters may differ.
-/
theorem logOp_both
    {contract : MemoryContract.Contract}
    {source target : EvmYul.SharedState .EVM}
    (hRel : SharedRel contract source target)
    (address size : Word) (topics : Array Word)
    (hAllowed :
      match contract.scratch? with
      | none => True
      | some reservation =>
          reservation.sourceAccessAllowed address.toNat size.toNat)
    (hExpansion :
      Compiler.MemoryRelation.ExpansionNoWrap
        address.toNat size.toNat)
    (hHost : address.toNat + size.toNat < USize.size)
    (hTargetNoWrap :
      target.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes <
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
            MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
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
                  source.memory.readWithPadding
                    address.toNat size.toNat⟩ } =
          { target.toState with
            substate.logSeries :=
              target.toState.substate.logSeries.push
                ⟨target.executionEnv.codeOwner, topics,
                  target.memory.readWithPadding
                    address.toNat size.toNat⟩ }
      rw [hRel.world, hRead]
  · simp [EvmYul.SharedState.logOp]
  · simpa [EvmYul.SharedState.logOp] using hActiveMono
  · simpa [EvmYul.SharedState.logOp] using hFinalNoWrap

/--
Canonical log forms admitted by the no-external-effects primitive boundary.
-/
inductive LogFamily : Structured.BasicOp → Prop where
  | log0 : LogFamily .log0
  | log1 : LogFamily .log1
  | log2 : LogFamily .log2
  | log3 : LogFamily .log3
  | log4 : LogFamily .log4

namespace LogFamily

theorem observer_none
    {op : Structured.BasicOp}
    (family : LogFamily op) :
    Functions.ObserverSemantics.basicOpObserver? op = none := by
  cases family <;> rfl

theorem invocation_of_eval
    {op : Structured.BasicOp}
    (family : LogFamily op)
    {shared final : EvmYul.SharedState .EVM}
    {values outputs : List Word}
    (hEval :
      Locals.Source.PrimitiveSemantics.structured.eval
          op shared values =
        .ok (final, outputs)) :
    ∃ address size topics,
      LogInvocation op values address size topics := by
  cases family with
  | log0 =>
      cases values with
      | nil =>
          simp [Locals.Source.PrimitiveSemantics.structured,
            Expressions.Structured.BasicOp.inputs] at hEval
      | cons size rest =>
          cases rest with
          | nil =>
              simp [Locals.Source.PrimitiveSemantics.structured,
                Expressions.Structured.BasicOp.inputs] at hEval
          | cons address tail =>
              cases tail with
              | nil => exact ⟨address, size, #[], .log0 address size⟩
              | cons extra more =>
                  simp [Locals.Source.PrimitiveSemantics.structured,
                    Expressions.Structured.BasicOp.inputs] at hEval
  | log1 =>
      cases values with
      | nil =>
          simp [Locals.Source.PrimitiveSemantics.structured,
            Expressions.Structured.BasicOp.inputs] at hEval
      | cons topic0 rest =>
          cases rest with
          | nil =>
              simp [Locals.Source.PrimitiveSemantics.structured,
                Expressions.Structured.BasicOp.inputs] at hEval
          | cons size rest =>
              cases rest with
              | nil =>
                  simp [Locals.Source.PrimitiveSemantics.structured,
                    Expressions.Structured.BasicOp.inputs] at hEval
              | cons address tail =>
                  cases tail with
                  | nil =>
                      exact
                        ⟨address, size, #[topic0],
                          .log1 address size topic0⟩
                  | cons extra more =>
                      simp [Locals.Source.PrimitiveSemantics.structured,
                        Expressions.Structured.BasicOp.inputs] at hEval
  | log2 =>
      cases values with
      | nil =>
          simp [Locals.Source.PrimitiveSemantics.structured,
            Expressions.Structured.BasicOp.inputs] at hEval
      | cons topic1 rest =>
          cases rest with
          | nil =>
              simp [Locals.Source.PrimitiveSemantics.structured,
                Expressions.Structured.BasicOp.inputs] at hEval
          | cons topic0 rest =>
              cases rest with
              | nil =>
                  simp [Locals.Source.PrimitiveSemantics.structured,
                    Expressions.Structured.BasicOp.inputs] at hEval
              | cons size rest =>
                  cases rest with
                  | nil =>
                      simp [Locals.Source.PrimitiveSemantics.structured,
                        Expressions.Structured.BasicOp.inputs] at hEval
                  | cons address tail =>
                      cases tail with
                      | nil =>
                          exact
                            ⟨address, size, #[topic0, topic1],
                              .log2 address size topic0 topic1⟩
                      | cons extra more =>
                          simp [Locals.Source.PrimitiveSemantics.structured,
                            Expressions.Structured.BasicOp.inputs] at hEval
  | log3 =>
      cases values with
      | nil =>
          simp [Locals.Source.PrimitiveSemantics.structured,
            Expressions.Structured.BasicOp.inputs] at hEval
      | cons topic2 rest =>
          cases rest with
          | nil =>
              simp [Locals.Source.PrimitiveSemantics.structured,
                Expressions.Structured.BasicOp.inputs] at hEval
          | cons topic1 rest =>
              cases rest with
              | nil =>
                  simp [Locals.Source.PrimitiveSemantics.structured,
                    Expressions.Structured.BasicOp.inputs] at hEval
              | cons topic0 rest =>
                  cases rest with
                  | nil =>
                      simp [Locals.Source.PrimitiveSemantics.structured,
                        Expressions.Structured.BasicOp.inputs] at hEval
                  | cons size rest =>
                      cases rest with
                      | nil =>
                          simp [Locals.Source.PrimitiveSemantics.structured,
                            Expressions.Structured.BasicOp.inputs] at hEval
                      | cons address tail =>
                          cases tail with
                          | nil =>
                              exact
                                ⟨address, size, #[topic0, topic1, topic2],
                                  .log3 address size topic0 topic1 topic2⟩
                          | cons extra more =>
                              simp [Locals.Source.PrimitiveSemantics.structured,
                                Expressions.Structured.BasicOp.inputs] at hEval
  | log4 =>
      cases values with
      | nil =>
          simp [Locals.Source.PrimitiveSemantics.structured,
            Expressions.Structured.BasicOp.inputs] at hEval
      | cons topic3 rest =>
          cases rest with
          | nil =>
              simp [Locals.Source.PrimitiveSemantics.structured,
                Expressions.Structured.BasicOp.inputs] at hEval
          | cons topic2 rest =>
              cases rest with
              | nil =>
                  simp [Locals.Source.PrimitiveSemantics.structured,
                    Expressions.Structured.BasicOp.inputs] at hEval
              | cons topic1 rest =>
                  cases rest with
                  | nil =>
                      simp [Locals.Source.PrimitiveSemantics.structured,
                        Expressions.Structured.BasicOp.inputs] at hEval
                  | cons topic0 rest =>
                      cases rest with
                      | nil =>
                          simp [Locals.Source.PrimitiveSemantics.structured,
                            Expressions.Structured.BasicOp.inputs] at hEval
                      | cons size rest =>
                          cases rest with
                          | nil =>
                              simp [Locals.Source.PrimitiveSemantics.structured,
                                Expressions.Structured.BasicOp.inputs] at hEval
                          | cons address tail =>
                              cases tail with
                              | nil =>
                                  exact
                                    ⟨address, size,
                                      #[topic0, topic1, topic2, topic3],
                                      .log4 address size topic0 topic1
                                        topic2 topic3⟩
                              | cons extra more =>
                                  simp
                                    [Locals.Source.PrimitiveSemantics.structured,
                                      Expressions.Structured.BasicOp.inputs]
                                    at hEval

theorem simulate
    {contract : MemoryContract.Contract}
    {op : Structured.BasicOp}
    (family : LogFamily op)
    {sourceShared sourceFinal targetShared :
      EvmYul.SharedState .EVM}
    {values outputs : List Word}
    (hRel : SharedRel contract sourceShared targetShared)
    (hSafe :
      AllocationObserverSafety.PrimitiveMemorySafe
        contract op sourceShared.toMachineState values)
    (hTargetNoWrap :
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (hEval :
      Locals.Source.PrimitiveSemantics.structured.eval
          op sourceShared values =
        .ok (sourceFinal, outputs)) :
    ∃ targetFinal,
      Locals.Source.PrimitiveSemantics.structured.eval
          op targetShared values =
        .ok (targetFinal, outputs) ∧
      SharedRel contract sourceFinal targetFinal ∧
      targetFinal.toMachineState.memory =
        targetShared.toMachineState.memory ∧
      targetShared.toMachineState.activeWords.toNat ≤
        targetFinal.toMachineState.activeWords.toNat ∧
      targetFinal.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
  obtain ⟨address, size, topics, invocation⟩ :=
    family.invocation_of_eval hEval
  obtain ⟨_hConsistent, hAllowed, hExpansion, hHost⟩ :=
    invocation.memorySafe hSafe
  have hAllowed' :
      match contract.scratch? with
      | none => True
      | some reservation =>
          reservation.sourceAccessAllowed address.toNat size.toNat := by
    simpa [AllocationObserverSafety.RegionAllowed] using hAllowed
  have hSourceCanonical := invocation.eval sourceShared
  rw [hSourceCanonical] at hEval
  cases hEval
  obtain ⟨hShared, hMemory, hActive, hNoWrap⟩ :=
    logOp_both hRel address size topics hAllowed' hExpansion hHost
      hTargetNoWrap
  exact
    ⟨EvmYul.SharedState.logOp address size topics targetShared,
      invocation.eval targetShared, hShared, hMemory, hActive, hNoWrap⟩

end LogFamily

/--
Canonical `mload` preserves the allocation shared-state relation, including the
active-memory facts needed to retain an already allocated spill frame.
-/
theorem mload_simulate
    {contract : MemoryContract.Contract}
    {sourceShared sourceFinal targetShared :
      EvmYul.SharedState .EVM}
    {values outputs : List Word}
    (hRel : SharedRel contract sourceShared targetShared)
    (hConsistent :
      Compiler.MemoryRelation.MemoryConsistent
        sourceShared.toMachineState)
    (hAllowed :
      match contract.scratch? with
      | none => True
      | some reservation =>
          ∀ address,
            values = [address] →
            reservation.sourceAccessAllowed
              address.toNat MemoryContract.wordBytes)
    (hExpansion :
      ∀ address,
        values = [address] →
        Compiler.MemoryRelation.ExpansionNoWrap
          address.toNat MemoryContract.wordBytes)
    (hTargetNoWrap :
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (hEval :
      Locals.Source.PrimitiveSemantics.structured.eval
          .mload sourceShared values =
        .ok (sourceFinal, outputs)) :
    ∃ targetFinal,
      Locals.Source.PrimitiveSemantics.structured.eval
          .mload targetShared values =
        .ok (targetFinal, outputs) ∧
      SharedRel contract sourceFinal targetFinal ∧
      targetFinal.toMachineState.memory =
        targetShared.toMachineState.memory ∧
      targetShared.toMachineState.activeWords.toNat ≤
        targetFinal.toMachineState.activeWords.toNat ∧
      targetFinal.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
  cases values with
  | nil =>
      simp [Locals.Source.PrimitiveSemantics.structured,
        Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
        Structured.BasicOp.toPrimOp, Assembly.PrimOp.continuingStep?,
        Expressions.Structured.BasicOp.inputs]
        at hEval
  | cons address rest =>
      cases rest with
      | cons next tail =>
          simp [Locals.Source.PrimitiveSemantics.structured,
            Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
            Structured.BasicOp.toPrimOp, Assembly.PrimOp.continuingStep?,
            Expressions.Structured.BasicOp.inputs]
            at hEval
      | nil =>
          have hAllowed' :
              match contract.scratch? with
              | none => True
              | some reservation =>
                  reservation.sourceAccessAllowed
                    address.toNat MemoryContract.wordBytes := by
            cases hReservation : contract.scratch? with
            | none =>
                trivial
            | some reservation =>
                have hAllowedFn :
                    ∀ candidate,
                      [address] = [candidate] →
                      reservation.sourceAccessAllowed
                        candidate.toNat MemoryContract.wordBytes := by
                  simpa [hReservation] using hAllowed
                exact hAllowedFn address rfl
          have hMachine :=
            Compiler.MemoryRelation.MachineRel.mload_of_allowed
              hRel.machine hConsistent hTargetNoWrap address
              hAllowed' (hExpansion address rfl)
          rcases hMachine with
            ⟨hValue, hMachineRel, hFinalNoWrap, hActiveMono⟩
          have hSourceResult :
              sourceFinal =
                  { sourceShared with
                    toMachineState :=
                      (sourceShared.toMachineState.mload address).2 } ∧
                outputs =
                  [(sourceShared.toMachineState.mload address).1] := by
            simpa [Locals.Source.PrimitiveSemantics.structured,
              Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
              Structured.BasicOp.toPrimOp,
              Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
              Expressions.Structured.BasicOp.inputs,
              EvmYul.Stack.pop, EvmYul.Stack.push,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC] using hEval.symm
          rcases hSourceResult with ⟨rfl, rfl⟩
          let targetFinal : EvmYul.SharedState .EVM :=
            { targetShared with
              toMachineState :=
                (targetShared.toMachineState.mload address).2 }
          refine ⟨targetFinal, ?_, ?_, ?_, ?_, ?_⟩
          · simp [Locals.Source.PrimitiveSemantics.structured,
              Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
              Structured.BasicOp.toPrimOp,
              Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
              Expressions.Structured.BasicOp.inputs,
              EvmYul.Stack.pop, EvmYul.Stack.push,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC, targetFinal, hValue]
          · exact ⟨hMachineRel, hRel.world⟩
          · simp [targetFinal, EvmYul.MachineState.mload]
          · simpa [targetFinal] using hActiveMono
          · simpa [targetFinal] using hFinalNoWrap

/--
Canonical `mstore` performs the same source-owned write on both related machine
states and preserves the reservation-relative shared-state relation.
-/
theorem mstore_simulate
    {contract : MemoryContract.Contract}
    {sourceShared sourceFinal targetShared :
      EvmYul.SharedState .EVM}
    {address value : Word} {outputs : List Word}
    (hRel : SharedRel contract sourceShared targetShared)
    (hExpansion :
      Compiler.MemoryRelation.ExpansionNoWrap
        address.toNat MemoryContract.wordBytes)
    (hHost :
      address.toNat + MemoryContract.wordBytes < USize.size)
    (hTargetNoWrap :
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size)
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
          MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
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
      toMachineState :=
        targetShared.toMachineState.mstore address value }
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

/--
Canonical `mstore8` performs the same source-owned byte write on both related
machine states and preserves the reservation-relative shared-state relation.
-/
theorem mstore8_simulate
    {contract : MemoryContract.Contract}
    {sourceShared sourceFinal targetShared :
      EvmYul.SharedState .EVM}
    {address value : Word} {outputs : List Word}
    (hRel : SharedRel contract sourceShared targetShared)
    (hExpansion :
      Compiler.MemoryRelation.ExpansionNoWrap address.toNat 1)
    (hHost : address.toNat + 1 < USize.size)
    (hTargetNoWrap :
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size)
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
          MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
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
      toMachineState :=
        targetShared.toMachineState.mstore8 address value }
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

/--
Canonical `calldatacopy` writes the shared execution-environment calldata into
both related memories while preserving the allocation relation.
-/
theorem calldatacopy_simulate
    {contract : MemoryContract.Contract}
    {sourceShared sourceFinal targetShared :
      EvmYul.SharedState .EVM}
    {destination sourceOffset size : Word} {outputs : List Word}
    (hRel : SharedRel contract sourceShared targetShared)
    (hExpansion :
      Compiler.MemoryRelation.ExpansionNoWrap
        destination.toNat size.toNat)
    (hHost :
      destination.toNat + size.toNat < USize.size)
    (hTargetNoWrap :
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (hEval :
      Locals.Source.PrimitiveSemantics.structured.eval
          .calldatacopy sourceShared
          [size, sourceOffset, destination] =
        .ok (sourceFinal, outputs)) :
    ∃ targetFinal,
      Locals.Source.PrimitiveSemantics.structured.eval
          .calldatacopy targetShared
          [size, sourceOffset, destination] =
        .ok (targetFinal, outputs) ∧
      SharedRel contract sourceFinal targetFinal ∧
      targetFinal.toMachineState =
        (targetShared.calldatacopy
          destination sourceOffset size).toMachineState ∧
      targetShared.toMachineState.memory.size ≤
        targetFinal.toMachineState.memory.size ∧
      targetShared.toMachineState.activeWords.toNat ≤
        targetFinal.toMachineState.activeWords.toNat ∧
      targetFinal.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
  have hCalldata :
      sourceShared.executionEnv.calldata =
        targetShared.executionEnv.calldata :=
    congrArg EvmYul.ExecutionEnv.calldata hRel.executionEnv_eq
  have hMachine :=
    Compiler.MemoryRelation.MachineRel.copy_both
      hRel.machine hTargetNoWrap
      sourceShared.executionEnv.calldata sourceOffset.toNat
      destination.toNat size.toNat hExpansion hHost
  have hSourceResult :
      sourceFinal =
          sourceShared.calldatacopy
            destination sourceOffset size ∧
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
  let targetFinal :=
    targetShared.calldatacopy destination sourceOffset size
  have hMachine' :
      SharedRel contract
        (sourceShared.calldatacopy destination sourceOffset size)
        targetFinal := by
    refine ⟨?_, ?_⟩
    · simpa [EvmYul.SharedState.calldatacopy, targetFinal, hCalldata] using
        hMachine.1
    · simpa [EvmYul.SharedState.calldatacopy, targetFinal] using hRel.world
  refine ⟨targetFinal, ?_, hMachine', rfl, ?_, ?_, ?_⟩
  · simp [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      Expressions.Structured.BasicOp.inputs,
      EvmYul.EVM.ternaryCopyOp, EvmYul.Stack.pop3,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run, targetFinal]
  · simpa [EvmYul.SharedState.calldatacopy, targetFinal, hCalldata] using
      hMachine.2.2.2
  · simpa [EvmYul.SharedState.calldatacopy, targetFinal] using hMachine.2.2.1
  · simpa [EvmYul.SharedState.calldatacopy, targetFinal] using hMachine.2.1

/--
Canonical `codecopy` writes the shared execution-environment code into both
related memories while preserving the allocation relation.
-/
theorem codecopy_simulate
    {contract : MemoryContract.Contract}
    {sourceShared sourceFinal targetShared :
      EvmYul.SharedState .EVM}
    {destination sourceOffset size : Word} {outputs : List Word}
    (hRel : SharedRel contract sourceShared targetShared)
    (hExpansion :
      Compiler.MemoryRelation.ExpansionNoWrap
        destination.toNat size.toNat)
    (hHost :
      destination.toNat + size.toNat < USize.size)
    (hTargetNoWrap :
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (hEval :
      Locals.Source.PrimitiveSemantics.structured.eval
          .codecopy sourceShared
          [size, sourceOffset, destination] =
        .ok (sourceFinal, outputs)) :
    ∃ targetFinal,
      Locals.Source.PrimitiveSemantics.structured.eval
          .codecopy targetShared
          [size, sourceOffset, destination] =
        .ok (targetFinal, outputs) ∧
      SharedRel contract sourceFinal targetFinal ∧
      targetFinal.toMachineState =
        (targetShared.codeCopy
          destination sourceOffset size).toMachineState ∧
      targetShared.toMachineState.memory.size ≤
        targetFinal.toMachineState.memory.size ∧
      targetShared.toMachineState.activeWords.toNat ≤
        targetFinal.toMachineState.activeWords.toNat ∧
      targetFinal.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
  have hCode :
      sourceShared.executionEnv.code =
        targetShared.executionEnv.code :=
    congrArg EvmYul.ExecutionEnv.code hRel.executionEnv_eq
  have hMachine :=
    Compiler.MemoryRelation.MachineRel.copy_both
      hRel.machine hTargetNoWrap
      sourceShared.executionEnv.code sourceOffset.toNat
      destination.toNat size.toNat hExpansion hHost
  have hSourceResult :
      sourceFinal =
          sourceShared.codeCopy destination sourceOffset size ∧
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
  let targetFinal :=
    targetShared.codeCopy destination sourceOffset size
  have hMachine' :
      SharedRel contract
        (sourceShared.codeCopy destination sourceOffset size)
        targetFinal := by
    refine ⟨?_, ?_⟩
    · simpa [EvmYul.SharedState.codeCopy, targetFinal, hCode] using
        hMachine.1
    · simpa [EvmYul.SharedState.codeCopy, targetFinal] using hRel.world
  refine ⟨targetFinal, ?_, hMachine', rfl, ?_, ?_, ?_⟩
  · simp [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      Expressions.Structured.BasicOp.inputs,
      EvmYul.EVM.ternaryCopyOp, EvmYul.Stack.pop3,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run, targetFinal]
  · simpa [EvmYul.SharedState.codeCopy, targetFinal, hCode] using
      hMachine.2.2.2
  · simpa [EvmYul.SharedState.codeCopy, targetFinal] using hMachine.2.2.1
  · simpa [EvmYul.SharedState.codeCopy, targetFinal] using hMachine.2.1

/--
Canonical `returndatacopy` agrees on its bounds check because `MachineRel`
equates return data, then performs the same checked copy in both memories.
-/
theorem returndatacopy_simulate
    {contract : MemoryContract.Contract}
    {sourceShared sourceFinal targetShared :
      EvmYul.SharedState .EVM}
    {destination sourceOffset size : Word} {outputs : List Word}
    (hRel : SharedRel contract sourceShared targetShared)
    (hExpansion :
      Compiler.MemoryRelation.ExpansionNoWrap
        destination.toNat size.toNat)
    (hHost :
      destination.toNat + size.toNat < USize.size)
    (hTargetNoWrap :
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (hEval :
      Locals.Source.PrimitiveSemantics.structured.eval
          .returndatacopy sourceShared
          [size, sourceOffset, destination] =
        .ok (sourceFinal, outputs)) :
    ∃ targetFinal,
      Locals.Source.PrimitiveSemantics.structured.eval
          .returndatacopy targetShared
          [size, sourceOffset, destination] =
        .ok (targetFinal, outputs) ∧
      SharedRel contract sourceFinal targetFinal ∧
      targetFinal.toMachineState =
        targetShared.toMachineState.returndatacopy
          destination sourceOffset size ∧
      targetShared.toMachineState.memory.size ≤
        targetFinal.toMachineState.memory.size ∧
      targetShared.toMachineState.activeWords.toNat ≤
        targetFinal.toMachineState.activeWords.toNat ∧
      targetFinal.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
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
      hRel.machine hTargetNoWrap
      sourceShared.toMachineState.returnData sourceOffset.toNat
      destination.toNat size.toNat hExpansion hHost
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
  have hMachine' :
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
  refine ⟨targetFinal, ?_, hMachine', rfl, ?_, ?_, ?_⟩
  · simp [Locals.Source.PrimitiveSemantics.structured,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      Expressions.Structured.BasicOp.inputs,
      EvmYul.Stack.pop3, hTargetBound,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run, targetFinal]
  · simpa [EvmYul.MachineState.returndatacopy, EvmYul.writeBytes,
      targetFinal, hReturnData] using hMachine.2.2.2
  · simpa [EvmYul.MachineState.returndatacopy, EvmYul.writeBytes,
      targetFinal] using
      hMachine.2.2.1
  · simpa [EvmYul.MachineState.returndatacopy, EvmYul.writeBytes,
      targetFinal] using
      hMachine.2.1

/--
Canonical `extcodecopy` reads the same account code from related worlds, marks
the same account as accessed, and performs the same allocation-safe memory
copy.
-/
theorem extcodecopy_simulate
    {contract : MemoryContract.Contract}
    {sourceShared sourceFinal targetShared :
      EvmYul.SharedState .EVM}
    {account destination sourceOffset size : Word} {outputs : List Word}
    (hRel : SharedRel contract sourceShared targetShared)
    (hExpansion :
      Compiler.MemoryRelation.ExpansionNoWrap
        destination.toNat size.toNat)
    (hHost :
      destination.toNat + size.toNat < USize.size)
    (hTargetNoWrap :
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size)
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
        copied.write sourceOffset.toNat
          targetShared.toMachineState.memory
          destination.toNat size.toNat ∧
      targetShared.toMachineState.memory.size ≤
        targetFinal.toMachineState.memory.size ∧
      targetShared.toMachineState.activeWords.toNat ≤
        targetFinal.toMachineState.activeWords.toNat ∧
      targetFinal.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
  let address := EvmYul.AccountAddress.ofUInt256 account
  let copied : ByteArray :=
    sourceShared.toState.lookupAccount address |>.option
      .empty EvmYul.State.accountCodeImage
  have hWorld :
      sourceShared.toState = targetShared.toState :=
    hRel.world
  have hMachine :=
    Compiler.MemoryRelation.MachineRel.copy_both
      hRel.machine hTargetNoWrap copied sourceOffset.toNat
      destination.toNat size.toNat hExpansion hHost
  have hSourceResult :
      sourceFinal =
          sourceShared.extCodeCopy'
            account destination sourceOffset size ∧
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
        (sourceShared.extCodeCopy'
          account destination sourceOffset size)
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

/--
Canonical `mcopy` reads related source memories only through a source-approved
range, so both machines copy equal bytes while preserving allocation-owned
scratch memory.
-/
theorem mcopy_simulate
    {contract : MemoryContract.Contract}
    {sourceShared sourceFinal targetShared :
      EvmYul.SharedState .EVM}
    {destination sourceOffset size : Word} {outputs : List Word}
    (hRel : SharedRel contract sourceShared targetShared)
    (hSourceAllowed :
      match contract.scratch? with
      | none => True
      | some reservation =>
          reservation.sourceAccessAllowed
            sourceOffset.toNat size.toNat)
    (hExpansion :
      Compiler.MemoryRelation.ExpansionNoWrap
        (max destination.toNat sourceOffset.toNat) size.toNat)
    (hHost :
      destination.toNat + size.toNat < USize.size)
    (hTargetNoWrap :
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (hEval :
      Locals.Source.PrimitiveSemantics.structured.eval
          .mcopy sourceShared
          [size, sourceOffset, destination] =
        .ok (sourceFinal, outputs)) :
    ∃ targetFinal,
      Locals.Source.PrimitiveSemantics.structured.eval
          .mcopy targetShared
          [size, sourceOffset, destination] =
        .ok (targetFinal, outputs) ∧
      SharedRel contract sourceFinal targetFinal ∧
      targetFinal.toMachineState.memory =
        targetShared.toMachineState.memory.write sourceOffset.toNat
          targetShared.toMachineState.memory
          destination.toNat size.toNat ∧
      targetShared.toMachineState.memory.size ≤
        targetFinal.toMachineState.memory.size ∧
      targetShared.toMachineState.activeWords.toNat ≤
        targetFinal.toMachineState.activeWords.toNat ∧
      targetFinal.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
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
        targetShared.toMachineState.mcopy
          destination sourceOffset size }
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

/--
Pass-owned interface for primitives that only read source-visible memory and
may expand active memory. Hashing and logging share this allocation proof even
though their source-level results and world effects differ.
-/
structure ReadSpec (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) : Prop where
  observer_none :
    Functions.ObserverSemantics.basicOpObserver? op = none
  simulate :
    ∀ {sourceShared sourceFinal targetShared :
        EvmYul.SharedState .EVM}
      {values outputs : List Word},
      SharedRel contract sourceShared targetShared →
      AllocationObserverSafety.PrimitiveMemorySafe
        contract op sourceShared.toMachineState values →
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size →
      Locals.Source.PrimitiveSemantics.structured.eval
          op sourceShared values =
        .ok (sourceFinal, outputs) →
      ∃ targetFinal,
        Locals.Source.PrimitiveSemantics.structured.eval
            op targetShared values =
          .ok (targetFinal, outputs) ∧
        SharedRel contract sourceFinal targetFinal ∧
        targetFinal.toMachineState.memory =
          targetShared.toMachineState.memory ∧
        targetShared.toMachineState.activeWords.toNat ≤
          targetFinal.toMachineState.activeWords.toNat ∧
        targetFinal.toMachineState.activeWords.toNat *
            MemoryContract.wordBytes <
          EvmYul.UInt256.size

/--
One adjacent Functions-to-allocated-Expressions proof for every canonical
read-only memory primitive.
-/
theorem read_primitiveForward
    {contract : MemoryContract.Contract}
    {op : Structured.BasicOp}
    (spec : ReadSpec contract op) :
    AllocationObserverExpression.PrimitiveForward contract op where
  simulate := by
    intro transcript plan live stackOffset frameBase frameDepth frameWords
      sourceArgs sourceFinal targetInitial targetArgs values outputs
      hArgsRel hMemory hPrimitive
    cases hSourceEval :
        Locals.Source.PrimitiveSemantics.structured.eval
          op sourceArgs.source.shared values with
    | error err =>
        simp [Functions.ObserverSemantics.primitiveSemantics,
          Locals.ObserverSemantics.primitiveSemantics,
          spec.observer_none, hSourceEval] at hPrimitive
    | ok result =>
        rcases result with ⟨sourceSharedFinal, canonicalOutputs⟩
        have hPrimitiveResult :
            sourceArgs.withSource
                (sourceArgs.source.withShared sourceSharedFinal) =
              sourceFinal ∧
            canonicalOutputs = outputs := by
          simpa [Functions.ObserverSemantics.primitiveSemantics,
            Locals.ObserverSemantics.primitiveSemantics,
            spec.observer_none, hSourceEval] using hPrimitive
        rcases hPrimitiveResult with ⟨rfl, rfl⟩
        obtain
            ⟨targetSharedFinal, hTargetEval, hSharedFinal,
              hTargetMemory, hTargetActive, hFinalNoWrap⟩ :=
          spec.simulate hArgsRel.state.base.core.shared hMemory
            hArgsRel.state.activeNoWrap hSourceEval
        obtain ⟨evmFinal, hStep, hEvmShared, hEvmStack⟩ :=
          Locals.Source.PrimitiveSemantics.structured_eval_step_exists
            hTargetEval rfl hArgsRel.stack
        let targetFinal :
            Structured.ObserverSemantics.State transcript :=
          targetArgs.withSource
            (targetArgs.source.withEVM evmFinal)
        have hObserver := spec.observer_none
        have hRun :
            Structured.ObserverSemantics.Code.run [.op op] targetArgs =
              .ok targetFinal := by
          change
            Structured.ObserverSemantics.basicOpObserver? op = none
            at hObserver
          simp [Structured.ObserverSemantics.Code.run,
            Structured.EffectSemantics.Code.run,
            Structured.BasicInstr.step, hStep,
            Structured.ObserverSemantics.handler,
            hObserver, targetFinal]
        have hOutputsLength :
            canonicalOutputs.length =
              Expressions.Structured.BasicOp.outputs op :=
          Locals.Source.PrimitiveSemantics.structured_eval_length
            hSourceEval
        have hFinalMachine :
            targetFinal.source.evm.toMachineState =
              targetSharedFinal.toMachineState := by
          change evmFinal.toMachineState =
            targetSharedFinal.toMachineState
          exact congrArg EvmYul.SharedState.toMachineState hEvmShared
        have hMemoryEq :
            targetFinal.source.evm.toMachineState.memory =
              targetArgs.source.evm.toMachineState.memory := by
          rw [hFinalMachine, hTargetMemory]
        have hActiveMono :
            targetArgs.source.evm.activeWords.toNat ≤
              targetFinal.source.evm.activeWords.toNat := by
          simpa [hFinalMachine] using hTargetActive
        have hFinalActiveNoWrap :
            targetFinal.source.evm.activeWords.toNat *
                MemoryContract.wordBytes <
              EvmYul.UInt256.size := by
          simpa [hFinalMachine] using hFinalNoWrap
        have hFinalStack :
            targetFinal.source.evm.stack =
              canonicalOutputs.reverse ++
                targetInitial.source.evm.stack := by
          simpa [targetFinal] using hEvmStack
        have hOldStore :
            StoreRel plan live
              (stackOffset + values.reverse.length) frameBase
              sourceArgs.source targetArgs.source := by
          simpa [List.length_reverse, hArgsRel.valuesLength] using
            hArgsRel.state.base.core.store
        have hScratchStable :
            ∀ name slot,
              name ∈ live →
              plan.location? name = some (.scratch slot) →
              targetFinal.source.evm.toMachineState.lookupMemory
                  (EvmYul.UInt256.ofNat
                    (scratchAddress frameBase slot)) =
                targetArgs.source.evm.toMachineState.lookupMemory
                  (EvmYul.UInt256.ofNat
                    (scratchAddress frameBase slot)) := by
          intro name slot hLive hLocation
          have hSlot :=
            hArgsRel.state.scratchBound name slot hLive hLocation
          have hEndFrame :
              scratchAddress frameBase slot +
                  MemoryContract.wordBytes ≤
                frameBase +
                  MemoryContract.wordBytes * frameWords := by
            have hSucc : slot + 1 ≤ frameWords :=
              Nat.succ_le_iff.mpr hSlot
            calc
              scratchAddress frameBase slot +
                    MemoryContract.wordBytes =
                  frameBase +
                    MemoryContract.wordBytes * (slot + 1) := by
                      simp [scratchAddress, Nat.mul_add,
                        Nat.add_assoc]
              _ ≤ frameBase +
                    MemoryContract.wordBytes * frameWords :=
                Nat.add_le_add_left
                  (Nat.mul_le_mul_left
                    MemoryContract.wordBytes hSucc) frameBase
          have hQueryLt :
              scratchAddress frameBase slot <
                EvmYul.UInt256.size := by
            exact lt_of_le_of_lt
              (Nat.le_add_right
                (scratchAddress frameBase slot)
                MemoryContract.wordBytes)
              (hEndFrame.trans_lt hArgsRel.state.frameNoWrap)
          exact
            Compiler.MemoryRelation.MachineRel.lookupMemory_eq_of_memory_eq_active_growth
              (scratchAddress frameBase slot)
              (EvmYul.UInt256.toNat_ofNat_of_lt hQueryLt)
              hMemoryEq hActiveMono
              hArgsRel.state.activeNoWrap hFinalActiveNoWrap
              (hEndFrame.trans hArgsRel.state.frameAllocated)
              (hEndFrame.trans hArgsRel.state.frameActive)
        have hBaseRel :
            StateRel contract plan live
              (stackOffset + canonicalOutputs.reverse.length) frameBase
              (sourceArgs.withSource
                (sourceArgs.source.withShared sourceSharedFinal))
              targetFinal := by
          refine ⟨?_, ?_⟩
          · simpa [targetFinal] using hArgsRel.state.base.cursor
          · refine ⟨?_, ?_, ?_⟩
            · simpa [targetFinal, hEvmShared] using
                hSharedFinal.machine
            · simpa [targetFinal, hEvmShared] using
                hSharedFinal.world
            · exact
                StoreRel.rebase_prefix_of_lookup
                  (oldPrefix := values.reverse)
                  (newPrefix := canonicalOutputs.reverse)
                  (baseStack := targetInitial.source.evm.stack)
                  hOldStore hArgsRel.stack hFinalStack
                  hScratchStable rfl
        have hOldScratch :
            ScratchStateRel contract plan live
              (stackOffset + values.reverse.length) frameBase
              frameDepth frameWords sourceArgs targetArgs := by
          simpa [List.length_reverse, hArgsRel.valuesLength] using
            hArgsRel.state
        have hScratchRel :
            ScratchStateRel contract plan live
              (stackOffset + canonicalOutputs.reverse.length) frameBase
              frameDepth frameWords
              (sourceArgs.withSource
                (sourceArgs.source.withShared sourceSharedFinal))
              targetFinal :=
          ScratchStateRel.rebase_prefix_mono
            (oldPrefix := values.reverse)
            (newPrefix := canonicalOutputs.reverse)
            (baseStack := targetInitial.source.evm.stack)
            hOldScratch hBaseRel hArgsRel.stack hFinalStack
            (by simp [hMemoryEq])
            hActiveMono hFinalActiveNoWrap
        refine ⟨targetFinal, hRun, ?_, hOutputsLength, hFinalStack⟩
        simpa [List.length_reverse, hOutputsLength] using hScratchRel

def ReadSpec.stackSpec
    {contract : MemoryContract.Contract}
    {op : Structured.BasicOp}
    (spec : ReadSpec contract op) :
    StackSpec contract op where
  observerNone := spec.observer_none
  simulate := by
    intro sourceShared sourceFinal targetShared values outputs
      _hLength hRel hMemory hTargetNoWrap hEval
    obtain
        ⟨targetFinal, hTarget, hFinal,
          _hMemory, _hActive, hFinalNoWrap⟩ :=
      spec.simulate hRel hMemory hTargetNoWrap hEval
    exact ⟨targetFinal, hTarget, hFinal, hFinalNoWrap⟩

theorem read_stackPrimitiveForward
    {contract : MemoryContract.Contract}
    {op : Structured.BasicOp}
    (spec : ReadSpec contract op) :
    AllocationObserverExpression.StackPrimitiveForward contract op :=
  stack_primitiveForward spec.stackSpec

/--
Canonical hashing instantiates the shared read-only memory interface.
-/
theorem keccak256_readSpec
    (contract : MemoryContract.Contract) :
    ReadSpec contract .keccak256 where
  observer_none := rfl
  simulate := by
    intro sourceShared sourceFinal targetShared values outputs
      hRel hMemory hTargetNoWrap hEval
    cases values with
    | nil =>
        simp [Locals.Source.PrimitiveSemantics.structured,
          Expressions.Structured.BasicOp.inputs] at hEval
    | cons size rest =>
        cases rest with
        | nil =>
            simp [Locals.Source.PrimitiveSemantics.structured,
              Expressions.Structured.BasicOp.inputs] at hEval
        | cons address tail =>
            have hTail : tail = [] := by
              by_contra hNonempty
              cases tail with
              | nil => exact hNonempty rfl
              | cons extra more =>
                  simp [Locals.Source.PrimitiveSemantics.structured,
                    Expressions.Structured.BasicOp.inputs] at hEval
            subst tail
            have hSafety :
                Compiler.MemoryRelation.MemoryConsistent
                    sourceShared.toMachineState ∧
                  AllocationObserverSafety.RegionAllowed contract
                    address.toNat size.toNat ∧
                  Compiler.MemoryRelation.ExpansionNoWrap
                    address.toNat size.toNat ∧
                  address.toNat + size.toNat < USize.size := by
              simpa [AllocationObserverSafety.PrimitiveMemorySafe,
                AllocationObserverSafety.PrimitiveExpansionSafe,
                AllocationObserverSafety.PrimitiveHostSafe] using hMemory
            rcases hSafety with
              ⟨_hConsistent, hAllowed, hExpansion, hHost⟩
            have hAllowed' :
                match contract.scratch? with
                | none => True
                | some reservation =>
                    reservation.sourceAccessAllowed
                      address.toNat size.toNat := by
              simpa [AllocationObserverSafety.RegionAllowed] using hAllowed
            exact
              keccak256_simulate hRel hAllowed' hExpansion hHost
                hTargetNoWrap hEval

/--
Adjacent Functions-to-allocated-Expressions preservation for canonical
`keccak256`.
-/
theorem keccak256_primitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.PrimitiveForward contract .keccak256 :=
  read_primitiveForward (keccak256_readSpec contract)

theorem LogFamily.readSpec
    {op : Structured.BasicOp}
    (family : LogFamily op)
    (contract : MemoryContract.Contract) :
    ReadSpec contract op where
  observer_none := family.observer_none
  simulate := by
    intro sourceShared sourceFinal targetShared values outputs
      hRel hSafe hTargetNoWrap hEval
    exact
      family.simulate hRel hSafe hTargetNoWrap hEval

/--
One adjacent allocation theorem covers every canonical logging primitive.
-/
theorem LogFamily.primitiveForward
    {op : Structured.BasicOp}
    (family : LogFamily op)
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.PrimitiveForward contract op :=
  read_primitiveForward (family.readSpec contract)

theorem log0_primitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.PrimitiveForward contract .log0 :=
  LogFamily.log0.primitiveForward contract

theorem log1_primitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.PrimitiveForward contract .log1 :=
  LogFamily.log1.primitiveForward contract

theorem log2_primitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.PrimitiveForward contract .log2 :=
  LogFamily.log2.primitiveForward contract

theorem log3_primitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.PrimitiveForward contract .log3 :=
  LogFamily.log3.primitiveForward contract

theorem log4_primitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.PrimitiveForward contract .log4 :=
  LogFamily.log4.primitiveForward contract

def mload_readSpec
    (contract : MemoryContract.Contract) :
    ReadSpec contract .mload where
  observer_none := rfl
  simulate := by
    intro sourceShared sourceFinal targetShared values outputs
      hRel hMemory hTargetNoWrap hEval
    cases values with
    | nil =>
        simp [Locals.Source.PrimitiveSemantics.structured,
          Expressions.Structured.BasicOp.inputs] at hEval
    | cons address rest =>
        cases rest with
        | cons next tail =>
            simp [Locals.Source.PrimitiveSemantics.structured,
              Expressions.Structured.BasicOp.inputs] at hEval
        | nil =>
            have hSafety :
                Compiler.MemoryRelation.MemoryConsistent
                    sourceShared.toMachineState ∧
                  AllocationObserverSafety.RegionAllowed contract
                    address.toNat MemoryContract.wordBytes ∧
                  Compiler.MemoryRelation.ExpansionNoWrap
                    address.toNat MemoryContract.wordBytes := by
              simpa [AllocationObserverSafety.PrimitiveMemorySafe,
                AllocationObserverSafety.PrimitiveExpansionSafe] using
                hMemory
            rcases hSafety with
              ⟨hConsistent, hAllowed, hExpansion⟩
            exact
              mload_simulate hRel hConsistent
                (by
                  cases hReservation : contract.scratch? with
                  | none =>
                      trivial
                  | some reservation =>
                      simpa [hReservation] using
                        (show
                          ∀ candidate,
                            [address] = [candidate] →
                            reservation.sourceAccessAllowed
                              candidate.toNat
                              MemoryContract.wordBytes by
                          intro candidate hCandidate
                          cases hCandidate
                          simpa [AllocationObserverSafety.RegionAllowed,
                            hReservation] using hAllowed))
                (by
                  intro candidate hCandidate
                  cases hCandidate
                  exact hExpansion)
                hTargetNoWrap hEval

theorem mload_stackPrimitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.StackPrimitiveForward
      contract .mload :=
  read_stackPrimitiveForward (mload_readSpec contract)

/--
Adjacent Functions-to-allocated-Expressions preservation for canonical
`mload`.
-/
theorem mload_primitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.PrimitiveForward contract .mload where
  simulate := by
    intro transcript plan live stackOffset frameBase frameDepth frameWords
      sourceArgs sourceFinal targetInitial targetArgs values outputs
      hArgsRel hMemory hPrimitive
    have hLength : values.length = 1 := by
      simpa [Expressions.Structured.BasicOp.inputs] using
        hArgsRel.valuesLength
    cases values with
    | nil =>
        simp at hLength
    | cons address rest =>
        cases rest with
        | cons next tail =>
            simp at hLength
        | nil =>
            have hSafety :
                Compiler.MemoryRelation.MemoryConsistent
                    sourceArgs.source.shared.toMachineState ∧
                  AllocationObserverSafety.RegionAllowed contract
                    address.toNat MemoryContract.wordBytes ∧
                  Compiler.MemoryRelation.ExpansionNoWrap
                    address.toNat MemoryContract.wordBytes := by
              simpa [AllocationObserverSafety.PrimitiveMemorySafe,
                AllocationObserverSafety.PrimitiveExpansionSafe] using
                hMemory
            rcases hSafety with
              ⟨hConsistent, hAllowed, hExpansion⟩
            have hObserver :
                Functions.ObserverSemantics.basicOpObserver? .mload = none := by
              rfl
            cases hSourceEval :
                Locals.Source.PrimitiveSemantics.structured.eval
                  .mload sourceArgs.source.shared [address] with
            | error err =>
                simp [Functions.ObserverSemantics.primitiveSemantics,
                  Locals.ObserverSemantics.primitiveSemantics,
                  hObserver, hSourceEval] at hPrimitive
            | ok result =>
                rcases result with
                  ⟨sourceSharedFinal, canonicalOutputs⟩
                have hPrimitiveResult :
                    sourceArgs.withSource
                        (sourceArgs.source.withShared sourceSharedFinal) =
                      sourceFinal ∧
                    canonicalOutputs = outputs := by
                  simpa [Functions.ObserverSemantics.primitiveSemantics,
                    Locals.ObserverSemantics.primitiveSemantics,
                    hObserver, hSourceEval] using hPrimitive
                rcases hPrimitiveResult with ⟨rfl, rfl⟩
                have hAllowed' :
                    match contract.scratch? with
                    | none => True
                    | some reservation =>
                        reservation.sourceAccessAllowed address.toNat
                          MemoryContract.wordBytes := by
                  simpa [AllocationObserverSafety.RegionAllowed] using
                    hAllowed
                obtain
                    ⟨targetSharedFinal, hTargetEval, hSharedFinal,
                      hTargetMemory, hTargetActive, hFinalNoWrap⟩ :=
                  mload_simulate hArgsRel.state.base.core.shared
                    hConsistent
                    (by
                      cases hReservation : contract.scratch? with
                      | none =>
                          trivial
                      | some reservation =>
                          simpa [hReservation] using
                            (show
                              ∀ candidate,
                                [address] = [candidate] →
                                reservation.sourceAccessAllowed
                                  candidate.toNat
                                  MemoryContract.wordBytes by
                              intro candidate hCandidate
                              cases hCandidate
                              simpa [hReservation] using hAllowed'))
                    (by
                      intro candidate hCandidate
                      cases hCandidate
                      exact hExpansion)
                    hArgsRel.state.activeNoWrap hSourceEval
                obtain ⟨evmFinal, hStep, hEvmShared, hEvmStack⟩ :=
                  Locals.Source.PrimitiveSemantics.structured_eval_step_exists
                    hTargetEval rfl hArgsRel.stack
                let targetFinal :
                    Structured.ObserverSemantics.State transcript :=
                  targetArgs.withSource
                    (targetArgs.source.withEVM evmFinal)
                have hRun :
                    Structured.ObserverSemantics.Code.run [.op .mload]
                        targetArgs =
                      .ok targetFinal := by
                  simp [Structured.ObserverSemantics.Code.run,
                    Structured.EffectSemantics.Code.run,
                    Structured.BasicInstr.step, hStep,
                    Structured.ObserverSemantics.handler,
                    Structured.ObserverSemantics.basicOpObserver?,
                    Structured.BasicOp.toPrimOp,
                    Assembly.ResourceObserver.ofPrimOp?, targetFinal]
                have hOutputsLength :
                    canonicalOutputs.length =
                      Expressions.Structured.BasicOp.outputs .mload :=
                  Locals.Source.PrimitiveSemantics.structured_eval_length
                    hSourceEval
                have hFinalMachine :
                    targetFinal.source.evm.toMachineState =
                      targetSharedFinal.toMachineState := by
                  change evmFinal.toMachineState =
                    targetSharedFinal.toMachineState
                  exact congrArg EvmYul.SharedState.toMachineState hEvmShared
                have hMemoryEq :
                    targetFinal.source.evm.toMachineState.memory =
                      targetArgs.source.evm.toMachineState.memory := by
                  rw [hFinalMachine, hTargetMemory]
                have hActiveMono :
                    targetArgs.source.evm.activeWords.toNat ≤
                      targetFinal.source.evm.activeWords.toNat := by
                  simpa [hFinalMachine] using hTargetActive
                have hFinalActiveNoWrap :
                    targetFinal.source.evm.activeWords.toNat *
                        MemoryContract.wordBytes <
                      EvmYul.UInt256.size := by
                  simpa [hFinalMachine] using hFinalNoWrap
                have hFinalStack :
                    targetFinal.source.evm.stack =
                      canonicalOutputs.reverse ++
                        targetInitial.source.evm.stack := by
                  simpa [targetFinal] using hEvmStack
                have hOldStore :
                    StoreRel plan live
                      (stackOffset + [address].reverse.length) frameBase
                      sourceArgs.source targetArgs.source := by
                  simpa [hArgsRel.valuesLength] using
                    hArgsRel.state.base.core.store
                have hScratchStable :
                    ∀ name slot,
                      name ∈ live →
                      plan.location? name = some (.scratch slot) →
                      targetFinal.source.evm.toMachineState.lookupMemory
                          (EvmYul.UInt256.ofNat
                            (scratchAddress frameBase slot)) =
                        targetArgs.source.evm.toMachineState.lookupMemory
                          (EvmYul.UInt256.ofNat
                            (scratchAddress frameBase slot)) := by
                  intro name slot hLive hLocation
                  have hSlot :=
                    hArgsRel.state.scratchBound
                      name slot hLive hLocation
                  have hEndFrame :
                      scratchAddress frameBase slot +
                          MemoryContract.wordBytes ≤
                        frameBase +
                          MemoryContract.wordBytes * frameWords := by
                    have hSucc : slot + 1 ≤ frameWords :=
                      Nat.succ_le_iff.mpr hSlot
                    calc
                      scratchAddress frameBase slot +
                            MemoryContract.wordBytes =
                          frameBase +
                            MemoryContract.wordBytes * (slot + 1) := by
                              simp [scratchAddress, Nat.mul_add,
                                Nat.add_assoc]
                      _ ≤ frameBase +
                            MemoryContract.wordBytes * frameWords :=
                        Nat.add_le_add_left
                          (Nat.mul_le_mul_left
                            MemoryContract.wordBytes hSucc) frameBase
                  have hQueryLt :
                      scratchAddress frameBase slot <
                        EvmYul.UInt256.size := by
                    exact lt_of_le_of_lt
                      (Nat.le_add_right
                        (scratchAddress frameBase slot)
                        MemoryContract.wordBytes)
                      (hEndFrame.trans_lt hArgsRel.state.frameNoWrap)
                  exact
                    Compiler.MemoryRelation.MachineRel.lookupMemory_eq_of_memory_eq_active_growth
                      (scratchAddress frameBase slot)
                      (EvmYul.UInt256.toNat_ofNat_of_lt hQueryLt)
                      hMemoryEq hActiveMono
                      hArgsRel.state.activeNoWrap hFinalActiveNoWrap
                      (hEndFrame.trans hArgsRel.state.frameAllocated)
                      (hEndFrame.trans hArgsRel.state.frameActive)
                have hBaseRel :
                    StateRel contract plan live
                      (stackOffset + canonicalOutputs.reverse.length)
                      frameBase
                      (sourceArgs.withSource
                        (sourceArgs.source.withShared sourceSharedFinal))
                      targetFinal := by
                  refine ⟨?_, ?_⟩
                  · simpa [targetFinal] using
                      hArgsRel.state.base.cursor
                  · refine ⟨?_, ?_, ?_⟩
                    · simpa [targetFinal, hEvmShared] using
                        hSharedFinal.machine
                    · simpa [targetFinal, hEvmShared] using
                        hSharedFinal.world
                    · exact
                        StoreRel.rebase_prefix_of_lookup
                          (oldPrefix := [address].reverse)
                          (newPrefix := canonicalOutputs.reverse)
                          (baseStack := targetInitial.source.evm.stack)
                          hOldStore hArgsRel.stack hFinalStack
                          hScratchStable rfl
                have hOldScratch :
                    ScratchStateRel contract plan live
                      (stackOffset + [address].reverse.length) frameBase
                      frameDepth frameWords sourceArgs targetArgs := by
                  simpa [hArgsRel.valuesLength] using hArgsRel.state
                have hScratchRel :
                    ScratchStateRel contract plan live
                      (stackOffset + canonicalOutputs.reverse.length)
                      frameBase frameDepth frameWords
                      (sourceArgs.withSource
                        (sourceArgs.source.withShared sourceSharedFinal))
                      targetFinal :=
                  ScratchStateRel.rebase_prefix_mono
                    (oldPrefix := [address].reverse)
                    (newPrefix := canonicalOutputs.reverse)
                    (baseStack := targetInitial.source.evm.stack)
                    hOldScratch hBaseRel hArgsRel.stack hFinalStack
                    (by simp [hMemoryEq])
                    hActiveMono hFinalActiveNoWrap
                refine ⟨targetFinal, hRun, ?_, hOutputsLength, hFinalStack⟩
                simpa [List.length_reverse, hOutputsLength] using hScratchRel

def mstore_stackSpec
    (contract : MemoryContract.Contract) :
    StackSpec contract .mstore where
  observerNone := rfl
  simulate := by
    intro sourceShared sourceFinal targetShared values outputs
      _hLength hRel hMemory hTargetNoWrap hEval
    cases values with
    | nil =>
        simp [Locals.Source.PrimitiveSemantics.structured,
          Expressions.Structured.BasicOp.inputs] at hEval
    | cons value rest =>
        cases rest with
        | nil =>
            simp [Locals.Source.PrimitiveSemantics.structured,
              Expressions.Structured.BasicOp.inputs] at hEval
        | cons address tail =>
            have hTail : tail = [] := by
              by_contra hNonempty
              cases tail with
              | nil => contradiction
              | cons extra more =>
                  simp [Locals.Source.PrimitiveSemantics.structured,
                    Expressions.Structured.BasicOp.inputs] at hEval
            subst tail
            have hSafety :
                Compiler.MemoryRelation.MemoryConsistent
                    sourceShared.toMachineState ∧
                  AllocationObserverSafety.RegionAllowed contract
                    address.toNat MemoryContract.wordBytes ∧
                  Compiler.MemoryRelation.ExpansionNoWrap
                    address.toNat MemoryContract.wordBytes ∧
                  address.toNat + MemoryContract.wordBytes < USize.size := by
              simpa [AllocationObserverSafety.PrimitiveMemorySafe,
                AllocationObserverSafety.PrimitiveExpansionSafe,
                AllocationObserverSafety.PrimitiveHostSafe] using hMemory
            rcases hSafety with
              ⟨_hConsistent, _hAllowed, hExpansion, hHost⟩
            obtain
                ⟨targetFinal, hTarget, hFinal,
                  _hMachine, _hMemory, _hActive, hFinalNoWrap⟩ :=
              mstore_simulate hRel hExpansion hHost hTargetNoWrap hEval
            exact ⟨targetFinal, hTarget, hFinal, hFinalNoWrap⟩

theorem mstore_stackPrimitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.StackPrimitiveForward
      contract .mstore :=
  stack_primitiveForward (mstore_stackSpec contract)

/--
Adjacent Functions-to-allocated-Expressions preservation for canonical
`mstore`.
-/
theorem mstore_primitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.PrimitiveForward contract .mstore where
  simulate := by
    intro transcript plan live stackOffset frameBase frameDepth frameWords
      sourceArgs sourceFinal targetInitial targetArgs values outputs
      hArgsRel hMemory hPrimitive
    have hLength : values.length = 2 := by
      simpa [Expressions.Structured.BasicOp.inputs] using
        hArgsRel.valuesLength
    cases values with
    | nil =>
        simp at hLength
    | cons value rest =>
        cases rest with
        | nil =>
            simp at hLength
        | cons address tail =>
            have hTail : tail = [] := by
              simpa using hLength
            subst tail
            have hSafety :
                Compiler.MemoryRelation.MemoryConsistent
                    sourceArgs.source.shared.toMachineState ∧
                  AllocationObserverSafety.RegionAllowed contract
                    address.toNat MemoryContract.wordBytes ∧
                  Compiler.MemoryRelation.ExpansionNoWrap
                    address.toNat MemoryContract.wordBytes ∧
                  address.toNat + MemoryContract.wordBytes < USize.size := by
              simpa [AllocationObserverSafety.PrimitiveMemorySafe,
                AllocationObserverSafety.PrimitiveExpansionSafe,
                AllocationObserverSafety.PrimitiveHostSafe] using hMemory
            rcases hSafety with
              ⟨_hConsistent, hAllowed, hExpansion, hHost⟩
            have hObserver :
                Functions.ObserverSemantics.basicOpObserver? .mstore = none := by
              rfl
            cases hSourceEval :
                Locals.Source.PrimitiveSemantics.structured.eval
                  .mstore sourceArgs.source.shared [value, address] with
            | error err =>
                simp [Functions.ObserverSemantics.primitiveSemantics,
                  Locals.ObserverSemantics.primitiveSemantics,
                  hObserver, hSourceEval] at hPrimitive
            | ok result =>
                rcases result with
                  ⟨sourceSharedFinal, canonicalOutputs⟩
                have hPrimitiveResult :
                    sourceArgs.withSource
                        (sourceArgs.source.withShared sourceSharedFinal) =
                      sourceFinal ∧
                    canonicalOutputs = outputs := by
                  simpa [Functions.ObserverSemantics.primitiveSemantics,
                    Locals.ObserverSemantics.primitiveSemantics,
                    hObserver, hSourceEval] using hPrimitive
                rcases hPrimitiveResult with ⟨rfl, rfl⟩
                obtain
                    ⟨targetSharedFinal, hTargetEval, hSharedFinal,
                      hTargetMachine, hTargetMemory, hTargetActive,
                      hFinalNoWrap⟩ :=
                  mstore_simulate hArgsRel.state.base.core.shared
                    hExpansion hHost hArgsRel.state.activeNoWrap
                    hSourceEval
                obtain ⟨evmFinal, hStep, hEvmShared, hEvmStack⟩ :=
                  Locals.Source.PrimitiveSemantics.structured_eval_step_exists
                    hTargetEval rfl hArgsRel.stack
                let targetFinal :
                    Structured.ObserverSemantics.State transcript :=
                  targetArgs.withSource
                    (targetArgs.source.withEVM evmFinal)
                have hRun :
                    Structured.ObserverSemantics.Code.run [.op .mstore]
                        targetArgs =
                      .ok targetFinal := by
                  simp [Structured.ObserverSemantics.Code.run,
                    Structured.EffectSemantics.Code.run,
                    Structured.BasicInstr.step, hStep,
                    Structured.ObserverSemantics.handler,
                    Structured.ObserverSemantics.basicOpObserver?,
                    Structured.BasicOp.toPrimOp,
                    Assembly.ResourceObserver.ofPrimOp?, targetFinal]
                have hOutputsLength :
                    canonicalOutputs.length =
                      Expressions.Structured.BasicOp.outputs .mstore :=
                  Locals.Source.PrimitiveSemantics.structured_eval_length
                    hSourceEval
                have hFinalSharedMachine :
                    targetFinal.source.evm.toMachineState =
                      targetSharedFinal.toMachineState := by
                  change evmFinal.toMachineState =
                    targetSharedFinal.toMachineState
                  exact congrArg EvmYul.SharedState.toMachineState hEvmShared
                have hConcreteMachine :
                    targetFinal.source.evm.toMachineState =
                      targetArgs.source.evm.toMachineState.mstore
                        address value := by
                  exact hFinalSharedMachine.trans hTargetMachine
                have hMemoryMono :
                    targetArgs.source.evm.toMachineState.memory.size ≤
                      targetFinal.source.evm.toMachineState.memory.size := by
                  rw [hFinalSharedMachine]
                  exact hTargetMemory
                have hActiveMono :
                    targetArgs.source.evm.activeWords.toNat ≤
                      targetFinal.source.evm.activeWords.toNat := by
                  rw [hFinalSharedMachine]
                  exact hTargetActive
                have hFinalActiveNoWrap :
                    targetFinal.source.evm.activeWords.toNat *
                        MemoryContract.wordBytes <
                      EvmYul.UInt256.size := by
                  rw [hFinalSharedMachine]
                  exact hFinalNoWrap
                have hFinalStack :
                    targetFinal.source.evm.stack =
                      canonicalOutputs.reverse ++
                        targetInitial.source.evm.stack := by
                  simpa [targetFinal] using hEvmStack
                have hOldStore :
                    StoreRel plan live
                      (stackOffset + [value, address].reverse.length)
                      frameBase sourceArgs.source targetArgs.source := by
                  simpa [hArgsRel.valuesLength] using
                    hArgsRel.state.base.core.store
                obtain
                    ⟨reservation, hReservation, _hFrameReserved⟩ :=
                  hArgsRel.state.frameReserved
                have hAllowed' :
                    reservation.sourceAccessAllowed address.toNat
                      MemoryContract.wordBytes := by
                  simpa [AllocationObserverSafety.RegionAllowed,
                    hReservation] using hAllowed
                have hAddressWord :
                    EvmYul.UInt256.ofNat address.toNat = address :=
                  EvmYul.UInt256.ofNat_toNat address
                have hAddressToNat :
                    (EvmYul.UInt256.ofNat address.toNat).toNat =
                      address.toNat := by
                  rw [hAddressWord]
                have hScratchStable :
                    ∀ name slot,
                      name ∈ live →
                      plan.location? name = some (.scratch slot) →
                      targetFinal.source.evm.toMachineState.lookupMemory
                          (EvmYul.UInt256.ofNat
                            (scratchAddress frameBase slot)) =
                        targetArgs.source.evm.toMachineState.lookupMemory
                          (EvmYul.UInt256.ofNat
                            (scratchAddress frameBase slot)) := by
                  intro name slot hLive hLocation
                  have hSlotRegion :=
                    hArgsRel.state.scratchAddress_reserved
                      hLive hLocation hReservation
                  have hDisjoint :
                      scratchAddress frameBase slot +
                            MemoryContract.wordBytes ≤ address.toNat ∨
                        address.toNat + MemoryContract.wordBytes ≤
                          scratchAddress frameBase slot := by
                    rcases hAllowed' with hBefore | hAfter
                    · exact Or.inr (hBefore.trans hSlotRegion.1)
                    · exact Or.inl (hSlotRegion.2.trans hAfter)
                  have hQueryLt :
                      scratchAddress frameBase slot <
                        EvmYul.UInt256.size := by
                    exact lt_of_lt_of_le
                      (Nat.lt_add_of_pos_right
                        (by decide : 0 < MemoryContract.wordBytes))
                      (Nat.le_of_lt
                        (hArgsRel.state.scratchAddress_end_lt_size
                          hLive hLocation))
                  have hLookup :=
                    Compiler.MemoryRelation.lookupMemory_mstore_disjoint_growing
                      targetArgs.source.evm.toMachineState
                      address.toNat (scratchAddress frameBase slot) value
                      hAddressToNat
                      (EvmYul.UInt256.toNat_ofNat_of_lt hQueryLt)
                      (by simpa [MemoryContract.wordBytes] using hHost)
                      (by simpa [MemoryContract.wordBytes] using
                        (hArgsRel.state.scratchAddress_end_le_memory
                          hLive hLocation))
                      (by simpa [MemoryContract.wordBytes] using
                        (hArgsRel.state.scratchAddress_end_le_active
                          hLive hLocation))
                      (by simpa [MemoryContract.wordBytes] using
                        hArgsRel.state.activeNoWrap)
                      (by simpa [MemoryContract.wordBytes] using hDisjoint)
                  rw [hConcreteMachine, ← hAddressWord]
                  exact hLookup
                have hBaseRel :
                    StateRel contract plan live
                      (stackOffset + canonicalOutputs.reverse.length)
                      frameBase
                      (sourceArgs.withSource
                        (sourceArgs.source.withShared sourceSharedFinal))
                      targetFinal := by
                  refine ⟨?_, ?_⟩
                  · simpa [targetFinal] using
                      hArgsRel.state.base.cursor
                  · refine ⟨?_, ?_, ?_⟩
                    · simpa [targetFinal, hEvmShared] using
                        hSharedFinal.machine
                    · simpa [targetFinal, hEvmShared] using
                        hSharedFinal.world
                    · exact
                        StoreRel.rebase_prefix_of_lookup
                          (oldPrefix := [value, address].reverse)
                          (newPrefix := canonicalOutputs.reverse)
                          (baseStack := targetInitial.source.evm.stack)
                          hOldStore hArgsRel.stack hFinalStack
                          hScratchStable rfl
                have hOldScratch :
                    ScratchStateRel contract plan live
                      (stackOffset + [value, address].reverse.length)
                      frameBase frameDepth frameWords
                      sourceArgs targetArgs := by
                  simpa [hArgsRel.valuesLength] using hArgsRel.state
                have hScratchRel :
                    ScratchStateRel contract plan live
                      (stackOffset + canonicalOutputs.reverse.length)
                      frameBase frameDepth frameWords
                      (sourceArgs.withSource
                        (sourceArgs.source.withShared sourceSharedFinal))
                      targetFinal :=
                  ScratchStateRel.rebase_prefix_mono
                    (oldPrefix := [value, address].reverse)
                    (newPrefix := canonicalOutputs.reverse)
                    (baseStack := targetInitial.source.evm.stack)
                    hOldScratch hBaseRel hArgsRel.stack hFinalStack
                    hMemoryMono hActiveMono hFinalActiveNoWrap
                refine ⟨targetFinal, hRun, ?_, hOutputsLength, hFinalStack⟩
                simpa [List.length_reverse, hOutputsLength] using hScratchRel

def mstore8_stackSpec
    (contract : MemoryContract.Contract) :
    StackSpec contract .mstore8 where
  observerNone := rfl
  simulate := by
    intro sourceShared sourceFinal targetShared values outputs
      _hLength hRel hMemory hTargetNoWrap hEval
    cases values with
    | nil =>
        simp [Locals.Source.PrimitiveSemantics.structured,
          Expressions.Structured.BasicOp.inputs] at hEval
    | cons value rest =>
        cases rest with
        | nil =>
            simp [Locals.Source.PrimitiveSemantics.structured,
              Expressions.Structured.BasicOp.inputs] at hEval
        | cons address tail =>
            have hTail : tail = [] := by
              by_contra hNonempty
              cases tail with
              | nil => contradiction
              | cons extra more =>
                  simp [Locals.Source.PrimitiveSemantics.structured,
                    Expressions.Structured.BasicOp.inputs] at hEval
            subst tail
            have hSafety :
                Compiler.MemoryRelation.MemoryConsistent
                    sourceShared.toMachineState ∧
                  AllocationObserverSafety.RegionAllowed contract
                    address.toNat 1 ∧
                  Compiler.MemoryRelation.ExpansionNoWrap
                    address.toNat 1 ∧
                  address.toNat + 1 < USize.size := by
              simpa [AllocationObserverSafety.PrimitiveMemorySafe,
                AllocationObserverSafety.PrimitiveExpansionSafe,
                AllocationObserverSafety.PrimitiveHostSafe] using hMemory
            rcases hSafety with
              ⟨_hConsistent, _hAllowed, hExpansion, hHost⟩
            obtain
                ⟨targetFinal, hTarget, hFinal,
                  _hMachine, _hMemory, _hActive, hFinalNoWrap⟩ :=
              mstore8_simulate hRel hExpansion hHost hTargetNoWrap hEval
            exact ⟨targetFinal, hTarget, hFinal, hFinalNoWrap⟩

theorem mstore8_stackPrimitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.StackPrimitiveForward
      contract .mstore8 :=
  stack_primitiveForward (mstore8_stackSpec contract)

/--
Adjacent Functions-to-allocated-Expressions preservation for canonical
`mstore8`.
-/
theorem mstore8_primitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.PrimitiveForward contract .mstore8 where
  simulate := by
    intro transcript plan live stackOffset frameBase frameDepth frameWords
      sourceArgs sourceFinal targetInitial targetArgs values outputs
      hArgsRel hMemory hPrimitive
    have hLength : values.length = 2 := by
      simpa [Expressions.Structured.BasicOp.inputs] using
        hArgsRel.valuesLength
    cases values with
    | nil =>
        simp at hLength
    | cons value rest =>
        cases rest with
        | nil =>
            simp at hLength
        | cons address tail =>
            have hTail : tail = [] := by
              simpa using hLength
            subst tail
            have hSafety :
                Compiler.MemoryRelation.MemoryConsistent
                    sourceArgs.source.shared.toMachineState ∧
                  AllocationObserverSafety.RegionAllowed contract
                    address.toNat 1 ∧
                  Compiler.MemoryRelation.ExpansionNoWrap
                    address.toNat 1 ∧
                  address.toNat + 1 < USize.size := by
              simpa [AllocationObserverSafety.PrimitiveMemorySafe,
                AllocationObserverSafety.PrimitiveExpansionSafe,
                AllocationObserverSafety.PrimitiveHostSafe] using hMemory
            rcases hSafety with
              ⟨_hConsistent, hAllowed, hExpansion, hHost⟩
            have hObserver :
                Functions.ObserverSemantics.basicOpObserver? .mstore8 =
                  none := by
              rfl
            cases hSourceEval :
                Locals.Source.PrimitiveSemantics.structured.eval
                  .mstore8 sourceArgs.source.shared [value, address] with
            | error err =>
                simp [Functions.ObserverSemantics.primitiveSemantics,
                  Locals.ObserverSemantics.primitiveSemantics,
                  hObserver, hSourceEval] at hPrimitive
            | ok result =>
                rcases result with
                  ⟨sourceSharedFinal, canonicalOutputs⟩
                have hPrimitiveResult :
                    sourceArgs.withSource
                        (sourceArgs.source.withShared sourceSharedFinal) =
                      sourceFinal ∧
                    canonicalOutputs = outputs := by
                  simpa [Functions.ObserverSemantics.primitiveSemantics,
                    Locals.ObserverSemantics.primitiveSemantics,
                    hObserver, hSourceEval] using hPrimitive
                rcases hPrimitiveResult with ⟨rfl, rfl⟩
                obtain
                    ⟨targetSharedFinal, hTargetEval, hSharedFinal,
                      hTargetMachine, hTargetMemory, hTargetActive,
                      hFinalNoWrap⟩ :=
                  mstore8_simulate hArgsRel.state.base.core.shared
                    hExpansion hHost hArgsRel.state.activeNoWrap
                    hSourceEval
                obtain ⟨evmFinal, hStep, hEvmShared, hEvmStack⟩ :=
                  Locals.Source.PrimitiveSemantics.structured_eval_step_exists
                    hTargetEval rfl hArgsRel.stack
                let targetFinal :
                    Structured.ObserverSemantics.State transcript :=
                  targetArgs.withSource
                    (targetArgs.source.withEVM evmFinal)
                have hRun :
                    Structured.ObserverSemantics.Code.run [.op .mstore8]
                        targetArgs =
                      .ok targetFinal := by
                  simp [Structured.ObserverSemantics.Code.run,
                    Structured.EffectSemantics.Code.run,
                    Structured.BasicInstr.step, hStep,
                    Structured.ObserverSemantics.handler,
                    Structured.ObserverSemantics.basicOpObserver?,
                    Structured.BasicOp.toPrimOp,
                    Assembly.ResourceObserver.ofPrimOp?, targetFinal]
                have hOutputsLength :
                    canonicalOutputs.length =
                      Expressions.Structured.BasicOp.outputs .mstore8 :=
                  Locals.Source.PrimitiveSemantics.structured_eval_length
                    hSourceEval
                have hFinalSharedMachine :
                    targetFinal.source.evm.toMachineState =
                      targetSharedFinal.toMachineState := by
                  change evmFinal.toMachineState =
                    targetSharedFinal.toMachineState
                  exact congrArg EvmYul.SharedState.toMachineState hEvmShared
                have hConcreteMachine :
                    targetFinal.source.evm.toMachineState =
                      targetArgs.source.evm.toMachineState.mstore8
                        address value := by
                  exact hFinalSharedMachine.trans hTargetMachine
                have hMemoryMono :
                    targetArgs.source.evm.toMachineState.memory.size ≤
                      targetFinal.source.evm.toMachineState.memory.size := by
                  rw [hFinalSharedMachine]
                  exact hTargetMemory
                have hActiveMono :
                    targetArgs.source.evm.activeWords.toNat ≤
                      targetFinal.source.evm.activeWords.toNat := by
                  rw [hFinalSharedMachine]
                  exact hTargetActive
                have hFinalActiveNoWrap :
                    targetFinal.source.evm.activeWords.toNat *
                        MemoryContract.wordBytes <
                      EvmYul.UInt256.size := by
                  rw [hFinalSharedMachine]
                  exact hFinalNoWrap
                have hFinalStack :
                    targetFinal.source.evm.stack =
                      canonicalOutputs.reverse ++
                        targetInitial.source.evm.stack := by
                  simpa [targetFinal] using hEvmStack
                have hOldStore :
                    StoreRel plan live
                      (stackOffset + [value, address].reverse.length)
                      frameBase sourceArgs.source targetArgs.source := by
                  simpa [hArgsRel.valuesLength] using
                    hArgsRel.state.base.core.store
                obtain
                    ⟨reservation, hReservation, _hFrameReserved⟩ :=
                  hArgsRel.state.frameReserved
                have hAllowed' :
                    reservation.sourceAccessAllowed address.toNat 1 := by
                  simpa [AllocationObserverSafety.RegionAllowed,
                    hReservation] using hAllowed
                let bytes : ByteArray :=
                  ⟨#[UInt8.ofNat value.toNat]⟩
                have hBytes : bytes.size = 1 := by
                  rfl
                have hWrittenMemory :
                    targetFinal.source.evm.toMachineState.memory =
                      (EvmYul.writeBytes bytes 0
                        targetArgs.source.evm.toMachineState
                        address.toNat 1).memory := by
                  rw [hConcreteMachine]
                  rfl
                have hScratchStable :
                    ∀ name slot,
                      name ∈ live →
                      plan.location? name = some (.scratch slot) →
                      targetFinal.source.evm.toMachineState.lookupMemory
                          (EvmYul.UInt256.ofNat
                            (scratchAddress frameBase slot)) =
                        targetArgs.source.evm.toMachineState.lookupMemory
                          (EvmYul.UInt256.ofNat
                            (scratchAddress frameBase slot)) := by
                  intro name slot hLive hLocation
                  have hSlotRegion :=
                    hArgsRel.state.scratchAddress_reserved
                      hLive hLocation hReservation
                  have hDisjoint :
                      scratchAddress frameBase slot +
                            MemoryContract.wordBytes ≤ address.toNat ∨
                        address.toNat + 1 ≤
                          scratchAddress frameBase slot := by
                    rcases hAllowed' with hBefore | hAfter
                    · exact Or.inr (hBefore.trans hSlotRegion.1)
                    · exact Or.inl (hSlotRegion.2.trans hAfter)
                  have hQueryLt :
                      scratchAddress frameBase slot <
                        EvmYul.UInt256.size := by
                    exact lt_of_lt_of_le
                      (Nat.lt_add_of_pos_right
                        (by decide : 0 < MemoryContract.wordBytes))
                      (Nat.le_of_lt
                        (hArgsRel.state.scratchAddress_end_lt_size
                          hLive hLocation))
                  exact
                    Compiler.MemoryRelation.lookupMemory_eq_of_writeBytes_disjoint_growing
                      bytes targetArgs.source.evm.toMachineState
                      targetFinal.source.evm.toMachineState
                      address.toNat 1 (scratchAddress frameBase slot)
                      hBytes (by decide) hHost hWrittenMemory
                      (EvmYul.UInt256.toNat_ofNat_of_lt hQueryLt)
                      (hArgsRel.state.scratchAddress_end_le_memory
                        hLive hLocation)
                      (hArgsRel.state.scratchAddress_end_le_active
                        hLive hLocation)
                      hArgsRel.state.activeNoWrap hActiveMono
                      hFinalActiveNoWrap hDisjoint
                have hBaseRel :
                    StateRel contract plan live
                      (stackOffset + canonicalOutputs.reverse.length)
                      frameBase
                      (sourceArgs.withSource
                        (sourceArgs.source.withShared sourceSharedFinal))
                      targetFinal := by
                  refine ⟨?_, ?_⟩
                  · simpa [targetFinal] using
                      hArgsRel.state.base.cursor
                  · refine ⟨?_, ?_, ?_⟩
                    · simpa [targetFinal, hEvmShared] using
                        hSharedFinal.machine
                    · simpa [targetFinal, hEvmShared] using
                        hSharedFinal.world
                    · exact
                        StoreRel.rebase_prefix_of_lookup
                          (oldPrefix := [value, address].reverse)
                          (newPrefix := canonicalOutputs.reverse)
                          (baseStack := targetInitial.source.evm.stack)
                          hOldStore hArgsRel.stack hFinalStack
                          hScratchStable rfl
                have hOldScratch :
                    ScratchStateRel contract plan live
                      (stackOffset + [value, address].reverse.length)
                      frameBase frameDepth frameWords
                      sourceArgs targetArgs := by
                  simpa [hArgsRel.valuesLength] using hArgsRel.state
                have hScratchRel :
                    ScratchStateRel contract plan live
                      (stackOffset + canonicalOutputs.reverse.length)
                      frameBase frameDepth frameWords
                      (sourceArgs.withSource
                        (sourceArgs.source.withShared sourceSharedFinal))
                      targetFinal :=
                  ScratchStateRel.rebase_prefix_mono
                    (oldPrefix := [value, address].reverse)
                    (newPrefix := canonicalOutputs.reverse)
                    (baseStack := targetInitial.source.evm.stack)
                    hOldScratch hBaseRel hArgsRel.stack hFinalStack
                    hMemoryMono hActiveMono hFinalActiveNoWrap
                refine ⟨targetFinal, hRun, ?_, hOutputsLength, hFinalStack⟩
                simpa [List.length_reverse, hOutputsLength] using hScratchRel

/--
One decoded canonical byte-copy invocation.

The opcode owner identifies the source offset, destination, and length,
extracts the destination-disjointness facts needed by allocation, and proves
the exact shared-state simulation. This interface does not define an
interpreter or compiler.
-/
structure CopyInvocation (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) (values : List Word) where
  sourceOffset : Word
  destination : Word
  size : Word
  writeSafe :
    ∀ {sourceMachine : EvmYul.MachineState},
    AllocationObserverSafety.PrimitiveMemorySafe contract op
        sourceMachine values →
      AllocationObserverSafety.RegionAllowed contract
          destination.toNat size.toNat ∧
        destination.toNat + size.toNat < USize.size
  simulate :
    ∀ {sourceShared sourceFinal targetShared : EvmYul.SharedState .EVM}
      {outputs : List Word},
      SharedRel contract sourceShared targetShared →
      AllocationObserverSafety.PrimitiveMemorySafe contract op
          sourceShared.toMachineState values →
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size →
      Locals.Source.PrimitiveSemantics.structured.eval op sourceShared
          values =
        .ok (sourceFinal, outputs) →
      ∃ (targetFinal : EvmYul.SharedState .EVM) (copied : ByteArray),
        Locals.Source.PrimitiveSemantics.structured.eval op targetShared
            values =
          .ok (targetFinal, outputs) ∧
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
            MemoryContract.wordBytes <
          EvmYul.UInt256.size

/--
Pass-owned semantic-family interface for canonical byte-copy primitives.

Successful argument evaluation determines a unique usable copy invocation.
Stack realization, scratch-slot noninterference, memory growth, and observer
preservation are discharged once by `copy_primitiveForward`.
-/
structure CopySpec (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) where
  observerNone :
    Functions.ObserverSemantics.basicOpObserver? op = none
  decode :
    ∀ values,
      values.length = Expressions.Structured.BasicOp.inputs op →
      CopyInvocation contract op values

/--
One adjacent Functions-to-allocated-Expressions theorem for every canonical
byte-copy primitive satisfying `CopySpec`.
-/
theorem copy_primitiveForward
    {contract : MemoryContract.Contract} {op : Structured.BasicOp}
    (spec : CopySpec contract op) :
    AllocationObserverExpression.PrimitiveForward contract op where
  simulate := by
    intro transcript plan live stackOffset frameBase frameDepth frameWords
      sourceArgs sourceFinal targetInitial targetArgs values outputs
      hArgsRel hMemory hPrimitive
    have invocation :=
      spec.decode values hArgsRel.valuesLength
    rcases invocation with
      ⟨sourceOffset, destination, size, hWriteSafe, hSimulate⟩
    obtain ⟨hAllowed, hHost⟩ := hWriteSafe hMemory
    have hObserver := spec.observerNone
    cases hSourceEval :
        Locals.Source.PrimitiveSemantics.structured.eval
          op sourceArgs.source.shared values with
    | error err =>
        simp [Functions.ObserverSemantics.primitiveSemantics,
          Locals.ObserverSemantics.primitiveSemantics,
          hObserver, hSourceEval] at hPrimitive
    | ok result =>
        rcases result with
          ⟨sourceSharedFinal, canonicalOutputs⟩
        have hPrimitiveResult :
            sourceArgs.withSource
                (sourceArgs.source.withShared sourceSharedFinal) =
              sourceFinal ∧
            canonicalOutputs = outputs := by
          simpa [Functions.ObserverSemantics.primitiveSemantics,
            Locals.ObserverSemantics.primitiveSemantics,
            hObserver, hSourceEval] using hPrimitive
        rcases hPrimitiveResult with ⟨rfl, rfl⟩
        obtain
            ⟨targetSharedFinal, copied, hTargetEval,
              hSharedFinal, hTargetMemory, hMemoryMono,
              hActiveMono, hFinalNoWrap⟩ :=
          hSimulate hArgsRel.state.base.core.shared hMemory
            hArgsRel.state.activeNoWrap hSourceEval
        obtain ⟨evmFinal, hStep, hEvmShared, hEvmStack⟩ :=
          Locals.Source.PrimitiveSemantics.structured_eval_step_exists
            hTargetEval rfl hArgsRel.stack
        let targetFinal :
            Structured.ObserverSemantics.State transcript :=
          targetArgs.withSource
            (targetArgs.source.withEVM evmFinal)
        have hRun :
            Structured.ObserverSemantics.Code.run [.op op] targetArgs =
              .ok targetFinal := by
          change
            Structured.ObserverSemantics.basicOpObserver? op = none
            at hObserver
          simp [Structured.ObserverSemantics.Code.run,
            Structured.EffectSemantics.Code.run,
            Structured.BasicInstr.step, hStep,
            Structured.ObserverSemantics.handler, hObserver,
            targetFinal]
        have hOutputsLength :
            canonicalOutputs.length =
              Expressions.Structured.BasicOp.outputs op :=
          Locals.Source.PrimitiveSemantics.structured_eval_length
            hSourceEval
        have hFinalSharedMachine :
            targetFinal.source.evm.toMachineState =
              targetSharedFinal.toMachineState := by
          change evmFinal.toMachineState =
            targetSharedFinal.toMachineState
          exact congrArg EvmYul.SharedState.toMachineState hEvmShared
        have hMemoryMono' :
            targetArgs.source.evm.toMachineState.memory.size ≤
              targetFinal.source.evm.toMachineState.memory.size := by
          rw [hFinalSharedMachine]
          exact hMemoryMono
        have hActiveMono' :
            targetArgs.source.evm.activeWords.toNat ≤
              targetFinal.source.evm.activeWords.toNat := by
          rw [hFinalSharedMachine]
          exact hActiveMono
        have hFinalActiveNoWrap :
            targetFinal.source.evm.activeWords.toNat *
                MemoryContract.wordBytes <
              EvmYul.UInt256.size := by
          rw [hFinalSharedMachine]
          exact hFinalNoWrap
        have hFinalStack :
            targetFinal.source.evm.stack =
              canonicalOutputs.reverse ++
                targetInitial.source.evm.stack := by
          simpa [targetFinal] using hEvmStack
        have hOldStore :
            StoreRel plan live
              (stackOffset + values.reverse.length)
              frameBase sourceArgs.source targetArgs.source := by
          simpa [List.length_reverse, hArgsRel.valuesLength] using
            hArgsRel.state.base.core.store
        obtain
            ⟨reservation, hReservation, _hFrameReserved⟩ :=
          hArgsRel.state.frameReserved
        have hAllowed' :
            reservation.sourceAccessAllowed
              destination.toNat size.toNat := by
          simpa [AllocationObserverSafety.RegionAllowed,
            hReservation] using hAllowed
        have hWrittenMemory :
            targetFinal.source.evm.toMachineState.memory =
              copied.write sourceOffset.toNat
                targetArgs.source.evm.toMachineState.memory
                destination.toNat size.toNat := by
          rw [hFinalSharedMachine]
          exact hTargetMemory
        have hScratchStable :
            ∀ name slot,
              name ∈ live →
              plan.location? name = some (.scratch slot) →
              targetFinal.source.evm.toMachineState.lookupMemory
                  (EvmYul.UInt256.ofNat
                    (scratchAddress frameBase slot)) =
                targetArgs.source.evm.toMachineState.lookupMemory
                  (EvmYul.UInt256.ofNat
                    (scratchAddress frameBase slot)) := by
          intro name slot hLive hLocation
          have hSlotRegion :=
            hArgsRel.state.scratchAddress_reserved
              hLive hLocation hReservation
          have hDisjoint :
              scratchAddress frameBase slot +
                    MemoryContract.wordBytes ≤ destination.toNat ∨
                destination.toNat + size.toNat ≤
                  scratchAddress frameBase slot := by
            rcases hAllowed' with hBefore | hAfter
            · exact Or.inr (hBefore.trans hSlotRegion.1)
            · exact Or.inl (hSlotRegion.2.trans hAfter)
          have hQueryLt :
              scratchAddress frameBase slot <
                EvmYul.UInt256.size := by
            exact lt_of_lt_of_le
              (Nat.lt_add_of_pos_right
                (by decide : 0 < MemoryContract.wordBytes))
              (Nat.le_of_lt
                (hArgsRel.state.scratchAddress_end_lt_size
                  hLive hLocation))
          exact
            Compiler.MemoryRelation.lookupMemory_eq_of_write_disjoint_growing
              copied targetArgs.source.evm.toMachineState
              targetFinal.source.evm.toMachineState
              sourceOffset.toNat destination.toNat size.toNat
              (scratchAddress frameBase slot)
              hHost hWrittenMemory
              (EvmYul.UInt256.toNat_ofNat_of_lt hQueryLt)
              (hArgsRel.state.scratchAddress_end_le_memory
                hLive hLocation)
              (hArgsRel.state.scratchAddress_end_le_active
                hLive hLocation)
              hArgsRel.state.activeNoWrap hActiveMono'
              hFinalActiveNoWrap hDisjoint
        have hBaseRel :
            StateRel contract plan live
              (stackOffset + canonicalOutputs.reverse.length)
              frameBase
              (sourceArgs.withSource
                (sourceArgs.source.withShared sourceSharedFinal))
              targetFinal := by
          refine ⟨?_, ?_⟩
          · simpa [targetFinal] using hArgsRel.state.base.cursor
          · refine ⟨?_, ?_, ?_⟩
            · simpa [targetFinal, hEvmShared] using
                hSharedFinal.machine
            · simpa [targetFinal, hEvmShared] using
                hSharedFinal.world
            · exact
                StoreRel.rebase_prefix_of_lookup
                  (oldPrefix := values.reverse)
                  (newPrefix := canonicalOutputs.reverse)
                  (baseStack := targetInitial.source.evm.stack)
                  hOldStore hArgsRel.stack hFinalStack
                  hScratchStable rfl
        have hOldScratch :
            ScratchStateRel contract plan live
              (stackOffset + values.reverse.length)
              frameBase frameDepth frameWords
              sourceArgs targetArgs := by
          simpa [List.length_reverse, hArgsRel.valuesLength] using
            hArgsRel.state
        have hScratchRel :
            ScratchStateRel contract plan live
              (stackOffset + canonicalOutputs.reverse.length)
              frameBase frameDepth frameWords
              (sourceArgs.withSource
                (sourceArgs.source.withShared sourceSharedFinal))
              targetFinal :=
          ScratchStateRel.rebase_prefix_mono
            (oldPrefix := values.reverse)
            (newPrefix := canonicalOutputs.reverse)
            (baseStack := targetInitial.source.evm.stack)
            hOldScratch hBaseRel hArgsRel.stack hFinalStack
            hMemoryMono' hActiveMono' hFinalActiveNoWrap
        refine
          ⟨targetFinal, hRun, ?_, hOutputsLength, hFinalStack⟩
        simpa [List.length_reverse, hOutputsLength] using hScratchRel

def CopySpec.stackSpec
    {contract : MemoryContract.Contract} {op : Structured.BasicOp}
    (spec : CopySpec contract op) :
    StackSpec contract op where
  observerNone := spec.observerNone
  simulate := by
    intro sourceShared sourceFinal targetShared values outputs
      hLength hRel hMemory hTargetNoWrap hEval
    have invocation :=
      spec.decode values hLength
    rcases invocation with
      ⟨sourceOffset, destination, size, _hWriteSafe, hSimulate⟩
    obtain
        ⟨targetFinal, copied, hTarget, hFinal,
          _hMemory, _hMemoryMono, _hActive, hFinalNoWrap⟩ :=
      hSimulate hRel hMemory hTargetNoWrap hEval
    exact ⟨targetFinal, hTarget, hFinal, hFinalNoWrap⟩

theorem copy_stackPrimitiveForward
    {contract : MemoryContract.Contract} {op : Structured.BasicOp}
    (spec : CopySpec contract op) :
    AllocationObserverExpression.StackPrimitiveForward contract op :=
  stack_primitiveForward spec.stackSpec

/--
Adapter for the canonical three-argument copy family.
-/
structure Copy3Spec (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) : Prop where
  inputs :
    Expressions.Structured.BasicOp.inputs op = 3
  observerNone :
    Functions.ObserverSemantics.basicOpObserver? op = none
  memorySafe :
    ∀ {machine : EvmYul.MachineState}
      {size sourceOffset destination : Word},
      AllocationObserverSafety.PrimitiveMemorySafe contract op machine
          [size, sourceOffset, destination] →
        Compiler.MemoryRelation.MemoryConsistent machine ∧
          AllocationObserverSafety.RegionAllowed contract
            destination.toNat size.toNat ∧
          Compiler.MemoryRelation.ExpansionNoWrap
            destination.toNat size.toNat ∧
          destination.toNat + size.toNat < USize.size
  simulate :
    ∀ {sourceShared sourceFinal targetShared : EvmYul.SharedState .EVM}
      {destination sourceOffset size : Word} {outputs : List Word},
      SharedRel contract sourceShared targetShared →
      Compiler.MemoryRelation.ExpansionNoWrap
          destination.toNat size.toNat →
      destination.toNat + size.toNat < USize.size →
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size →
      Locals.Source.PrimitiveSemantics.structured.eval op sourceShared
          [size, sourceOffset, destination] =
        .ok (sourceFinal, outputs) →
      ∃ (targetFinal : EvmYul.SharedState .EVM) (copied : ByteArray),
        Locals.Source.PrimitiveSemantics.structured.eval op targetShared
            [size, sourceOffset, destination] =
          .ok (targetFinal, outputs) ∧
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
            MemoryContract.wordBytes <
          EvmYul.UInt256.size

private def Copy3Spec.toCopySpec
    {contract : MemoryContract.Contract} {op : Structured.BasicOp}
    (spec : Copy3Spec contract op) :
    CopySpec contract op where
  observerNone := spec.observerNone
  decode := by
    intro values hLength
    have hLength3 : values.length = 3 :=
      hLength.trans spec.inputs
    cases values with
    | nil =>
        simp at hLength3
    | cons size rest =>
        cases rest with
        | nil =>
            simp at hLength3
        | cons sourceOffset tail =>
            cases tail with
            | nil =>
                simp at hLength3
            | cons destination extra =>
                have hExtra : extra = [] := by
                  simpa using hLength3
                subst extra
                exact
                  { sourceOffset := sourceOffset
                    destination := destination
                    size := size
                    writeSafe := by
                      intro sourceMachine hSafe
                      have hFacts := spec.memorySafe hSafe
                      exact ⟨hFacts.2.1, hFacts.2.2.2⟩
                    simulate := by
                      intro sourceShared sourceFinal targetShared outputs
                        hRel hSafe hNoWrap hEval
                      have hFacts := spec.memorySafe hSafe
                      exact
                        spec.simulate hRel hFacts.2.2.1 hFacts.2.2.2
                          hNoWrap hEval }

/--
Three-argument canonical copy primitives use the general copy-family proof.
-/
theorem copy3_primitiveForward
    {contract : MemoryContract.Contract} {op : Structured.BasicOp}
    (spec : Copy3Spec contract op) :
    AllocationObserverExpression.PrimitiveForward contract op :=
  copy_primitiveForward spec.toCopySpec

private theorem calldatacopy_copy3Spec
    (contract : MemoryContract.Contract) :
    Copy3Spec contract .calldatacopy where
  inputs := rfl
  observerNone := rfl
  memorySafe := by
    intro machine size sourceOffset destination hSafe
    simpa [AllocationObserverSafety.PrimitiveMemorySafe,
      AllocationObserverSafety.PrimitiveExpansionSafe,
      AllocationObserverSafety.PrimitiveHostSafe] using hSafe
  simulate := by
    intro sourceShared sourceFinal targetShared destination sourceOffset size
      outputs hRel hExpansion hHost hNoWrap hEval
    obtain
        ⟨targetFinal, hTargetEval, hShared, hMachine, hMemory,
          hActive, hFinalNoWrap⟩ :=
      calldatacopy_simulate hRel hExpansion hHost hNoWrap hEval
    refine
      ⟨targetFinal, targetShared.executionEnv.calldata,
        hTargetEval, hShared, ?_, hMemory, hActive, hFinalNoWrap⟩
    rw [hMachine]
    rfl

private theorem codecopy_copy3Spec
    (contract : MemoryContract.Contract) :
    Copy3Spec contract .codecopy where
  inputs := rfl
  observerNone := rfl
  memorySafe := by
    intro machine size sourceOffset destination hSafe
    simpa [AllocationObserverSafety.PrimitiveMemorySafe,
      AllocationObserverSafety.PrimitiveExpansionSafe,
      AllocationObserverSafety.PrimitiveHostSafe] using hSafe
  simulate := by
    intro sourceShared sourceFinal targetShared destination sourceOffset size
      outputs hRel hExpansion hHost hNoWrap hEval
    obtain
        ⟨targetFinal, hTargetEval, hShared, hMachine, hMemory,
          hActive, hFinalNoWrap⟩ :=
      codecopy_simulate hRel hExpansion hHost hNoWrap hEval
    refine
      ⟨targetFinal, targetShared.executionEnv.code,
        hTargetEval, hShared, ?_, hMemory, hActive, hFinalNoWrap⟩
    rw [hMachine]
    rfl

private theorem returndatacopy_copy3Spec
    (contract : MemoryContract.Contract) :
    Copy3Spec contract .returndatacopy where
  inputs := rfl
  observerNone := rfl
  memorySafe := by
    intro machine size sourceOffset destination hSafe
    simpa [AllocationObserverSafety.PrimitiveMemorySafe,
      AllocationObserverSafety.PrimitiveExpansionSafe,
      AllocationObserverSafety.PrimitiveHostSafe] using hSafe
  simulate := by
    intro sourceShared sourceFinal targetShared destination sourceOffset size
      outputs hRel hExpansion hHost hNoWrap hEval
    obtain
        ⟨targetFinal, hTargetEval, hShared, hMachine, hMemory,
          hActive, hFinalNoWrap⟩ :=
      returndatacopy_simulate hRel hExpansion hHost hNoWrap hEval
    refine
      ⟨targetFinal, targetShared.toMachineState.returnData,
        hTargetEval, hShared, ?_, hMemory, hActive, hFinalNoWrap⟩
    rw [hMachine]
    rfl

private def extcodecopy_copySpec
    (contract : MemoryContract.Contract) :
    CopySpec contract .extcodecopy where
  observerNone := rfl
  decode := by
    intro values hLength
    have hLength4 : values.length = 4 := by
      simpa [Expressions.Structured.BasicOp.inputs] using hLength
    cases values with
    | nil =>
        simp at hLength4
    | cons size rest =>
        cases rest with
        | nil =>
            simp at hLength4
        | cons sourceOffset tail =>
            cases tail with
            | nil =>
                simp at hLength4
            | cons destination tail =>
                cases tail with
                | nil =>
                    simp at hLength4
                | cons account extra =>
                    have hExtra : extra = [] := by
                      simpa using hLength4
                    subst extra
                    exact
                      { sourceOffset := sourceOffset
                        destination := destination
                        size := size
                        writeSafe := by
                          intro sourceMachine hSafe
                          have hFacts :
                              Compiler.MemoryRelation.MemoryConsistent
                                  sourceMachine ∧
                                AllocationObserverSafety.RegionAllowed
                                  contract destination.toNat size.toNat ∧
                                Compiler.MemoryRelation.ExpansionNoWrap
                                  destination.toNat size.toNat ∧
                                destination.toNat + size.toNat <
                                  USize.size := by
                            simpa
                              [AllocationObserverSafety.PrimitiveMemorySafe,
                                AllocationObserverSafety.PrimitiveExpansionSafe,
                                AllocationObserverSafety.PrimitiveHostSafe]
                              using hSafe
                          exact ⟨hFacts.2.1, hFacts.2.2.2⟩
                        simulate := by
                          intro sourceShared sourceFinal targetShared outputs
                            hRel hSafe hNoWrap hEval
                          have hFacts :
                              Compiler.MemoryRelation.MemoryConsistent
                                  sourceShared.toMachineState ∧
                                AllocationObserverSafety.RegionAllowed
                                  contract destination.toNat size.toNat ∧
                                Compiler.MemoryRelation.ExpansionNoWrap
                                  destination.toNat size.toNat ∧
                                destination.toNat + size.toNat <
                                  USize.size := by
                            simpa
                              [AllocationObserverSafety.PrimitiveMemorySafe,
                                AllocationObserverSafety.PrimitiveExpansionSafe,
                                AllocationObserverSafety.PrimitiveHostSafe]
                              using hSafe
                          exact
                            extcodecopy_simulate hRel hFacts.2.2.1
                              hFacts.2.2.2 hNoWrap hEval }

private def mcopy_copySpec
    (contract : MemoryContract.Contract) :
    CopySpec contract .mcopy where
  observerNone := rfl
  decode := by
    intro values hLength
    have hLength3 : values.length = 3 := by
      simpa [Expressions.Structured.BasicOp.inputs] using hLength
    cases values with
    | nil =>
        simp at hLength3
    | cons size rest =>
        cases rest with
        | nil =>
            simp at hLength3
        | cons sourceOffset tail =>
            cases tail with
            | nil =>
                simp at hLength3
            | cons destination extra =>
                have hExtra : extra = [] := by
                  simpa using hLength3
                subst extra
                exact
                  { sourceOffset := sourceOffset
                    destination := destination
                    size := size
                    writeSafe := by
                      intro sourceMachine hSafe
                      have hFacts :
                          Compiler.MemoryRelation.MemoryConsistent
                              sourceMachine ∧
                            AllocationObserverSafety.RegionAllowed contract
                              destination.toNat size.toNat ∧
                            AllocationObserverSafety.RegionAllowed contract
                              sourceOffset.toNat size.toNat ∧
                            Compiler.MemoryRelation.ExpansionNoWrap
                              (max destination.toNat sourceOffset.toNat)
                              size.toNat ∧
                            (destination.toNat + size.toNat < USize.size ∧
                              sourceOffset.toNat + size.toNat <
                                USize.size) := by
                        simpa
                          [AllocationObserverSafety.PrimitiveMemorySafe,
                            AllocationObserverSafety.PrimitiveExpansionSafe,
                            AllocationObserverSafety.PrimitiveHostSafe]
                          using hSafe
                      exact ⟨hFacts.2.1, hFacts.2.2.2.2.1⟩
                    simulate := by
                      intro sourceShared sourceFinal targetShared outputs
                        hRel hSafe hNoWrap hEval
                      have hFacts :
                          Compiler.MemoryRelation.MemoryConsistent
                              sourceShared.toMachineState ∧
                            AllocationObserverSafety.RegionAllowed contract
                              destination.toNat size.toNat ∧
                            AllocationObserverSafety.RegionAllowed contract
                              sourceOffset.toNat size.toNat ∧
                            Compiler.MemoryRelation.ExpansionNoWrap
                              (max destination.toNat sourceOffset.toNat)
                              size.toNat ∧
                            (destination.toNat + size.toNat < USize.size ∧
                              sourceOffset.toNat + size.toNat <
                                USize.size) := by
                        simpa
                          [AllocationObserverSafety.PrimitiveMemorySafe,
                            AllocationObserverSafety.PrimitiveExpansionSafe,
                            AllocationObserverSafety.PrimitiveHostSafe]
                          using hSafe
                      obtain
                          ⟨targetFinal, hTargetEval, hShared, hMemory,
                            hMemoryMono, hActiveMono, hFinalNoWrap⟩ :=
                        mcopy_simulate hRel hFacts.2.2.1
                          hFacts.2.2.2.1 hFacts.2.2.2.2.1
                          hNoWrap hEval
                      exact
                        ⟨targetFinal, targetShared.toMachineState.memory,
                          hTargetEval, hShared, hMemory, hMemoryMono,
                          hActiveMono, hFinalNoWrap⟩ }

/--
Adjacent Functions-to-allocated-Expressions preservation for canonical
`calldatacopy`.
-/
theorem calldatacopy_primitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.PrimitiveForward contract .calldatacopy :=
  copy3_primitiveForward (calldatacopy_copy3Spec contract)

/--
Adjacent Functions-to-allocated-Expressions preservation for canonical
`codecopy`.
-/
theorem codecopy_primitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.PrimitiveForward contract .codecopy :=
  copy3_primitiveForward (codecopy_copy3Spec contract)

/--
Adjacent Functions-to-allocated-Expressions preservation for canonical
`returndatacopy`.
-/
theorem returndatacopy_primitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.PrimitiveForward contract .returndatacopy :=
  copy3_primitiveForward (returndatacopy_copy3Spec contract)

/--
Adjacent Functions-to-allocated-Expressions preservation for canonical
`extcodecopy`.
-/
theorem extcodecopy_primitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.PrimitiveForward contract .extcodecopy :=
  copy_primitiveForward (extcodecopy_copySpec contract)

/--
Adjacent Functions-to-allocated-Expressions preservation for canonical
`mcopy`.
-/
theorem mcopy_primitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.PrimitiveForward contract .mcopy :=
  copy_primitiveForward (mcopy_copySpec contract)

theorem calldatacopy_stackPrimitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.StackPrimitiveForward
      contract .calldatacopy :=
  copy_stackPrimitiveForward
    (calldatacopy_copy3Spec contract).toCopySpec

theorem codecopy_stackPrimitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.StackPrimitiveForward
      contract .codecopy :=
  copy_stackPrimitiveForward
    (codecopy_copy3Spec contract).toCopySpec

theorem returndatacopy_stackPrimitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.StackPrimitiveForward
      contract .returndatacopy :=
  copy_stackPrimitiveForward
    (returndatacopy_copy3Spec contract).toCopySpec

theorem extcodecopy_stackPrimitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.StackPrimitiveForward
      contract .extcodecopy :=
  copy_stackPrimitiveForward (extcodecopy_copySpec contract)

theorem mcopy_stackPrimitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.StackPrimitiveForward
      contract .mcopy :=
  copy_stackPrimitiveForward (mcopy_copySpec contract)

theorem keccak256_stackPrimitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.StackPrimitiveForward
      contract .keccak256 :=
  read_stackPrimitiveForward (keccak256_readSpec contract)

theorem LogFamily.stackPrimitiveForward
    {op : Structured.BasicOp}
    (family : LogFamily op)
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.StackPrimitiveForward contract op :=
  read_stackPrimitiveForward (family.readSpec contract)

theorem log0_stackPrimitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.StackPrimitiveForward contract .log0 :=
  LogFamily.log0.stackPrimitiveForward contract

theorem log1_stackPrimitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.StackPrimitiveForward contract .log1 :=
  LogFamily.log1.stackPrimitiveForward contract

theorem log2_stackPrimitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.StackPrimitiveForward contract .log2 :=
  LogFamily.log2.stackPrimitiveForward contract

theorem log3_stackPrimitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.StackPrimitiveForward contract .log3 :=
  LogFamily.log3.stackPrimitiveForward contract

theorem log4_stackPrimitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.StackPrimitiveForward contract .log4 :=
  LogFamily.log4.stackPrimitiveForward contract

end MemoryFamily

/--
Primitives rejected by the canonical stack-free Functions semantics cannot
occur in a successful source evaluation. This covers backend-only DUP/SWAP
instructions without assigning them a second source meaning.
-/
theorem rejected_primitiveForward
    {op : Structured.BasicOp}
    (contract : MemoryContract.Contract)
    (hObserver :
      Functions.ObserverSemantics.basicOpObserver? op = none)
    (hRejected :
      Locals.Source.PrimitiveSemantics.sourceContinuingStep? op = none) :
    AllocationObserverExpression.PrimitiveForward contract op where
  simulate := by
    intro transcript plan live stackOffset frameBase frameDepth frameWords
      sourceArgs sourceFinal targetInitial targetArgs values outputs
      _hArgsRel _hMemory hPrimitive
    by_cases hLength :
        values.length = Expressions.Structured.BasicOp.inputs op
    · simp [Functions.ObserverSemantics.primitiveSemantics,
        Locals.ObserverSemantics.primitiveSemantics, hObserver,
        Locals.Source.PrimitiveSemantics.structured, hRejected,
        hLength] at hPrimitive
    · simp [Functions.ObserverSemantics.primitiveSemantics,
        Locals.ObserverSemantics.primitiveSemantics, hObserver,
        Locals.Source.PrimitiveSemantics.structured, hLength] at hPrimitive

/--
Canonical `invalid` always errors, so it also has no successful source
evaluation to preserve.
-/
theorem invalid_primitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.PrimitiveForward contract .invalid where
  simulate := by
    intro transcript plan live stackOffset frameBase frameDepth frameWords
      sourceArgs sourceFinal targetInitial targetArgs values outputs
      _hArgsRel _hMemory hPrimitive
    have hObserver :
        Functions.ObserverSemantics.basicOpObserver? .invalid = none := by
      rfl
    by_cases hLength :
        values.length =
          Expressions.Structured.BasicOp.inputs .invalid
    · simp [Functions.ObserverSemantics.primitiveSemantics,
        Locals.ObserverSemantics.primitiveSemantics,
        hObserver,
        Locals.Source.PrimitiveSemantics.structured,
        Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
        Structured.BasicOp.toPrimOp, Assembly.PrimOp.continuingStep?,
        Assembly.PrimStep.run, hLength] at hPrimitive
    · simp [Functions.ObserverSemantics.primitiveSemantics,
        Locals.ObserverSemantics.primitiveSemantics,
        hObserver,
        Locals.Source.PrimitiveSemantics.structured,
        hLength] at hPrimitive

/--
External call/create primitives are excluded by the source-facing memory-safety
judgment for the checked no-external-effects theorem.
-/
theorem externallyEffectful_primitiveForward
    {op : Structured.BasicOp}
    (contract : MemoryContract.Contract)
    (hImpossible :
      ∀ machine values,
        ¬ AllocationObserverSafety.PrimitiveMemorySafe
          contract op machine values) :
    AllocationObserverExpression.PrimitiveForward contract op where
  simulate := by
    intro transcript plan live stackOffset frameBase frameDepth frameWords
      sourceArgs sourceFinal targetInitial targetArgs values outputs
      _hArgsRel hMemory _hPrimitive
    exact False.elim (hImpossible _ _ hMemory)

theorem rejected_stackPrimitiveForward
    {op : Structured.BasicOp}
    (contract : MemoryContract.Contract)
    (hObserver :
      Functions.ObserverSemantics.basicOpObserver? op = none)
    (hRejected :
      Locals.Source.PrimitiveSemantics.sourceContinuingStep? op = none) :
    AllocationObserverExpression.StackPrimitiveForward contract op where
  simulate := by
    intro transcript plan live stackOffset frameBase
      sourceArgs sourceFinal targetInitial targetArgs values outputs
      _hOnly _hActive _hArgsRel _hMemory hPrimitive
    by_cases hLength :
        values.length = Expressions.Structured.BasicOp.inputs op
    · simp [Functions.ObserverSemantics.primitiveSemantics,
        Locals.ObserverSemantics.primitiveSemantics, hObserver,
        Locals.Source.PrimitiveSemantics.structured, hRejected,
        hLength] at hPrimitive
    · simp [Functions.ObserverSemantics.primitiveSemantics,
        Locals.ObserverSemantics.primitiveSemantics, hObserver,
        Locals.Source.PrimitiveSemantics.structured, hLength] at hPrimitive

theorem invalid_stackPrimitiveForward
    (contract : MemoryContract.Contract) :
    AllocationObserverExpression.StackPrimitiveForward
      contract .invalid where
  simulate := by
    intro transcript plan live stackOffset frameBase
      sourceArgs sourceFinal targetInitial targetArgs values outputs
      _hOnly _hActive _hArgsRel _hMemory hPrimitive
    have hObserver :
        Functions.ObserverSemantics.basicOpObserver? .invalid = none := by
      rfl
    by_cases hLength :
        values.length =
          Expressions.Structured.BasicOp.inputs .invalid
    · simp [Functions.ObserverSemantics.primitiveSemantics,
        Locals.ObserverSemantics.primitiveSemantics,
        hObserver,
        Locals.Source.PrimitiveSemantics.structured,
        Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
        Structured.BasicOp.toPrimOp, Assembly.PrimOp.continuingStep?,
        Assembly.PrimStep.run, hLength] at hPrimitive
    · simp [Functions.ObserverSemantics.primitiveSemantics,
        Locals.ObserverSemantics.primitiveSemantics,
        hObserver,
        Locals.Source.PrimitiveSemantics.structured,
        hLength] at hPrimitive

theorem externallyEffectful_stackPrimitiveForward
    {op : Structured.BasicOp}
    (contract : MemoryContract.Contract)
    (hImpossible :
      ∀ machine values,
        ¬ AllocationObserverSafety.PrimitiveMemorySafe
          contract op machine values) :
    AllocationObserverExpression.StackPrimitiveForward contract op where
  simulate := by
    intro transcript plan live stackOffset frameBase
      sourceArgs sourceFinal targetInitial targetArgs values outputs
      _hOnly _hActive _hArgsRel hMemory _hPrimitive
    exact False.elim (hImpossible _ _ hMemory)

/--
Complete primitive interface for the checked no-external-effects allocation
boundary.

Every `Structured.BasicOp` is classified through an existing semantic family,
an observer primitive, a memory-family theorem, or an impossible successful
source case. No compiler implementation or generated-code evidence appears in
the interface.
-/
theorem canonicalPrimitiveForward
    (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) :
    AllocationObserverExpression.PrimitiveForward contract op := by
  cases op <;>
    first
    | exact AllocationObserverExpression.PrimitiveForward.gas contract
    | exact AllocationObserverExpression.PrimitiveForward.msize contract
    | exact MemoryFamily.mload_primitiveForward contract
    | exact MemoryFamily.mstore_primitiveForward contract
    | exact MemoryFamily.mstore8_primitiveForward contract
    | exact MemoryFamily.calldatacopy_primitiveForward contract
    | exact MemoryFamily.codecopy_primitiveForward contract
    | exact MemoryFamily.returndatacopy_primitiveForward contract
    | exact MemoryFamily.extcodecopy_primitiveForward contract
    | exact MemoryFamily.mcopy_primitiveForward contract
    | exact MemoryFamily.keccak256_primitiveForward contract
    | exact MemoryFamily.log0_primitiveForward contract
    | exact MemoryFamily.log1_primitiveForward contract
    | exact MemoryFamily.log2_primitiveForward contract
    | exact MemoryFamily.log3_primitiveForward contract
    | exact MemoryFamily.log4_primitiveForward contract
    | exact SharedFamily.primitiveForward (.bin _ rfl)
    | exact SharedFamily.primitiveForward (.un _ rfl)
    | exact SharedFamily.primitiveForward (.tri _ rfl)
    | exact SharedFamily.primitiveForward (.pop rfl)
    | exact SharedFamily.primitiveForward (.executionEnv _ rfl)
    | exact SharedFamily.primitiveForward (.unaryExecutionEnv _ rfl)
    | exact SharedFamily.primitiveForward (.state _ rfl)
    | exact SharedFamily.primitiveForward (.unaryState _ rfl)
    | exact SharedFamily.primitiveForward (.binaryState _ rfl)
    | exact SharedFamily.primitiveForward .returnDataSize
    | exact rejected_primitiveForward contract rfl rfl
    | exact invalid_primitiveForward contract
    | exact externallyEffectful_primitiveForward contract (by
        intro machine values
        simp [AllocationObserverSafety.PrimitiveMemorySafe])

/--
Complete primitive interface for a stack-only activation.
-/
theorem canonicalStackPrimitiveForward
    (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) :
    AllocationObserverExpression.StackPrimitiveForward contract op := by
  cases op <;>
    first
    | exact AllocationObserverExpression.StackPrimitiveForward.gas contract
    | exact AllocationObserverExpression.StackPrimitiveForward.msize contract
    | exact MemoryFamily.mload_stackPrimitiveForward contract
    | exact MemoryFamily.mstore_stackPrimitiveForward contract
    | exact MemoryFamily.mstore8_stackPrimitiveForward contract
    | exact MemoryFamily.calldatacopy_stackPrimitiveForward contract
    | exact MemoryFamily.codecopy_stackPrimitiveForward contract
    | exact MemoryFamily.returndatacopy_stackPrimitiveForward contract
    | exact MemoryFamily.extcodecopy_stackPrimitiveForward contract
    | exact MemoryFamily.mcopy_stackPrimitiveForward contract
    | exact MemoryFamily.keccak256_stackPrimitiveForward contract
    | exact MemoryFamily.log0_stackPrimitiveForward contract
    | exact MemoryFamily.log1_stackPrimitiveForward contract
    | exact MemoryFamily.log2_stackPrimitiveForward contract
    | exact MemoryFamily.log3_stackPrimitiveForward contract
    | exact MemoryFamily.log4_stackPrimitiveForward contract
    | exact SharedFamily.stackPrimitiveForward (.bin _ rfl)
    | exact SharedFamily.stackPrimitiveForward (.un _ rfl)
    | exact SharedFamily.stackPrimitiveForward (.tri _ rfl)
    | exact SharedFamily.stackPrimitiveForward (.pop rfl)
    | exact SharedFamily.stackPrimitiveForward (.executionEnv _ rfl)
    | exact SharedFamily.stackPrimitiveForward (.unaryExecutionEnv _ rfl)
    | exact SharedFamily.stackPrimitiveForward (.state _ rfl)
    | exact SharedFamily.stackPrimitiveForward (.unaryState _ rfl)
    | exact SharedFamily.stackPrimitiveForward (.binaryState _ rfl)
    | exact SharedFamily.stackPrimitiveForward .returnDataSize
    | exact rejected_stackPrimitiveForward contract rfl rfl
    | exact invalid_stackPrimitiveForward contract
    | exact externallyEffectful_stackPrimitiveForward contract (by
        intro machine values
        simp [AllocationObserverSafety.PrimitiveMemorySafe])

/--
Complete activation-aware primitive interface used by the single recursive
expression proof.
-/
theorem canonicalActivationPrimitiveForward
    (contract : MemoryContract.Contract)
    (op : Structured.BasicOp) :
    AllocationObserverExpression.ActivationPrimitiveForward contract op where
  stack := canonicalStackPrimitiveForward contract op
  scratch := canonicalPrimitiveForward contract op

end AllocationObserverPrimitive
end Functions
end EvmCompiler
