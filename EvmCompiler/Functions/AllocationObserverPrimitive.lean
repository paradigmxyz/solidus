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

end AllocationObserverPrimitive
end Functions
end EvmCompiler
