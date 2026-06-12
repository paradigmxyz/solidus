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

namespace MemoryFamily

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

end MemoryFamily

end AllocationObserverPrimitive
end Functions
end EvmCompiler
