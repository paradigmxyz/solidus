import EvmCompiler.Yul.FunctionsObserverPrimitive.Core

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverPrimitive

inductive EnvironmentNullary :
    EvmYul.Operation .Yul → Structured.BasicOp →
      (EvmYul.ExecutionEnv .Yul → Word) →
      (EvmYul.ExecutionEnv .EVM → Word) → Prop where
  | address :
      EnvironmentNullary (.Env .ADDRESS) .address
        (EvmYul.UInt256.ofNat ∘ Fin.val ∘
          EvmYul.ExecutionEnv.codeOwner)
        (EvmYul.UInt256.ofNat ∘ Fin.val ∘
          EvmYul.ExecutionEnv.codeOwner)
  | origin :
      EnvironmentNullary (.Env .ORIGIN) .origin
        (EvmYul.UInt256.ofNat ∘ Fin.val ∘
          EvmYul.ExecutionEnv.sender)
        (EvmYul.UInt256.ofNat ∘ Fin.val ∘
          EvmYul.ExecutionEnv.sender)
  | caller :
      EnvironmentNullary (.Env .CALLER) .caller
        (EvmYul.UInt256.ofNat ∘ Fin.val ∘
          EvmYul.ExecutionEnv.source)
        (EvmYul.UInt256.ofNat ∘ Fin.val ∘
          EvmYul.ExecutionEnv.source)
  | callvalue :
      EnvironmentNullary (.Env .CALLVALUE) .callvalue
        EvmYul.ExecutionEnv.weiValue
        EvmYul.ExecutionEnv.weiValue
  | calldatasize :
      EnvironmentNullary (.Env .CALLDATASIZE) .calldatasize
        (EvmYul.UInt256.ofNat ∘ ByteArray.size ∘
          EvmYul.ExecutionEnv.calldata)
        (EvmYul.UInt256.ofNat ∘ ByteArray.size ∘
          EvmYul.ExecutionEnv.calldata)
  | codesize :
      EnvironmentNullary (.Env .CODESIZE) .codesize
        (EvmYul.UInt256.ofNat ∘ ByteArray.size ∘
          EvmYul.ExecutionEnv.codeBytes)
        (EvmYul.UInt256.ofNat ∘ ByteArray.size ∘
          EvmYul.ExecutionEnv.code)
  | gasprice :
      EnvironmentNullary (.Env .GASPRICE) .gasprice
        (EvmYul.UInt256.ofNat ∘ EvmYul.ExecutionEnv.gasPrice)
        (EvmYul.UInt256.ofNat ∘ EvmYul.ExecutionEnv.gasPrice)
  | prevrandao :
      EnvironmentNullary (.Block .PREVRANDAO) .prevrandao
        EvmYul.prevRandao EvmYul.prevRandao
  | basefee :
      EnvironmentNullary (.Block .BASEFEE) .basefee
        EvmYul.basefee EvmYul.basefee
  | blobbasefee :
      EnvironmentNullary (.Block .BLOBBASEFEE) .blobbasefee
        EvmYul.ExecutionEnv.getBlobGasprice
        EvmYul.ExecutionEnv.getBlobGasprice

theorem EnvironmentNullary.metadata
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.ExecutionEnv .Yul → Word}
    {targetResult : EvmYul.ExecutionEnv .EVM → Word}
    (hFamily :
      EnvironmentNullary prim op sourceResult targetResult) :
    Expressions.Structured.BasicOp.inputs op = 0 ∧
      Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
        some (.executionEnv targetResult) ∧
      ObserverSemantics.yulPrimObserver? prim = none ∧
      Functions.ObserverSemantics.basicOpObserver? op = none ∧
      Prim.terminal? prim = none ∧
      Prim.toUncheckedBasicOp? prim = some op := by
  cases hFamily <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem EnvironmentNullary.result_eq
    {codeRel : StateRelation.CodeRel}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.ExecutionEnv .Yul → Word}
    {targetResult : EvmYul.ExecutionEnv .EVM → Word}
    (hFamily :
      EnvironmentNullary prim op sourceResult targetResult)
    {source : EvmYul.ExecutionEnv .Yul}
    {target : EvmYul.ExecutionEnv .EVM}
    (hRel : StateRelation.ExecutionEnv.Rel codeRel source target) :
    sourceResult source = targetResult target := by
  cases hFamily with
  | address =>
      simpa [Function.comp_def] using
        congrArg (fun address => EvmYul.UInt256.ofNat address.val)
          hRel.codeOwner
  | origin =>
      simpa [Function.comp_def] using
        congrArg (fun address => EvmYul.UInt256.ofNat address.val)
          hRel.sender
  | caller =>
      simpa [Function.comp_def] using
        congrArg (fun address => EvmYul.UInt256.ofNat address.val)
          hRel.sourceAddress
  | callvalue =>
      exact hRel.weiValue
  | calldatasize =>
      simpa [Function.comp_def] using
        congrArg (fun bytes => EvmYul.UInt256.ofNat bytes.size)
          hRel.calldata
  | codesize =>
      simpa [Function.comp_def] using
        congrArg (fun bytes => EvmYul.UInt256.ofNat bytes.size)
          hRel.codeImage
  | gasprice =>
      simpa [Function.comp_def] using
        congrArg EvmYul.UInt256.ofNat hRel.gasPrice
  | prevrandao =>
      simpa [EvmYul.prevRandao] using
        congrArg EvmYul.BlockHeader.prevRandao hRel.header
  | basefee =>
      simpa [EvmYul.basefee] using
        congrArg
          (fun header =>
            EvmYul.UInt256.ofNat header.baseFeePerGas)
          hRel.header
  | blobbasefee =>
      simpa [EvmYul.ExecutionEnv.getBlobGasprice] using
        congrArg
          (fun header =>
            EvmYul.UInt256.ofNat header.getBlobGasprice)
          hRel.header

theorem yul_primCall_succ_eq_of_environmentNullary
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.ExecutionEnv .Yul → Word}
    {targetResult : EvmYul.ExecutionEnv .EVM → Word}
    (hFamily :
      EnvironmentNullary prim op sourceResult targetResult)
    (fuel : Nat) (source : EvmYul.Yul.State)
    (args : List Word) :
    EvmYul.Yul.primCall fuel.succ source prim args =
      (match EvmYul.Yul.executionEnvOp sourceResult source args with
      | .ok (state, value?) => .ok (state, value?.toList)
      | .error err => .error err) := by
  cases hFamily <;>
    simp [EvmYul.Yul.primCall] <;>
    unfold EvmYul.step <;>
    rfl

theorem EnvironmentNullary.rawNoObservableFailureAt
    {fuel : Nat} {prim : EvmYul.Operation .Yul}
    {op : Structured.BasicOp}
    {sourceResult : EvmYul.ExecutionEnv .Yul → Word}
    {targetResult : EvmYul.ExecutionEnv .EVM → Word}
    (hFamily :
      EnvironmentNullary prim op sourceResult targetResult) :
    RawNoObservableFailureAt fuel prim := by
  intro source values exception hRun hObservable
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hRun
      subst exception
      simp [Yul.Source.Effectful.Exception.Observable] at hObservable
  | succ previous =>
      rw [yul_primCall_succ_eq_of_environmentNullary hFamily] at hRun
      cases values with
      | nil =>
          simp [EvmYul.Yul.executionEnvOp] at hRun
      | cons head tail =>
          simp [EvmYul.Yul.executionEnvOp] at hRun

theorem forwardAtArity_of_environmentNullary
    {codeRel : StateRelation.CodeRel} {fuel : Nat}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.ExecutionEnv .Yul → Word}
    {targetResult : EvmYul.ExecutionEnv .EVM → Word}
    (hFamily :
      EnvironmentNullary prim op sourceResult targetResult) :
    ForwardAtArity codeRel fuel prim op := by
  intro source source' target sourceValues outputs hRel hArity hCall
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  obtain ⟨hInputs, hStep, _⟩ := hFamily.metadata
  have hValues : sourceValues = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa [hInputs] using hArity
  subst sourceValues
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hCall
  | succ fuel =>
      rw [yul_primCall_succ_eq_of_environmentNullary hFamily] at hCall
      simp [EvmYul.Yul.executionEnvOp] at hCall
      rcases hCall with ⟨rfl, rfl⟩
      have hResult :
          sourceResult sourceShared.executionEnv =
            targetResult target.shared.executionEnv := by
        apply hFamily.result_eq
        exact hShared.world.executionEnv
      refine ⟨target.shared, ?_, ?_, by rfl⟩
      · simp [Locals.Source.PrimitiveSemantics.structured,
          hInputs, hStep, Assembly.PrimStep.run,
          EvmYul.EVM.executionEnvOp,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push,
          EvmYul.Yul.State.executionEnv, hResult]
        rfl
      · simpa [Locals.Source.State.withShared] using
          (show
            StateRelation.Regular.Rel codeRel
              (.Ok sourceShared sourceVars) target from
            ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩)

theorem backwardAt_of_environmentNullary
    {codeRel : StateRelation.CodeRel} (fuel : Nat)
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.ExecutionEnv .Yul → Word}
    {targetResult : EvmYul.ExecutionEnv .EVM → Word}
    (hFamily :
      EnvironmentNullary prim op sourceResult targetResult) :
    BackwardAt codeRel (fuel + 1) prim op := by
  intro source target targetShared sourceValues outputs
    hRel _hPermitted hRun
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  obtain ⟨hInputs, hStep, _⟩ := hFamily.metadata
  cases sourceValues with
  | cons head tail =>
      simp [Locals.Source.PrimitiveSemantics.structured,
        hInputs, Structured.invalid] at hRun
  | nil =>
      have hResult :
          sourceResult sourceShared.executionEnv =
            targetResult target.shared.executionEnv := by
        exact hFamily.result_eq hShared.world.executionEnv
      have hExpected :
          Locals.Source.PrimitiveSemantics.structured.eval
              op target.shared [] =
            .ok
              (target.shared,
                [targetResult target.shared.executionEnv]) := by
        simp [Locals.Source.PrimitiveSemantics.structured,
          hInputs, hStep, Assembly.PrimStep.run,
          EvmYul.EVM.executionEnvOp,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push]
        rfl
      have hRun' :
          Locals.Source.PrimitiveSemantics.structured.eval
              op target.shared [] =
            .ok (targetShared, outputs) := by
        simpa using hRun
      rw [hExpected] at hRun'
      have hPair := Except.ok.inj hRun'
      have hSharedEq := congrArg Prod.fst hPair
      have hOutputsEq := congrArg Prod.snd hPair
      change target.shared = targetShared at hSharedEq
      change
        [targetResult target.shared.executionEnv] = outputs at hOutputsEq
      subst targetShared
      subst outputs
      refine
        ⟨.Ok sourceShared sourceVars, ?_, ?_, rfl⟩
      · rw [yul_primCall_succ_eq_of_environmentNullary hFamily]
        simp [EvmYul.Yul.executionEnvOp,
          EvmYul.Yul.State.executionEnv, hResult]
      · simpa [Locals.Source.State.withShared] using
          (show
            StateRelation.Regular.Rel codeRel
              (.Ok sourceShared sourceVars) target from
            ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩)

theorem safeEnvironmentNullary
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.ExecutionEnv .Yul → Word}
    {targetResult : EvmYul.ExecutionEnv .EVM → Word}
    {sourceValues outputs : List Word}
    (hFamily :
      EnvironmentNullary prim op sourceResult targetResult)
    (hArity :
      sourceValues.length = Expressions.Structured.BasicOp.inputs op)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval fuel.succ source prim sourceValues =
        .ok (source', outputs)) :
    ∃ target' : Functions.ObserverSemantics.State transcript,
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval op target sourceValues.reverse =
        .ok (target', outputs) ∧
      StateRelation.Replay.Rel codeRel source' target' ∧
      source'.source.store = source.source.store := by
  obtain ⟨_hInputs, _hStep, hYulObserver, hFunctionsObserver,
      hTerminal, hOp⟩ := hFamily.metadata
  exact
    safeBasicOpArity hYulObserver hFunctionsObserver hTerminal hOp
      (fun _ => by cases hFamily <;> trivial)
      (forwardAtArity_of_environmentNullary hFamily)
      hArity hRel hRun

inductive EnvironmentUnary :
    EvmYul.Operation .Yul → Structured.BasicOp →
      (EvmYul.ExecutionEnv .Yul → Word → Word) →
      (EvmYul.ExecutionEnv .EVM → Word → Word) → Prop where
  | blobhash :
      EnvironmentUnary (.Block .BLOBHASH) .blobhash
        EvmYul.blobhash EvmYul.blobhash

theorem EnvironmentUnary.metadata
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.ExecutionEnv .Yul → Word → Word}
    {targetResult : EvmYul.ExecutionEnv .EVM → Word → Word}
    (hFamily :
      EnvironmentUnary prim op sourceResult targetResult) :
    Expressions.Structured.BasicOp.inputs op = 1 ∧
      Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
        some (.unaryExecutionEnv targetResult) ∧
      ObserverSemantics.yulPrimObserver? prim = none ∧
      Functions.ObserverSemantics.basicOpObserver? op = none ∧
      Prim.terminal? prim = none ∧
      Prim.toUncheckedBasicOp? prim = some op := by
  cases hFamily <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem EnvironmentUnary.result_eq
    {codeRel : StateRelation.CodeRel}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.ExecutionEnv .Yul → Word → Word}
    {targetResult : EvmYul.ExecutionEnv .EVM → Word → Word}
    (hFamily :
      EnvironmentUnary prim op sourceResult targetResult)
    {source : EvmYul.ExecutionEnv .Yul}
    {target : EvmYul.ExecutionEnv .EVM}
    (hRel : StateRelation.ExecutionEnv.Rel codeRel source target)
    (value : Word) :
    sourceResult source value = targetResult target value := by
  cases hFamily
  simp [EvmYul.blobhash, hRel.blobVersionedHashes]

theorem yul_primCall_succ_eq_of_environmentUnary
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.ExecutionEnv .Yul → Word → Word}
    {targetResult : EvmYul.ExecutionEnv .EVM → Word → Word}
    (hFamily :
      EnvironmentUnary prim op sourceResult targetResult)
    (fuel : Nat) (source : EvmYul.Yul.State)
    (args : List Word) :
    EvmYul.Yul.primCall fuel.succ source prim args =
      (match EvmYul.Yul.unaryExecutionEnvOp
        sourceResult source args with
      | .ok (state, value?) => .ok (state, value?.toList)
      | .error err => .error err) := by
  cases hFamily <;>
    simp [EvmYul.Yul.primCall] <;>
    unfold EvmYul.step <;>
    rfl

theorem EnvironmentUnary.rawNoObservableFailureAt
    {fuel : Nat} {prim : EvmYul.Operation .Yul}
    {op : Structured.BasicOp}
    {sourceResult : EvmYul.ExecutionEnv .Yul → Word → Word}
    {targetResult : EvmYul.ExecutionEnv .EVM → Word → Word}
    (hFamily :
      EnvironmentUnary prim op sourceResult targetResult) :
    RawNoObservableFailureAt fuel prim := by
  intro source values exception hRun hObservable
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hRun
      subst exception
      simp [Yul.Source.Effectful.Exception.Observable] at hObservable
  | succ previous =>
      rw [yul_primCall_succ_eq_of_environmentUnary hFamily] at hRun
      cases values with
      | nil =>
          simp [EvmYul.Yul.unaryExecutionEnvOp] at hRun
          subst exception
          simp [Yul.Source.Effectful.Exception.Observable] at hObservable
      | cons value extra =>
          cases extra with
          | nil =>
              simp [EvmYul.Yul.unaryExecutionEnvOp] at hRun
          | cons head tail =>
              simp [EvmYul.Yul.unaryExecutionEnvOp] at hRun
              subst exception
              simp [Yul.Source.Effectful.Exception.Observable] at hObservable

theorem forwardAt_of_environmentUnary
    {codeRel : StateRelation.CodeRel} {fuel : Nat}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.ExecutionEnv .Yul → Word → Word}
    {targetResult : EvmYul.ExecutionEnv .EVM → Word → Word}
    (hFamily :
      EnvironmentUnary prim op sourceResult targetResult) :
    ForwardAt codeRel fuel prim op := by
  intro source source' target sourceValues outputs hRel hCall
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  obtain ⟨hInputs, hStep, _⟩ := hFamily.metadata
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hCall
  | succ fuel =>
      rw [yul_primCall_succ_eq_of_environmentUnary hFamily] at hCall
      cases sourceValues with
      | nil =>
          simp [EvmYul.Yul.unaryExecutionEnvOp] at hCall
      | cons value rest =>
          cases rest with
          | cons next tail =>
              simp [EvmYul.Yul.unaryExecutionEnvOp] at hCall
          | nil =>
              simp [EvmYul.Yul.unaryExecutionEnvOp] at hCall
              rcases hCall with ⟨rfl, rfl⟩
              have hResult :
                  sourceResult sourceShared.executionEnv value =
                    targetResult target.shared.executionEnv value := by
                exact hFamily.result_eq
                  hShared.world.executionEnv value
              refine ⟨target.shared, ?_, ?_, by rfl⟩
              · simp [Locals.Source.PrimitiveSemantics.structured,
                  hInputs, hStep, Assembly.PrimStep.run,
                  EvmYul.EVM.unaryExecutionEnvOp,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC, EvmYul.Stack.pop,
                  EvmYul.Stack.push, hResult, Id.run]
                simpa using hResult.symm
              · simpa [Locals.Source.State.withShared] using
                  (show
                    StateRelation.Regular.Rel codeRel
                      (.Ok sourceShared sourceVars) target from
                    ⟨sourceShared, sourceVars, rfl,
                      hShared, hVars⟩)

theorem backwardAt_of_environmentUnary
    {codeRel : StateRelation.CodeRel} (fuel : Nat)
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.ExecutionEnv .Yul → Word → Word}
    {targetResult : EvmYul.ExecutionEnv .EVM → Word → Word}
    (hFamily :
      EnvironmentUnary prim op sourceResult targetResult) :
    BackwardAt codeRel (fuel + 1) prim op := by
  intro source target targetShared sourceValues outputs
    hRel _hPermitted hRun
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  obtain ⟨hInputs, hStep, _⟩ := hFamily.metadata
  cases sourceValues with
  | nil =>
      simp [Locals.Source.PrimitiveSemantics.structured,
        hInputs, Structured.invalid] at hRun
  | cons value extra =>
      cases extra with
      | cons head tail =>
          simp [Locals.Source.PrimitiveSemantics.structured,
            hInputs, Structured.invalid] at hRun
      | nil =>
          have hResult :
              sourceResult sourceShared.executionEnv value =
                targetResult target.shared.executionEnv value := by
            exact hFamily.result_eq
              hShared.world.executionEnv value
          have hExpected :
              Locals.Source.PrimitiveSemantics.structured.eval
                  op target.shared [value] =
                .ok
                  (target.shared,
                    [targetResult target.shared.executionEnv value]) := by
            simp [Locals.Source.PrimitiveSemantics.structured,
              hInputs, hStep, Assembly.PrimStep.run,
              EvmYul.EVM.unaryExecutionEnvOp,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC, EvmYul.Stack.pop,
              EvmYul.Stack.push, Id.run]
          have hRun' :
              Locals.Source.PrimitiveSemantics.structured.eval
                  op target.shared [value] =
                .ok (targetShared, outputs) := by
            simpa using hRun
          rw [hExpected] at hRun'
          have hPair := Except.ok.inj hRun'
          have hSharedEq := congrArg Prod.fst hPair
          have hOutputsEq := congrArg Prod.snd hPair
          change target.shared = targetShared at hSharedEq
          change
            [targetResult target.shared.executionEnv value] =
              outputs at hOutputsEq
          subst targetShared
          subst outputs
          refine
            ⟨.Ok sourceShared sourceVars, ?_, ?_, rfl⟩
          · rw [yul_primCall_succ_eq_of_environmentUnary hFamily]
            simp [EvmYul.Yul.unaryExecutionEnvOp,
              EvmYul.Yul.State.executionEnv, hResult]
          · simpa [Locals.Source.State.withShared] using
              (show
                StateRelation.Regular.Rel codeRel
                  (.Ok sourceShared sourceVars) target from
                ⟨sourceShared, sourceVars, rfl,
                  hShared, hVars⟩)

theorem safeEnvironmentUnary
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.ExecutionEnv .Yul → Word → Word}
    {targetResult : EvmYul.ExecutionEnv .EVM → Word → Word}
    {sourceValues outputs : List Word}
    (hFamily :
      EnvironmentUnary prim op sourceResult targetResult)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval fuel.succ source prim sourceValues =
        .ok (source', outputs)) :
    ∃ target' : Functions.ObserverSemantics.State transcript,
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval op target sourceValues.reverse =
        .ok (target', outputs) ∧
      StateRelation.Replay.Rel codeRel source' target' ∧
      source'.source.store = source.source.store := by
  obtain ⟨_hInputs, _hStep, hYulObserver, hFunctionsObserver,
      hTerminal, hOp⟩ := hFamily.metadata
  exact
    safeBasicOp hYulObserver hFunctionsObserver hTerminal hOp
      (fun _ => by cases hFamily <;> trivial)
      (forwardAt_of_environmentUnary hFamily) hRel hRun

theorem safeEnvironmentNullaryBackward
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target target' : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.ExecutionEnv .Yul → Word}
    {targetResult : EvmYul.ExecutionEnv .EVM → Word}
    {sourceValues outputs : List Word}
    (hFamily :
      EnvironmentNullary prim op sourceResult targetResult)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval op target sourceValues.reverse =
        .ok (target', outputs)) :
    ∃ source' : ObserverSemantics.SourceReplay.State transcript,
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval (fuel + 2) source prim sourceValues =
          .ok (source', outputs) ∧
        StateRelation.Replay.Rel codeRel source' target' ∧
        source'.source.store = source.source.store := by
  obtain ⟨_hInputs, _hStep, hYulObserver, hFunctionsObserver,
      hTerminal, hOp⟩ := hFamily.metadata
  simpa using
    (safeBasicOpBackward hYulObserver hFunctionsObserver hTerminal hOp
      (backwardAt_of_environmentNullary
        (codeRel := codeRel) fuel hFamily)
      hRel hRun)

theorem safeEnvironmentUnaryBackward
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target target' : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.ExecutionEnv .Yul → Word → Word}
    {targetResult : EvmYul.ExecutionEnv .EVM → Word → Word}
    {sourceValues outputs : List Word}
    (hFamily :
      EnvironmentUnary prim op sourceResult targetResult)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval op target sourceValues.reverse =
        .ok (target', outputs)) :
    ∃ source' : ObserverSemantics.SourceReplay.State transcript,
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval (fuel + 2) source prim sourceValues =
          .ok (source', outputs) ∧
        StateRelation.Replay.Rel codeRel source' target' ∧
        source'.source.store = source.source.store := by
  obtain ⟨_hInputs, _hStep, hYulObserver, hFunctionsObserver,
      hTerminal, hOp⟩ := hFamily.metadata
  simpa using
    (safeBasicOpBackward hYulObserver hFunctionsObserver hTerminal hOp
      (backwardAt_of_environmentUnary
        (codeRel := codeRel) fuel hFamily)
      hRel hRun)

end FunctionsObserverPrimitive
end Yul
end EvmCompiler
