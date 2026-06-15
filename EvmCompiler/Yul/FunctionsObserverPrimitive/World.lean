import EvmCompiler.Yul.FunctionsObserverPrimitive.Core

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverPrimitive

inductive WorldNullary :
    EvmYul.Operation .Yul → Structured.BasicOp →
      (EvmYul.State .Yul → Word) →
      (EvmYul.State .EVM → Word) → Prop where
  | coinbase :
      WorldNullary (.Block .COINBASE) .coinbase
        (EvmYul.UInt256.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase)
        (EvmYul.UInt256.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase)
  | timestamp :
      WorldNullary (.Block .TIMESTAMP) .timestamp
        EvmYul.State.timeStamp EvmYul.State.timeStamp
  | number :
      WorldNullary (.Block .NUMBER) .number
        EvmYul.State.number EvmYul.State.number
  | gaslimit :
      WorldNullary (.Block .GASLIMIT) .gaslimit
        EvmYul.State.gasLimit EvmYul.State.gasLimit
  | chainid :
      WorldNullary (.Block .CHAINID) .chainid
        EvmYul.State.chainId EvmYul.State.chainId
  | selfbalance :
      WorldNullary (.Block .SELFBALANCE) .selfbalance
        EvmYul.State.selfbalance EvmYul.State.selfbalance

theorem WorldNullary.metadata
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.State .Yul → Word}
    {targetResult : EvmYul.State .EVM → Word}
    (hFamily : WorldNullary prim op sourceResult targetResult) :
    Expressions.Structured.BasicOp.inputs op = 0 ∧
      Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
        some (.state targetResult) ∧
      ObserverSemantics.yulPrimObserver? prim = none ∧
      Functions.ObserverSemantics.basicOpObserver? op = none ∧
      Prim.terminal? prim = none ∧
      Prim.toUncheckedBasicOp? prim = some op := by
  cases hFamily <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem selfbalance_eq
    {codeRel : StateRelation.CodeRel}
    {source : EvmYul.State .Yul}
    {target : EvmYul.State .EVM}
    (hRel : StateRelation.World.Rel codeRel source target) :
    EvmYul.State.selfbalance source =
      EvmYul.State.selfbalance target := by
  unfold EvmYul.State.selfbalance
  rw [← hRel.executionEnv.codeOwner]
  have hAccount :=
    hRel.accounts source.executionEnv.codeOwner
  cases hSource :
      source.accountMap.find? source.executionEnv.codeOwner with
  | none =>
      rw [hSource] at hAccount
      cases hTarget :
          target.accountMap.find? source.executionEnv.codeOwner with
      | none =>
          simp [hSource, hTarget]
      | some targetAccount =>
          simp [StateRelation.OptionRel, hTarget] at hAccount
  | some sourceAccount =>
      rw [hSource] at hAccount
      cases hTarget :
          target.accountMap.find? source.executionEnv.codeOwner with
      | none =>
          simp [StateRelation.OptionRel, hTarget] at hAccount
      | some targetAccount =>
          rw [hTarget] at hAccount
          have hAccountRel :
              StateRelation.Account.Rel codeRel
                sourceAccount targetAccount := by
            simpa [StateRelation.OptionRel] using hAccount
          have hBalance :
              sourceAccount.balance = targetAccount.balance := by
            exact hAccountRel.balance
          simp [hSource, hTarget, hBalance]

theorem WorldNullary.result_eq
    {codeRel : StateRelation.CodeRel}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.State .Yul → Word}
    {targetResult : EvmYul.State .EVM → Word}
    (hFamily : WorldNullary prim op sourceResult targetResult)
    {source : EvmYul.State .Yul}
    {target : EvmYul.State .EVM}
    (hRel : StateRelation.World.Rel codeRel source target) :
    sourceResult source = targetResult target := by
  cases hFamily with
  | coinbase =>
      simpa [Function.comp_def, EvmYul.State.coinBase] using
        congrArg
          (fun header =>
            EvmYul.UInt256.ofNat header.beneficiary.val)
          hRel.executionEnv.header
  | timestamp =>
      simpa [EvmYul.State.timeStamp] using
        congrArg
          (fun header => EvmYul.UInt256.ofNat header.timestamp)
          hRel.executionEnv.header
  | number =>
      simpa [EvmYul.State.number] using
        congrArg
          (fun header => EvmYul.UInt256.ofNat header.number)
          hRel.executionEnv.header
  | gaslimit =>
      simpa [EvmYul.State.gasLimit] using
        congrArg
          (fun header => EvmYul.UInt256.ofNat header.gasLimit)
          hRel.executionEnv.header
  | chainid =>
      rfl
  | selfbalance =>
      exact selfbalance_eq hRel

theorem yul_primCall_succ_eq_of_worldNullary
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.State .Yul → Word}
    {targetResult : EvmYul.State .EVM → Word}
    (hFamily : WorldNullary prim op sourceResult targetResult)
    (fuel : Nat) (source : EvmYul.Yul.State)
    (args : List Word) :
    EvmYul.Yul.primCall fuel.succ source prim args =
      (match EvmYul.Yul.stateOp sourceResult source args with
      | .ok (state, value?) => .ok (state, value?.toList)
      | .error err => .error err) := by
  cases hFamily <;>
    simp [EvmYul.Yul.primCall] <;>
    unfold EvmYul.step <;>
    rfl

theorem WorldNullary.rawNoObservableFailureAt
    {fuel : Nat} {prim : EvmYul.Operation .Yul}
    {op : Structured.BasicOp}
    {sourceResult : EvmYul.State .Yul → Word}
    {targetResult : EvmYul.State .EVM → Word}
    (hFamily : WorldNullary prim op sourceResult targetResult) :
    RawNoObservableFailureAt fuel prim := by
  intro source values exception hRun hObservable
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hRun
      subst exception
      simp [Yul.Source.Effectful.Exception.Observable] at hObservable
  | succ previous =>
      rw [yul_primCall_succ_eq_of_worldNullary hFamily] at hRun
      cases values with
      | nil =>
          simp [EvmYul.Yul.stateOp] at hRun
      | cons head tail =>
          simp [EvmYul.Yul.stateOp] at hRun

theorem forwardAtArity_of_worldNullary
    {codeRel : StateRelation.CodeRel} {fuel : Nat}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.State .Yul → Word}
    {targetResult : EvmYul.State .EVM → Word}
    (hFamily : WorldNullary prim op sourceResult targetResult) :
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
      rw [yul_primCall_succ_eq_of_worldNullary hFamily] at hCall
      simp [EvmYul.Yul.stateOp] at hCall
      rcases hCall with ⟨rfl, rfl⟩
      have hResult :
          sourceResult sourceShared.toState =
            targetResult target.shared.toState :=
        hFamily.result_eq hShared.world
      refine ⟨target.shared, ?_, ?_, by rfl⟩
      · simp [Locals.Source.PrimitiveSemantics.structured,
          hInputs, hStep, Assembly.PrimStep.run,
          EvmYul.EVM.stateOp,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push,
          Id.run, hResult] <;>
        simpa [Id.run] using hResult.symm
      · simpa [Locals.Source.State.withShared] using
          (show
            StateRelation.Regular.Rel codeRel
              (.Ok sourceShared sourceVars) target from
            ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩)

theorem backwardAt_of_worldNullary
    {codeRel : StateRelation.CodeRel} (fuel : Nat)
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.State .Yul → Word}
    {targetResult : EvmYul.State .EVM → Word}
    (hFamily : WorldNullary prim op sourceResult targetResult) :
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
          sourceResult sourceShared.toState =
            targetResult target.shared.toState :=
        hFamily.result_eq hShared.world
      have hExpected :
          Locals.Source.PrimitiveSemantics.structured.eval
              op target.shared [] =
            .ok (target.shared,
              [targetResult target.shared.toState]) := by
        simp [Locals.Source.PrimitiveSemantics.structured,
          hInputs, hStep, Assembly.PrimStep.run,
          EvmYul.EVM.stateOp,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push, Id.run]
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
        [targetResult target.shared.toState] = outputs at hOutputsEq
      subst targetShared
      subst outputs
      refine
        ⟨.Ok sourceShared sourceVars, ?_, ?_, rfl⟩
      · rw [yul_primCall_succ_eq_of_worldNullary hFamily]
        change
          Except.ok
              (EvmYul.Yul.State.Ok sourceShared sourceVars,
                [sourceResult sourceShared.toState]) =
            Except.ok
              (EvmYul.Yul.State.Ok sourceShared sourceVars,
                [targetResult target.shared.toState])
        simp [hResult]
      · simpa [Locals.Source.State.withShared] using
          (show
            StateRelation.Regular.Rel codeRel
              (.Ok sourceShared sourceVars) target from
            ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩)

theorem safeWorldNullary
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.State .Yul → Word}
    {targetResult : EvmYul.State .EVM → Word}
    {sourceValues outputs : List Word}
    (hFamily : WorldNullary prim op sourceResult targetResult)
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
      (forwardAtArity_of_worldNullary hFamily)
      hArity hRel hRun

inductive WorldUnaryRead :
    EvmYul.Operation .Yul → Structured.BasicOp →
      (EvmYul.State .Yul → Word → Word) →
      (EvmYul.State .EVM → Word → Word) → Prop where
  | calldataload :
      WorldUnaryRead (.Env .CALLDATALOAD) .calldataload
        EvmYul.State.calldataload EvmYul.State.calldataload
  | blockhash :
      WorldUnaryRead (.Block .BLOCKHASH) .blockhash
        EvmYul.State.blockHash EvmYul.State.blockHash

theorem WorldUnaryRead.metadata
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.State .Yul → Word → Word}
    {targetResult : EvmYul.State .EVM → Word → Word}
    (hFamily : WorldUnaryRead prim op sourceResult targetResult) :
    Expressions.Structured.BasicOp.inputs op = 1 ∧
      Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
        some (.unaryState
          (fun state value => (state, targetResult state value))) ∧
      ObserverSemantics.yulPrimObserver? prim = none ∧
      Functions.ObserverSemantics.basicOpObserver? op = none ∧
      Prim.terminal? prim = none ∧
      Prim.toUncheckedBasicOp? prim = some op := by
  cases hFamily <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem WorldUnaryRead.result_eq
    {codeRel : StateRelation.CodeRel}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.State .Yul → Word → Word}
    {targetResult : EvmYul.State .EVM → Word → Word}
    (hFamily : WorldUnaryRead prim op sourceResult targetResult)
    {source : EvmYul.State .Yul}
    {target : EvmYul.State .EVM}
    (hRel : StateRelation.World.Rel codeRel source target)
    (value : Word) :
    sourceResult source value = targetResult target value := by
  cases hFamily with
  | calldataload =>
      simp [EvmYul.State.calldataload,
        hRel.executionEnv.calldata]
  | blockhash =>
      simp [EvmYul.State.blockHash,
        EvmYul.State.blockHashes,
        hRel.executionEnv.header, hRel.blocks]

theorem yul_primCall_succ_eq_of_worldUnaryRead
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.State .Yul → Word → Word}
    {targetResult : EvmYul.State .EVM → Word → Word}
    (hFamily : WorldUnaryRead prim op sourceResult targetResult)
    (fuel : Nat) (source : EvmYul.Yul.State)
    (args : List Word) :
    EvmYul.Yul.primCall fuel.succ source prim args =
      (match EvmYul.Yul.unaryStateOp
        (fun state value => (state, sourceResult state value))
        source args with
      | .ok (state, value?) => .ok (state, value?.toList)
      | .error err => .error err) := by
  cases hFamily <;>
    simp [EvmYul.Yul.primCall] <;>
    unfold EvmYul.step <;>
    rfl

theorem WorldUnaryRead.rawNoObservableFailureAt
    {fuel : Nat} {prim : EvmYul.Operation .Yul}
    {op : Structured.BasicOp}
    {sourceResult : EvmYul.State .Yul → Word → Word}
    {targetResult : EvmYul.State .EVM → Word → Word}
    (hFamily :
      WorldUnaryRead prim op sourceResult targetResult) :
    RawNoObservableFailureAt fuel prim := by
  intro source values exception hRun hObservable
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hRun
      subst exception
      simp [Yul.Source.Effectful.Exception.Observable] at hObservable
  | succ previous =>
      rw [yul_primCall_succ_eq_of_worldUnaryRead hFamily] at hRun
      cases values with
      | nil =>
          simp [EvmYul.Yul.unaryStateOp] at hRun
          rw [← hRun] at hObservable
          simp [Yul.Source.Effectful.Exception.Observable] at hObservable
      | cons value extra =>
          cases extra with
          | nil =>
              simp [EvmYul.Yul.unaryStateOp] at hRun
          | cons head tail =>
              simp [EvmYul.Yul.unaryStateOp] at hRun
              rw [← hRun] at hObservable
              simp [Yul.Source.Effectful.Exception.Observable] at hObservable

theorem forwardAt_of_worldUnaryRead
    {codeRel : StateRelation.CodeRel} {fuel : Nat}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.State .Yul → Word → Word}
    {targetResult : EvmYul.State .EVM → Word → Word}
    (hFamily : WorldUnaryRead prim op sourceResult targetResult) :
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
      rw [yul_primCall_succ_eq_of_worldUnaryRead hFamily] at hCall
      cases sourceValues with
      | nil =>
          simp [EvmYul.Yul.unaryStateOp] at hCall
      | cons value rest =>
          cases rest with
          | cons next tail =>
              simp [EvmYul.Yul.unaryStateOp] at hCall
          | nil =>
              simp [EvmYul.Yul.unaryStateOp,
                EvmYul.Yul.State.setSharedState] at hCall
              rcases hCall with ⟨rfl, rfl⟩
              have hResult :
                  sourceResult sourceShared.toState value =
                    targetResult target.shared.toState value :=
                hFamily.result_eq hShared.world value
              refine ⟨target.shared, ?_, ?_, by rfl⟩
              · simp [Locals.Source.PrimitiveSemantics.structured,
                  hInputs, hStep, Assembly.PrimStep.run,
                  EvmYul.EVM.unaryStateOp,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC, EvmYul.Stack.pop,
                  EvmYul.Stack.push, Id.run, hResult] <;>
                simpa using hResult.symm
              · simpa [Locals.Source.State.withShared] using
                  (show
                    StateRelation.Regular.Rel codeRel
                      (.Ok sourceShared sourceVars) target from
                    ⟨sourceShared, sourceVars, rfl,
                      hShared, hVars⟩)

theorem backwardAt_of_worldUnaryRead
    {codeRel : StateRelation.CodeRel} (fuel : Nat)
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.State .Yul → Word → Word}
    {targetResult : EvmYul.State .EVM → Word → Word}
    (hFamily : WorldUnaryRead prim op sourceResult targetResult) :
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
              sourceResult sourceShared.toState value =
                targetResult target.shared.toState value :=
            hFamily.result_eq hShared.world value
          have hExpected :
              Locals.Source.PrimitiveSemantics.structured.eval
                  op target.shared [value] =
                .ok (target.shared,
                  [targetResult target.shared.toState value]) := by
            simp [Locals.Source.PrimitiveSemantics.structured,
              hInputs, hStep, Assembly.PrimStep.run,
              EvmYul.EVM.unaryStateOp,
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
            [targetResult target.shared.toState value] =
              outputs at hOutputsEq
          subst targetShared
          subst outputs
          refine
            ⟨.Ok sourceShared sourceVars, ?_, ?_, rfl⟩
          · rw [yul_primCall_succ_eq_of_worldUnaryRead hFamily]
            change
              Except.ok
                  (EvmYul.Yul.State.Ok sourceShared sourceVars,
                    [sourceResult sourceShared.toState value]) =
                Except.ok
                  (EvmYul.Yul.State.Ok sourceShared sourceVars,
                    [targetResult target.shared.toState value])
            simp [hResult]
          · simpa [Locals.Source.State.withShared] using
              (show
                StateRelation.Regular.Rel codeRel
                  (.Ok sourceShared sourceVars) target from
                ⟨sourceShared, sourceVars, rfl,
                  hShared, hVars⟩)

theorem safeWorldUnaryRead
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.State .Yul → Word → Word}
    {targetResult : EvmYul.State .EVM → Word → Word}
    {sourceValues outputs : List Word}
    (hFamily : WorldUnaryRead prim op sourceResult targetResult)
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
      (forwardAt_of_worldUnaryRead hFamily) hRel hRun

inductive WorldUnaryAccess :
    EvmYul.Operation .Yul → Structured.BasicOp →
      (EvmYul.State .Yul → Word →
        EvmYul.State .Yul × Word) →
      (EvmYul.State .EVM → Word →
        EvmYul.State .EVM × Word) → Prop where
  | balance :
      WorldUnaryAccess (.Env .BALANCE) .balance
        EvmYul.State.balance EvmYul.State.balance
  | extcodesize :
      WorldUnaryAccess (.Env .EXTCODESIZE) .extcodesize
        EvmYul.State.extCodeSize EvmYul.State.extCodeSize
  | extcodehash :
      WorldUnaryAccess (.Env .EXTCODEHASH) .extcodehash
        EvmYul.State.extCodeHash EvmYul.State.extCodeHash
  | sload :
      WorldUnaryAccess (.StackMemFlow .SLOAD) .sload
        EvmYul.State.sload EvmYul.State.sload
  | tload :
      WorldUnaryAccess (.StackMemFlow .TLOAD) .tload
        EvmYul.State.tload EvmYul.State.tload

theorem WorldUnaryAccess.metadata
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceStep :
      EvmYul.State .Yul → Word → EvmYul.State .Yul × Word}
    {targetStep :
      EvmYul.State .EVM → Word → EvmYul.State .EVM × Word}
    (hFamily : WorldUnaryAccess prim op sourceStep targetStep) :
    Expressions.Structured.BasicOp.inputs op = 1 ∧
      Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
        some (.unaryState targetStep) ∧
      ObserverSemantics.yulPrimObserver? prim = none ∧
      Functions.ObserverSemantics.basicOpObserver? op = none ∧
      Prim.terminal? prim = none ∧
      Prim.toUncheckedBasicOp? prim = some op := by
  cases hFamily <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem WorldUnaryAccess.related
    {codeRel : StateRelation.CodeRel}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceStep :
      EvmYul.State .Yul → Word → EvmYul.State .Yul × Word}
    {targetStep :
      EvmYul.State .EVM → Word → EvmYul.State .EVM × Word}
    (hFamily : WorldUnaryAccess prim op sourceStep targetStep)
    {source : EvmYul.State .Yul}
    {target : EvmYul.State .EVM}
    (hRel : StateRelation.World.Rel codeRel source target)
    (value : Word) :
    StateRelation.World.Rel codeRel
        (sourceStep source value).1
        (targetStep target value).1 ∧
      (sourceStep source value).2 =
        (targetStep target value).2 := by
  let address := EvmYul.AccountAddress.ofUInt256 value
  cases hFamily with
  | balance =>
      constructor
      · simpa [EvmYul.State.balance, address] using
          StateRelation.World.addAccessedAccount hRel address
      · simpa [EvmYul.State.balance, address] using
          StateRelation.AccountMap.balance_eq
            hRel.accounts address
  | extcodesize =>
      constructor
      · simpa [EvmYul.State.extCodeSize, address] using
          StateRelation.World.addAccessedAccount hRel address
      · simpa [EvmYul.State.extCodeSize,
          EvmYul.State.lookupAccount, address] using
          StateRelation.AccountMap.codeSize_eq
            hRel.accounts address
  | extcodehash =>
      have hDead :
          EvmYul.State.dead source.accountMap address =
            EvmYul.State.dead target.accountMap address :=
        StateRelation.AccountMap.dead_eq hRel.accounts address
      constructor
      · by_cases hIsDead :
            EvmYul.State.dead target.accountMap address = true
        all_goals
          simpa [EvmYul.State.extCodeHash, address, hDead,
            hIsDead] using
            StateRelation.World.addAccessedAccount hRel address
      · by_cases hIsDead :
            EvmYul.State.dead target.accountMap address = true
        · simp [EvmYul.State.extCodeHash, address, hDead, hIsDead]
        · simpa [EvmYul.State.extCodeHash,
            EvmYul.State.lookupAccount, address, hDead, hIsDead] using
            StateRelation.AccountMap.codeHash_eq
              hRel.accounts address
  | sload =>
      let owner := source.executionEnv.codeOwner
      have hTargetOwner :
          target.executionEnv.codeOwner = owner := by
        simpa [owner] using hRel.executionEnv.codeOwner.symm
      constructor
      · simpa [EvmYul.State.sload, owner, hTargetOwner] using
          StateRelation.World.addAccessedStorageKey hRel
            (owner, value)
      · simpa [EvmYul.State.sload,
          EvmYul.State.lookupAccount, owner, hTargetOwner] using
          StateRelation.AccountMap.storageValue_eq
            hRel.accounts owner value
  | tload =>
      let owner := source.executionEnv.codeOwner
      have hTargetOwner :
          target.executionEnv.codeOwner = owner := by
        simpa [owner] using hRel.executionEnv.codeOwner.symm
      constructor
      · simpa [EvmYul.State.tload] using hRel
      · simpa [EvmYul.State.tload,
          EvmYul.State.lookupAccount, owner, hTargetOwner] using
          StateRelation.AccountMap.transientStorageValue_eq
            hRel.accounts owner value

theorem yul_primCall_succ_eq_of_worldUnaryAccess
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceStep :
      EvmYul.State .Yul → Word → EvmYul.State .Yul × Word}
    {targetStep :
      EvmYul.State .EVM → Word → EvmYul.State .EVM × Word}
    (hFamily : WorldUnaryAccess prim op sourceStep targetStep)
    (fuel : Nat) (source : EvmYul.Yul.State)
    (args : List Word) :
    EvmYul.Yul.primCall fuel.succ source prim args =
      (match EvmYul.Yul.unaryStateOp sourceStep source args with
      | .ok (state, value?) => .ok (state, value?.toList)
      | .error err => .error err) := by
  cases hFamily <;>
    simp [EvmYul.Yul.primCall] <;>
    unfold EvmYul.step <;>
    rfl

theorem WorldUnaryAccess.rawNoObservableFailureAt
    {fuel : Nat} {prim : EvmYul.Operation .Yul}
    {op : Structured.BasicOp}
    {sourceStep :
      EvmYul.State .Yul → Word → EvmYul.State .Yul × Word}
    {targetStep :
      EvmYul.State .EVM → Word → EvmYul.State .EVM × Word}
    (hFamily :
      WorldUnaryAccess prim op sourceStep targetStep) :
    RawNoObservableFailureAt fuel prim := by
  intro source values exception hRun hObservable
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hRun
      subst exception
      simp [Yul.Source.Effectful.Exception.Observable] at hObservable
  | succ previous =>
      rw [yul_primCall_succ_eq_of_worldUnaryAccess hFamily] at hRun
      cases values with
      | nil =>
          simp [EvmYul.Yul.unaryStateOp] at hRun
          rw [← hRun] at hObservable
          simp [Yul.Source.Effectful.Exception.Observable] at hObservable
      | cons value extra =>
          cases extra with
          | nil =>
              simp [EvmYul.Yul.unaryStateOp] at hRun
          | cons head tail =>
              simp [EvmYul.Yul.unaryStateOp] at hRun
              rw [← hRun] at hObservable
              simp [Yul.Source.Effectful.Exception.Observable] at hObservable

theorem forwardAt_of_worldUnaryAccess
    {codeRel : StateRelation.CodeRel} {fuel : Nat}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceStep :
      EvmYul.State .Yul → Word → EvmYul.State .Yul × Word}
    {targetStep :
      EvmYul.State .EVM → Word → EvmYul.State .EVM × Word}
    (hFamily : WorldUnaryAccess prim op sourceStep targetStep) :
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
      rw [yul_primCall_succ_eq_of_worldUnaryAccess hFamily] at hCall
      cases sourceValues with
      | nil =>
          simp [EvmYul.Yul.unaryStateOp] at hCall
      | cons value rest =>
          cases rest with
          | cons next tail =>
              simp [EvmYul.Yul.unaryStateOp] at hCall
          | nil =>
              simp [EvmYul.Yul.unaryStateOp,
                EvmYul.Yul.State.setSharedState] at hCall
              rcases hCall with ⟨rfl, rfl⟩
              let sourceResult :=
                sourceStep sourceShared.toState value
              let targetResult :=
                targetStep target.shared.toState value
              have hResult :
                  StateRelation.World.Rel codeRel
                      sourceResult.1 targetResult.1 ∧
                    sourceResult.2 = targetResult.2 := by
                simpa [sourceResult, targetResult] using
                  hFamily.related hShared.world value
              let targetShared : EvmYul.SharedState .EVM :=
                { target.shared with toState := targetResult.1 }
              refine ⟨targetShared, ?_, ?_, by rfl⟩
              · simp [Locals.Source.PrimitiveSemantics.structured,
                  hInputs, hStep, Assembly.PrimStep.run,
                  EvmYul.EVM.unaryStateOp,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC, EvmYul.Stack.pop,
                  EvmYul.Stack.push, sourceResult, targetResult,
                  targetShared, Id.run, hResult.2] <;>
                simpa [sourceResult, targetResult] using hResult.2.symm
              · exact
                  ⟨{ sourceShared with
                      toState := sourceResult.1 },
                    sourceVars, rfl,
                    { world := hResult.1
                      machine := by
                        simpa [targetShared] using hShared.machine },
                    hVars⟩

theorem backwardAt_of_worldUnaryAccess
    {codeRel : StateRelation.CodeRel} (fuel : Nat)
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceStep :
      EvmYul.State .Yul → Word → EvmYul.State .Yul × Word}
    {targetStep :
      EvmYul.State .EVM → Word → EvmYul.State .EVM × Word}
    (hFamily : WorldUnaryAccess prim op sourceStep targetStep) :
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
          let sourceResult :=
            sourceStep sourceShared.toState value
          let targetResult :=
            targetStep target.shared.toState value
          have hResult :
              StateRelation.World.Rel codeRel
                  sourceResult.1 targetResult.1 ∧
                sourceResult.2 = targetResult.2 := by
            simpa [sourceResult, targetResult] using
              hFamily.related hShared.world value
          let targetAfter : EvmYul.SharedState .EVM :=
            { target.shared with toState := targetResult.1 }
          have hExpected :
              Locals.Source.PrimitiveSemantics.structured.eval
                  op target.shared [value] =
                .ok (targetAfter, [targetResult.2]) := by
            simp [Locals.Source.PrimitiveSemantics.structured,
              hInputs, hStep, Assembly.PrimStep.run,
              EvmYul.EVM.unaryStateOp,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC, EvmYul.Stack.pop,
              EvmYul.Stack.push, targetResult, targetAfter, Id.run]
          have hRun' :
              Locals.Source.PrimitiveSemantics.structured.eval
                  op target.shared [value] =
                .ok (targetShared, outputs) := by
            simpa using hRun
          rw [hExpected] at hRun'
          have hPair := Except.ok.inj hRun'
          have hSharedEq := congrArg Prod.fst hPair
          have hOutputsEq := congrArg Prod.snd hPair
          change targetAfter = targetShared at hSharedEq
          change [targetResult.2] = outputs at hOutputsEq
          subst targetShared
          subst outputs
          refine
            ⟨.Ok
                { sourceShared with toState := sourceResult.1 }
                sourceVars,
              ?_, ?_, rfl⟩
          · rw [yul_primCall_succ_eq_of_worldUnaryAccess hFamily]
            change
              Except.ok
                  (EvmYul.Yul.State.Ok
                    { sourceShared with
                      toState := sourceResult.1 }
                    sourceVars,
                    [sourceResult.2]) =
                Except.ok
                  (EvmYul.Yul.State.Ok
                    { sourceShared with
                      toState := sourceResult.1 }
                    sourceVars,
                    [targetResult.2])
            simp [hResult.2]
          · exact
              ⟨{ sourceShared with
                  toState := sourceResult.1 },
                sourceVars, rfl,
                { world := hResult.1
                  machine := by
                    simpa [targetAfter] using hShared.machine },
                hVars⟩

theorem safeWorldUnaryAccess
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceStep :
      EvmYul.State .Yul → Word → EvmYul.State .Yul × Word}
    {targetStep :
      EvmYul.State .EVM → Word → EvmYul.State .EVM × Word}
    {sourceValues outputs : List Word}
    (hFamily : WorldUnaryAccess prim op sourceStep targetStep)
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
      (forwardAt_of_worldUnaryAccess hFamily) hRel hRun

inductive WorldBinaryWrite :
    EvmYul.Operation .Yul → Structured.BasicOp →
      (EvmYul.State .Yul → Word → Word → EvmYul.State .Yul) →
      (EvmYul.State .EVM → Word → Word → EvmYul.State .EVM) → Prop where
  | sstore :
      WorldBinaryWrite (.StackMemFlow .SSTORE) .sstore
        EvmYul.State.sstore EvmYul.State.sstore
  | tstore :
      WorldBinaryWrite (.StackMemFlow .TSTORE) .tstore
        EvmYul.State.tstore EvmYul.State.tstore

theorem WorldBinaryWrite.metadata
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceStep :
      EvmYul.State .Yul → Word → Word → EvmYul.State .Yul}
    {targetStep :
      EvmYul.State .EVM → Word → Word → EvmYul.State .EVM}
    (hFamily : WorldBinaryWrite prim op sourceStep targetStep) :
    Expressions.Structured.BasicOp.inputs op = 2 ∧
      Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
        some (.binaryState targetStep) ∧
      ObserverSemantics.yulPrimObserver? prim = none ∧
      Functions.ObserverSemantics.basicOpObserver? op = none ∧
      Prim.terminal? prim = none ∧
      Prim.toUncheckedBasicOp? prim = some op := by
  cases hFamily <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem WorldBinaryWrite.related
    {codeRel : StateRelation.CodeRel}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceStep :
      EvmYul.State .Yul → Word → Word → EvmYul.State .Yul}
    {targetStep :
      EvmYul.State .EVM → Word → Word → EvmYul.State .EVM}
    (hFamily : WorldBinaryWrite prim op sourceStep targetStep)
    {source : EvmYul.State .Yul}
    {target : EvmYul.State .EVM}
    (hRel : StateRelation.World.Rel codeRel source target)
    (key value : Word) :
    StateRelation.World.Rel codeRel
      (sourceStep source key value)
      (targetStep target key value) := by
  cases hFamily with
  | sstore =>
      exact StateRelation.World.sstore hRel key value
  | tstore =>
      exact StateRelation.World.tstore hRel key value

theorem yul_primCall_succ_eq_of_worldBinaryWrite
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceStep :
      EvmYul.State .Yul → Word → Word → EvmYul.State .Yul}
    {targetStep :
      EvmYul.State .EVM → Word → Word → EvmYul.State .EVM}
    (hFamily : WorldBinaryWrite prim op sourceStep targetStep)
    (fuel : Nat) (source : EvmYul.Yul.State)
    (args : List Word) :
    EvmYul.Yul.primCall fuel.succ source prim args =
      if source.executionEnv.perm = false then
        .error .StaticModeViolation
      else
        (match EvmYul.Yul.binaryStateOp sourceStep source args with
        | .ok (state, value?) => .ok (state, value?.toList)
        | .error err => .error err) := by
  cases hFamily <;>
    simp [EvmYul.Yul.primCall] <;>
    unfold EvmYul.step <;>
    rfl

theorem WorldBinaryWrite.targetPermitted_of_run
    {codeRel : StateRelation.CodeRel} {fuel : Nat}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceStep :
      EvmYul.State .Yul → Word → Word → EvmYul.State .Yul}
    {targetStep :
      EvmYul.State .EVM → Word → Word → EvmYul.State .EVM}
    {source source' : EvmYul.Yul.State}
    {target : Locals.Source.State}
    {sourceValues outputs : List Word}
    (hFamily : WorldBinaryWrite prim op sourceStep targetStep)
    (hRel : StateRelation.Regular.Rel codeRel source target)
    (hRun :
      EvmYul.Yul.primCall fuel source prim sourceValues =
        .ok (source', outputs)) :
    Functions.ObserverSafety.PrimitivePermitted op target.shared := by
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hRun
  | succ previous =>
      rw [yul_primCall_succ_eq_of_worldBinaryWrite hFamily] at hRun
      cases hPermission : sourceShared.executionEnv.perm with
      | false =>
          simp [EvmYul.Yul.State.executionEnv,
            hPermission] at hRun
      | true =>
          cases hFamily <;>
            simpa [Functions.ObserverSafety.PrimitivePermitted,
              hPermission] using
              hShared.world.executionEnv.permission.symm

theorem WorldBinaryWrite.rawNoObservableFailureAt
    {fuel : Nat} {prim : EvmYul.Operation .Yul}
    {op : Structured.BasicOp}
    {sourceStep :
      EvmYul.State .Yul → Word → Word → EvmYul.State .Yul}
    {targetStep :
      EvmYul.State .EVM → Word → Word → EvmYul.State .EVM}
    (hFamily :
      WorldBinaryWrite prim op sourceStep targetStep) :
    RawNoObservableFailureAt fuel prim := by
  intro source values exception hRun hObservable
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hRun
      subst exception
      simp [Yul.Source.Effectful.Exception.Observable] at hObservable
  | succ previous =>
      rw [yul_primCall_succ_eq_of_worldBinaryWrite hFamily] at hRun
      cases hPermission : source.executionEnv.perm with
      | false =>
          simp [hPermission] at hRun
          rw [← hRun] at hObservable
          simp [Yul.Source.Effectful.Exception.Observable] at hObservable
      | true =>
          simp [hPermission] at hRun
          cases values with
          | nil =>
              simp [EvmYul.Yul.binaryStateOp] at hRun
              rw [← hRun] at hObservable
              simp [Yul.Source.Effectful.Exception.Observable] at hObservable
          | cons key rest =>
              cases rest with
              | nil =>
                  simp [EvmYul.Yul.binaryStateOp] at hRun
                  rw [← hRun] at hObservable
                  simp [Yul.Source.Effectful.Exception.Observable] at hObservable
              | cons value extra =>
                  cases extra with
                  | nil =>
                      simp [EvmYul.Yul.binaryStateOp] at hRun
                  | cons head tail =>
                      simp [EvmYul.Yul.binaryStateOp] at hRun
                      rw [← hRun] at hObservable
                      simp [Yul.Source.Effectful.Exception.Observable] at hObservable

theorem forwardAt_of_worldBinaryWrite
    {codeRel : StateRelation.CodeRel} {fuel : Nat}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceStep :
      EvmYul.State .Yul → Word → Word → EvmYul.State .Yul}
    {targetStep :
      EvmYul.State .EVM → Word → Word → EvmYul.State .EVM}
    (hFamily : WorldBinaryWrite prim op sourceStep targetStep) :
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
      rw [yul_primCall_succ_eq_of_worldBinaryWrite hFamily] at hCall
      cases hPermission : sourceShared.executionEnv.perm with
      | false =>
          simp [EvmYul.Yul.State.executionEnv,
            hPermission] at hCall
      | true =>
          simp [EvmYul.Yul.State.executionEnv,
            hPermission] at hCall
          cases sourceValues with
          | nil =>
              simp [EvmYul.Yul.binaryStateOp] at hCall
          | cons key rest =>
              cases rest with
              | nil =>
                  simp [EvmYul.Yul.binaryStateOp] at hCall
              | cons value extra =>
                  cases extra with
                  | cons head tail =>
                      simp [EvmYul.Yul.binaryStateOp] at hCall
                  | nil =>
                      simp [EvmYul.Yul.binaryStateOp,
                        EvmYul.Yul.State.setState] at hCall
                      rcases hCall with ⟨rfl, rfl⟩
                      let sourceWorld :=
                        sourceStep sourceShared.toState key value
                      let targetWorld :=
                        targetStep target.shared.toState key value
                      have hWorld :
                          StateRelation.World.Rel codeRel
                            sourceWorld targetWorld := by
                        simpa [sourceWorld, targetWorld] using
                          hFamily.related hShared.world key value
                      let targetShared : EvmYul.SharedState .EVM :=
                        { target.shared with toState := targetWorld }
                      refine ⟨targetShared, ?_, ?_, by rfl⟩
                      · simp [
                          Locals.Source.PrimitiveSemantics.structured,
                          hInputs, hStep, Assembly.PrimStep.run,
                          EvmYul.EVM.binaryStateOp,
                          EvmYul.EVM.State.replaceStackAndIncrPC,
                          EvmYul.EVM.State.incrPC,
                          EvmYul.Stack.pop2, targetShared,
                          targetWorld, Id.run]
                      · exact
                          ⟨{ sourceShared with
                              toState := sourceWorld },
                            sourceVars, rfl,
                            { world := hWorld
                              machine := by
                                simpa [targetShared] using
                                  hShared.machine },
                            hVars⟩

theorem backwardAt_of_worldBinaryWrite
    {codeRel : StateRelation.CodeRel} (fuel : Nat)
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceStep :
      EvmYul.State .Yul → Word → Word → EvmYul.State .Yul}
    {targetStep :
      EvmYul.State .EVM → Word → Word → EvmYul.State .EVM}
    (hFamily : WorldBinaryWrite prim op sourceStep targetStep) :
    BackwardAt codeRel (fuel + 1) prim op := by
  intro source target targetShared sourceValues outputs
    hRel hPermitted hRun
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  obtain ⟨hInputs, hStep, _⟩ := hFamily.metadata
  cases sourceValues with
  | nil =>
      simp [Locals.Source.PrimitiveSemantics.structured,
        hInputs, Structured.invalid] at hRun
  | cons key rest =>
      cases rest with
      | nil =>
          simp [Locals.Source.PrimitiveSemantics.structured,
            hInputs, Structured.invalid] at hRun
      | cons value extra =>
          cases extra with
          | cons head tail =>
              simp [Locals.Source.PrimitiveSemantics.structured,
                hInputs, Structured.invalid] at hRun
          | nil =>
              have hTargetPermission :
                  target.shared.executionEnv.perm = true := by
                cases hFamily <;>
                  simpa [
                    Functions.ObserverSafety.PrimitivePermitted] using
                    hPermitted
              have hSourcePermission :
                  sourceShared.executionEnv.perm = true := by
                rw [hShared.world.executionEnv.permission]
                exact hTargetPermission
              let sourceWorld :=
                sourceStep sourceShared.toState key value
              let targetWorld :=
                targetStep target.shared.toState key value
              have hWorld :
                  StateRelation.World.Rel codeRel
                    sourceWorld targetWorld := by
                simpa [sourceWorld, targetWorld] using
                  hFamily.related hShared.world key value
              let targetAfter : EvmYul.SharedState .EVM :=
                { target.shared with toState := targetWorld }
              have hExpected :
                  Locals.Source.PrimitiveSemantics.structured.eval
                      op target.shared [value, key] =
                    .ok (targetAfter, []) := by
                simp [Locals.Source.PrimitiveSemantics.structured,
                  hInputs, hStep, Assembly.PrimStep.run,
                  EvmYul.EVM.binaryStateOp,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC,
                  EvmYul.Stack.pop2, targetAfter,
                  targetWorld, Id.run]
              have hRun' :
                  Locals.Source.PrimitiveSemantics.structured.eval
                      op target.shared [value, key] =
                    .ok (targetShared, outputs) := by
                simpa using hRun
              rw [hExpected] at hRun'
              have hPair := Except.ok.inj hRun'
              have hSharedEq := congrArg Prod.fst hPair
              have hOutputsEq := congrArg Prod.snd hPair
              change targetAfter = targetShared at hSharedEq
              change [] = outputs at hOutputsEq
              subst targetShared
              subst outputs
              refine
                ⟨.Ok
                    { sourceShared with toState := sourceWorld }
                    sourceVars,
                  ?_, ?_, rfl⟩
              · rw [yul_primCall_succ_eq_of_worldBinaryWrite hFamily]
                simp [EvmYul.Yul.State.executionEnv,
                  hSourcePermission, EvmYul.Yul.binaryStateOp,
                  EvmYul.Yul.State.setState, sourceWorld]
                rfl
              · exact
                  ⟨{ sourceShared with toState := sourceWorld },
                    sourceVars, rfl,
                    { world := hWorld
                      machine := by
                        simpa [targetAfter] using hShared.machine },
                    hVars⟩

theorem safeWorldBinaryWrite
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceStep :
      EvmYul.State .Yul → Word → Word → EvmYul.State .Yul}
    {targetStep :
      EvmYul.State .EVM → Word → Word → EvmYul.State .EVM}
    {sourceValues outputs : List Word}
    (hFamily : WorldBinaryWrite prim op sourceStep targetStep)
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
      (fun hRaw =>
        hFamily.targetPermitted_of_run hRel.2 hRaw)
      (forwardAt_of_worldBinaryWrite hFamily) hRel hRun

theorem safeWorldBinaryWriteBackward
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target target' : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceStep :
      EvmYul.State .Yul → Word → Word → EvmYul.State .Yul}
    {targetStep :
      EvmYul.State .EVM → Word → Word → EvmYul.State .EVM}
    {sourceValues outputs : List Word}
    (hFamily : WorldBinaryWrite prim op sourceStep targetStep)
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
      (backwardAt_of_worldBinaryWrite
        (codeRel := codeRel) fuel hFamily)
      hRel hRun)

theorem safeWorldNullaryBackward
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target target' : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.State .Yul → Word}
    {targetResult : EvmYul.State .EVM → Word}
    {sourceValues outputs : List Word}
    (hFamily : WorldNullary prim op sourceResult targetResult)
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
      (backwardAt_of_worldNullary (codeRel := codeRel) fuel hFamily)
      hRel hRun)

theorem safeWorldUnaryReadBackward
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target target' : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.State .Yul → Word → Word}
    {targetResult : EvmYul.State .EVM → Word → Word}
    {sourceValues outputs : List Word}
    (hFamily : WorldUnaryRead prim op sourceResult targetResult)
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
      (backwardAt_of_worldUnaryRead
        (codeRel := codeRel) fuel hFamily)
      hRel hRun)

theorem safeWorldUnaryAccessBackward
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target target' : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceStep :
      EvmYul.State .Yul → Word → EvmYul.State .Yul × Word}
    {targetStep :
      EvmYul.State .EVM → Word → EvmYul.State .EVM × Word}
    {sourceValues outputs : List Word}
    (hFamily : WorldUnaryAccess prim op sourceStep targetStep)
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
      (backwardAt_of_worldUnaryAccess
        (codeRel := codeRel) fuel hFamily)
      hRel hRun)

end FunctionsObserverPrimitive
end Yul
end EvmCompiler
