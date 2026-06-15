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
      refine ⟨target.shared, ?_, ?_⟩
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
      StateRelation.Replay.Rel codeRel source' target' := by
  obtain ⟨_hInputs, _hStep, hYulObserver, hFunctionsObserver,
      hTerminal, hOp⟩ := hFamily.metadata
  exact
    safeBasicOpArity hYulObserver hFunctionsObserver hTerminal hOp
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
              refine ⟨target.shared, ?_, ?_⟩
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
      StateRelation.Replay.Rel codeRel source' target' := by
  obtain ⟨_hInputs, _hStep, hYulObserver, hFunctionsObserver,
      hTerminal, hOp⟩ := hFamily.metadata
  exact
    safeBasicOp hYulObserver hFunctionsObserver hTerminal hOp
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
              refine ⟨targetShared, ?_, ?_⟩
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
      StateRelation.Replay.Rel codeRel source' target' := by
  obtain ⟨_hInputs, _hStep, hYulObserver, hFunctionsObserver,
      hTerminal, hOp⟩ := hFamily.metadata
  exact
    safeBasicOp hYulObserver hFunctionsObserver hTerminal hOp
      (forwardAt_of_worldUnaryAccess hFamily) hRel hRun

end FunctionsObserverPrimitive
end Yul
end EvmCompiler
