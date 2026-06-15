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

end FunctionsObserverPrimitive
end Yul
end EvmCompiler
