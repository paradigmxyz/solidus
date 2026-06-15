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
      refine ⟨target.shared, ?_, ?_⟩
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
      StateRelation.Replay.Rel codeRel source' target' := by
  obtain ⟨_hInputs, _hStep, hYulObserver, hFunctionsObserver,
      hTerminal, hOp⟩ := hFamily.metadata
  exact
    safeBasicOpArity hYulObserver hFunctionsObserver hTerminal hOp
      (forwardAtArity_of_environmentNullary hFamily)
      hArity hRel hRun

end FunctionsObserverPrimitive
end Yul
end EvmCompiler
