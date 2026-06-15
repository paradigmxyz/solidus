import EvmCompiler.Yul.FunctionsObserverPrimitive.Core

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverPrimitive

inductive MachineBinaryZero :
    EvmYul.Operation .Yul → Structured.BasicOp →
      (EvmYul.MachineState → Word → Word →
        EvmYul.MachineState) → Prop where
  | mstore :
      MachineBinaryZero (.StackMemFlow .MSTORE) .mstore
        EvmYul.MachineState.mstore
  | mstore8 :
      MachineBinaryZero (.StackMemFlow .MSTORE8) .mstore8
        EvmYul.MachineState.mstore8

theorem MachineBinaryZero.metadata
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.MachineState → Word → Word → EvmYul.MachineState}
    (hFamily : MachineBinaryZero prim op f) :
    Expressions.Structured.BasicOp.inputs op = 2 ∧
      Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
        some (.binaryMachineState f) ∧
      ObserverSemantics.yulPrimObserver? prim = none ∧
      Functions.ObserverSemantics.basicOpObserver? op = none ∧
      Prim.terminal? prim = none ∧
      Prim.toUncheckedBasicOp? prim = some op := by
  cases hFamily <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem yul_primCall_succ_eq_of_machineBinaryZero
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.MachineState → Word → Word → EvmYul.MachineState}
    (hFamily : MachineBinaryZero prim op f)
    (fuel : Nat) (source : EvmYul.Yul.State)
    (args : List Word) :
    EvmYul.Yul.primCall fuel.succ source prim args =
      (match EvmYul.Yul.binaryMachineStateOp f source args with
      | .ok (state, value?) => .ok (state, value?.toList)
      | .error err => .error err) := by
  cases hFamily <;>
    simp [EvmYul.Yul.primCall] <;>
    unfold EvmYul.step <;>
    rfl

theorem MachineBinaryZero.rawNoObservableFailureAt
    {fuel : Nat} {prim : EvmYul.Operation .Yul}
    {op : Structured.BasicOp}
    {f : EvmYul.MachineState → Word → Word →
      EvmYul.MachineState}
    (hFamily : MachineBinaryZero prim op f) :
    RawNoObservableFailureAt fuel prim := by
  intro source values exception hRun hObservable
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hRun
      subst exception
      simp [Yul.Source.Effectful.Exception.Observable] at hObservable
  | succ previous =>
      rw [yul_primCall_succ_eq_of_machineBinaryZero hFamily] at hRun
      cases values with
      | nil =>
          simp [EvmYul.Yul.binaryMachineStateOp] at hRun
          rw [← hRun] at hObservable
          simp [Yul.Source.Effectful.Exception.Observable] at hObservable
      | cons first rest =>
          cases rest with
          | nil =>
              simp [EvmYul.Yul.binaryMachineStateOp] at hRun
              rw [← hRun] at hObservable
              simp [Yul.Source.Effectful.Exception.Observable] at hObservable
          | cons second extra =>
              cases extra with
              | nil =>
                  simp [EvmYul.Yul.binaryMachineStateOp] at hRun
              | cons head tail =>
                  simp [EvmYul.Yul.binaryMachineStateOp] at hRun
                  rw [← hRun] at hObservable
                  simp [Yul.Source.Effectful.Exception.Observable] at hObservable

theorem forwardAt_of_machineBinaryZero
    {codeRel : StateRelation.CodeRel} {fuel : Nat}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.MachineState → Word → Word → EvmYul.MachineState}
    (hFamily : MachineBinaryZero prim op f) :
    ForwardAt codeRel fuel prim op := by
  intro source source' target sourceValues outputs hRel hCall
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hCall
  | succ fuel =>
      rw [yul_primCall_succ_eq_of_machineBinaryZero hFamily] at hCall
      cases sourceValues with
      | nil =>
          simp [EvmYul.Yul.binaryMachineStateOp] at hCall
      | cons left rest =>
          cases rest with
          | nil =>
              simp [EvmYul.Yul.binaryMachineStateOp] at hCall
          | cons right extra =>
              cases extra with
              | cons head tail =>
                  simp [EvmYul.Yul.binaryMachineStateOp] at hCall
              | nil =>
                  simp [EvmYul.Yul.binaryMachineStateOp,
                    EvmYul.Yul.State.setMachineState] at hCall
                  rcases hCall with ⟨rfl, rfl⟩
                  let sourceMachine :=
                    f sourceShared.toMachineState left right
                  let targetMachine :=
                    f target.shared.toMachineState left right
                  have hMachine : sourceMachine = targetMachine := by
                    simp [sourceMachine, targetMachine, hShared.machine]
                  let targetShared : EvmYul.SharedState .EVM :=
                    { target.shared with
                      toMachineState := targetMachine }
                  refine ⟨targetShared, ?_, ?_, by rfl⟩
                  · obtain ⟨hInputs, hStep, _⟩ := hFamily.metadata
                    simp [Locals.Source.PrimitiveSemantics.structured,
                      hInputs, hStep,
                      Assembly.PrimStep.run,
                      EvmYul.EVM.binaryMachineStateOp,
                      EvmYul.Stack.pop2,
                      EvmYul.EVM.State.replaceStackAndIncrPC,
                      EvmYul.EVM.State.incrPC, targetShared,
                      targetMachine]
                    rfl
                  · exact
                      ⟨{ sourceShared with
                          toMachineState := sourceMachine },
                        sourceVars, rfl,
                        StateRelation.Shared.withMachine hShared
                          sourceMachine targetMachine hMachine,
                        hVars⟩

theorem safeMachineBinaryZero
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.MachineState → Word → Word → EvmYul.MachineState}
    {sourceValues outputs : List Word}
    (hFamily : MachineBinaryZero prim op f)
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
      (forwardAt_of_machineBinaryZero hFamily) hRel hRun

theorem forwardAt_mcopy
    {codeRel : StateRelation.CodeRel} {fuel : Nat} :
    ForwardAt codeRel fuel (.StackMemFlow .MCOPY) .mcopy := by
  intro source source' target sourceValues outputs hRel hCall
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hCall
  | succ fuel =>
      have hDispatch :
          EvmYul.Yul.primCall fuel.succ
              (.Ok sourceShared sourceVars)
              (.StackMemFlow .MCOPY) sourceValues =
            (match
              EvmYul.Yul.ternaryMachineStateOp
                EvmYul.MachineState.mcopy
                (.Ok sourceShared sourceVars) sourceValues with
            | .ok (state, value?) => .ok (state, value?.toList)
            | .error err => .error err) := by
        simp [EvmYul.Yul.primCall]
        unfold EvmYul.step
        rfl
      rw [hDispatch] at hCall
      cases sourceValues with
      | nil =>
          simp [EvmYul.Yul.ternaryMachineStateOp] at hCall
      | cons destination rest =>
          cases rest with
          | nil =>
              simp [EvmYul.Yul.ternaryMachineStateOp] at hCall
          | cons readStart rest =>
              cases rest with
              | nil =>
                  simp [EvmYul.Yul.ternaryMachineStateOp] at hCall
              | cons size extra =>
                  cases extra with
                  | cons head tail =>
                      simp [EvmYul.Yul.ternaryMachineStateOp] at hCall
                  | nil =>
                      simp [EvmYul.Yul.ternaryMachineStateOp,
                        EvmYul.Yul.State.setMachineState] at hCall
                      rcases hCall with ⟨rfl, rfl⟩
                      let sourceMachine :=
                        EvmYul.MachineState.mcopy
                          sourceShared.toMachineState
                          destination readStart size
                      let targetMachine :=
                        EvmYul.MachineState.mcopy
                          target.shared.toMachineState
                          destination readStart size
                      have hMachine : sourceMachine = targetMachine := by
                        simp [sourceMachine, targetMachine, hShared.machine]
                      let targetShared : EvmYul.SharedState .EVM :=
                        { target.shared with
                          toMachineState := targetMachine }
                      refine ⟨targetShared, ?_, ?_, by rfl⟩
                      · simp [Locals.Source.PrimitiveSemantics.structured,
                          Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
                          Expressions.Structured.BasicOp.inputs,
                          Assembly.PrimStep.run,
                          EvmYul.EVM.ternaryMachineStateOp,
                          EvmYul.Stack.pop3,
                          EvmYul.EVM.State.replaceStackAndIncrPC,
                          EvmYul.EVM.State.incrPC,
                          targetShared, targetMachine]
                        rfl
                      · exact
                          ⟨{ sourceShared with
                              toMachineState := sourceMachine },
                            sourceVars, rfl,
                            StateRelation.Shared.withMachine hShared
                              sourceMachine targetMachine hMachine,
                            hVars⟩

theorem safeMcopy
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {sourceValues outputs : List Word}
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval fuel.succ source
          (.StackMemFlow .MCOPY) sourceValues =
        .ok (source', outputs)) :
    ∃ target' : Functions.ObserverSemantics.State transcript,
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval .mcopy target sourceValues.reverse =
        .ok (target', outputs) ∧
      StateRelation.Replay.Rel codeRel source' target' ∧
      source'.source.store = source.source.store :=
  safeBasicOp (by rfl) (by rfl) (by rfl) (by rfl)
    forwardAt_mcopy hRel hRun

theorem rawNoObservableFailureAt_mcopy
    (fuel : Nat) :
    RawNoObservableFailureAt fuel (.StackMemFlow .MCOPY) := by
  intro source values exception hRun hObservable
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hRun
      subst exception
      simp [Yul.Source.Effectful.Exception.Observable] at hObservable
  | succ previous =>
      have hDispatch :
          EvmYul.Yul.primCall previous.succ source
              (.StackMemFlow .MCOPY) values =
            (match
              EvmYul.Yul.ternaryMachineStateOp
                EvmYul.MachineState.mcopy source values with
            | .ok (state, value?) => .ok (state, value?.toList)
            | .error err => .error err) := by
        simp [EvmYul.Yul.primCall]
        unfold EvmYul.step
        rfl
      rw [hDispatch] at hRun
      cases values with
      | nil =>
          simp [EvmYul.Yul.ternaryMachineStateOp] at hRun
          rw [← hRun] at hObservable
          simp [Yul.Source.Effectful.Exception.Observable] at hObservable
      | cons destination rest =>
          cases rest with
          | nil =>
              simp [EvmYul.Yul.ternaryMachineStateOp] at hRun
              rw [← hRun] at hObservable
              simp [Yul.Source.Effectful.Exception.Observable] at hObservable
          | cons readStart rest =>
              cases rest with
              | nil =>
                  simp [EvmYul.Yul.ternaryMachineStateOp] at hRun
                  rw [← hRun] at hObservable
                  simp [Yul.Source.Effectful.Exception.Observable] at hObservable
              | cons size extra =>
                  cases extra with
                  | nil =>
                      simp [EvmYul.Yul.ternaryMachineStateOp] at hRun
                  | cons head tail =>
                      simp [EvmYul.Yul.ternaryMachineStateOp] at hRun
                      rw [← hRun] at hObservable
                      simp [Yul.Source.Effectful.Exception.Observable] at hObservable

theorem forwardAt_mload
    {codeRel : StateRelation.CodeRel} {fuel : Nat} :
    ForwardAt codeRel fuel (.StackMemFlow .MLOAD) .mload := by
  intro source source' target sourceValues outputs hRel hCall
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hCall
  | succ fuel =>
      have hDispatch :
          EvmYul.Yul.primCall fuel.succ
              (.Ok sourceShared sourceVars)
              (.StackMemFlow .MLOAD) sourceValues =
            (match
              EvmYul.step (τ := .Yul) (.StackMemFlow .MLOAD)
                (arg := none)
                (.Ok sourceShared sourceVars) sourceValues with
            | .ok (state, value?) => .ok (state, value?.toList)
            | .error err => .error err) := by
        simp [EvmYul.Yul.primCall]
        rfl
      rw [hDispatch] at hCall
      unfold EvmYul.step at hCall
      cases sourceValues with
      | nil =>
          simp [Id.run] at hCall
      | cons address rest =>
          cases rest with
          | cons next tail =>
              cases tail <;> simp [Id.run] at hCall
          | nil =>
              simp [Id.run] at hCall
              rcases hCall with ⟨rfl, rfl⟩
              let sourceResult :=
                sourceShared.toMachineState.mload address
              let targetResult :=
                target.shared.toMachineState.mload address
              have hResult : sourceResult = targetResult := by
                simp [sourceResult, targetResult, hShared.machine]
              have hValue : sourceResult.1 = targetResult.1 :=
                congrArg Prod.fst hResult
              let targetShared : EvmYul.SharedState .EVM :=
                { target.shared with
                  toMachineState := targetResult.2 }
              refine ⟨targetShared, ?_, ?_, by rfl⟩
              · simp [Locals.Source.PrimitiveSemantics.structured,
                  Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
                  Structured.BasicOp.toPrimOp,
                  Assembly.PrimOp.continuingStep?,
                  Expressions.Structured.BasicOp.inputs,
                  Assembly.PrimStep.run, EvmYul.Stack.pop,
                  EvmYul.Stack.push,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC,
                  sourceResult, targetResult, targetShared,
                  hShared.machine, hValue] <;>
                simpa [sourceResult, targetResult] using hValue.symm
              · exact
                  ⟨{ sourceShared with
                      toMachineState := sourceResult.2 },
                    sourceVars, rfl,
                    StateRelation.Shared.withMachine hShared
                      sourceResult.2 targetResult.2
                      (congrArg Prod.snd hResult),
                    hVars⟩

theorem safeMload
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {sourceValues outputs : List Word}
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval fuel.succ source
          (.StackMemFlow .MLOAD) sourceValues =
        .ok (source', outputs)) :
    ∃ target' : Functions.ObserverSemantics.State transcript,
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval .mload target sourceValues.reverse =
        .ok (target', outputs) ∧
      StateRelation.Replay.Rel codeRel source' target' ∧
      source'.source.store = source.source.store :=
  safeBasicOp (by rfl) (by rfl) (by rfl) (by rfl)
    forwardAt_mload hRel hRun

theorem rawNoObservableFailureAt_mload
    (fuel : Nat) :
    RawNoObservableFailureAt fuel (.StackMemFlow .MLOAD) := by
  intro source values exception hRun hObservable
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hRun
      subst exception
      simp [Yul.Source.Effectful.Exception.Observable] at hObservable
  | succ previous =>
      have hDispatch :
          EvmYul.Yul.primCall previous.succ source
              (.StackMemFlow .MLOAD) values =
            (match
              EvmYul.step (τ := .Yul) (.StackMemFlow .MLOAD)
                (arg := none) source values with
            | .ok (state, value?) => .ok (state, value?.toList)
            | .error err => .error err) := by
        simp [EvmYul.Yul.primCall]
        rfl
      rw [hDispatch] at hRun
      unfold EvmYul.step at hRun
      cases values with
      | nil =>
          simp [Id.run] at hRun
          rw [← hRun] at hObservable
          simp [Yul.Source.Effectful.Exception.Observable] at hObservable
      | cons address rest =>
          cases rest with
          | nil =>
              simp [Id.run] at hRun
          | cons next tail =>
              cases tail with
              | nil =>
                  simp [Id.run] at hRun
                  rw [← hRun] at hObservable
                  simp [Yul.Source.Effectful.Exception.Observable] at hObservable
              | cons head extra =>
                  simp [Id.run] at hRun
                  rw [← hRun] at hObservable
                  simp [Yul.Source.Effectful.Exception.Observable] at hObservable

theorem forwardAt_keccak256
    {codeRel : StateRelation.CodeRel} {fuel : Nat} :
    ForwardAt codeRel fuel (.Keccak .KECCAK256) .keccak256 := by
  intro source source' target sourceValues outputs hRel hCall
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hCall
  | succ fuel =>
      have hDispatch :
          EvmYul.Yul.primCall fuel.succ
              (.Ok sourceShared sourceVars)
              (.Keccak .KECCAK256) sourceValues =
            (match EvmYul.Yul.binaryMachineStateOp'
              EvmYul.MachineState.keccak256
              (.Ok sourceShared sourceVars) sourceValues with
            | .ok (state, value?) => .ok (state, value?.toList)
            | .error err => .error err) := by
        simp [EvmYul.Yul.primCall]
        unfold EvmYul.step
        rfl
      rw [hDispatch] at hCall
      cases sourceValues with
      | nil =>
          simp [EvmYul.Yul.binaryMachineStateOp'] at hCall
      | cons address rest =>
          cases rest with
          | nil =>
              simp [EvmYul.Yul.binaryMachineStateOp'] at hCall
          | cons size extra =>
              cases extra with
              | cons head tail =>
                  simp [EvmYul.Yul.binaryMachineStateOp'] at hCall
              | nil =>
                  simp [EvmYul.Yul.binaryMachineStateOp',
                    EvmYul.Yul.State.setMachineState] at hCall
                  rcases hCall with ⟨rfl, rfl⟩
                  let sourceResult :=
                    sourceShared.toMachineState.keccak256 address size
                  let targetResult :=
                    target.shared.toMachineState.keccak256 address size
                  have hResult : sourceResult = targetResult := by
                    simp [sourceResult, targetResult, hShared.machine]
                  have hValue : sourceResult.1 = targetResult.1 :=
                    congrArg Prod.fst hResult
                  let targetShared : EvmYul.SharedState .EVM :=
                    { target.shared with
                      toMachineState := targetResult.2 }
                  refine ⟨targetShared, ?_, ?_, by rfl⟩
                  · simp [Locals.Source.PrimitiveSemantics.structured,
                      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
                      Structured.BasicOp.toPrimOp,
                      Assembly.PrimOp.continuingStep?,
                      Expressions.Structured.BasicOp.inputs,
                      Assembly.PrimStep.run,
                      EvmYul.EVM.binaryMachineStateOp',
                      EvmYul.Stack.pop2, EvmYul.Stack.push,
                      EvmYul.EVM.State.replaceStackAndIncrPC,
                      EvmYul.EVM.State.incrPC, Id.run,
                      sourceResult, targetResult, targetShared,
                      hShared.machine, hValue] <;>
                    simpa [sourceResult, targetResult] using hValue.symm
                  · exact
                      ⟨{ sourceShared with
                          toMachineState := sourceResult.2 },
                        sourceVars, rfl,
                        StateRelation.Shared.withMachine hShared
                          sourceResult.2 targetResult.2
                          (congrArg Prod.snd hResult),
                        hVars⟩

theorem safeKeccak256
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {sourceValues outputs : List Word}
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval fuel.succ source
          (.Keccak .KECCAK256) sourceValues =
        .ok (source', outputs)) :
    ∃ target' : Functions.ObserverSemantics.State transcript,
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval .keccak256 target
          sourceValues.reverse =
        .ok (target', outputs) ∧
      StateRelation.Replay.Rel codeRel source' target' ∧
      source'.source.store = source.source.store :=
  safeBasicOp (by rfl) (by rfl) (by rfl) (by rfl)
    forwardAt_keccak256 hRel hRun

theorem rawNoObservableFailureAt_keccak256
    (fuel : Nat) :
    RawNoObservableFailureAt fuel (.Keccak .KECCAK256) := by
  intro source values exception hRun hObservable
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hRun
      subst exception
      simp [Yul.Source.Effectful.Exception.Observable] at hObservable
  | succ previous =>
      have hDispatch :
          EvmYul.Yul.primCall previous.succ source
              (.Keccak .KECCAK256) values =
            (match EvmYul.Yul.binaryMachineStateOp'
              EvmYul.MachineState.keccak256 source values with
            | .ok (state, value?) => .ok (state, value?.toList)
            | .error err => .error err) := by
        simp [EvmYul.Yul.primCall]
        unfold EvmYul.step
        rfl
      rw [hDispatch] at hRun
      cases values with
      | nil =>
          simp [EvmYul.Yul.binaryMachineStateOp'] at hRun
          rw [← hRun] at hObservable
          simp [Yul.Source.Effectful.Exception.Observable] at hObservable
      | cons address rest =>
          cases rest with
          | nil =>
              simp [EvmYul.Yul.binaryMachineStateOp'] at hRun
              rw [← hRun] at hObservable
              simp [Yul.Source.Effectful.Exception.Observable] at hObservable
          | cons size extra =>
              cases extra with
              | nil =>
                  simp [EvmYul.Yul.binaryMachineStateOp'] at hRun
              | cons head tail =>
                  simp [EvmYul.Yul.binaryMachineStateOp'] at hRun
                  rw [← hRun] at hObservable
                  simp [Yul.Source.Effectful.Exception.Observable] at hObservable

theorem forwardAtArity_returndatasize
    {codeRel : StateRelation.CodeRel} {fuel : Nat} :
    ForwardAtArity codeRel fuel
      (.Env .RETURNDATASIZE) .returndatasize := by
  intro source source' target sourceValues outputs hRel hArity hCall
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  have hValues : sourceValues = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa [Expressions.Structured.BasicOp.inputs] using hArity
  subst sourceValues
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hCall
  | succ fuel =>
      have hDispatch :
          EvmYul.Yul.primCall fuel.succ
              (.Ok sourceShared sourceVars)
              (.Env .RETURNDATASIZE) [] =
            .ok
              (.Ok sourceShared sourceVars,
                [EvmYul.MachineState.returndatasize
                  sourceShared.toMachineState]) := by
        simp [EvmYul.Yul.primCall]
        unfold EvmYul.step
        rfl
      rw [hDispatch] at hCall
      rcases hCall with ⟨rfl, rfl⟩
      have hResult :
          EvmYul.MachineState.returndatasize sourceShared.toMachineState =
            EvmYul.MachineState.returndatasize
              target.shared.toMachineState :=
        congrArg EvmYul.MachineState.returndatasize hShared.machine
      refine ⟨target.shared, ?_, ?_, by rfl⟩
      · simp [Locals.Source.PrimitiveSemantics.structured,
          Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
          Expressions.Structured.BasicOp.inputs,
          Assembly.PrimStep.run, EvmYul.EVM.machineStateOp,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push,
          EvmYul.Yul.State.toMachineState, hResult]
        rfl
      · simpa [Locals.Source.State.withShared] using
          (show
            StateRelation.Regular.Rel codeRel
              (.Ok sourceShared sourceVars) target from
            ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩)

theorem safeReturndatasize
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {sourceValues outputs : List Word}
    (hArity :
      sourceValues.length =
        Expressions.Structured.BasicOp.inputs .returndatasize)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval fuel.succ source
          (.Env .RETURNDATASIZE) sourceValues =
        .ok (source', outputs)) :
    ∃ target' : Functions.ObserverSemantics.State transcript,
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval .returndatasize target
          sourceValues.reverse =
        .ok (target', outputs) ∧
      StateRelation.Replay.Rel codeRel source' target' ∧
      source'.source.store = source.source.store :=
  safeBasicOpArity (by rfl) (by rfl) (by rfl) (by rfl)
    forwardAtArity_returndatasize hArity hRel hRun

theorem rawNoObservableFailure_returndatasize
    {fuel : Nat} {source : EvmYul.Yul.State}
    {exception : EvmYul.Yul.Exception}
    (hRun :
      EvmYul.Yul.primCall fuel source
          (.Env .RETURNDATASIZE) [] =
        .error exception) :
    ¬Yul.Source.Effectful.Exception.Observable exception := by
  intro hObservable
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hRun
      subst exception
      simp [Yul.Source.Effectful.Exception.Observable] at hObservable
  | succ previous =>
      have hDispatch :
          EvmYul.Yul.primCall previous.succ source
              (.Env .RETURNDATASIZE) [] =
            .ok
              (source,
                [EvmYul.MachineState.returndatasize
                  source.toMachineState]) := by
        simp [EvmYul.Yul.primCall]
        unfold EvmYul.step
        rfl
      rw [hDispatch] at hRun
      cases hRun

theorem forwardAtArity_pop
    {codeRel : StateRelation.CodeRel} {fuel : Nat} :
    ForwardAtArity codeRel fuel (.StackMemFlow .POP) .pop := by
  intro source source' target sourceValues outputs hRel hArity hCall
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  have hValues : ∃ value, sourceValues = [value] := by
    cases sourceValues with
    | nil =>
        simp [Expressions.Structured.BasicOp.inputs] at hArity
    | cons value rest =>
        cases rest with
        | nil => exact ⟨value, rfl⟩
        | cons head tail =>
            simp [Expressions.Structured.BasicOp.inputs] at hArity
  rcases hValues with ⟨value, rfl⟩
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hCall
  | succ fuel =>
      have hDispatch :
          EvmYul.Yul.primCall fuel.succ
              (.Ok sourceShared sourceVars)
              (.StackMemFlow .POP) [value] =
            .ok (.Ok sourceShared sourceVars, []) := by
        simp [EvmYul.Yul.primCall]
        unfold EvmYul.step
        rfl
      rw [hDispatch] at hCall
      rcases hCall with ⟨rfl, rfl⟩
      refine ⟨target.shared, ?_, ?_, by rfl⟩
      · simp [Locals.Source.PrimitiveSemantics.structured,
          Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
          Expressions.Structured.BasicOp.inputs,
          Assembly.PrimStep.run, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.pop]
        rfl
      · simpa [Locals.Source.State.withShared] using
          (show
            StateRelation.Regular.Rel codeRel
              (.Ok sourceShared sourceVars) target from
            ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩)

theorem rawNoObservableFailure_pop
    {fuel : Nat} {source : EvmYul.Yul.State} {value : Word}
    {exception : EvmYul.Yul.Exception}
    (hRun :
      EvmYul.Yul.primCall fuel source
          (.StackMemFlow .POP) [value] =
        .error exception) :
    ¬Yul.Source.Effectful.Exception.Observable exception := by
  intro hObservable
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hRun
      subst exception
      simp [Yul.Source.Effectful.Exception.Observable] at hObservable
  | succ previous =>
      have hDispatch :
          EvmYul.Yul.primCall previous.succ source
              (.StackMemFlow .POP) [value] =
            .ok (source, []) := by
        simp [EvmYul.Yul.primCall]
        unfold EvmYul.step
        rfl
      rw [hDispatch] at hRun
      cases hRun

theorem safePop
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {sourceValues outputs : List Word}
    (hArity :
      sourceValues.length = Expressions.Structured.BasicOp.inputs .pop)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval fuel.succ source
          (.StackMemFlow .POP) sourceValues =
        .ok (source', outputs)) :
    ∃ target' : Functions.ObserverSemantics.State transcript,
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval .pop target sourceValues.reverse =
        .ok (target', outputs) ∧
      StateRelation.Replay.Rel codeRel source' target' ∧
      source'.source.store = source.source.store :=
  safeBasicOpArity (by rfl) (by rfl) (by rfl) (by rfl)
    forwardAtArity_pop hArity hRel hRun

end FunctionsObserverPrimitive
end Yul
end EvmCompiler
