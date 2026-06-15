import EvmCompiler.Yul.FunctionsObserverPrimitive.Core

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverPrimitive

inductive SharedTernaryCopy :
    EvmYul.Operation .Yul → Structured.BasicOp →
      (EvmYul.SharedState .Yul → Word → Word → Word →
        EvmYul.SharedState .Yul) →
      (EvmYul.SharedState .EVM → Word → Word → Word →
        EvmYul.SharedState .EVM) → Prop where
  | calldatacopy :
      SharedTernaryCopy (.Env .CALLDATACOPY) .calldatacopy
        EvmYul.SharedState.calldatacopy
        EvmYul.SharedState.calldatacopy
  | codecopy :
      SharedTernaryCopy (.Env .CODECOPY) .codecopy
        EvmYul.SharedState.codeBytesCopy
        EvmYul.SharedState.codeCopy

theorem SharedTernaryCopy.metadata
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceCopy :
      EvmYul.SharedState .Yul → Word → Word → Word →
        EvmYul.SharedState .Yul}
    {targetCopy :
      EvmYul.SharedState .EVM → Word → Word → Word →
        EvmYul.SharedState .EVM}
    (hFamily : SharedTernaryCopy prim op sourceCopy targetCopy) :
    Expressions.Structured.BasicOp.inputs op = 3 ∧
      Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
        some (.ternaryCopy targetCopy) ∧
      ObserverSemantics.yulPrimObserver? prim = none ∧
      Functions.ObserverSemantics.basicOpObserver? op = none ∧
      Prim.terminal? prim = none ∧
      Prim.toUncheckedBasicOp? prim = some op := by
  cases hFamily <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SharedTernaryCopy.related
    {codeRel : StateRelation.CodeRel}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceCopy :
      EvmYul.SharedState .Yul → Word → Word → Word →
        EvmYul.SharedState .Yul}
    {targetCopy :
      EvmYul.SharedState .EVM → Word → Word → Word →
        EvmYul.SharedState .EVM}
    (hFamily : SharedTernaryCopy prim op sourceCopy targetCopy)
    {source : EvmYul.SharedState .Yul}
    {target : EvmYul.SharedState .EVM}
    (hRel : StateRelation.Shared.Rel codeRel source target)
    (destination readStart size : Word) :
    StateRelation.Shared.Rel codeRel
      (sourceCopy source destination readStart size)
      (targetCopy target destination readStart size) := by
  cases hFamily with
  | calldatacopy =>
      constructor
      · simpa [EvmYul.SharedState.calldatacopy] using hRel.world
      · simp [EvmYul.SharedState.calldatacopy,
          hRel.machine, hRel.world.executionEnv.calldata]
  | codecopy =>
      constructor
      · simpa [EvmYul.SharedState.codeBytesCopy,
          EvmYul.SharedState.codeCopy] using hRel.world
      · simp [EvmYul.SharedState.codeBytesCopy,
          EvmYul.SharedState.codeCopy, hRel.machine,
          hRel.world.executionEnv.codeImage]

theorem yul_primCall_succ_eq_of_sharedTernaryCopy
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceCopy :
      EvmYul.SharedState .Yul → Word → Word → Word →
        EvmYul.SharedState .Yul}
    {targetCopy :
      EvmYul.SharedState .EVM → Word → Word → Word →
        EvmYul.SharedState .EVM}
    (hFamily : SharedTernaryCopy prim op sourceCopy targetCopy)
    (fuel : Nat) (source : EvmYul.Yul.State)
    (args : List Word) :
    EvmYul.Yul.primCall fuel.succ source prim args =
      (match EvmYul.Yul.ternaryCopyOp sourceCopy source args with
      | .ok (state, value?) => .ok (state, value?.toList)
      | .error err => .error err) := by
  cases hFamily <;>
    simp [EvmYul.Yul.primCall] <;>
    unfold EvmYul.step <;>
    rfl

theorem SharedTernaryCopy.rawNoObservableFailureAt
    {fuel : Nat} {prim : EvmYul.Operation .Yul}
    {op : Structured.BasicOp}
    {sourceCopy :
      EvmYul.SharedState .Yul → Word → Word → Word →
        EvmYul.SharedState .Yul}
    {targetCopy :
      EvmYul.SharedState .EVM → Word → Word → Word →
        EvmYul.SharedState .EVM}
    (hFamily : SharedTernaryCopy prim op sourceCopy targetCopy) :
    RawNoObservableFailureAt fuel prim := by
  intro source values exception hRun hObservable
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hRun
      subst exception
      simp [Yul.Source.Effectful.Exception.Observable] at hObservable
  | succ previous =>
      rw [yul_primCall_succ_eq_of_sharedTernaryCopy hFamily] at hRun
      cases values with
      | nil =>
          simp [EvmYul.Yul.ternaryCopyOp] at hRun
          rw [← hRun] at hObservable
          simp [Yul.Source.Effectful.Exception.Observable] at hObservable
      | cons destination rest =>
          cases rest with
          | nil =>
              simp [EvmYul.Yul.ternaryCopyOp] at hRun
              rw [← hRun] at hObservable
              simp [Yul.Source.Effectful.Exception.Observable] at hObservable
          | cons readStart rest =>
              cases rest with
              | nil =>
                  simp [EvmYul.Yul.ternaryCopyOp] at hRun
                  rw [← hRun] at hObservable
                  simp [Yul.Source.Effectful.Exception.Observable] at hObservable
              | cons size extra =>
                  cases extra with
                  | nil =>
                      simp [EvmYul.Yul.ternaryCopyOp] at hRun
                  | cons head tail =>
                      simp [EvmYul.Yul.ternaryCopyOp] at hRun
                      rw [← hRun] at hObservable
                      simp [Yul.Source.Effectful.Exception.Observable] at hObservable

theorem forwardAt_of_sharedTernaryCopy
    {codeRel : StateRelation.CodeRel} {fuel : Nat}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceCopy :
      EvmYul.SharedState .Yul → Word → Word → Word →
        EvmYul.SharedState .Yul}
    {targetCopy :
      EvmYul.SharedState .EVM → Word → Word → Word →
        EvmYul.SharedState .EVM}
    (hFamily : SharedTernaryCopy prim op sourceCopy targetCopy) :
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
      rw [yul_primCall_succ_eq_of_sharedTernaryCopy hFamily] at hCall
      cases sourceValues with
      | nil =>
          simp [EvmYul.Yul.ternaryCopyOp] at hCall
      | cons destination rest =>
          cases rest with
          | nil =>
              simp [EvmYul.Yul.ternaryCopyOp] at hCall
          | cons readStart rest =>
              cases rest with
              | nil =>
                  simp [EvmYul.Yul.ternaryCopyOp] at hCall
              | cons size extra =>
                  cases extra with
                  | cons head tail =>
                      simp [EvmYul.Yul.ternaryCopyOp] at hCall
                  | nil =>
                      simp [EvmYul.Yul.ternaryCopyOp,
                        EvmYul.Yul.State.setSharedState] at hCall
                      rcases hCall with ⟨rfl, rfl⟩
                      let targetShared :=
                        targetCopy target.shared
                          destination readStart size
                      refine ⟨targetShared, ?_, ?_, by rfl⟩
                      · simp [Locals.Source.PrimitiveSemantics.structured,
                          hInputs, hStep, Assembly.PrimStep.run,
                          EvmYul.EVM.ternaryCopyOp,
                          EvmYul.EVM.State.replaceStackAndIncrPC,
                          EvmYul.EVM.State.incrPC,
                          EvmYul.Stack.pop3, targetShared, Id.run]
                      · exact
                          ⟨sourceCopy sourceShared
                              destination readStart size,
                            sourceVars, rfl,
                            hFamily.related hShared
                              destination readStart size,
                            hVars⟩

theorem safeSharedTernaryCopy
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceCopy :
      EvmYul.SharedState .Yul → Word → Word → Word →
        EvmYul.SharedState .Yul}
    {targetCopy :
      EvmYul.SharedState .EVM → Word → Word → Word →
        EvmYul.SharedState .EVM}
    {sourceValues outputs : List Word}
    (hFamily : SharedTernaryCopy prim op sourceCopy targetCopy)
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
      (forwardAt_of_sharedTernaryCopy hFamily) hRel hRun

theorem forwardAt_returndatacopy
    {codeRel : StateRelation.CodeRel} {fuel : Nat} :
    ForwardAt codeRel fuel
      (.Env .RETURNDATACOPY) .returndatacopy := by
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
              (.Env .RETURNDATACOPY) sourceValues =
            (match
              EvmYul.step (τ := .Yul) (.Env .RETURNDATACOPY)
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
      | cons destination rest =>
          cases rest with
          | nil =>
              simp [Id.run] at hCall
          | cons readStart rest =>
              cases rest with
              | nil =>
                  simp [Id.run] at hCall
              | cons size extra =>
                  cases extra with
                  | cons head tail =>
                      simp [Id.run] at hCall
                  | nil =>
                      by_cases hInvalid :
                          sourceShared.returnData.size <
                            readStart.toNat + size.toNat
                      · simp [Id.run,
                          EvmYul.Yul.State.toSharedState,
                          hInvalid] at hCall
                      · simp [Id.run, hInvalid,
                          EvmYul.Yul.State.toSharedState,
                          EvmYul.Yul.State.setMachineState] at hCall
                        rcases hCall with ⟨rfl, rfl⟩
                        let sourceMachine :=
                          sourceShared.toMachineState.returndatacopy
                            destination readStart size
                        let targetMachine :=
                          target.shared.toMachineState.returndatacopy
                            destination readStart size
                        have hMachine :
                            sourceMachine = targetMachine := by
                          simp [sourceMachine, targetMachine,
                            hShared.machine]
                        have hTargetValid :
                            ¬ target.shared.returnData.size <
                              readStart.toNat + size.toNat := by
                          simpa [hShared.machine] using hInvalid
                        let targetShared : EvmYul.SharedState .EVM :=
                          { target.shared with
                            toMachineState := targetMachine }
                        refine ⟨targetShared, ?_, ?_, by rfl⟩
                        · simp [
                            Locals.Source.PrimitiveSemantics.structured,
                            Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
                            Structured.BasicOp.toPrimOp,
                            Assembly.PrimOp.continuingStep?,
                            Expressions.Structured.BasicOp.inputs,
                            Assembly.PrimStep.run,
                            EvmYul.Stack.pop3,
                            EvmYul.EVM.State.replaceStackAndIncrPC,
                            EvmYul.EVM.State.incrPC, Id.run,
                            hTargetValid, targetShared, targetMachine]
                        · exact
                            ⟨{ sourceShared with
                                toMachineState := sourceMachine },
                              sourceVars, rfl,
                              StateRelation.Shared.withMachine hShared
                                sourceMachine targetMachine hMachine,
                              hVars⟩

theorem safeReturndatacopy
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
          (.Env .RETURNDATACOPY) sourceValues =
        .ok (source', outputs)) :
    ∃ target' : Functions.ObserverSemantics.State transcript,
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval .returndatacopy target
          sourceValues.reverse =
        .ok (target', outputs) ∧
      StateRelation.Replay.Rel codeRel source' target' ∧
      source'.source.store = source.source.store :=
  safeBasicOp (by rfl) (by rfl) (by rfl) (by rfl)
    forwardAt_returndatacopy hRel hRun

theorem rawNoObservableFailure_returndatacopy
    {fuel : Nat}
    {sourceShared : EvmYul.SharedState .Yul}
    {sourceVars : EvmYul.Yul.VarStore}
    {destination readStart size : Word}
    {exception : EvmYul.Yul.Exception}
    (hRun :
      EvmYul.Yul.primCall fuel (.Ok sourceShared sourceVars)
          (.Env .RETURNDATACOPY)
          [destination, readStart, size] =
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
          EvmYul.Yul.primCall previous.succ
              (.Ok sourceShared sourceVars)
              (.Env .RETURNDATACOPY)
              [destination, readStart, size] =
            (match
              EvmYul.step (τ := .Yul) (.Env .RETURNDATACOPY)
                (arg := none) (.Ok sourceShared sourceVars)
                [destination, readStart, size] with
            | .ok (state, value?) => .ok (state, value?.toList)
            | .error err => .error err) := by
        simp [EvmYul.Yul.primCall]
        rfl
      rw [hDispatch] at hRun
      unfold EvmYul.step at hRun
      by_cases hInvalid :
          sourceShared.returnData.size <
            readStart.toNat + size.toNat
      · simp [Id.run, EvmYul.Yul.State.toSharedState,
          hInvalid] at hRun
        rw [← hRun] at hObservable
        simp [Yul.Source.Effectful.Exception.Observable] at hObservable
      · simp [Id.run, EvmYul.Yul.State.toSharedState,
          hInvalid] at hRun

theorem extCodeCopy_related
    {codeRel : StateRelation.CodeRel}
    {source : EvmYul.SharedState .Yul}
    {target : EvmYul.SharedState .EVM}
    (hRel : StateRelation.Shared.Rel codeRel source target)
    (account destination readStart size : Word) :
    StateRelation.Shared.Rel codeRel
      (EvmYul.SharedState.extCodeCopy'
        source account destination readStart size)
      (EvmYul.SharedState.extCodeCopy'
        target account destination readStart size) := by
  let address := EvmYul.AccountAddress.ofUInt256 account
  have hCode :=
    StateRelation.AccountMap.codeImage_eq
      hRel.world.accounts address
  constructor
  · simpa [EvmYul.SharedState.extCodeCopy',
      EvmYul.State.addAccessedAccount, address] using
      StateRelation.World.addAccessedAccount hRel.world address
  · simp [EvmYul.SharedState.extCodeCopy',
      EvmYul.State.lookupAccount, address,
      hRel.machine, hCode]

theorem forwardAt_extcodecopy
    {codeRel : StateRelation.CodeRel} {fuel : Nat} :
    ForwardAt codeRel fuel
      (.Env .EXTCODECOPY) .extcodecopy := by
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
              (.Env .EXTCODECOPY) sourceValues =
            (match EvmYul.Yul.quaternaryCopyOp
              EvmYul.SharedState.extCodeCopy'
              (.Ok sourceShared sourceVars) sourceValues with
            | .ok (state, value?) => .ok (state, value?.toList)
            | .error err => .error err) := by
        simp [EvmYul.Yul.primCall]
        unfold EvmYul.step
        rfl
      rw [hDispatch] at hCall
      cases sourceValues with
      | nil =>
          simp [EvmYul.Yul.quaternaryCopyOp] at hCall
      | cons account rest =>
          cases rest with
          | nil =>
              simp [EvmYul.Yul.quaternaryCopyOp] at hCall
          | cons destination rest =>
              cases rest with
              | nil =>
                  simp [EvmYul.Yul.quaternaryCopyOp] at hCall
              | cons readStart rest =>
                  cases rest with
                  | nil =>
                      simp [EvmYul.Yul.quaternaryCopyOp] at hCall
                  | cons size extra =>
                      cases extra with
                      | cons head tail =>
                          simp [EvmYul.Yul.quaternaryCopyOp] at hCall
                      | nil =>
                          simp [EvmYul.Yul.quaternaryCopyOp,
                            EvmYul.Yul.State.setSharedState] at hCall
                          rcases hCall with ⟨rfl, rfl⟩
                          let targetShared :=
                            EvmYul.SharedState.extCodeCopy'
                              target.shared account destination
                                readStart size
                          refine ⟨targetShared, ?_, ?_, by rfl⟩
                          · simp [
                              Locals.Source.PrimitiveSemantics.structured,
                              Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
                              Structured.BasicOp.toPrimOp,
                              Assembly.PrimOp.continuingStep?,
                              Expressions.Structured.BasicOp.inputs,
                              Assembly.PrimStep.run,
                              EvmYul.EVM.quaternaryCopyOp,
                              EvmYul.EVM.State.replaceStackAndIncrPC,
                              EvmYul.EVM.State.incrPC,
                              EvmYul.Stack.pop4, targetShared, Id.run]
                          · exact
                              ⟨EvmYul.SharedState.extCodeCopy'
                                  sourceShared account destination
                                    readStart size,
                                sourceVars, rfl,
                                extCodeCopy_related hShared account
                                  destination readStart size,
                                hVars⟩

theorem safeExtcodecopy
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
          (.Env .EXTCODECOPY) sourceValues =
        .ok (source', outputs)) :
    ∃ target' : Functions.ObserverSemantics.State transcript,
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval .extcodecopy target
          sourceValues.reverse =
        .ok (target', outputs) ∧
      StateRelation.Replay.Rel codeRel source' target' ∧
      source'.source.store = source.source.store :=
  safeBasicOp (by rfl) (by rfl) (by rfl) (by rfl)
    forwardAt_extcodecopy hRel hRun

theorem rawNoObservableFailure_extcodecopy
    {fuel : Nat}
    {sourceShared : EvmYul.SharedState .Yul}
    {sourceVars : EvmYul.Yul.VarStore}
    {account destination readStart size : Word}
    {exception : EvmYul.Yul.Exception}
    (hRun :
      EvmYul.Yul.primCall fuel (.Ok sourceShared sourceVars)
          (.Env .EXTCODECOPY)
          [account, destination, readStart, size] =
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
          EvmYul.Yul.primCall previous.succ
              (.Ok sourceShared sourceVars)
              (.Env .EXTCODECOPY)
              [account, destination, readStart, size] =
            (match EvmYul.Yul.quaternaryCopyOp
              EvmYul.SharedState.extCodeCopy'
              (.Ok sourceShared sourceVars)
              [account, destination, readStart, size] with
            | .ok (state, value?) => .ok (state, value?.toList)
            | .error err => .error err) := by
        simp [EvmYul.Yul.primCall]
        unfold EvmYul.step
        rfl
      rw [hDispatch] at hRun
      simp [EvmYul.Yul.quaternaryCopyOp] at hRun

end FunctionsObserverPrimitive
end Yul
end EvmCompiler
