import EvmCompiler.Simulation.ObserverPass
import EvmCompiler.Yul.FunctionsObserverPrimitive.Core

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverPrimitive

/-!
Primitive preservation owned by the adjacent Yul-to-Functions pass.

The guarded theorems relate canonical Yul and Functions source semantics
directly. They use the shared reservation contract and the ordinary compiler's
primitive selection; no lower compiler pass or target execution appears here.
-/

abbrev Trace := Assembly.ResourceTrace

theorem observerPrim
    {transcript : Trace} {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {kind : Assembly.ResourceObserver} {values : List Word}
    (hYulObserver :
      ObserverSemantics.yulPrimObserver? prim = some kind)
    (hFunctionsObserver :
      Functions.ObserverSemantics.basicOpObserver? op = some kind)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      ObserverSemantics.SourceReplay.primCall fuel.succ source prim [] =
        .ok (source', values)) :
    ∃ target' : Functions.ObserverSemantics.State transcript,
      (Functions.ObserverSemantics.primitiveSemantics transcript).eval
          op target [] =
        .ok (target', values) ∧
      StateRelation.Replay.Rel codeRel source' target' ∧
      source'.source.store = source.source.store := by
  unfold ObserverSemantics.SourceReplay.primCall at hRun
  rw [hYulObserver] at hRun
  cases hConsume :
      Simulation.ResourceReplay.consume? kind source with
  | none =>
      simp [hConsume, Yul.Source.Effectful.fail] at hRun
  | some result =>
      rcases result with ⟨value, sourceAfter⟩
      simp [hConsume] at hRun
      rcases hRun with ⟨hSource, hValues⟩
      subst source'
      subst values
      obtain ⟨targetAfter, hTargetConsume, hCursor, hSourceRel⟩ :=
        Simulation.ResourceReplay.consume?_rel
          hRel.1 hRel.2 hConsume
      refine ⟨targetAfter, ?_, ⟨hCursor, hSourceRel⟩, ?_⟩
      exact
        Functions.ObserverSemantics.primitiveSemantics_eval_observer
          hFunctionsObserver hTargetConsume
      rw [Simulation.ResourceReplay.consume?_source hConsume]

theorem gas
    {transcript : Trace} {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {values : List Word}
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      ObserverSemantics.SourceReplay.primCall fuel.succ source
          (.StackMemFlow .GAS) [] =
        .ok (source', values)) :
    ∃ target' : Functions.ObserverSemantics.State transcript,
      (Functions.ObserverSemantics.primitiveSemantics transcript).eval
          .gas target [] =
        .ok (target', values) ∧
      StateRelation.Replay.Rel codeRel source' target' ∧
      source'.source.store = source.source.store :=
  observerPrim ObserverSemantics.yulPrimObserver?_gas (by rfl) hRel hRun

theorem msize
    {transcript : Trace} {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {values : List Word}
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      ObserverSemantics.SourceReplay.primCall fuel.succ source
          (.StackMemFlow .MSIZE) [] =
        .ok (source', values)) :
    ∃ target' : Functions.ObserverSemantics.State transcript,
      (Functions.ObserverSemantics.primitiveSemantics transcript).eval
          .msize target [] =
        .ok (target', values) ∧
      StateRelation.Replay.Rel codeRel source' target' ∧
      source'.source.store = source.source.store :=
  observerPrim ObserverSemantics.yulPrimObserver?_msize (by rfl) hRel hRun

theorem safeObserverPrim
    {contract : MemoryContract.Contract}
    {transcript : Trace} {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {kind : Assembly.ResourceObserver} {values : List Word}
    (hYulObserver :
      ObserverSemantics.yulPrimObserver? prim = some kind)
    (hFunctionsObserver :
      Functions.ObserverSemantics.basicOpObserver? op = some kind)
    (hTerminal : Prim.terminal? prim = none)
    (hOp : Prim.toUncheckedBasicOp? prim = some op)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval fuel.succ source prim [] =
        .ok (source', values)) :
    ∃ target' : Functions.ObserverSemantics.State transcript,
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval op target [] =
        .ok (target', values) ∧
      StateRelation.Replay.Rel codeRel source' target' ∧
      source'.source.store = source.source.store := by
  obtain ⟨hSourceSafe, hSourceRun⟩ :=
    ObserverSafety.SafeSemantics.eval_ok_parts hRun
  obtain ⟨target', hTargetRun, hFinalRel, hStore⟩ :=
    observerPrim hYulObserver hFunctionsObserver hRel hSourceRun
  have hSourceMemorySafe :
      Simulation.MemorySafety.PrimitiveMemorySafe contract op
        source.source.sharedState.toMachineState [] :=
    (ObserverSafety.primitiveSafe_basicOp hTerminal hOp).mp hSourceSafe
  rcases hRel.2 with
    ⟨sourceShared, sourceVars, hSource, hShared, _hVars⟩
  have hSourceSharedSafe :
      Simulation.MemorySafety.PrimitiveMemorySafe contract op
        sourceShared.toMachineState [] := by
    simpa only [hSource, EvmYul.Yul.State.sharedState] using
      hSourceMemorySafe
  have hTargetSafe :
      Functions.ObserverSafety.PrimitiveMemorySafe contract op
        target.source.shared.toMachineState [] := by
    change
      Simulation.MemorySafety.PrimitiveMemorySafe contract op
        target.source.shared.toMachineState []
    rw [← hShared.machine]
    exact hSourceSharedSafe
  have hTargetPermitted :
      Functions.ObserverSafety.PrimitivePermitted
        op target.source.shared :=
    Functions.ObserverSafety.primitivePermitted_of_observer
      hFunctionsObserver
  refine ⟨target', ?_, hFinalRel, hStore⟩
  exact
    Functions.ObserverSafety.SafeSemantics.eval_of_safe
      hTargetSafe hTargetPermitted hTargetRun

theorem safeObserverPrimBackward
    {contract : MemoryContract.Contract}
    {transcript : Trace} {codeRel : StateRelation.CodeRel} {fuel : Nat}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target target' : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {kind : Assembly.ResourceObserver} {outputs : List Word}
    (hYulObserver :
      ObserverSemantics.yulPrimObserver? prim = some kind)
    (hFunctionsObserver :
      Functions.ObserverSemantics.basicOpObserver? op = some kind)
    (hSourceSafe :
      ObserverSafety.PrimitiveSafe contract prim
        source.source.sharedState.toMachineState [])
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval op target [] =
        .ok (target', outputs)) :
    ∃ source' : ObserverSemantics.SourceReplay.State transcript,
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval fuel.succ source prim [] =
          .ok (source', outputs) ∧
        StateRelation.Replay.Rel codeRel source' target' ∧
        source'.source.store = source.source.store := by
  classical
  obtain ⟨_hTargetSafe, _hTargetPermitted, hTargetRun⟩ :=
    Functions.ObserverSafety.SafeSemantics.eval_parts hRun
  obtain ⟨value, hOutputs, hTargetConsume⟩ :=
    Functions.ObserverSemantics.primitiveSemantics_eval_observer_parts
      hFunctionsObserver hTargetRun
  obtain ⟨source', hSourceConsume, hCursor, hState⟩ :=
    Simulation.ResourceReplay.consume?_rel
      (rel := fun targetState sourceState =>
        StateRelation.Regular.Rel codeRel sourceState targetState)
      hRel.1.symm hRel.2 hTargetConsume
  have hSourceRaw :
      ObserverSemantics.SourceReplay.primCall fuel.succ source prim [] =
        .ok (source', [value]) := by
    simp [ObserverSemantics.SourceReplay.primCall,
      hYulObserver, hSourceConsume]
  refine ⟨source', ?_, ⟨hCursor.symm, hState⟩, ?_⟩
  · rw [hOutputs]
    simpa [ObserverSafety.SafeSemantics.primitiveSemantics,
      hSourceSafe] using hSourceRaw
  · exact congrArg (fun state => state.store)
      (Simulation.ResourceReplay.consume?_source hSourceConsume)

theorem safeObserverNoObservableFailure
    {contract : MemoryContract.Contract}
    {transcript : Trace} {fuel : Nat}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {prim : EvmYul.Operation .Yul}
    {kind : Assembly.ResourceObserver}
    (hYulObserver :
      ObserverSemantics.yulPrimObserver? prim = some kind)
    (hRun :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval fuel.succ source prim [] =
        .error failure)
    (hObservable :
      Yul.Source.Effectful.Exception.Observable failure.exception) :
    False := by
  rcases failure with ⟨exception, failureState⟩
  cases exception with
  | YulHalt sourceFinal value =>
      obtain ⟨_hSafe, hSourceRun⟩ :=
        ObserverSafety.SafeSemantics.eval_yulHalt_parts hRun
      unfold ObserverSemantics.SourceReplay.primCall at hSourceRun
      rw [hYulObserver] at hSourceRun
      cases hConsume :
          Simulation.ResourceReplay.consume? kind source <;>
        simp [hConsume, Yul.Source.Effectful.fail] at hSourceRun
  | Revert sourceFinal =>
      obtain ⟨_hSafe, hSourceRun⟩ :=
        ObserverSafety.SafeSemantics.eval_revert_parts hRun
      unfold ObserverSemantics.SourceReplay.primCall at hSourceRun
      rw [hYulObserver] at hSourceRun
      cases hConsume :
          Simulation.ResourceReplay.consume? kind source <;>
        simp [hConsume, Yul.Source.Effectful.fail] at hSourceRun
  | _ =>
      simp [Yul.Source.Effectful.Exception.Observable] at hObservable

theorem gasSafe
    {contract : MemoryContract.Contract}
    {transcript : Trace} {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {values : List Word}
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval fuel.succ source
          (.StackMemFlow .GAS) [] =
        .ok (source', values)) :
    ∃ target' : Functions.ObserverSemantics.State transcript,
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval .gas target [] =
        .ok (target', values) ∧
      StateRelation.Replay.Rel codeRel source' target' ∧
      source'.source.store = source.source.store :=
  safeObserverPrim ObserverSemantics.yulPrimObserver?_gas (by rfl)
    (by rfl) (by rfl) hRel hRun

theorem msizeSafe
    {contract : MemoryContract.Contract}
    {transcript : Trace} {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {values : List Word}
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval fuel.succ source
          (.StackMemFlow .MSIZE) [] =
        .ok (source', values)) :
    ∃ target' : Functions.ObserverSemantics.State transcript,
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval .msize target [] =
        .ok (target', values) ∧
      StateRelation.Replay.Rel codeRel source' target' ∧
      source'.source.store = source.source.store :=
  safeObserverPrim ObserverSemantics.yulPrimObserver?_msize (by rfl)
    (by rfl) (by rfl) hRel hRun

theorem gasSafeBackward
    {contract : MemoryContract.Contract}
    {transcript : Trace} {codeRel : StateRelation.CodeRel} {fuel : Nat}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target target' : Functions.ObserverSemantics.State transcript}
    {outputs : List Word}
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval .gas target [] =
        .ok (target', outputs)) :
    ∃ source' : ObserverSemantics.SourceReplay.State transcript,
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval fuel.succ source
          (.StackMemFlow .GAS) [] =
          .ok (source', outputs) ∧
        StateRelation.Replay.Rel codeRel source' target' ∧
        source'.source.store = source.source.store :=
  safeObserverPrimBackward
    ObserverSemantics.yulPrimObserver?_gas (by rfl)
    (ObserverSafety.primitiveSafe_gas contract
      source.source.sharedState.toMachineState)
    hRel hRun

theorem msizeSafeBackward
    {contract : MemoryContract.Contract}
    {transcript : Trace} {codeRel : StateRelation.CodeRel} {fuel : Nat}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target target' : Functions.ObserverSemantics.State transcript}
    {outputs : List Word}
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval .msize target [] =
        .ok (target', outputs)) :
    ∃ source' : ObserverSemantics.SourceReplay.State transcript,
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval fuel.succ source
          (.StackMemFlow .MSIZE) [] =
          .ok (source', outputs) ∧
        StateRelation.Replay.Rel codeRel source' target' ∧
        source'.source.store = source.source.store :=
  safeObserverPrimBackward
    ObserverSemantics.yulPrimObserver?_msize (by rfl)
    (ObserverSafety.primitiveSafe_msize contract
      source.source.sharedState.toMachineState)
    hRel hRun

end FunctionsObserverPrimitive
end Yul
end EvmCompiler
