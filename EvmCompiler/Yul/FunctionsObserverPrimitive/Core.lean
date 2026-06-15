import EvmCompiler.Functions.ObserverSafety
import EvmCompiler.Yul.ObserverSafety
import EvmCompiler.Yul.StateRelation

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverPrimitive

abbrev Word := Assembly.Word

theorem list_eq_four_of_length_eq
    {α : Type} {values : List α} (hLength : values.length = 4) :
    ∃ first second third fourth,
      values = [first, second, third, fourth] := by
  cases values with
  | nil => simp at hLength
  | cons first rest =>
      have hRest : rest.length = 3 := by simpa using hLength
      obtain ⟨second, third, fourth, rfl⟩ :=
        List.length_eq_three.mp hRest
      exact ⟨first, second, third, fourth, rfl⟩

theorem list_eq_five_of_length_eq
    {α : Type} {values : List α} (hLength : values.length = 5) :
    ∃ first second third fourth fifth,
      values = [first, second, third, fourth, fifth] := by
  cases values with
  | nil => simp at hLength
  | cons first rest =>
      have hRest : rest.length = 4 := by simpa using hLength
      obtain ⟨second, third, fourth, fifth, rfl⟩ :=
        list_eq_four_of_length_eq hRest
      exact ⟨first, second, third, fourth, fifth, rfl⟩

theorem list_eq_six_of_length_eq
    {α : Type} {values : List α} (hLength : values.length = 6) :
    ∃ first second third fourth fifth sixth,
      values = [first, second, third, fourth, fifth, sixth] := by
  cases values with
  | nil => simp at hLength
  | cons first rest =>
      have hRest : rest.length = 5 := by simpa using hLength
      obtain ⟨second, third, fourth, fifth, sixth, rfl⟩ :=
        list_eq_five_of_length_eq hRest
      exact ⟨first, second, third, fourth, fifth, sixth, rfl⟩

/--
The semantic obligation for one ordinary compiler-selected Yul primitive.

Yul primitive handlers receive arguments in source order. The Functions
compiler reverses the corresponding expression sequence, so the canonical
Functions primitive receives `sourceValues.reverse` in EVM stack order.
-/
def ForwardAt (codeRel : StateRelation.CodeRel) (fuel : Nat)
    (prim : EvmYul.Operation .Yul) (op : Structured.BasicOp) : Prop :=
  ∀ {source source' : EvmYul.Yul.State}
    {target : Locals.Source.State}
    {sourceValues outputs : List Word},
    StateRelation.Regular.Rel codeRel source target →
    EvmYul.Yul.primCall fuel source prim sourceValues =
      .ok (source', outputs) →
    ∃ targetShared : EvmYul.SharedState .EVM,
      Locals.Source.PrimitiveSemantics.structured.eval
          op target.shared sourceValues.reverse =
        .ok (targetShared, outputs) ∧
      StateRelation.Regular.Rel codeRel source'
        (target.withShared targetShared) ∧
      source'.store = source.store

def ForwardAtArity (codeRel : StateRelation.CodeRel) (fuel : Nat)
    (prim : EvmYul.Operation .Yul) (op : Structured.BasicOp) : Prop :=
  ∀ {source source' : EvmYul.Yul.State}
    {target : Locals.Source.State}
    {sourceValues outputs : List Word},
    StateRelation.Regular.Rel codeRel source target →
    sourceValues.length = Expressions.Structured.BasicOp.inputs op →
    EvmYul.Yul.primCall fuel source prim sourceValues =
      .ok (source', outputs) →
    ∃ targetShared : EvmYul.SharedState .EVM,
      Locals.Source.PrimitiveSemantics.structured.eval
          op target.shared sourceValues.reverse =
        .ok (targetShared, outputs) ∧
      StateRelation.Regular.Rel codeRel source'
        (target.withShared targetShared) ∧
      source'.store = source.store

def BackwardAt (codeRel : StateRelation.CodeRel) (fuel : Nat)
    (prim : EvmYul.Operation .Yul) (op : Structured.BasicOp) : Prop :=
  ∀ {source : EvmYul.Yul.State}
    {target : Locals.Source.State}
    {targetShared : EvmYul.SharedState .EVM}
    {sourceValues outputs : List Word},
    StateRelation.Regular.Rel codeRel source target →
    Locals.Source.PrimitiveSemantics.structured.eval
        op target.shared sourceValues.reverse =
      .ok (targetShared, outputs) →
    ∃ source',
      EvmYul.Yul.primCall fuel source prim sourceValues =
          .ok (source', outputs) ∧
        StateRelation.Regular.Rel codeRel source'
          (target.withShared targetShared) ∧
        source'.store = source.store

def BackwardAtArity (codeRel : StateRelation.CodeRel) (fuel : Nat)
    (prim : EvmYul.Operation .Yul) (op : Structured.BasicOp) : Prop :=
  ∀ {source : EvmYul.Yul.State}
    {target : Locals.Source.State}
    {targetShared : EvmYul.SharedState .EVM}
    {sourceValues outputs : List Word},
    StateRelation.Regular.Rel codeRel source target →
    sourceValues.length = Expressions.Structured.BasicOp.inputs op →
    Locals.Source.PrimitiveSemantics.structured.eval
        op target.shared sourceValues.reverse =
      .ok (targetShared, outputs) →
    ∃ source',
      EvmYul.Yul.primCall fuel source prim sourceValues =
          .ok (source', outputs) ∧
        StateRelation.Regular.Rel codeRel source'
          (target.withShared targetShared) ∧
        source'.store = source.store

def RawNoObservableFailureAt (fuel : Nat)
    (prim : EvmYul.Operation .Yul) : Prop :=
  ∀ {source : EvmYul.Yul.State} {values : List Word}
    {exception : EvmYul.Yul.Exception},
    EvmYul.Yul.primCall fuel source prim values =
        .error exception →
      ¬Yul.Source.Effectful.Exception.Observable exception

theorem guardedNoObservableFailure_of_raw
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {fuel : Nat}
    {source :
      ObserverSemantics.SourceReplay.State transcript}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {prim : EvmYul.Operation .Yul} {sourceValues : List Word}
    (hObserver : ObserverSemantics.yulPrimObserver? prim = none)
    (hRaw :
      ∀ {rawException : EvmYul.Yul.Exception},
        EvmYul.Yul.primCall fuel source.source prim sourceValues =
            .error rawException →
          ¬Yul.Source.Effectful.Exception.Observable rawException)
    (hRun :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval fuel.succ source prim sourceValues =
        .error failure)
    (hObservable :
      Yul.Source.Effectful.Exception.Observable failure.exception) :
    False := by
  rcases failure with ⟨exception, failureState⟩
  cases exception with
  | YulHalt sourceFinal value =>
      obtain ⟨_hSafe, hSourceRun⟩ :=
        ObserverSafety.SafeSemantics.eval_yulHalt_parts hRun
      cases hRawRun :
          EvmYul.Yul.primCall fuel source.source prim sourceValues with
      | ok result =>
          simp [ObserverSemantics.SourceReplay.primCall,
            hObserver, hRawRun] at hSourceRun
      | error rawException =>
          have hExceptionEq :=
            congrArg
              (fun result =>
                match result with
                | .ok _ => none
                | .error rawFailure =>
                    some rawFailure.exception)
              hSourceRun
          simp [ObserverSemantics.SourceReplay.primCall,
            hObserver, hRawRun, Yul.Source.Effectful.fail] at hExceptionEq
          subst rawException
          have hExceptionObservable :
              Yul.Source.Effectful.Exception.Observable
                (.YulHalt sourceFinal value) := by simp
          exact hRaw hRawRun hExceptionObservable
  | Revert sourceFinal =>
      obtain ⟨_hSafe, hSourceRun⟩ :=
        ObserverSafety.SafeSemantics.eval_revert_parts hRun
      cases hRawRun :
          EvmYul.Yul.primCall fuel source.source prim sourceValues with
      | ok result =>
          simp [ObserverSemantics.SourceReplay.primCall,
            hObserver, hRawRun] at hSourceRun
      | error rawException =>
          have hExceptionEq :=
            congrArg
              (fun result =>
                match result with
                | .ok _ => none
                | .error rawFailure =>
                    some rawFailure.exception)
              hSourceRun
          simp [ObserverSemantics.SourceReplay.primCall,
            hObserver, hRawRun, Yul.Source.Effectful.fail] at hExceptionEq
          subst rawException
          have hExceptionObservable :
              Yul.Source.Effectful.Exception.Observable
                (.Revert sourceFinal) := by simp
          exact hRaw hRawRun hExceptionObservable
  | _ =>
      simp [Yul.Source.Effectful.Exception.Observable] at hObservable

theorem ForwardAt.withArity
    {codeRel : StateRelation.CodeRel} {fuel : Nat}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    (hForward : ForwardAt codeRel fuel prim op) :
    ForwardAtArity codeRel fuel prim op := by
  intro source source' target sourceValues outputs hRel _hArity hRun
  exact hForward hRel hRun

theorem BackwardAt.withArity
    {codeRel : StateRelation.CodeRel} {fuel : Nat}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    (hBackward : BackwardAt codeRel fuel prim op) :
    BackwardAtArity codeRel fuel prim op := by
  intro source target targetShared sourceValues outputs hRel _hArity hRun
  exact hBackward hRel hRun

/--
Shared guarded lift after fixing the related source and target states.
-/
private theorem safeBasicOp_of_raw
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceValues outputs : List Word}
    (hYulObserver :
      ObserverSemantics.yulPrimObserver? prim = none)
    (hFunctionsObserver :
      Functions.ObserverSemantics.basicOpObserver? op = none)
    (hTerminal : Prim.terminal? prim = none)
    (hOp : Prim.toUncheckedBasicOp? prim = some op)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRawForward :
      ∀ {sourceAfter : EvmYul.Yul.State}
        {rawOutputs : List Word},
        EvmYul.Yul.primCall fuel source.source prim sourceValues =
            .ok (sourceAfter, rawOutputs) →
          ∃ targetShared : EvmYul.SharedState .EVM,
            Locals.Source.PrimitiveSemantics.structured.eval
                op target.source.shared sourceValues.reverse =
              .ok (targetShared, rawOutputs) ∧
            StateRelation.Regular.Rel codeRel sourceAfter
              (target.source.withShared targetShared) ∧
            sourceAfter.store = source.source.store)
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
  obtain ⟨hSourceSafe, hSourceRun⟩ :=
    ObserverSafety.SafeSemantics.eval_ok_parts hRun
  have hSourceMemorySafe :
      Simulation.MemorySafety.PrimitiveMemorySafe contract op
        source.source.sharedState.toMachineState sourceValues.reverse :=
    (ObserverSafety.primitiveSafe_basicOp hTerminal hOp).mp hSourceSafe
  cases hRaw :
      EvmYul.Yul.primCall fuel source.source prim sourceValues with
  | error err =>
      simp [ObserverSemantics.SourceReplay.primCall,
        hYulObserver, hRaw, Yul.Source.Effectful.fail] at hSourceRun
  | ok result =>
      rcases result with ⟨sourceAfter, rawOutputs⟩
      have hSourceEq :
          source.withSource sourceAfter = source' ∧
            rawOutputs = outputs := by
        simpa [ObserverSemantics.SourceReplay.primCall,
          hYulObserver, hRaw] using hSourceRun
      rcases hSourceEq with ⟨hSourceEq, hOutputs⟩
      subst source'
      subst outputs
      obtain ⟨targetShared, hTargetRaw, hFinalRegular, hStore⟩ :=
        hRawForward hRaw
      have hTargetSafe :
          Functions.ObserverSafety.PrimitiveMemorySafe contract op
            target.source.shared.toMachineState sourceValues.reverse := by
        change
          Simulation.MemorySafety.PrimitiveMemorySafe contract op
            target.source.shared.toMachineState sourceValues.reverse
        rw [← StateRelation.Replay.machine_eq hRel]
        exact hSourceMemorySafe
      let target' : Functions.ObserverSemantics.State transcript :=
        target.withSource (target.source.withShared targetShared)
      refine ⟨target', ?_, ⟨hRel.1, hFinalRegular⟩, ?_⟩
      · have hTargetObserver :=
          Functions.ObserverSemantics.primitiveSemantics_eval_nonObserver
            hFunctionsObserver hTargetRaw
        exact
          Functions.ObserverSafety.SafeSemantics.eval_of_safe
            hTargetSafe (by simpa [target'] using hTargetObserver)
      · simpa using hStore

/--
Lift an adjacent raw primitive proof to the canonical guarded Yul and
Functions observer semantics for a non-observer basic operation.
-/
theorem safeBasicOp
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceValues outputs : List Word}
    (hYulObserver :
      ObserverSemantics.yulPrimObserver? prim = none)
    (hFunctionsObserver :
      Functions.ObserverSemantics.basicOpObserver? op = none)
    (hTerminal : Prim.terminal? prim = none)
    (hOp : Prim.toUncheckedBasicOp? prim = some op)
    (hForward : ForwardAt codeRel fuel prim op)
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
  apply safeBasicOp_of_raw hYulObserver hFunctionsObserver
    hTerminal hOp hRel _ hRun
  intro sourceAfter rawOutputs hRaw
  exact hForward hRel.2 hRaw

theorem safeBasicOpBackward
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target target' : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceValues outputs : List Word}
    (hYulObserver :
      ObserverSemantics.yulPrimObserver? prim = none)
    (hFunctionsObserver :
      Functions.ObserverSemantics.basicOpObserver? op = none)
    (hTerminal : Prim.terminal? prim = none)
    (hOp : Prim.toUncheckedBasicOp? prim = some op)
    (hBackward : BackwardAt codeRel fuel prim op)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval op target sourceValues.reverse =
        .ok (target', outputs)) :
    ∃ source' : ObserverSemantics.SourceReplay.State transcript,
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval (fuel + 1) source prim sourceValues =
          .ok (source', outputs) ∧
        StateRelation.Replay.Rel codeRel source' target' ∧
        source'.source.store = source.source.store := by
  classical
  obtain ⟨hTargetSafe, hTargetRun⟩ :=
    Functions.ObserverSafety.SafeSemantics.eval_parts hRun
  have hSourceMemorySafe :
      Simulation.MemorySafety.PrimitiveMemorySafe contract op
        source.source.sharedState.toMachineState sourceValues.reverse := by
    rw [StateRelation.Replay.machine_eq hRel]
    exact hTargetSafe
  have hSourceSafe :
      ObserverSafety.PrimitiveSafe contract prim
        source.source.sharedState.toMachineState sourceValues :=
    (ObserverSafety.primitiveSafe_basicOp hTerminal hOp).mpr
      hSourceMemorySafe
  obtain ⟨targetShared, hTargetRaw, hTargetShape⟩ :
      ∃ targetShared,
        Locals.Source.PrimitiveSemantics.structured.eval
            op target.source.shared sourceValues.reverse =
          .ok (targetShared, outputs) ∧
        target' =
          target.withSource
            (target.source.withShared targetShared) := by
    obtain ⟨targetShared, hTargetRaw, hTargetEq⟩ :=
      Functions.ObserverSemantics.primitiveSemantics_eval_nonObserver_parts
        hFunctionsObserver hTargetRun
    exact ⟨targetShared, hTargetRaw, hTargetEq⟩
  obtain ⟨sourceAfter, hSourceRaw, hFinalRel, hStore⟩ :=
    hBackward hRel.2 hTargetRaw
  rw [hTargetShape]
  have hSourceObserver :
      ObserverSemantics.SourceReplay.primCall
          (fuel + 1) source prim sourceValues =
        .ok (source.withSource sourceAfter, outputs) := by
    simp [ObserverSemantics.SourceReplay.primCall,
      hYulObserver, hSourceRaw,
      ObserverSemantics.SourceReplay.State.withSource,
      Simulation.ResourceReplay.State.withSource]
  refine
    ⟨source.withSource sourceAfter, ?_, ⟨hRel.1, hFinalRel⟩, ?_⟩
  · simpa [ObserverSafety.SafeSemantics.primitiveSemantics,
      hSourceSafe] using hSourceObserver
  · simpa using hStore

theorem safeBasicOpArity
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceValues outputs : List Word}
    (hYulObserver :
      ObserverSemantics.yulPrimObserver? prim = none)
    (hFunctionsObserver :
      Functions.ObserverSemantics.basicOpObserver? op = none)
    (hTerminal : Prim.terminal? prim = none)
    (hOp : Prim.toUncheckedBasicOp? prim = some op)
    (hForward : ForwardAtArity codeRel fuel prim op)
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
  apply safeBasicOp_of_raw hYulObserver hFunctionsObserver
    hTerminal hOp hRel _ hRun
  intro sourceAfter rawOutputs hRaw
  exact hForward hRel.2 hArity hRaw

end FunctionsObserverPrimitive
end Yul
end EvmCompiler
