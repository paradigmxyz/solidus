import EvmCompiler.Functions.ObserverSafety
import EvmCompiler.Yul.ObserverSafety
import EvmCompiler.Yul.StateRelation

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverPrimitive

abbrev Word := Assembly.Word

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

theorem ForwardAt.withArity
    {codeRel : StateRelation.CodeRel} {fuel : Nat}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    (hForward : ForwardAt codeRel fuel prim op) :
    ForwardAtArity codeRel fuel prim op := by
  intro source source' target sourceValues outputs hRel _hArity hRun
  exact hForward hRel hRun

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
