import EvmCompiler.Simulation.ObserverPass
import EvmCompiler.Yul.FunctionsObserverPrimitive.Copy
import EvmCompiler.Yul.FunctionsObserverPrimitive.Environment
import EvmCompiler.Yul.FunctionsObserverPrimitive.Machine
import EvmCompiler.Yul.FunctionsObserverPrimitive.Pure
import EvmCompiler.Yul.FunctionsObserverPrimitive.World

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
      StateRelation.Replay.Rel codeRel source' target' := by
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
      refine ⟨targetAfter, ?_, hCursor, hSourceRel⟩
      exact
        Functions.ObserverSemantics.primitiveSemantics_eval_observer
          hFunctionsObserver hTargetConsume

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
      StateRelation.Replay.Rel codeRel source' target' :=
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
      StateRelation.Replay.Rel codeRel source' target' :=
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
      StateRelation.Replay.Rel codeRel source' target' := by
  obtain ⟨hSourceSafe, hSourceRun⟩ :=
    ObserverSafety.SafeSemantics.eval_ok_parts hRun
  obtain ⟨target', hTargetRun, hFinalRel⟩ :=
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
  refine ⟨target', ?_, hFinalRel⟩
  simpa [Functions.ObserverSafety.SafeSemantics.primitiveSemantics,
    hTargetSafe] using hTargetRun

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
      StateRelation.Replay.Rel codeRel source' target' :=
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
      StateRelation.Replay.Rel codeRel source' target' :=
  safeObserverPrim ObserverSemantics.yulPrimObserver?_msize (by rfl)
    (by rfl) (by rfl) hRel hRun

end FunctionsObserverPrimitive
end Yul
end EvmCompiler
