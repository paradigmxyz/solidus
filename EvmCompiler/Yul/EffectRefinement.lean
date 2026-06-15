import EvmCompiler.Yul.EffectSemantics

namespace EvmCompiler
namespace Yul
namespace Source
namespace Effectful

namespace Exception

/--
Interpreter exceptions represented as successful public Yul outcomes.

Other failures remain outside the execution claimed by the compiler theorem.
-/
@[simp] def Observable : EvmYul.Yul.Exception → Prop
  | .YulHalt _ _ => True
  | .Revert _ => True
  | _ => False

end Exception

namespace Result

@[simp] def Observable {σ α : Type} : Result σ α → Prop
  | .ok _ => True
  | .error failure => Exception.Observable failure.exception

/--
Outcome-sensitive refinement for one effectful computation.

Only source results represented by the public Yul outcome type constrain the
target computation. This makes deliberate safety rejection compositional
without treating `InvalidInstruction` as a successful source execution.
-/
def Refines {σ α : Type} (source target : Result σ α) : Prop :=
  Observable source → target = source

theorem Refines.refl {σ α : Type} (result : Result σ α) :
    Refines result result := by
  intro _hObservable
  rfl

theorem Refines.eq_of_observable
    {σ α : Type} {source target : Result σ α}
    (hRefines : Refines source target)
    (hObservable : Observable source) :
    target = source :=
  hRefines hObservable

theorem Refines.map
    {σ α β : Type} {source target : Result σ α}
    (f : α → β) (hRefines : Refines source target) :
    Refines (source.map f) (target.map f) := by
  intro hObservable
  cases source with
  | error failure =>
      have hSourceObservable :
          Observable (.error failure : Result σ α) := by
        simpa [Except.map] using hObservable
      rw [hRefines hSourceObservable]
  | ok value =>
      rw [hRefines (by simp [Observable])]

theorem Refines.bind
    {σ α β : Type} {source target : Result σ α}
    {sourceNext targetNext : α → Result σ β}
    (hFirst : Refines source target)
    (hNext :
      ∀ value, Refines (sourceNext value) (targetNext value)) :
    Refines
      (source.bind sourceNext)
      (target.bind targetNext) := by
  intro hObservable
  cases source with
  | error failure =>
      have hSourceObservable :
          Observable (.error failure : Result σ α) := by
        simpa [Bind.bind, Except.bind] using hObservable
      rw [hFirst hSourceObservable]
      simp [Bind.bind, Except.bind]
  | ok value =>
      rw [hFirst (by simp [Observable])]
      exact hNext value hObservable

end Result

namespace PrimitiveSemantics

/--
A primitive-handler refinement sufficient for public Yul outcomes.

Ordinary successes and terminal `YulHalt`/`Revert` failures must be reproduced
exactly. Nonterminal source failures are outside the claimed execution.
-/
structure ObservableRefines {σ : Type}
    (source target : PrimitiveSemantics σ) : Prop where
  eval :
    ∀ {fuel state prim values result},
      Result.Observable result →
      source.eval fuel state prim values = result →
      target.eval fuel state prim values = result

theorem ObservableRefines.result
    {σ : Type} {source target : PrimitiveSemantics σ}
    (hRefines : source.ObservableRefines target)
    (fuel : Nat) (state : σ) (prim : EvmYul.Operation .Yul)
    (values : List Word) :
    Result.Refines
      (source.eval fuel state prim values)
      (target.eval fuel state prim values) := by
  intro hObservable
  apply hRefines.eval hObservable
  rfl

theorem ObservableRefines.ok
    {σ : Type} {source target : PrimitiveSemantics σ}
    (hRefines : source.ObservableRefines target)
    {fuel state prim values final outputs}
    (hEval :
      source.eval fuel state prim values = .ok (final, outputs)) :
    target.eval fuel state prim values = .ok (final, outputs) :=
  hRefines.eval (by simp [Result.Observable]) hEval

theorem ObservableRefines.yulHalt
    {σ : Type} {source target : PrimitiveSemantics σ}
    (hRefines : source.ObservableRefines target)
    {fuel state prim values sourceState value failureState}
    (hEval :
      source.eval fuel state prim values =
        .error
          { exception := .YulHalt sourceState value
            state := failureState }) :
    target.eval fuel state prim values =
      .error
        { exception := .YulHalt sourceState value
          state := failureState } :=
  hRefines.eval (by simp [Result.Observable, Exception.Observable]) hEval

theorem ObservableRefines.revert
    {σ : Type} {source target : PrimitiveSemantics σ}
    (hRefines : source.ObservableRefines target)
    {fuel state prim values sourceState failureState}
    (hEval :
      source.eval fuel state prim values =
        .error
          { exception := .Revert sourceState
            state := failureState }) :
    target.eval fuel state prim values =
      .error
        { exception := .Revert sourceState
          state := failureState } :=
  hRefines.eval (by simp [Result.Observable, Exception.Observable]) hEval

end PrimitiveSemantics

theorem multifill_refines
    {σ : Type} (model : StateModel σ)
    (vars : List EvmYul.Identifier)
    {source target : Result σ (σ × List Word)}
    (hRefines : Result.Refines source target) :
    Result.Refines
      (multifill model vars source)
      (multifill model vars target) := by
  intro hObservable
  cases source with
  | error failure =>
      have hSourceObservable :
          Result.Observable
            (.error failure : Result σ (σ × List Word)) := by
        simpa [multifill] using hObservable
      rw [hRefines hSourceObservable]
  | ok result =>
      rw [hRefines (by simp [Result.Observable])]

end Effectful
end Source
end Yul
end EvmCompiler
