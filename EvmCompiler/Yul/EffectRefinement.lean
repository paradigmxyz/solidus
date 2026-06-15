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

theorem evalTail_zero_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    {sourceInput targetInput : Result σ (σ × Word)}
    (hInput : Result.Refines sourceInput targetInput) :
    Result.Refines
      (evalTail model sourcePrim 0 args codeOverride sourceInput)
      (evalTail model targetPrim 0 args codeOverride targetInput) := by
  intro hObservable
  cases sourceInput with
  | error failure =>
      have hInputObservable :
          Result.Observable
            (.error failure : Result σ (σ × Word)) := by
        simpa [evalTail] using hObservable
      rw [hInput hInputObservable]
      simp [evalTail]
  | ok input =>
      rcases input with ⟨state, value⟩
      rw [hInput (by simp [Result.Observable])]
      simp only [evalTail]

theorem evalTail_succ_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat) (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    {sourceInput targetInput : Result σ (σ × Word)}
    (hInput : Result.Refines sourceInput targetInput)
    (hArgs :
      ∀ state,
        Result.Refines
          (evalArgs model sourcePrim fuel args codeOverride state)
          (evalArgs model targetPrim fuel args codeOverride state)) :
    Result.Refines
      (evalTail model sourcePrim fuel.succ args codeOverride sourceInput)
      (evalTail model targetPrim fuel.succ args codeOverride targetInput) := by
  intro hObservable
  cases sourceInput with
  | error failure =>
      have hInputObservable :
          Result.Observable
            (.error failure : Result σ (σ × Word)) := by
        simpa [evalTail] using hObservable
      rw [hInput hInputObservable]
      simp [evalTail]
  | ok input =>
      rcases input with ⟨state, value⟩
      rw [hInput (by simp [Result.Observable])]
      generalize hSourceArgs :
        evalArgs model sourcePrim fuel args codeOverride state = sourceArgs
      cases sourceArgs with
      | error failure =>
          have hArgsObservable :
              Result.Observable
                (.error failure : Result σ (σ × List Word)) := by
            simpa only [evalTail, hSourceArgs] using hObservable
          have hSourceArgsObservable :
              Result.Observable
                (evalArgs model sourcePrim fuel args codeOverride state) := by
            rw [hSourceArgs]
            exact hArgsObservable
          have hTargetArgs := hArgs state hSourceArgsObservable
          rw [hSourceArgs] at hTargetArgs
          simpa only [evalTail, hSourceArgs, hTargetArgs]
      | ok result =>
          rcases result with ⟨final, values⟩
          have hSourceArgsObservable :
              Result.Observable
                (evalArgs model sourcePrim fuel args codeOverride state) := by
            rw [hSourceArgs]
            simp [Result.Observable]
          have hTargetArgs := hArgs state hSourceArgsObservable
          rw [hSourceArgs] at hTargetArgs
          simpa only [evalTail, hSourceArgs, hTargetArgs]

theorem evalArgs_zero_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ) :
    Result.Refines
      (evalArgs model sourcePrim 0 args codeOverride state)
      (evalArgs model targetPrim 0 args codeOverride state) :=
  by
    simpa [evalArgs] using
      (Result.Refines.refl
        (fail state .OutOfFuel : Result σ (σ × List Word)))

theorem evalArgs_nil_succ_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ) :
    Result.Refines
      (evalArgs model sourcePrim fuel.succ [] codeOverride state)
      (evalArgs model targetPrim fuel.succ [] codeOverride state) :=
  by
    simpa [evalArgs] using
      (Result.Refines.refl
        (.ok (state, []) : Result σ (σ × List Word)))

theorem evalArgs_cons_succ_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat) (arg : EvmYul.Yul.Ast.Expr)
    (rest : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ)
    (hTail :
      Result.Refines
        (evalTail model sourcePrim fuel rest codeOverride
          (Effectful.eval model sourcePrim fuel arg codeOverride state))
        (evalTail model targetPrim fuel rest codeOverride
          (Effectful.eval model targetPrim fuel arg codeOverride state))) :
    Result.Refines
      (evalArgs model sourcePrim fuel.succ (arg :: rest)
        codeOverride state)
      (evalArgs model targetPrim fuel.succ (arg :: rest)
        codeOverride state) := by
  simpa [evalArgs] using hTail

theorem evalValues_primitive_succ_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (hPrim : sourcePrim.ObservableRefines targetPrim)
    (fuel : Nat) (op : EvmYul.Operation .Yul)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ)
    (hArgs :
      Result.Refines
        (evalArgs model sourcePrim fuel args.reverse codeOverride state)
        (evalArgs model targetPrim fuel args.reverse codeOverride state)) :
    Result.Refines
      (evalValues model sourcePrim fuel.succ
        (.Call (.inl op) args) codeOverride state)
      (evalValues model targetPrim fuel.succ
        (.Call (.inl op) args) codeOverride state) := by
  intro hObservable
  generalize hSourceArgs :
    evalArgs model sourcePrim fuel args.reverse codeOverride state = sourceArgs
  cases sourceArgs with
  | error failure =>
      have hArgsObservable :
          Result.Observable
            (.error failure : Result σ (σ × List Word)) := by
        simpa only [evalValues, hSourceArgs] using hObservable
      have hSourceArgsObservable :
          Result.Observable
            (evalArgs model sourcePrim fuel args.reverse
              codeOverride state) := by
        rw [hSourceArgs]
        exact hArgsObservable
      have hTargetArgs := hArgs hSourceArgsObservable
      rw [hSourceArgs] at hTargetArgs
      simpa only [evalValues, hSourceArgs, hTargetArgs]
  | ok result =>
      rcases result with ⟨stateAfterArgs, values⟩
      have hSourceArgsObservable :
          Result.Observable
            (evalArgs model sourcePrim fuel args.reverse
              codeOverride state) := by
        rw [hSourceArgs]
        simp [Result.Observable]
      have hTargetArgs := hArgs hSourceArgsObservable
      rw [hSourceArgs] at hTargetArgs
      have hPrimitiveObservable :
          Result.Observable
            (sourcePrim.eval fuel stateAfterArgs op values.reverse) := by
        simpa only [evalValues, hSourceArgs] using hObservable
      have hPrimitive :=
        hPrim.result fuel stateAfterArgs op values.reverse
          hPrimitiveObservable
      simpa only [evalValues, hSourceArgs, hTargetArgs] using hPrimitive

theorem evalValues_function_succ_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat) (functionName : EvmYul.Yul.Ast.YulFunctionName)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ)
    (hArgs :
      Result.Refines
        (evalArgs model sourcePrim fuel args.reverse codeOverride state)
        (evalArgs model targetPrim fuel args.reverse codeOverride state))
    (hCall :
      ∀ callArgs callState,
        Result.Refines
          (Effectful.call model sourcePrim fuel callArgs
            (some functionName) codeOverride callState)
          (Effectful.call model targetPrim fuel callArgs
            (some functionName) codeOverride callState)) :
    Result.Refines
      (evalValues model sourcePrim fuel.succ
        (.Call (.inr functionName) args) codeOverride state)
      (evalValues model targetPrim fuel.succ
        (.Call (.inr functionName) args) codeOverride state) := by
  intro hObservable
  generalize hSourceArgs :
    evalArgs model sourcePrim fuel args.reverse codeOverride state = sourceArgs
  cases sourceArgs with
  | error failure =>
      have hArgsObservable :
          Result.Observable
            (.error failure : Result σ (σ × List Word)) := by
        simpa only [evalValues, hSourceArgs] using hObservable
      have hSourceArgsObservable :
          Result.Observable
            (evalArgs model sourcePrim fuel args.reverse
              codeOverride state) := by
        rw [hSourceArgs]
        exact hArgsObservable
      have hTargetArgs := hArgs hSourceArgsObservable
      rw [hSourceArgs] at hTargetArgs
      simpa only [evalValues, hSourceArgs, hTargetArgs]
  | ok result =>
      rcases result with ⟨stateAfterArgs, values⟩
      have hSourceArgsObservable :
          Result.Observable
            (evalArgs model sourcePrim fuel args.reverse
              codeOverride state) := by
        rw [hSourceArgs]
        simp [Result.Observable]
      have hTargetArgs := hArgs hSourceArgsObservable
      rw [hSourceArgs] at hTargetArgs
      have hCallObservable :
          Result.Observable
            (Effectful.call model sourcePrim fuel values.reverse
              (some functionName) codeOverride stateAfterArgs) := by
        simpa only [evalValues, hSourceArgs] using hObservable
      have hCallResult :=
        hCall values.reverse stateAfterArgs hCallObservable
      simpa only [evalValues, hSourceArgs, hTargetArgs] using hCallResult

theorem evalValues_var_succ_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat) (name : EvmYul.Identifier)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ) :
    Result.Refines
      (evalValues model sourcePrim fuel.succ (.Var name)
        codeOverride state)
      (evalValues model targetPrim fuel.succ (.Var name)
        codeOverride state) :=
  by
    simpa [evalValues] using
      (Result.Refines.refl
        (match (model.source state).lookup? name with
        | some found => .ok (state, [found])
        | none => fail state (.UnknownIdentifier name)))

theorem evalValues_lit_succ_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat) (value : Word)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ) :
    Result.Refines
      (evalValues model sourcePrim fuel.succ (.Lit value)
        codeOverride state)
      (evalValues model targetPrim fuel.succ (.Lit value)
        codeOverride state) :=
  by
    simpa [evalValues] using
      (Result.Refines.refl
        (.ok (state, [value]) : Result σ (σ × List Word)))

theorem eval_refines_of_evalValues
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat) (expr : EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ)
    (hValues :
      Result.Refines
        (evalValues model sourcePrim fuel expr codeOverride state)
        (evalValues model targetPrim fuel expr codeOverride state)) :
    Result.Refines
      (Effectful.eval model sourcePrim fuel expr codeOverride state)
      (Effectful.eval model targetPrim fuel expr codeOverride state) := by
  intro hObservable
  generalize hSourceValues :
    evalValues model sourcePrim fuel expr codeOverride state = sourceValues
  cases sourceValues with
  | error failure =>
      have hValuesObservable :
          Result.Observable
            (.error failure : Result σ (σ × List Word)) := by
        simpa only [Effectful.eval, hSourceValues] using hObservable
      have hSourceValuesObservable :
          Result.Observable
            (evalValues model sourcePrim fuel expr codeOverride state) := by
        rw [hSourceValues]
        exact hValuesObservable
      have hTargetValues := hValues hSourceValuesObservable
      rw [hSourceValues] at hTargetValues
      simpa only [Effectful.eval, hSourceValues, hTargetValues]
  | ok result =>
      rcases result with ⟨final, values⟩
      have hSourceValuesObservable :
          Result.Observable
            (evalValues model sourcePrim fuel expr codeOverride state) := by
        rw [hSourceValues]
        simp [Result.Observable]
      have hTargetValues := hValues hSourceValuesObservable
      rw [hSourceValues] at hTargetValues
      simpa only [Effectful.eval, hSourceValues, hTargetValues]

end Effectful
end Source
end Yul
end EvmCompiler
