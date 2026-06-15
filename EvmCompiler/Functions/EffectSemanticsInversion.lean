import EvmCompiler.Functions.EffectSemantics

namespace EvmCompiler
namespace Functions
namespace Source
namespace Effectful

/-!
Successful-evaluation inversions owned by the Functions semantics boundary.
-/

namespace Expr

theorem eval_lit_ok_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    {value : Word} {state final : σ} {values : List Word}
    (hEval :
      eval model prim (.lit value : Functions.Expr 1) state =
        .ok (final, values)) :
    final = state ∧ values = [value] := by
  simp [eval, Locals.Source.Effectful.Expr.eval] at hEval
  exact ⟨hEval.1.symm, hEval.2.symm⟩

theorem eval_var_ok_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    {name : Name} {state final : σ} {values : List Word}
    (hEval :
      eval model prim (.var name : Functions.Expr 1) state =
        .ok (final, values)) :
    ∃ value,
      model.vars state name = some value ∧
      final = state ∧ values = [value] := by
  cases hLookup : model.vars state name with
  | none =>
      simp [eval, Locals.Source.Effectful.Expr.eval,
        hLookup, Functions.Source.invalid,
        Structured.invalid] at hEval
  | some value =>
      simp [eval, Locals.Source.Effectful.Expr.eval,
        hLookup] at hEval
      exact
        ⟨value, rfl, hEval.1.symm, hEval.2.symm⟩

theorem eval_singleton_of_evalOne {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    {expr : Functions.Expr 1} {state final : σ} {value : Word}
    (hEval :
      evalOne model prim expr state =
        .ok (final, value)) :
    eval model prim expr state =
      .ok (final, [value]) := by
  unfold evalOne at hEval
  unfold Locals.Source.Effectful.Expr.evalOne at hEval
  cases hExpr : eval model prim expr state with
  | error err =>
      simp [hExpr] at hEval
  | ok result =>
      rcases result with ⟨afterExpr, values⟩
      cases values with
      | nil =>
          simp [hExpr, Functions.Source.invalid,
            Structured.invalid] at hEval
      | cons first rest =>
          cases rest with
          | nil =>
              simp [hExpr] at hEval
              rcases hEval with ⟨rfl, rfl⟩
              rfl
          | cons second tail =>
              simp [hExpr, Functions.Source.invalid,
                Structured.invalid] at hEval

theorem eval_prim_ok_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    {op : Structured.BasicOp}
    {args : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op)}
    {state final : σ} {values : List Word}
    (hEval :
      eval model prim
          (.prim op args :
            Functions.Expr (Expressions.Structured.BasicOp.outputs op))
          state =
        .ok (final, values)) :
    ∃ afterArgs inputValues,
      Locals.Source.Effectful.Expr.ExprSeq.eval
          model prim args state =
        .ok (afterArgs, inputValues) ∧
      prim.eval op afterArgs inputValues =
        .ok (final, values) := by
  unfold eval at hEval
  unfold Locals.Source.Effectful.Expr.eval at hEval
  cases hArgs :
      Locals.Source.Effectful.Expr.ExprSeq.eval
        model prim args state with
  | error err =>
      simp [hArgs] at hEval
  | ok result =>
      rcases result with ⟨afterArgs, inputValues⟩
      exact
        ⟨afterArgs, inputValues, rfl,
          by simpa [hArgs] using hEval⟩

theorem eval_outputs_length_of {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (hPrimitive :
      ∀ {op : Structured.BasicOp} {state final : σ}
        {values outputs : List Word},
        prim.eval op state values = .ok (final, outputs) →
          outputs.length =
            Expressions.Structured.BasicOp.outputs op)
    {results : Nat} {expr : Functions.Expr results}
    {state final : σ} {values : List Word}
    (hEval :
      eval model prim expr state =
        .ok (final, values)) :
    values.length = results := by
  cases expr with
  | lit value =>
      simp [eval, Locals.Source.Effectful.Expr.eval] at hEval
      rcases hEval with ⟨rfl, rfl⟩
      rfl
  | var name =>
      cases hLookup : model.vars state name with
      | none =>
          simp [eval, Locals.Source.Effectful.Expr.eval,
            hLookup, Functions.Source.invalid,
            Structured.invalid] at hEval
      | some value =>
          simp [eval, Locals.Source.Effectful.Expr.eval,
            hLookup] at hEval
          rcases hEval with ⟨rfl, rfl⟩
          rfl
  | code code =>
      simp [eval, Locals.Source.Effectful.Expr.eval,
        Functions.Source.invalid, Structured.invalid] at hEval
  | prim op args =>
      obtain ⟨afterArgs, inputValues, _hArgs, hOp⟩ :=
        eval_prim_ok_parts model prim hEval
      exact hPrimitive hOp

end Expr

namespace ArgList

theorem eval_nil_ok_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    {source final : σ} {values : List Word}
    (hEval :
      eval model prim [] source =
        .ok (final, values)) :
    final = source ∧ values = [] := by
  simp [eval] at hEval
  exact ⟨hEval.1.symm, hEval.2⟩

theorem eval_cons_ok_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    {head : Functions.Expr 1} {rest : List (Functions.Expr 1)}
    {source final : σ} {values : List Word}
    (hEval :
      eval model prim (head :: rest) source =
        .ok (final, values)) :
    ∃ afterHead value restValues,
      Expr.eval model prim head source =
        .ok (afterHead, [value]) ∧
      eval model prim rest afterHead =
        .ok (final, restValues) ∧
      values = value :: restValues := by
  unfold eval at hEval
  cases hHead :
      Expr.evalOne model prim head source with
  | error err =>
      simp [hHead] at hEval
  | ok result =>
      rcases result with ⟨afterHead, value⟩
      cases hRest : eval model prim rest afterHead with
      | error err =>
          simp [hHead, hRest] at hEval
      | ok result =>
          rcases result with ⟨afterRest, restValues⟩
          simp [hHead, hRest] at hEval
          rcases hEval with ⟨rfl, rfl⟩
          exact
            ⟨afterHead, value, restValues,
              Expr.eval_singleton_of_evalOne model prim hHead,
              hRest, rfl⟩

end ArgList

end Effectful
end Source
end Functions
end EvmCompiler
