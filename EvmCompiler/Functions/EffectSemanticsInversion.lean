import EvmCompiler.Functions.EffectSemantics

namespace EvmCompiler
namespace Functions
namespace Source
namespace Effectful

/-!
Successful-evaluation inversions owned by the Functions semantics boundary.
-/

namespace Expr

theorem eval_lit {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (value : Word) (state : σ) :
    eval model prim (.lit value : Functions.Expr 1) state =
      .ok (state, [value]) := by
  simp [eval, Locals.Source.Effectful.Expr.eval]

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

theorem eval_var_of_lookup {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    {name : Name} {state : σ} {value : Word}
    (hLookup : model.vars state name = some value) :
    eval model prim (.var name : Functions.Expr 1) state =
      .ok (state, [value]) := by
  simp [eval, Locals.Source.Effectful.Expr.eval, hLookup]

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

theorem evalCondition_ok_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    {expr : Functions.Expr 1} {state final : σ} {condition : Bool}
    (hEval :
      evalCondition model prim expr state =
        .ok (final, condition)) :
    ∃ value,
      eval model prim expr state =
        .ok (final, [value]) ∧
      condition = (value != EvmYul.UInt256.ofNat 0) := by
  unfold evalCondition at hEval
  unfold Locals.Source.Effectful.Expr.evalCondition at hEval
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
      | cons value rest =>
          cases rest with
          | nil =>
              simp [hExpr] at hEval
              rcases hEval with ⟨rfl, rfl⟩
              exact ⟨value, rfl, rfl⟩
          | cons second tail =>
              simp [hExpr, Functions.Source.invalid,
                Structured.invalid] at hEval

theorem evalCondition_false_ok_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    {expr : Functions.Expr 1} {state final : σ}
    (hEval :
      evalCondition model prim expr state =
        .ok (final, false)) :
    ∃ value,
      eval model prim expr state =
        .ok (final, [value]) ∧
      value = EvmYul.UInt256.ofNat 0 := by
  obtain ⟨value, hValue, hCondition⟩ :=
    evalCondition_ok_parts model prim hEval
  refine ⟨value, hValue, ?_⟩
  rcases value with ⟨value⟩
  have hBne := hCondition.symm
  change
    (!(value == Fin.ofNat EvmYul.UInt256.size 0)) = false
    at hBne
  have hValue : value = Fin.ofNat EvmYul.UInt256.size 0 := by
    simpa using hBne
  cases hValue
  rfl

theorem evalCondition_true_ok_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    {expr : Functions.Expr 1} {state final : σ}
    (hEval :
      evalCondition model prim expr state =
        .ok (final, true)) :
    ∃ value,
      eval model prim expr state =
        .ok (final, [value]) ∧
      value ≠ EvmYul.UInt256.ofNat 0 := by
  obtain ⟨value, hValue, hCondition⟩ :=
    evalCondition_ok_parts model prim hEval
  refine ⟨value, hValue, ?_⟩
  rcases value with ⟨value⟩
  have hBne := hCondition.symm
  change
    (!(value == Fin.ofNat EvmYul.UInt256.size 0)) = true
    at hBne
  have hValueNe : value ≠ Fin.ofNat EvmYul.UInt256.size 0 := by
    simpa using hBne
  intro hZero
  apply hValueNe
  have hVal := congrArg EvmYul.UInt256.val hZero
  simpa [EvmYul.UInt256.ofNat] using hVal

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

namespace Stmt

theorem run_expr_regular_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx finalCtx : Source.Ctx} {fuel : Nat}
    {expr : Functions.Expr 0}
    {source final : σ}
    (hRun :
      run model prim program ctx fuel (.expr expr) source =
        .ok (Outcome.regular final, finalCtx)) :
    ∃ values,
      Expr.eval model prim expr source =
        .ok (final, values) ∧
      finalCtx = ctx := by
  unfold run at hRun
  cases hEval : Expr.eval model prim expr source with
  | error err =>
      simp [hEval] at hRun
  | ok evaluated =>
      rcases evaluated with ⟨afterExpr, values⟩
      simp [hEval] at hRun
      rcases hRun with ⟨hFinal, hCtx⟩
      injection hFinal with hState
      subst final
      exact ⟨values, rfl, hCtx.symm⟩

theorem run_let_regular_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx finalCtx : Source.Ctx} {fuel : Nat}
    {name : Name} {value : Functions.Expr 1}
    {source final : σ}
    (hRun :
      run model prim program ctx fuel (.let_ name value) source =
        .ok (Outcome.regular final, finalCtx)) :
    ∃ afterValue result,
      Expr.eval model prim value source =
        .ok (afterValue, [result]) ∧
      final = model.insert afterValue name result ∧
      finalCtx = { ctx with scope := name :: ctx.scope } := by
  unfold run at hRun
  cases hEval : Expr.evalOne model prim value source with
  | error err =>
      simp [hEval] at hRun
  | ok evaluated =>
      rcases evaluated with ⟨afterValue, result⟩
      simp [hEval] at hRun
      rcases hRun with ⟨hFinal, hCtx⟩
      exact
        ⟨afterValue, result,
          Expr.eval_singleton_of_evalOne model prim hEval,
          by
            injection hFinal with hState
            exact hState.symm,
          hCtx.symm⟩

theorem run_assign_regular_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx finalCtx : Source.Ctx} {fuel : Nat}
    {name : Name} {value : Functions.Expr 1}
    {source final : σ}
    (hRun :
      run model prim program ctx fuel (.assign name value) source =
        .ok (Outcome.regular final, finalCtx)) :
    (model.vars source).contains name = true ∧
      ∃ afterValue result,
        Expr.eval model prim value source =
          .ok (afterValue, [result]) ∧
        final =
          model.withVars afterValue
            (Locals.Source.Store.insert
              (model.vars afterValue) name result) ∧
        finalCtx = ctx := by
  unfold run at hRun
  by_cases hContains : (model.vars source).contains name = true
  · simp only [hContains, ↓reduceIte] at hRun
    cases hEval : Expr.evalOne model prim value source with
    | error err =>
        simp [hEval] at hRun
    | ok evaluated =>
        rcases evaluated with ⟨afterValue, result⟩
        simp [hEval] at hRun
        rcases hRun with ⟨hFinal, hCtx⟩
        exact
          ⟨hContains, afterValue, result,
            Expr.eval_singleton_of_evalOne model prim hEval,
            by
              injection hFinal with hState
              exact hState.symm,
            hCtx.symm⟩
  · have hContainsFalse :
        (model.vars source).contains name = false := by
      exact Bool.eq_false_of_not_eq_true hContains
    simp [hContainsFalse, Functions.Source.invalid,
      Structured.invalid] at hRun

theorem run_if_ok_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx finalCtx : Source.Ctx} {fuel : Nat}
    {cond : Functions.Expr 1} {body : Functions.Block}
    {source : σ} {outcome : Outcome σ}
    (hRun :
      run model prim program ctx fuel (.if_ cond body) source =
        .ok (outcome, finalCtx)) :
    ∃ previous,
      fuel = previous + 1 ∧
      ((∃ afterCond,
          Expr.evalCondition model prim cond source =
            .ok (afterCond, false) ∧
          outcome = Outcome.regular afterCond ∧
          finalCtx = ctx) ∨
        (∃ afterCond bodyOutcome,
          Expr.evalCondition model prim cond source =
            .ok (afterCond, true) ∧
          Block.runScoped model prim program ctx body previous afterCond =
            .ok bodyOutcome ∧
          outcome = bodyOutcome ∧
          finalCtx = ctx)) := by
  cases fuel with
  | zero =>
      simp [run, Functions.Source.invalid, Structured.invalid] at hRun
  | succ previous =>
      refine ⟨previous, by omega, ?_⟩
      exact run_if_cases model prim program hRun

theorem run_switch_ok_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx finalCtx : Source.Ctx} {fuel : Nat}
    {scrutinee : Functions.Expr 1}
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block}
    {source : σ} {outcome : Outcome σ}
    (hRun :
      run model prim program ctx fuel
          (.switch scrutinee cases defaultBody) source =
        .ok (outcome, finalCtx)) :
    ∃ previous,
      fuel = previous + 1 ∧
      ((∃ afterScrutinee value,
          Expr.evalOne model prim scrutinee source =
            .ok (afterScrutinee, value) ∧
          Switch.select value cases defaultBody = none ∧
          outcome = Outcome.regular afterScrutinee ∧
          finalCtx = ctx) ∨
        (∃ afterScrutinee value selected bodyOutcome,
          Expr.evalOne model prim scrutinee source =
            .ok (afterScrutinee, value) ∧
          Switch.select value cases defaultBody = some selected ∧
          Block.runScoped model prim program ctx selected previous
              afterScrutinee =
            .ok bodyOutcome ∧
          outcome = bodyOutcome ∧
          finalCtx = ctx)) := by
  cases fuel with
  | zero =>
      simp [run, Functions.Source.invalid, Structured.invalid] at hRun
  | succ previous =>
      refine ⟨previous, by omega, ?_⟩
      exact run_switch_cases model prim program hRun

/--
Expose the canonical scoped-body execution represented by a successful
Functions `block` statement. The statement restores its incoming context for
every outcome mode.
-/
theorem run_block_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx finalCtx : Source.Ctx} {fuel : Nat}
    {body : Functions.Block} {source : σ} {outcome : Outcome σ}
    (hRun :
      run model prim program ctx fuel (.block body) source =
        .ok (outcome, finalCtx)) :
    Block.runScoped model prim program ctx body fuel source =
        .ok outcome ∧
      finalCtx = ctx := by
  unfold run at hRun
  cases hBody :
      Block.runScoped model prim program ctx body fuel source with
  | error err =>
      simp [hBody] at hRun
  | ok bodyOutcome =>
      simp [hBody] at hRun
      rcases hRun with ⟨hOutcome, hCtx⟩
      exact ⟨by simpa [hOutcome], hCtx.symm⟩

end Stmt

namespace Block

theorem runOpen_success_unique {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx leftCtx rightCtx : Source.Ctx}
    {leftFuel rightFuel : Nat} {block : Functions.Block}
    {source : σ} {leftOutcome rightOutcome : Outcome σ}
    (hLeft :
      runOpen model prim program ctx leftFuel block source =
        .ok (leftOutcome, leftCtx))
    (hRight :
      runOpen model prim program ctx rightFuel block source =
        .ok (rightOutcome, rightCtx)) :
    (leftOutcome, leftCtx) = (rightOutcome, rightCtx) := by
  let commonFuel := Nat.max leftFuel rightFuel
  have hLeft' :
      runOpen model prim program ctx commonFuel block source =
        .ok (leftOutcome, leftCtx) :=
    runOpen_mono model prim program (Nat.le_max_left _ _) hLeft
  have hRight' :
      runOpen model prim program ctx commonFuel block source =
        .ok (rightOutcome, rightCtx) :=
    runOpen_mono model prim program (Nat.le_max_right _ _) hRight
  rw [hLeft'] at hRight'
  exact Except.ok.inj hRight'

theorem runOpen_regular_unique {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx leftCtx rightCtx : Source.Ctx}
    {leftFuel rightFuel : Nat} {block : Functions.Block}
    {source leftFinal rightFinal : σ}
    (hLeft :
      runOpen model prim program ctx leftFuel block source =
        .ok (Outcome.regular leftFinal, leftCtx))
    (hRight :
      runOpen model prim program ctx rightFuel block source =
        .ok (Outcome.regular rightFinal, rightCtx)) :
    leftFinal = rightFinal ∧ leftCtx = rightCtx := by
  let commonFuel := Nat.max leftFuel rightFuel
  have hLeft' :
      runOpen model prim program ctx commonFuel block source =
        .ok (Outcome.regular leftFinal, leftCtx) :=
    runOpen_mono model prim program (Nat.le_max_left _ _) hLeft
  have hRight' :
      runOpen model prim program ctx commonFuel block source =
        .ok (Outcome.regular rightFinal, rightCtx) :=
    runOpen_mono model prim program (Nat.le_max_right _ _) hRight
  rw [hLeft'] at hRight'
  have hPair :
      (Outcome.regular leftFinal, leftCtx) =
        (Outcome.regular rightFinal, rightCtx) :=
    Except.ok.inj hRight'
  injection hPair with hOutcome hCtx
  injection hOutcome with hFinal
  exact ⟨hFinal, hCtx⟩

theorem runOpen_singleton_regular_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx finalCtx : Source.Ctx} {fuel : Nat}
    {stmt : Functions.Stmt} {source final : σ}
    (hRun :
      runOpen model prim program ctx fuel
          { stmts := [stmt] } source =
        .ok (Outcome.regular final, finalCtx)) :
    ∃ stmtFuel,
      Stmt.run model prim program ctx stmtFuel stmt source =
        .ok (Outcome.regular final, finalCtx) := by
  cases fuel with
  | zero =>
      simp [runOpen, Source.invalid, Structured.invalid] at hRun
  | succ stmtFuel =>
      rcases
          runOpen_cons_cases model prim program hRun with
        hRegular | hNonregular
      · rcases hRegular with
          ⟨middle, middleCtx, hStmt, hTail⟩
        obtain ⟨hOutcome, hCtx⟩ :=
          runOpen_nil_ok model prim program hTail
        injection hOutcome with hFinal
        subst middle
        subst middleCtx
        exact ⟨stmtFuel, hStmt⟩
      · rcases hNonregular with
          ⟨headOutcome, _headCtx, _hStmt, hMode,
            hOutcome, _hCtx⟩
        exfalso
        apply hMode
        rw [← hOutcome]
        rfl

/--
Invert a successful singleton block while retaining its exact one-step fuel
decrease. Higher-language recursive adequacy uses the bound without unfolding
the Functions block interpreter.
-/
theorem runOpen_singleton_regular_bounded_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx finalCtx : Source.Ctx} {fuel : Nat}
    {stmt : Functions.Stmt} {source final : σ}
    (hRun :
      runOpen model prim program ctx fuel
          { stmts := [stmt] } source =
        .ok (Outcome.regular final, finalCtx)) :
    ∃ stmtFuel,
      fuel = stmtFuel + 1 ∧
      Stmt.run model prim program ctx stmtFuel stmt source =
        .ok (Outcome.regular final, finalCtx) := by
  cases fuel with
  | zero =>
      simp [runOpen, Source.invalid, Structured.invalid] at hRun
  | succ stmtFuel =>
      rcases
          runOpen_cons_cases model prim program hRun with
        hRegular | hNonregular
      · rcases hRegular with
          ⟨middle, middleCtx, hStmt, hTail⟩
        obtain ⟨hOutcome, hCtx⟩ :=
          runOpen_nil_ok model prim program hTail
        injection hOutcome with hFinal
        subst middle
        subst middleCtx
        exact ⟨stmtFuel, by omega, hStmt⟩
      · rcases hNonregular with
          ⟨headOutcome, _headCtx, _hStmt, hMode,
            hOutcome, _hCtx⟩
        exfalso
        apply hMode
        rw [← hOutcome]
        rfl

/--
Invert an abrupt singleton block while retaining its exact one-step fuel
decrease. The enclosing open block restores its incoming context when the
statement does not complete regularly.
-/
theorem runOpen_singleton_nonregular_bounded_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx finalCtx : Source.Ctx} {fuel : Nat}
    {stmt : Functions.Stmt} {source : σ} {outcome : Outcome σ}
    (hRun :
      runOpen model prim program ctx fuel
          { stmts := [stmt] } source =
        .ok (outcome, finalCtx))
    (hMode : outcome.mode ≠ .regular) :
    ∃ stmtFuel stmtCtx,
      fuel = stmtFuel + 1 ∧
      Stmt.run model prim program ctx stmtFuel stmt source =
        .ok (outcome, stmtCtx) ∧
      finalCtx = ctx := by
  cases fuel with
  | zero =>
      simp [runOpen, Source.invalid, Structured.invalid] at hRun
  | succ stmtFuel =>
      rcases
          runOpen_cons_cases model prim program hRun with
        hRegular | hNonregular
      · rcases hRegular with
          ⟨middle, middleCtx, hStmt, hTail⟩
        obtain ⟨hOutcome, _hCtx⟩ :=
          runOpen_nil_ok model prim program hTail
        exfalso
        apply hMode
        rw [hOutcome]
        rfl
      · rcases hNonregular with
          ⟨headOutcome, headCtx, hStmt, _hHeadMode,
            hOutcome, hCtx⟩
        subst outcome
        exact ⟨stmtFuel, headCtx, by omega, hStmt, hCtx⟩

theorem runOpen_singleton_bounded_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx finalCtx : Source.Ctx} {fuel : Nat}
    {stmt : Functions.Stmt} {source : σ} {outcome : Outcome σ}
    (hRun :
      runOpen model prim program ctx fuel
          { stmts := [stmt] } source =
        .ok (outcome, finalCtx)) :
    ∃ stmtFuel stmtCtx,
      fuel = stmtFuel + 1 ∧
      Stmt.run model prim program ctx stmtFuel stmt source =
        .ok (outcome, stmtCtx) ∧
      (outcome.mode = .regular → finalCtx = stmtCtx) ∧
      (outcome.mode ≠ .regular → finalCtx = ctx) := by
  by_cases hRegular : outcome.mode = .regular
  · have hOutcomeEq :
        outcome = Outcome.regular outcome.state :=
      Outcome.eq_regular_of_mode hRegular
    have hRun' := hRun
    rw [hOutcomeEq] at hRun'
    obtain ⟨stmtFuel, hFuel, hStmt⟩ :=
      runOpen_singleton_regular_bounded_parts
        model prim program hRun'
    refine
      ⟨stmtFuel, finalCtx, hFuel, ?_, fun _ => rfl, ?_⟩
    · rw [hOutcomeEq]
      exact hStmt
    · intro hNonregular
      exact False.elim (hNonregular hRegular)
  · obtain ⟨stmtFuel, stmtCtx, hFuel, hStmt, hFinalCtx⟩ :=
      runOpen_singleton_nonregular_bounded_parts
        model prim program hRun hRegular
    exact
      ⟨stmtFuel, stmtCtx, hFuel, hStmt,
        fun h => False.elim (hRegular h), fun _ => hFinalCtx⟩

theorem runOpen_append_regular_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program) :
    ∀ {left right : List Functions.Stmt}
      {ctx finalCtx : Source.Ctx} {fuel : Nat}
      {source final : σ},
      runOpen model prim program ctx fuel
          { stmts := left ++ right } source =
        .ok (Outcome.regular final, finalCtx) →
      ∃ middle middleCtx,
        (∃ leftFuel,
          runOpen model prim program ctx leftFuel
              { stmts := left } source =
            .ok (Outcome.regular middle, middleCtx)) ∧
        (∃ rightFuel,
          runOpen model prim program middleCtx rightFuel
              { stmts := right } middle =
            .ok (Outcome.regular final, finalCtx)) := by
  intro left
  induction left with
  | nil =>
      intro right ctx finalCtx fuel source final hRun
      exact
        ⟨source, ctx,
          ⟨1, by simp [runOpen]⟩,
          ⟨fuel, by simpa using hRun⟩⟩
  | cons stmt rest ih =>
      intro right ctx finalCtx fuel source final hRun
      cases fuel with
      | zero =>
          simp [runOpen, Source.invalid, Structured.invalid] at hRun
      | succ fuel =>
          rcases
              runOpen_cons_cases model prim program hRun with
            hRegular | hNonregular
          · rcases hRegular with
              ⟨afterStmt, stmtCtx, hStmt, hTail⟩
            obtain
                ⟨middle, middleCtx, hRest, hRight⟩ :=
              ih hTail
            obtain ⟨restFuel, hRest⟩ := hRest
            obtain ⟨leftFuel, hLeft⟩ :=
              runOpen_cons_regular_exists model prim program
                hStmt hRest
            exact
              ⟨middle, middleCtx, ⟨leftFuel, hLeft⟩, hRight⟩
          · rcases hNonregular with
              ⟨headOutcome, _headCtx, _hHead, hMode,
                hOutcome, _hCtx⟩
            exfalso
            apply hMode
            rw [← hOutcome]
            rfl

/--
Split a successful regular block while retaining a target-fuel bound.

The left prefix can be rerun at the enclosing fuel. The right suffix is
exposed at a fuel no greater than the enclosing fuel, which is the measure
needed by higher-language backward adequacy proofs.
-/
theorem runOpen_append_regular_bounded_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program) :
    ∀ {left right : List Functions.Stmt}
      {ctx finalCtx : Source.Ctx} {fuel : Nat}
      {source final : σ},
      runOpen model prim program ctx fuel
          { stmts := left ++ right } source =
        .ok (Outcome.regular final, finalCtx) →
      ∃ middle middleCtx rightFuel,
        runOpen model prim program ctx fuel
            { stmts := left } source =
          .ok (Outcome.regular middle, middleCtx) ∧
        runOpen model prim program middleCtx rightFuel
            { stmts := right } middle =
          .ok (Outcome.regular final, finalCtx) ∧
        rightFuel ≤ fuel := by
  intro left
  induction left with
  | nil =>
      intro right ctx finalCtx fuel source final hRun
      cases fuel with
      | zero =>
          simp [runOpen, Source.invalid, Structured.invalid] at hRun
      | succ previous =>
          exact
            ⟨source, ctx, previous + 1,
              by simp [runOpen], by simpa using hRun, by omega⟩
  | cons stmt rest ih =>
      intro right ctx finalCtx fuel source final hRun
      cases fuel with
      | zero =>
          simp [runOpen, Source.invalid, Structured.invalid] at hRun
      | succ previous =>
          rcases
              runOpen_cons_cases model prim program hRun with
            hRegular | hNonregular
          · rcases hRegular with
              ⟨afterStmt, stmtCtx, hStmt, hTail⟩
            obtain
                ⟨middle, middleCtx, rightFuel,
                  hRest, hRight, hRightFuel⟩ :=
              ih hTail
            refine
              ⟨middle, middleCtx, rightFuel, ?_, hRight, by omega⟩
            simpa [runOpen, hStmt, hRest]
          · rcases hNonregular with
              ⟨headOutcome, _headCtx, _hHead, hMode,
                hOutcome, _hCtx⟩
            exfalso
            apply hMode
            rw [← hOutcome]
            rfl

/--
Split an arbitrary successful block run at an appended statement boundary.

Either the left prefix completes regularly and the right suffix realizes the
observed outcome at no more fuel than the enclosing run, or the left prefix
itself realizes that exact nonregular outcome. Higher-language adequacy proofs
can therefore recurse over statement lists without unfolding `runOpen`.
-/
theorem runOpen_append_bounded_cases {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program) :
    ∀ {left right : List Functions.Stmt}
      {ctx finalCtx : Source.Ctx} {fuel : Nat}
      {source : σ} {outcome : Outcome σ},
      runOpen model prim program ctx fuel
          { stmts := left ++ right } source =
        .ok (outcome, finalCtx) →
      (∃ middle middleCtx rightFuel,
          runOpen model prim program ctx fuel
              { stmts := left } source =
            .ok (Outcome.regular middle, middleCtx) ∧
          runOpen model prim program middleCtx rightFuel
              { stmts := right } middle =
            .ok (outcome, finalCtx) ∧
          rightFuel ≤ fuel) ∨
        (∃ leftOutcome leftCtx,
          runOpen model prim program ctx fuel
              { stmts := left } source =
            .ok (leftOutcome, leftCtx) ∧
          leftOutcome.mode ≠ .regular ∧
          outcome = leftOutcome ∧
          finalCtx = leftCtx) := by
  intro left
  induction left with
  | nil =>
      intro right ctx finalCtx fuel source outcome hRun
      cases fuel with
      | zero =>
          simp [runOpen, Source.invalid, Structured.invalid] at hRun
      | succ previous =>
          left
          exact
            ⟨source, ctx, previous + 1,
              by simp [runOpen], by simpa using hRun, by omega⟩
  | cons stmt rest ih =>
      intro right ctx finalCtx fuel source outcome hRun
      cases fuel with
      | zero =>
          simp [runOpen, Source.invalid, Structured.invalid] at hRun
      | succ previous =>
          rcases
              runOpen_cons_cases model prim program hRun with
            hHeadRegular | hHeadNonregular
          · rcases hHeadRegular with
              ⟨afterHead, headCtx, hHead, hTail⟩
            rcases ih hTail with hRestRegular | hRestNonregular
            · rcases hRestRegular with
                ⟨middle, middleCtx, rightFuel,
                  hRest, hRight, hRightFuel⟩
              left
              refine
                ⟨middle, middleCtx, rightFuel, ?_,
                  hRight, by omega⟩
              simpa [runOpen, hHead, hRest]
            · rcases hRestNonregular with
                ⟨leftOutcome, leftCtx, hRest, hMode,
                  hOutcome, hFinalCtx⟩
              right
              refine
                ⟨leftOutcome, leftCtx, ?_, hMode,
                  hOutcome, hFinalCtx⟩
              simpa [runOpen, hHead, hRest]
          · rcases hHeadNonregular with
              ⟨headOutcome, headCtx, hHead, hMode,
                hOutcome, hFinalCtx⟩
            right
            exact
              ⟨headOutcome, ctx,
                by
                  simpa [List.cons_append] using
                    runOpen_cons_nonregular model prim program
                      (rest := rest) hHead hMode,
                hMode, hOutcome, hFinalCtx⟩

theorem runOpen_append_two_regular_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    (program : Functions.Program) :
    ∀ {prefixStmts : List Functions.Stmt}
      {first second : Functions.Stmt}
      {ctx finalCtx : Source.Ctx} {fuel : Nat}
      {source final : σ},
      runOpen model prim program ctx fuel
          { stmts := prefixStmts ++ [first, second] } source =
        .ok (Outcome.regular final, finalCtx) →
      ∃ prefixFinal prefixCtx firstFinal firstCtx
          prefixFuel firstFuel secondFuel,
        runOpen model prim program ctx prefixFuel
            { stmts := prefixStmts } source =
          .ok (Outcome.regular prefixFinal, prefixCtx) ∧
        Stmt.run model prim program prefixCtx firstFuel first prefixFinal =
          .ok (Outcome.regular firstFinal, firstCtx) ∧
        Stmt.run model prim program firstCtx secondFuel second firstFinal =
          .ok (Outcome.regular final, finalCtx) ∧
        secondFuel + 2 ≤ fuel := by
  intro prefixStmts
  induction prefixStmts with
  | nil =>
      intro first second ctx finalCtx fuel source final hRun
      cases fuel with
      | zero =>
          simp [runOpen, Source.invalid, Structured.invalid] at hRun
      | succ firstFuel =>
          rcases
              runOpen_cons_cases model prim program hRun with
            hFirstRegular | hFirstNonregular
          · rcases hFirstRegular with
              ⟨firstFinal, firstCtx, hFirst, hSecondBlock⟩
            cases firstFuel with
            | zero =>
                simp [runOpen, Source.invalid, Structured.invalid]
                  at hSecondBlock
            | succ secondFuel =>
                rcases
                    runOpen_cons_cases model prim program hSecondBlock with
                  hSecondRegular | hSecondNonregular
                · rcases hSecondRegular with
                    ⟨secondFinal, secondCtx, hSecond, hEmpty⟩
                  obtain ⟨hOutcome, hCtx⟩ :=
                    runOpen_nil_ok model prim program hEmpty
                  injection hOutcome with hFinal
                  subst secondFinal
                  subst secondCtx
                  exact
                    ⟨source, ctx, firstFinal, firstCtx,
                      1, secondFuel + 1, secondFuel,
                      by simp [runOpen], hFirst, hSecond, by omega⟩
                · rcases hSecondNonregular with
                    ⟨headOutcome, _headCtx, _hSecond, hMode,
                      hOutcome, _hCtx⟩
                  exfalso
                  apply hMode
                  rw [← hOutcome]
                  rfl
          · rcases hFirstNonregular with
              ⟨headOutcome, _headCtx, _hFirst, hMode,
                hOutcome, _hCtx⟩
            exfalso
            apply hMode
            rw [← hOutcome]
            rfl
  | cons stmt rest ih =>
      intro first second ctx finalCtx fuel source final hRun
      cases fuel with
      | zero =>
          simp [runOpen, Source.invalid, Structured.invalid] at hRun
      | succ tailFuel =>
          rcases
              runOpen_cons_cases model prim program hRun with
            hHeadRegular | hHeadNonregular
          · rcases hHeadRegular with
              ⟨afterHead, headCtx, hHead, hTail⟩
            obtain
                ⟨prefixFinal, prefixCtx, firstFinal, firstCtx,
                  restFuel, firstFuel, secondFuel,
                  hRest, hFirst, hSecond, hBound⟩ :=
              ih hTail
            obtain ⟨prefixFuel, hPrefix⟩ :=
              runOpen_cons_regular_exists model prim program hHead hRest
            exact
              ⟨prefixFinal, prefixCtx, firstFinal, firstCtx,
                prefixFuel, firstFuel, secondFuel,
                hPrefix, hFirst, hSecond, by omega⟩
          · rcases hHeadNonregular with
              ⟨headOutcome, _headCtx, _hHead, hMode,
                hOutcome, _hCtx⟩
            exfalso
            apply hMode
            rw [← hOutcome]
            rfl

end Block

end Effectful
end Source
end Functions
end EvmCompiler
