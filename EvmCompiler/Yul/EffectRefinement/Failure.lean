import EvmCompiler.Yul.EffectRefinement

namespace EvmCompiler
namespace Yul
namespace Source
namespace Effectful

attribute [local simp] Bind.bind Except.bind

/-!
Observable-failure inversions for the canonical parameterized Yul semantics.

These theorems classify existing interpreter executions; they do not define a
second evaluator. Non-public failures such as fuel exhaustion and missing
lookup entries are eliminated by `Exception.Observable`.
-/

theorem evalArgs_observable_error_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {args : List EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state : σ} {failure : Failure σ}
    (hRun :
      evalArgs model prim fuel args codeOverride state =
        .error failure)
    (hObservable : Exception.Observable failure.exception) :
    ∃ previous head tail,
      fuel = previous + 1 ∧
      args = head :: tail ∧
      ((eval model prim previous head codeOverride state =
          .error failure) ∨
        ∃ tailFuel stateAfterHead value,
          previous = tailFuel + 1 ∧
          eval model prim previous head codeOverride state =
            .ok (stateAfterHead, value) ∧
          evalArgs model prim tailFuel tail codeOverride stateAfterHead =
            .error failure) := by
  cases fuel with
  | zero =>
      simp [evalArgs, fail] at hRun
      rw [← hRun] at hObservable
      simp [Exception.Observable] at hObservable
  | succ previous =>
      cases args with
      | nil =>
          simp [evalArgs] at hRun
      | cons head tail =>
          cases hHead :
              eval model prim previous head codeOverride state with
          | error headFailure =>
              simp [evalArgs, evalTail, hHead] at hRun
              subst failure
              exact
                ⟨previous, head, tail, rfl, rfl, Or.inl hHead⟩
          | ok headResult =>
              rcases headResult with ⟨stateAfterHead, value⟩
              cases previous with
              | zero =>
                  simp [evalArgs, evalTail, hHead, fail] at hRun
                  rw [← hRun] at hObservable
                  simp [Exception.Observable] at hObservable
              | succ tailFuel =>
                  cases hTail :
                      evalArgs model prim tailFuel tail
                        codeOverride stateAfterHead with
                  | error tailFailure =>
                      simp [evalArgs, evalTail, hHead, hTail] at hRun
                      subst failure
                      exact
                        ⟨tailFuel + 1, head, tail, rfl, rfl,
                          Or.inr
                            ⟨tailFuel, stateAfterHead, value,
                              rfl, hHead, hTail⟩⟩
                  | ok tailResult =>
                      simp [evalArgs, evalTail, hHead, hTail] at hRun

theorem evalArgs_singleton_observable_error_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {expr : EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state : σ} {failure : Failure σ}
    (hRun :
      evalArgs model prim fuel [expr] codeOverride state =
        .error failure)
    (hObservable : Exception.Observable failure.exception) :
    ∃ evalFuel,
      fuel = evalFuel + 1 ∧
      eval model prim evalFuel expr codeOverride state =
        .error failure := by
  obtain
      ⟨previous, head, tail, hFuel, hArgs,
        hFailureCase⟩ :=
    evalArgs_observable_error_parts
      model prim hRun hObservable
  injection hArgs with hHead hTail
  subst head
  rcases hFailureCase with hHeadFailure | hTailFailure
  · exact ⟨previous, hFuel, hHeadFailure⟩
  · rcases hTailFailure with
      ⟨tailFuel, stateAfterHead, value,
        _hPrevious, _hHead, hTailRun⟩
    rw [← hTail] at hTailRun
    cases tailFuel with
    | zero =>
        simp [evalArgs, fail] at hTailRun
        rw [← hTailRun] at hObservable
        simp [Exception.Observable] at hObservable
    | succ previous =>
        simp [evalArgs] at hTailRun

theorem eval_observable_error
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {expr : EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state : σ} {failure : Failure σ}
    (hRun :
      eval model prim fuel expr codeOverride state =
        .error failure) :
    evalValues model prim fuel expr codeOverride state =
      .error failure := by
  unfold eval at hRun
  cases hValues :
      evalValues model prim fuel expr codeOverride state with
  | error valuesFailure =>
      simp [hValues] at hRun
      subst failure
      rfl
  | ok result =>
      simp [hValues] at hRun

theorem evalValues_primitive_observable_error_parts
    {σ : Type} (model : StateModel σ)
    (primSemantics : PrimitiveSemantics σ)
    {fuel : Nat} {prim : EvmYul.Operation .Yul}
    {args : List EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state : σ} {failure : Failure σ}
    (hRun :
      evalValues model primSemantics fuel
          (.Call (.inl prim) args) codeOverride state =
        .error failure)
    (hObservable : Exception.Observable failure.exception) :
    ∃ callFuel,
      fuel = callFuel + 1 ∧
      ((evalArgs model primSemantics callFuel args.reverse
            codeOverride state =
          .error failure) ∨
        ∃ stateAfterArgs reversedValues,
          evalArgs model primSemantics callFuel args.reverse
              codeOverride state =
            .ok (stateAfterArgs, reversedValues) ∧
          primSemantics.eval callFuel stateAfterArgs prim
              reversedValues.reverse =
            .error failure) := by
  cases fuel with
  | zero =>
      simp [evalValues, fail] at hRun
      rw [← hRun] at hObservable
      simp [Exception.Observable] at hObservable
  | succ callFuel =>
      cases hArgs :
          evalArgs model primSemantics callFuel args.reverse
            codeOverride state with
      | error argsFailure =>
          simp [evalValues, hArgs] at hRun
          subst failure
          exact ⟨callFuel, rfl, Or.inl hArgs⟩
      | ok argsResult =>
          rcases argsResult with ⟨stateAfterArgs, reversedValues⟩
          cases hPrim :
              primSemantics.eval callFuel stateAfterArgs prim
                reversedValues.reverse with
          | error primFailure =>
              simp [evalValues, hArgs, hPrim] at hRun
              subst failure
              exact
                ⟨callFuel, rfl, Or.inr
                  ⟨stateAfterArgs, reversedValues, hArgs, hPrim⟩⟩
          | ok result =>
              simp [evalValues, hArgs, hPrim] at hRun

theorem evalValues_function_observable_error_parts
    {σ : Type} (model : StateModel σ)
    (primSemantics : PrimitiveSemantics σ)
    {fuel : Nat}
    {functionName : EvmYul.Yul.Ast.YulFunctionName}
    {args : List EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state : σ} {failure : Failure σ}
    (hRun :
      evalValues model primSemantics fuel
          (.Call (.inr functionName) args) codeOverride state =
        .error failure)
    (hObservable : Exception.Observable failure.exception) :
    ∃ callFuel,
      fuel = callFuel + 1 ∧
      ((evalArgs model primSemantics callFuel args.reverse
            codeOverride state =
          .error failure) ∨
        ∃ stateAfterArgs reversedValues,
          evalArgs model primSemantics callFuel args.reverse
              codeOverride state =
            .ok (stateAfterArgs, reversedValues) ∧
          call model primSemantics callFuel reversedValues.reverse
              (some functionName) codeOverride stateAfterArgs =
            .error failure) := by
  cases fuel with
  | zero =>
      simp [evalValues, fail] at hRun
      rw [← hRun] at hObservable
      simp [Exception.Observable] at hObservable
  | succ callFuel =>
      cases hArgs :
          evalArgs model primSemantics callFuel args.reverse
            codeOverride state with
      | error argsFailure =>
          simp [evalValues, hArgs] at hRun
          subst failure
          exact ⟨callFuel, rfl, Or.inl hArgs⟩
      | ok argsResult =>
          rcases argsResult with ⟨stateAfterArgs, reversedValues⟩
          cases hCall :
              call model primSemantics callFuel reversedValues.reverse
                (some functionName) codeOverride stateAfterArgs with
          | error callFailure =>
              simp [evalValues, hArgs, hCall] at hRun
              subst failure
              exact
                ⟨callFuel, rfl, Or.inr
                  ⟨stateAfterArgs, reversedValues, hArgs, hCall⟩⟩
          | ok result =>
              simp [evalValues, hArgs, hCall] at hRun

theorem exec_expr_function_observable_error_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat}
    {functionName : EvmYul.Yul.Ast.YulFunctionName}
    {args : List EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state : σ} {failure : Failure σ}
    (hRun :
      exec model prim fuel
          (.ExprStmtCall (.Call (.inr functionName) args))
          codeOverride state =
        .error failure)
    (hObservable : Exception.Observable failure.exception) :
    ∃ argsFuel,
      fuel = argsFuel + 1 ∧
      ((evalArgs model prim argsFuel args.reverse
            codeOverride state =
          .error failure) ∨
        ∃ callFuel stateAfterArgs reversedValues,
          argsFuel = callFuel + 1 ∧
          evalArgs model prim argsFuel args.reverse
              codeOverride state =
            .ok (stateAfterArgs, reversedValues) ∧
          call model prim callFuel reversedValues.reverse
              (some functionName) codeOverride stateAfterArgs =
            .error failure) := by
  cases fuel with
  | zero =>
      simp [exec, fail] at hRun
      rw [← hRun] at hObservable
      simp [Exception.Observable] at hObservable
  | succ argsFuel =>
      cases hArgs :
          evalArgs model prim argsFuel args.reverse
            codeOverride state with
      | error argsFailure =>
          simp [exec, hArgs] at hRun
          subst failure
          exact ⟨argsFuel, rfl, Or.inl hArgs⟩
      | ok argsResult =>
          rcases argsResult with ⟨stateAfterArgs, reversedValues⟩
          cases argsFuel with
          | zero =>
              simp [exec, hArgs, fail] at hRun
              rw [← hRun] at hObservable
              simp [Exception.Observable] at hObservable
          | succ callFuel =>
              cases hCall :
                  call model prim callFuel reversedValues.reverse
                    (some functionName) codeOverride stateAfterArgs with
              | error callFailure =>
                  simp [exec, hArgs, hCall, multifill] at hRun
                  subst failure
                  exact
                    ⟨callFuel + 1, rfl, Or.inr
                      ⟨callFuel, stateAfterArgs, reversedValues,
                        rfl, hArgs, hCall⟩⟩
              | ok callResult =>
                  simp [exec, hArgs, hCall, multifill] at hRun

theorem call_observable_error_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {args : List Word}
    {functionName? : Option EvmYul.Yul.Ast.YulFunctionName}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state : σ} {failure : Failure σ}
    (hRun :
      call model prim fuel args functionName?
          codeOverride state =
        .error failure)
    (hObservable : Exception.Observable failure.exception) :
    ∃ previous code params returns body,
      fuel = previous + 1 ∧
      resolveActiveCode? (model.source state) codeOverride = some code ∧
      (match functionName? with
        | none =>
            some
              (EvmYul.Yul.Ast.FunctionDefinition.Def [] []
                [code.dispatcher])
        | some functionName =>
            code.functions.lookup functionName) =
        some
          (EvmYul.Yul.Ast.FunctionDefinition.Def
            params returns body) ∧
      exec model prim previous (.Block body) codeOverride
          (model.withSource state
            (EvmYul.Yul.State.mkOk
              ((model.source state).initcall
                params returns args))) =
        .error failure := by
  cases fuel with
  | zero =>
      simp [call, fail] at hRun
      rw [← hRun] at hObservable
      simp [Exception.Observable] at hObservable
  | succ previous =>
      cases hCode :
          resolveActiveCode? (model.source state) codeOverride with
      | none =>
          simp [call, hCode, fail] at hRun
          rw [← hRun] at hObservable
          simp [Exception.Observable] at hObservable
      | some code =>
          cases functionName? with
          | none =>
              cases hBody :
                  exec model prim previous
                    (.Block [code.dispatcher])
                    codeOverride
                    (model.withSource state
                      (EvmYul.Yul.State.mkOk
                        ((model.source state).initcall [] [] args))) with
              | error bodyFailure =>
                  simp [call, hCode, hBody] at hRun
                  subst failure
                  exact
                    ⟨previous, code, [], [], [code.dispatcher],
                      rfl, rfl, rfl, hBody⟩
              | ok stateAfterBody =>
                  simp [call, hCode, hBody] at hRun
          | some functionName =>
              cases hFunction :
                  code.functions.lookup functionName with
              | none =>
                  simp [call, hCode, hFunction, fail] at hRun
                  rw [← hRun] at hObservable
                  simp [Exception.Observable] at hObservable
              | some fn =>
                  cases fn with
                  | Def params returns body =>
                      cases hBody :
                          exec model prim previous (.Block body)
                            codeOverride
                            (model.withSource state
                              (EvmYul.Yul.State.mkOk
                                ((model.source state).initcall
                                  params returns args))) with
                      | error bodyFailure =>
                          simp [call, hCode, hFunction, hBody] at hRun
                          subst failure
                          exact
                            ⟨previous, code, params, returns, body,
                              rfl, rfl, hFunction, hBody⟩
                      | ok stateAfterBody =>
                          simp [call, hCode, hFunction, hBody] at hRun

theorem callDispatcher_observable_error_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state : σ} {failure : Failure σ}
    (hRun :
      callDispatcher model prim fuel codeOverride state =
        .error failure)
    (hObservable : Exception.Observable failure.exception) :
    ∃ previous,
      fuel = previous + 1 ∧
      exec model prim previous
          (.Block [(model.source state).executionEnv.code.dispatcher])
          codeOverride
          (model.withSource state
            (EvmYul.Yul.State.mkOk
              ((model.source state).initcall [] [] []))) =
        .error failure := by
  cases fuel with
  | zero =>
      simp [callDispatcher, fail] at hRun
      rw [← hRun] at hObservable
      simp [Exception.Observable] at hObservable
  | succ previous =>
      cases hBody :
          exec model prim previous
            (.Block [(model.source state).executionEnv.code.dispatcher])
            codeOverride
            (model.withSource state
              (EvmYul.Yul.State.mkOk
                ((model.source state).initcall [] [] []))) with
      | error bodyFailure =>
          simp [callDispatcher, hBody] at hRun
          subst failure
          exact ⟨previous, rfl, hBody⟩
      | ok stateAfterBody =>
          simp [callDispatcher, hBody] at hRun

theorem exec_expr_primitive_observable_error_evalValues
    {σ : Type} (model : StateModel σ)
    (primSemantics : PrimitiveSemantics σ)
    {fuel : Nat} {prim : EvmYul.Operation .Yul}
    {args : List EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state : σ} {failure : Failure σ}
    (hRun :
      exec model primSemantics fuel
          (.ExprStmtCall (.Call (.inl prim) args))
          codeOverride state =
        .error failure)
    (hObservable : Exception.Observable failure.exception) :
    evalValues model primSemantics fuel
        (.Call (.inl prim) args) codeOverride state =
      .error failure := by
  rcases
      exec_expr_primitive_error_parts
        model primSemantics hRun with hOuter | hPrevious
  · rcases hOuter with ⟨rfl, hFailure⟩
    rw [← hFailure] at hObservable
    simp [Exception.Observable] at hObservable
  · rcases hPrevious with
      ⟨previous, hFuel, hArgsFailure | hPrimitiveFailure⟩
    · subst fuel
      simp [evalValues, hArgsFailure]
    · rcases hPrimitiveFailure with
        ⟨stateAfterArgs, reversedValues, hArgsRun, hPrimRun⟩
      subst fuel
      simp [evalValues, hArgsRun, hPrimRun]

theorem exec_let_some_observable_error_evalValues
    {σ : Type} (model : StateModel σ)
    (primSemantics : PrimitiveSemantics σ)
    {fuel : Nat} {names : List EvmYul.Identifier}
    {expr : EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state : σ} {failure : Failure σ}
    (hCheck :
      EvmYul.Yul.checkDeclaration (model.source state) names = .ok ())
    (hRun :
      exec model primSemantics fuel (.Let names (some expr))
          codeOverride state =
        .error failure)
    (hObservable : Exception.Observable failure.exception) :
    ∃ previous,
      fuel = previous + 1 ∧
      evalValues model primSemantics previous expr codeOverride state =
        .error failure := by
  cases fuel with
  | zero =>
      simp [exec, fail] at hRun
      rw [← hRun] at hObservable
      simp [Exception.Observable] at hObservable
  | succ previous =>
      cases hEval :
          evalValues model primSemantics previous expr
            codeOverride state with
      | error evalFailure =>
          simp [exec, hCheck, multifill, hEval] at hRun
          subst failure
          exact ⟨previous, rfl, hEval⟩
      | ok result =>
          simp [exec, hCheck, multifill, hEval] at hRun

theorem exec_assign_observable_error_evalValues
    {σ : Type} (model : StateModel σ)
    (primSemantics : PrimitiveSemantics σ)
    {fuel : Nat} {names : List EvmYul.Identifier}
    {expr : EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state : σ} {failure : Failure σ}
    (hCheck :
      EvmYul.Yul.checkAssignment (model.source state) names = .ok ())
    (hRun :
      exec model primSemantics fuel (.Assign names expr)
          codeOverride state =
        .error failure)
    (hObservable : Exception.Observable failure.exception) :
    ∃ previous,
      fuel = previous + 1 ∧
      evalValues model primSemantics previous expr codeOverride state =
        .error failure := by
  cases fuel with
  | zero =>
      simp [exec, fail] at hRun
      rw [← hRun] at hObservable
      simp [Exception.Observable] at hObservable
  | succ previous =>
      cases hEval :
          evalValues model primSemantics previous expr
            codeOverride state with
      | error evalFailure =>
          simp [exec, hCheck, multifill, hEval] at hRun
          subst failure
          exact ⟨previous, rfl, hEval⟩
      | ok result =>
          simp [exec, hCheck, multifill, hEval] at hRun

theorem exec_let_none_observable_error_false
    {σ : Type} (model : StateModel σ)
    (primSemantics : PrimitiveSemantics σ)
    {fuel : Nat} {names : List EvmYul.Identifier}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state : σ} {failure : Failure σ}
    (hCheck :
      EvmYul.Yul.checkDeclaration (model.source state) names = .ok ())
    (hRun :
      exec model primSemantics fuel (.Let names none)
          codeOverride state =
        .error failure)
    (hObservable : Exception.Observable failure.exception) :
    False := by
  cases fuel with
  | zero =>
      simp [exec, fail] at hRun
      rw [← hRun] at hObservable
      simp [Exception.Observable] at hObservable
  | succ previous =>
      simp [exec, hCheck] at hRun

theorem exec_continue_observable_error_false
    {σ : Type} (model : StateModel σ)
    (primSemantics : PrimitiveSemantics σ)
    {fuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state : σ} {failure : Failure σ}
    (hRun :
      exec model primSemantics fuel .Continue codeOverride state =
        .error failure)
    (hObservable : Exception.Observable failure.exception) :
    False := by
  cases fuel with
  | zero =>
      simp [exec, fail] at hRun
      rw [← hRun] at hObservable
      simp [Exception.Observable] at hObservable
  | succ previous =>
      simp [exec] at hRun

theorem exec_break_observable_error_false
    {σ : Type} (model : StateModel σ)
    (primSemantics : PrimitiveSemantics σ)
    {fuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state : σ} {failure : Failure σ}
    (hRun :
      exec model primSemantics fuel .Break codeOverride state =
        .error failure)
    (hObservable : Exception.Observable failure.exception) :
    False := by
  cases fuel with
  | zero =>
      simp [exec, fail] at hRun
      rw [← hRun] at hObservable
      simp [Exception.Observable] at hObservable
  | succ previous =>
      simp [exec] at hRun

theorem exec_leave_observable_error_false
    {σ : Type} (model : StateModel σ)
    (primSemantics : PrimitiveSemantics σ)
    {fuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state : σ} {failure : Failure σ}
    (hRun :
      exec model primSemantics fuel .Leave codeOverride state =
        .error failure)
    (hObservable : Exception.Observable failure.exception) :
    False := by
  cases fuel with
  | zero =>
      simp [exec, fail] at hRun
      rw [← hRun] at hObservable
      simp [Exception.Observable] at hObservable
  | succ previous =>
      simp [exec] at hRun

theorem exec_if_observable_error_parts
    {σ : Type} (model : StateModel σ)
    (primSemantics : PrimitiveSemantics σ)
    {fuel : Nat} {cond : EvmYul.Yul.Ast.Expr}
    {body : List EvmYul.Yul.Ast.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state : σ} {failure : Failure σ}
    (hRun :
      exec model primSemantics fuel (.If cond body)
          codeOverride state =
        .error failure)
    (hObservable : Exception.Observable failure.exception) :
    ∃ previous,
      fuel = previous + 1 ∧
      ((eval model primSemantics previous cond codeOverride state =
          .error failure) ∨
        ∃ stateAfterCond condValue,
          eval model primSemantics previous cond codeOverride state =
            .ok (stateAfterCond, condValue) ∧
          condValue ≠ ⟨0⟩ ∧
          exec model primSemantics previous (.Block body)
              codeOverride stateAfterCond =
            .error failure) := by
  cases fuel with
  | zero =>
      simp [exec, fail] at hRun
      rw [← hRun] at hObservable
      simp [Exception.Observable] at hObservable
  | succ previous =>
      cases hCond :
          eval model primSemantics previous cond codeOverride state with
      | error condFailure =>
          simp [exec, hCond] at hRun
          subst failure
          exact ⟨previous, rfl, Or.inl hCond⟩
      | ok condResult =>
          rcases condResult with ⟨stateAfterCond, condValue⟩
          by_cases hNonzero : condValue ≠ ⟨0⟩
          · cases hBody :
                exec model primSemantics previous (.Block body)
                  codeOverride stateAfterCond with
            | error bodyFailure =>
                simp [exec, hCond, hNonzero, hBody] at hRun
                subst failure
                exact
                  ⟨previous, rfl, Or.inr
                    ⟨stateAfterCond, condValue,
                      hCond, hNonzero, hBody⟩⟩
            | ok stateAfterBody =>
                simp [exec, hCond, hNonzero, hBody] at hRun
          · have hZero :
                condValue = ⟨0⟩ :=
              Decidable.not_not.mp hNonzero
            simp [exec, hCond, hZero] at hRun

theorem exec_switch_observable_error_parts
    {σ : Type} (model : StateModel σ)
    (primSemantics : PrimitiveSemantics σ)
    {fuel : Nat} {cond : EvmYul.Yul.Ast.Expr}
    {cases : List (Word × List EvmYul.Yul.Ast.Stmt)}
    {defaultBody : List EvmYul.Yul.Ast.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state : σ} {failure : Failure σ}
    (hRun :
      exec model primSemantics fuel
          (.Switch cond cases defaultBody)
          codeOverride state =
        .error failure)
    (hObservable : Exception.Observable failure.exception) :
    ∃ previous,
      fuel = previous + 1 ∧
      ((eval model primSemantics previous cond codeOverride state =
          .error failure) ∨
        ∃ stateAfterCond condValue,
          eval model primSemantics previous cond codeOverride state =
            .ok (stateAfterCond, condValue) ∧
          exec model primSemantics previous
              (.Block
                (EvmYul.Yul.selectSwitchCase
                  condValue defaultBody cases))
              codeOverride stateAfterCond =
            .error failure) := by
  cases fuel with
  | zero =>
      simp [exec, fail] at hRun
      rw [← hRun] at hObservable
      simp [Exception.Observable] at hObservable
  | succ previous =>
      cases hCond :
          eval model primSemantics previous cond codeOverride state with
      | error condFailure =>
          simp [exec, hCond] at hRun
          subst failure
          exact ⟨previous, rfl, Or.inl hCond⟩
      | ok condResult =>
          rcases condResult with ⟨stateAfterCond, condValue⟩
          cases hBody :
              exec model primSemantics previous
                (.Block
                  (EvmYul.Yul.selectSwitchCase
                    condValue defaultBody cases))
                codeOverride stateAfterCond with
          | error bodyFailure =>
              simp [exec, hCond, hBody] at hRun
              subst failure
              exact
                ⟨previous, rfl, Or.inr
                  ⟨stateAfterCond, condValue, hCond, hBody⟩⟩
          | ok stateAfterBody =>
              simp [exec, hCond, hBody] at hRun

theorem exec_block_nil_observable_error_false
    {σ : Type} (model : StateModel σ)
    (primSemantics : PrimitiveSemantics σ)
    {fuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state : σ} {failure : Failure σ}
    (hRun :
      exec model primSemantics fuel (.Block [])
          codeOverride state =
        .error failure)
    (hObservable : Exception.Observable failure.exception) :
    False := by
  cases fuel with
  | zero =>
      simp [exec, fail] at hRun
      rw [← hRun] at hObservable
      simp [Exception.Observable] at hObservable
  | succ previous =>
      cases previous with
      | zero =>
          simp [exec, execSeq, fail] at hRun
          rw [← hRun] at hObservable
          simp [Exception.Observable] at hObservable
      | succ rest =>
          simp [exec, execSeq] at hRun

inductive LoopObservableErrorCase
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (fuel : Nat)
    (cond : EvmYul.Yul.Ast.Expr)
    (post body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (outer : EvmYul.Yul.State)
    (afterCond : σ) (condValue : Word) (failure : Failure σ) : Prop where
  | body
      (hNonzero : condValue ≠ EvmYul.UInt256.ofNat 0)
      (hBody :
        exec model prim fuel (.Block body) codeOverride afterCond =
          .error failure) :
      LoopObservableErrorCase model prim fuel cond post body codeOverride
        outer afterCond condValue failure
  | post
      (hNonzero : condValue ≠ EvmYul.UInt256.ofNat 0)
      {afterBody : σ}
      (hBody :
        exec model prim fuel (.Block body) codeOverride afterCond =
          .ok afterBody)
      (hBodyContinues : LoopBodyContinues (model.source afterBody))
      (hPost :
        exec model prim fuel (.Block post) codeOverride
            (model.withSource afterBody
              (model.source afterBody).reviveJump) =
          .error failure) :
      LoopObservableErrorCase model prim fuel cond post body codeOverride
        outer afterCond condValue failure
  | recurse
      (hNonzero : condValue ≠ EvmYul.UInt256.ofNat 0)
      {afterBody afterPost : σ}
      (hBody :
        exec model prim fuel (.Block body) codeOverride afterCond =
          .ok afterBody)
      (hBodyContinues : LoopBodyContinues (model.source afterBody))
      (hPost :
        exec model prim fuel (.Block post) codeOverride
            (model.withSource afterBody
              (model.source afterBody).reviveJump) =
          .ok afterPost)
      (hPostRecurs : LoopPostRecurs (model.source afterPost))
      (hLoop :
        exec model prim fuel (.For cond post body) codeOverride
            (model.withSource afterPost
              ((model.source afterPost).overwrite? outer)) =
          .error failure) :
      LoopObservableErrorCase model prim fuel cond post body codeOverride
        outer afterCond condValue failure

theorem loop_observable_error_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {cond : EvmYul.Yul.Ast.Expr}
    {post body : List EvmYul.Yul.Ast.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state : σ} {failure : Failure σ}
    (hRun :
      loop model prim fuel cond post body codeOverride state =
        .error failure)
    (hObservable : Exception.Observable failure.exception) :
    ∃ previous,
      fuel = previous + 2 ∧
      ((eval model prim previous cond codeOverride
          (model.withSource state
            (EvmYul.Yul.State.mkOk (model.source state))) =
          .error failure) ∨
        ∃ afterCond condValue,
          eval model prim previous cond codeOverride
              (model.withSource state
                (EvmYul.Yul.State.mkOk (model.source state))) =
            .ok (afterCond, condValue) ∧
          LoopObservableErrorCase model prim previous cond post body
            codeOverride (model.source state) afterCond condValue failure) := by
  cases fuel with
  | zero =>
      simp [loop, fail] at hRun
      rw [← hRun] at hObservable
      simp [Exception.Observable] at hObservable
  | succ first =>
      cases first with
      | zero =>
          simp [loop, fail] at hRun
          rw [← hRun] at hObservable
          simp [Exception.Observable] at hObservable
      | succ previous =>
          cases hCond :
              eval model prim previous cond codeOverride
                (model.withSource state
                  (EvmYul.Yul.State.mkOk (model.source state))) with
          | error condFailure =>
              simp [loop, hCond] at hRun
              subst failure
              exact ⟨previous, by omega, Or.inl hCond⟩
          | ok condResult =>
              rcases condResult with ⟨afterCond, condValue⟩
              by_cases hZero :
                  condValue = EvmYul.UInt256.ofNat 0
              · have hZeroLit : condValue = ⟨0⟩ := by
                  simpa using hZero
                simp [loop, hCond, hZeroLit] at hRun
              · have hNonzeroLit : condValue ≠ ⟨0⟩ := by
                  simpa using hZero
                cases hBody :
                    exec model prim previous (.Block body) codeOverride
                      afterCond with
                | error bodyFailure =>
                    simp [loop, hCond, hNonzeroLit, hBody] at hRun
                    subst failure
                    exact
                      ⟨previous, by omega, Or.inr
                        ⟨afterCond, condValue, hCond,
                          .body hZero hBody⟩⟩
                | ok afterBody =>
                    simp only [loop, hCond, if_neg hNonzeroLit, hBody,
                      Bind.bind, Except.bind] at hRun
                    cases hBodySource : model.source afterBody with
                    | OutOfFuel =>
                        rw [hBodySource] at hRun
                        contradiction
                    | Checkpoint jump =>
                        cases jump with
                        | Break shared store =>
                            rw [hBodySource] at hRun
                            contradiction
                        | Leave shared store =>
                            rw [hBodySource] at hRun
                            contradiction
                        | Continue shared store =>
                            rw [hBodySource] at hRun
                            simp only at hRun
                            cases hPost :
                                exec model prim previous (.Block post)
                                  codeOverride
                                  (model.withSource afterBody
                                    (model.source afterBody).reviveJump) with
                            | error postFailure =>
                                have hPost' := hPost
                                simp only [hBodySource] at hPost'
                                rw [hPost'] at hRun
                                have hFailure :
                                    postFailure = failure :=
                                  Except.error.inj hRun
                                subst failure
                                exact
                                  ⟨previous, by omega, Or.inr
                                    ⟨afterCond, condValue, hCond,
                                      .post hZero hBody
                                        (by simp [LoopBodyContinues,
                                          hBodySource])
                                        hPost⟩⟩
                            | ok afterPost =>
                                have hPost' := hPost
                                simp only [hBodySource] at hPost'
                                rw [hPost'] at hRun
                                simp only at hRun
                                cases hPostSource :
                                    model.source afterPost with
                                | OutOfFuel =>
                                    rw [hPostSource] at hRun
                                    contradiction
                                | Checkpoint postJump =>
                                    cases postJump with
                                    | Leave postShared postStore =>
                                        rw [hPostSource] at hRun
                                        contradiction
                                    | Continue postShared postStore =>
                                        rw [hPostSource] at hRun
                                        simp only at hRun
                                        cases hLoop :
                                            exec model prim previous
                                              (.For cond post body)
                                              codeOverride
                                              (model.withSource afterPost
                                                ((model.source afterPost).overwrite?
                                                  (model.source state))) with
                                        | error loopFailure =>
                                            have hLoop' := hLoop
                                            simp only [hPostSource] at hLoop'
                                            rw [hLoop'] at hRun
                                            have hFailure :
                                                loopFailure = failure :=
                                              Except.error.inj hRun
                                            subst failure
                                            exact
                                              ⟨previous, by omega, Or.inr
                                                ⟨afterCond, condValue, hCond,
                                                  .recurse hZero hBody
                                                    (by simp
                                                      [LoopBodyContinues,
                                                        hBodySource])
                                                    hPost
                                                    (by simp [LoopPostRecurs,
                                                      hPostSource])
                                                    hLoop⟩⟩
                                        | ok afterLoop =>
                                            have hLoop' := hLoop
                                            simp only [hPostSource] at hLoop'
                                            rw [hLoop'] at hRun
                                            contradiction
                                    | Break postShared postStore =>
                                        rw [hPostSource] at hRun
                                        simp only at hRun
                                        cases hLoop :
                                            exec model prim previous
                                              (.For cond post body)
                                              codeOverride
                                              (model.withSource afterPost
                                                ((model.source afterPost).overwrite?
                                                  (model.source state))) with
                                        | error loopFailure =>
                                            have hLoop' := hLoop
                                            simp only [hPostSource] at hLoop'
                                            rw [hLoop'] at hRun
                                            have hFailure :
                                                loopFailure = failure :=
                                              Except.error.inj hRun
                                            subst failure
                                            exact
                                              ⟨previous, by omega, Or.inr
                                                ⟨afterCond, condValue, hCond,
                                                  .recurse hZero hBody
                                                    (by simp
                                                      [LoopBodyContinues,
                                                        hBodySource])
                                                    hPost
                                                    (by simp [LoopPostRecurs,
                                                      hPostSource])
                                                    hLoop⟩⟩
                                        | ok afterLoop =>
                                            have hLoop' := hLoop
                                            simp only [hPostSource] at hLoop'
                                            rw [hLoop'] at hRun
                                            contradiction
                                | Ok postShared postStore =>
                                    rw [hPostSource] at hRun
                                    simp only at hRun
                                    cases hLoop :
                                        exec model prim previous
                                          (.For cond post body) codeOverride
                                          (model.withSource afterPost
                                            ((model.source afterPost).overwrite?
                                              (model.source state))) with
                                    | error loopFailure =>
                                        have hLoop' := hLoop
                                        simp only [hPostSource] at hLoop'
                                        rw [hLoop'] at hRun
                                        have hFailure :
                                            loopFailure = failure :=
                                          Except.error.inj hRun
                                        subst failure
                                        exact
                                          ⟨previous, by omega, Or.inr
                                            ⟨afterCond, condValue, hCond,
                                              .recurse hZero hBody
                                                (by simp [LoopBodyContinues,
                                                  hBodySource])
                                                hPost
                                                (by simp [LoopPostRecurs,
                                                  hPostSource])
                                                hLoop⟩⟩
                                    | ok afterLoop =>
                                        have hLoop' := hLoop
                                        simp only [hPostSource] at hLoop'
                                        rw [hLoop'] at hRun
                                        contradiction
                    | Ok shared store =>
                        rw [hBodySource] at hRun
                        simp only at hRun
                        cases hPost :
                            exec model prim previous (.Block post)
                              codeOverride
                              (model.withSource afterBody
                                (model.source afterBody).reviveJump) with
                        | error postFailure =>
                            have hPost' := hPost
                            simp only [hBodySource] at hPost'
                            rw [hPost'] at hRun
                            have hFailure :
                                postFailure = failure :=
                              Except.error.inj hRun
                            subst failure
                            exact
                              ⟨previous, by omega, Or.inr
                                ⟨afterCond, condValue, hCond,
                                  .post hZero hBody
                                    (by simp [LoopBodyContinues, hBodySource])
                                    hPost⟩⟩
                        | ok afterPost =>
                            have hPost' := hPost
                            simp only [hBodySource] at hPost'
                            rw [hPost'] at hRun
                            simp only at hRun
                            cases hPostSource : model.source afterPost with
                            | OutOfFuel =>
                                rw [hPostSource] at hRun
                                contradiction
                            | Checkpoint postJump =>
                                cases postJump with
                                | Leave postShared postStore =>
                                    rw [hPostSource] at hRun
                                    contradiction
                                | Continue postShared postStore =>
                                    rw [hPostSource] at hRun
                                    simp only at hRun
                                    cases hLoop :
                                        exec model prim previous
                                          (.For cond post body) codeOverride
                                          (model.withSource afterPost
                                            ((model.source afterPost).overwrite?
                                              (model.source state))) with
                                    | error loopFailure =>
                                        have hLoop' := hLoop
                                        simp only [hPostSource] at hLoop'
                                        rw [hLoop'] at hRun
                                        have hFailure :
                                            loopFailure = failure :=
                                          Except.error.inj hRun
                                        subst failure
                                        exact
                                          ⟨previous, by omega, Or.inr
                                            ⟨afterCond, condValue, hCond,
                                              .recurse hZero hBody
                                                (by simp [LoopBodyContinues,
                                                  hBodySource])
                                                hPost
                                                (by simp [LoopPostRecurs,
                                                  hPostSource])
                                                hLoop⟩⟩
                                    | ok afterLoop =>
                                        have hLoop' := hLoop
                                        simp only [hPostSource] at hLoop'
                                        rw [hLoop'] at hRun
                                        contradiction
                                | Break postShared postStore =>
                                    rw [hPostSource] at hRun
                                    simp only at hRun
                                    cases hLoop :
                                        exec model prim previous
                                          (.For cond post body) codeOverride
                                          (model.withSource afterPost
                                            ((model.source afterPost).overwrite?
                                              (model.source state))) with
                                    | error loopFailure =>
                                        have hLoop' := hLoop
                                        simp only [hPostSource] at hLoop'
                                        rw [hLoop'] at hRun
                                        have hFailure :
                                            loopFailure = failure :=
                                          Except.error.inj hRun
                                        subst failure
                                        exact
                                          ⟨previous, by omega, Or.inr
                                            ⟨afterCond, condValue, hCond,
                                              .recurse hZero hBody
                                                (by simp [LoopBodyContinues,
                                                  hBodySource])
                                                hPost
                                                (by simp [LoopPostRecurs,
                                                  hPostSource])
                                                hLoop⟩⟩
                                    | ok afterLoop =>
                                        have hLoop' := hLoop
                                        simp only [hPostSource] at hLoop'
                                        rw [hLoop'] at hRun
                                        contradiction
                            | Ok postShared postStore =>
                                rw [hPostSource] at hRun
                                simp only at hRun
                                cases hLoop :
                                    exec model prim previous
                                      (.For cond post body) codeOverride
                                      (model.withSource afterPost
                                        ((model.source afterPost).overwrite?
                                          (model.source state))) with
                                | error loopFailure =>
                                    have hLoop' := hLoop
                                    simp only [hPostSource] at hLoop'
                                    rw [hLoop'] at hRun
                                    have hFailure :
                                        loopFailure = failure :=
                                      Except.error.inj hRun
                                    subst failure
                                    exact
                                      ⟨previous, by omega, Or.inr
                                        ⟨afterCond, condValue, hCond,
                                          .recurse hZero hBody
                                            (by simp [LoopBodyContinues,
                                              hBodySource])
                                            hPost
                                            (by simp [LoopPostRecurs,
                                              hPostSource])
                                            hLoop⟩⟩
                                | ok afterLoop =>
                                    have hLoop' := hLoop
                                    simp only [hPostSource] at hLoop'
                                    rw [hLoop'] at hRun
                                    contradiction

theorem exec_for_observable_error_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {cond : EvmYul.Yul.Ast.Expr}
    {post body : List EvmYul.Yul.Ast.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state : σ} {failure : Failure σ}
    (hRun :
      exec model prim fuel (.For cond post body) codeOverride state =
        .error failure)
    (hObservable : Exception.Observable failure.exception) :
    ∃ loopFuel,
      fuel = loopFuel + 1 ∧
      loop model prim loopFuel cond post body codeOverride state =
        .error failure := by
  cases fuel with
  | zero =>
      simp [exec, fail] at hRun
      rw [← hRun] at hObservable
      simp [Exception.Observable] at hObservable
  | succ loopFuel =>
      exact ⟨loopFuel, rfl, by simpa [exec] using hRun⟩

end Effectful
end Source
end Yul
end EvmCompiler
