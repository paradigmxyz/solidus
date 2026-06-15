import EvmCompiler.Yul.EffectRefinement

namespace EvmCompiler
namespace Yul
namespace Source
namespace Effectful

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
    ∃ previous yulContract params returns body,
      fuel = previous + 1 ∧
      (model.source state).sharedState.accountMap.find?
          (model.source state).executionEnv.codeOwner =
        some yulContract ∧
      (match functionName? with
        | none =>
            some
              (EvmYul.Yul.Ast.FunctionDefinition.Def [] []
                [(codeOverride.getD yulContract.code).dispatcher])
        | some functionName =>
            (codeOverride.getD yulContract.code).functions.lookup
              functionName) =
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
      cases hContract :
          (model.source state).sharedState.accountMap.find?
            (model.source state).executionEnv.codeOwner with
      | none =>
          simp [call, hContract, fail] at hRun
          rw [← hRun] at hObservable
          simp [Exception.Observable] at hObservable
      | some yulContract =>
          cases functionName? with
          | none =>
              cases hBody :
                  exec model prim previous
                    (.Block
                      [(codeOverride.getD yulContract.code).dispatcher])
                    codeOverride
                    (model.withSource state
                      (EvmYul.Yul.State.mkOk
                        ((model.source state).initcall [] [] args))) with
              | error bodyFailure =>
                  simp [call, hContract, hBody] at hRun
                  subst failure
                  exact
                    ⟨previous, yulContract, [], [],
                      [(codeOverride.getD yulContract.code).dispatcher],
                      rfl, rfl, rfl, hBody⟩
              | ok stateAfterBody =>
                  simp [call, hContract, hBody] at hRun
          | some functionName =>
              cases hFunction :
                  (codeOverride.getD yulContract.code).functions.lookup
                    functionName with
              | none =>
                  simp [call, hContract, hFunction, fail] at hRun
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
                          simp [call, hContract, hFunction, hBody] at hRun
                          subst failure
                          exact
                            ⟨previous, yulContract, params, returns, body,
                              rfl, rfl, hFunction, hBody⟩
                      | ok stateAfterBody =>
                          simp [call, hContract, hFunction, hBody] at hRun

end Effectful
end Source
end Yul
end EvmCompiler
