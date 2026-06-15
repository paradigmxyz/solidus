import EvmCompiler.Yul.EffectRefinement.Control

namespace EvmCompiler
namespace Yul
namespace Source
namespace Effectful

theorem exec_zero_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ) :
    Result.Refines
      (exec model sourcePrim 0 stmt codeOverride state)
      (exec model targetPrim 0 stmt codeOverride state) := by
  simpa [exec] using
    (Result.Refines.refl (fail state .OutOfFuel : Result σ σ))

theorem exec_block_succ_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat) (stmts : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ)
    (hSeq :
      Result.Refines
        (execSeq model sourcePrim fuel stmts codeOverride state)
        (execSeq model targetPrim fuel stmts codeOverride state)) :
    Result.Refines
      (exec model sourcePrim fuel.succ (.Block stmts)
        codeOverride state)
      (exec model targetPrim fuel.succ (.Block stmts)
        codeOverride state) := by
  intro hObservable
  generalize hSourceSeq :
    execSeq model sourcePrim fuel stmts codeOverride state = sourceSeq
  cases sourceSeq with
  | error failure =>
      have hSeqObservable :
          Result.Observable (.error failure : Result σ σ) := by
        simpa only [exec, hSourceSeq] using hObservable
      have hSourceSeqObservable :
          Result.Observable
            (execSeq model sourcePrim fuel stmts codeOverride state) := by
        rw [hSourceSeq]
        exact hSeqObservable
      have hTargetSeq := hSeq hSourceSeqObservable
      rw [hSourceSeq] at hTargetSeq
      simpa only [exec, hSourceSeq, hTargetSeq]
  | ok stateAfterBody =>
      have hSourceSeqObservable :
          Result.Observable
            (execSeq model sourcePrim fuel stmts codeOverride state) := by
        rw [hSourceSeq]
        simp [Result.Observable]
      have hTargetSeq := hSeq hSourceSeqObservable
      rw [hSourceSeq] at hTargetSeq
      simpa only [exec, hSourceSeq, hTargetSeq]

theorem exec_let_none_succ_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat) (vars : List EvmYul.Identifier)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ) :
    Result.Refines
      (exec model sourcePrim fuel.succ (.Let vars none)
        codeOverride state)
      (exec model targetPrim fuel.succ (.Let vars none)
        codeOverride state) := by
  simpa [exec] using
    (Result.Refines.refl
      (exec model sourcePrim fuel.succ (.Let vars none)
        codeOverride state))

theorem exec_let_some_succ_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat) (vars : List EvmYul.Identifier)
    (expr : EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ)
    (hValues :
      Result.Refines
        (evalValues model sourcePrim fuel expr codeOverride state)
        (evalValues model targetPrim fuel expr codeOverride state)) :
    Result.Refines
      (exec model sourcePrim fuel.succ (.Let vars (some expr))
        codeOverride state)
      (exec model targetPrim fuel.succ (.Let vars (some expr))
        codeOverride state) := by
  cases hDeclaration :
    EvmYul.Yul.checkDeclaration (model.source state) vars with
  | error err =>
      simpa [exec, hDeclaration] using
        (Result.Refines.refl (fail state err : Result σ σ))
  | ok unit =>
      simpa only [exec, hDeclaration] using
        (multifill_refines model vars hValues)

theorem exec_assign_succ_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat) (vars : List EvmYul.Identifier)
    (expr : EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ)
    (hValues :
      Result.Refines
        (evalValues model sourcePrim fuel expr codeOverride state)
        (evalValues model targetPrim fuel expr codeOverride state)) :
    Result.Refines
      (exec model sourcePrim fuel.succ (.Assign vars expr)
        codeOverride state)
      (exec model targetPrim fuel.succ (.Assign vars expr)
        codeOverride state) := by
  cases hAssignment :
    EvmYul.Yul.checkAssignment (model.source state) vars with
  | error err =>
      simpa [exec, hAssignment] using
        (Result.Refines.refl (fail state err : Result σ σ))
  | ok unit =>
      simpa only [exec, hAssignment] using
        (multifill_refines model vars hValues)

theorem exec_if_succ_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat) (cond : EvmYul.Yul.Ast.Expr)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ)
    (hCond :
      Result.Refines
        (eval model sourcePrim fuel cond codeOverride state)
        (eval model targetPrim fuel cond codeOverride state))
    (hBody :
      ∀ stateAfterCond,
        Result.Refines
          (exec model sourcePrim fuel (.Block body)
            codeOverride stateAfterCond)
          (exec model targetPrim fuel (.Block body)
            codeOverride stateAfterCond)) :
    Result.Refines
      (exec model sourcePrim fuel.succ (.If cond body)
        codeOverride state)
      (exec model targetPrim fuel.succ (.If cond body)
        codeOverride state) := by
  intro hObservable
  generalize hSourceCond :
    eval model sourcePrim fuel cond codeOverride state = sourceCond
  cases sourceCond with
  | error failure =>
      have hCondObservable :
          Result.Observable
            (.error failure : Result σ (σ × Word)) := by
        simpa only [exec, hSourceCond] using hObservable
      have hSourceCondObservable :
          Result.Observable
            (eval model sourcePrim fuel cond codeOverride state) := by
        rw [hSourceCond]
        exact hCondObservable
      have hTargetCond := hCond hSourceCondObservable
      rw [hSourceCond] at hTargetCond
      simpa only [exec, hSourceCond, hTargetCond]
  | ok result =>
      rcases result with ⟨stateAfterCond, condValue⟩
      have hSourceCondObservable :
          Result.Observable
            (eval model sourcePrim fuel cond codeOverride state) := by
        rw [hSourceCond]
        simp [Result.Observable]
      have hTargetCond := hCond hSourceCondObservable
      rw [hSourceCond] at hTargetCond
      by_cases hTrue : condValue ≠ ⟨0⟩
      · have hBodyObservable :
            Result.Observable
              (exec model sourcePrim fuel (.Block body)
                codeOverride stateAfterCond) := by
          simpa only [exec, hSourceCond, if_pos hTrue]
            using hObservable
        have hTargetBody := hBody stateAfterCond hBodyObservable
        simpa only [exec, hSourceCond, hTargetCond, if_pos hTrue]
          using hTargetBody
      · simpa only [exec, hSourceCond, hTargetCond, if_neg hTrue]

theorem exec_exprPrimitive_succ_refines
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
      (exec model sourcePrim fuel.succ
        (.ExprStmtCall (.Call (.inl op) args)) codeOverride state)
      (exec model targetPrim fuel.succ
        (.ExprStmtCall (.Call (.inl op) args)) codeOverride state) := by
  intro hObservable
  generalize hSourceArgs :
    evalArgs model sourcePrim fuel args.reverse codeOverride state = sourceArgs
  cases sourceArgs with
  | error failure =>
      have hArgsObservable :
          Result.Observable
            (.error failure : Result σ (σ × List Word)) := by
        simpa only [exec, hSourceArgs] using hObservable
      have hSourceArgsObservable :
          Result.Observable
            (evalArgs model sourcePrim fuel args.reverse
              codeOverride state) := by
        rw [hSourceArgs]
        exact hArgsObservable
      have hTargetArgs := hArgs hSourceArgsObservable
      rw [hSourceArgs] at hTargetArgs
      simpa only [exec, hSourceArgs, hTargetArgs]
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
      have hFilled :=
        multifill_refines model []
          (hPrim.result fuel stateAfterArgs op values.reverse)
      have hFilledObservable :
          Result.Observable
            (multifill model []
              (sourcePrim.eval fuel stateAfterArgs op values.reverse)) := by
        simpa only [exec, hSourceArgs] using hObservable
      have hTargetFilled := hFilled hFilledObservable
      simpa only [exec, hSourceArgs, hTargetArgs]
        using hTargetFilled

theorem exec_exprFunction_one_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (functionName : EvmYul.Yul.Ast.YulFunctionName)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ) :
    Result.Refines
      (exec model sourcePrim 1
        (.ExprStmtCall (.Call (.inr functionName) args))
        codeOverride state)
      (exec model targetPrim 1
        (.ExprStmtCall (.Call (.inr functionName) args))
        codeOverride state) := by
  simpa [exec, evalArgs] using
    (Result.Refines.refl
      (fail state .OutOfFuel : Result σ σ))

theorem exec_exprFunction_succ_succ_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat)
    (functionName : EvmYul.Yul.Ast.YulFunctionName)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ)
    (hArgs :
      Result.Refines
        (evalArgs model sourcePrim fuel.succ args.reverse
          codeOverride state)
        (evalArgs model targetPrim fuel.succ args.reverse
          codeOverride state))
    (hCall :
      ∀ callArgs callState,
        Result.Refines
          (call model sourcePrim fuel callArgs
            (some functionName) codeOverride callState)
          (call model targetPrim fuel callArgs
            (some functionName) codeOverride callState)) :
    Result.Refines
      (exec model sourcePrim fuel.succ.succ
        (.ExprStmtCall (.Call (.inr functionName) args))
        codeOverride state)
      (exec model targetPrim fuel.succ.succ
        (.ExprStmtCall (.Call (.inr functionName) args))
        codeOverride state) := by
  intro hObservable
  generalize hSourceArgs :
    evalArgs model sourcePrim fuel.succ args.reverse
      codeOverride state = sourceArgs
  cases sourceArgs with
  | error failure =>
      have hArgsObservable :
          Result.Observable
            (.error failure : Result σ (σ × List Word)) := by
        simpa only [exec, hSourceArgs] using hObservable
      have hSourceArgsObservable :
          Result.Observable
            (evalArgs model sourcePrim fuel.succ args.reverse
              codeOverride state) := by
        rw [hSourceArgs]
        exact hArgsObservable
      have hTargetArgs := hArgs hSourceArgsObservable
      rw [hSourceArgs] at hTargetArgs
      simpa only [exec, hSourceArgs, hTargetArgs]
  | ok result =>
      rcases result with ⟨stateAfterArgs, values⟩
      have hSourceArgsObservable :
          Result.Observable
            (evalArgs model sourcePrim fuel.succ args.reverse
              codeOverride state) := by
        rw [hSourceArgs]
        simp [Result.Observable]
      have hTargetArgs := hArgs hSourceArgsObservable
      rw [hSourceArgs] at hTargetArgs
      have hFilled :=
        multifill_refines model []
          (hCall values.reverse stateAfterArgs)
      have hFilledObservable :
          Result.Observable
            (multifill model []
              (call model sourcePrim fuel values.reverse
                (some functionName) codeOverride stateAfterArgs)) := by
        simpa only [exec, hSourceArgs] using hObservable
      have hTargetFilled := hFilled hFilledObservable
      simpa only [exec, hSourceArgs, hTargetArgs]
        using hTargetFilled

theorem exec_exprInvalid_succ_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat) (expr : EvmYul.Yul.Ast.Expr)
    (hInvalid :
      (∀ op args, expr ≠ .Call (.inl op) args) ∧
      (∀ functionName args, expr ≠ .Call (.inr functionName) args))
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ) :
    Result.Refines
      (exec model sourcePrim fuel.succ (.ExprStmtCall expr)
        codeOverride state)
      (exec model targetPrim fuel.succ (.ExprStmtCall expr)
        codeOverride state) := by
  cases expr with
  | Call callee args =>
      cases callee with
      | inl op => exact False.elim (hInvalid.1 op args rfl)
      | inr functionName => exact False.elim (hInvalid.2 functionName args rfl)
  | Var name =>
      simpa [exec] using
        (Result.Refines.refl
          (fail state .InvalidExpression : Result σ σ))
  | Lit value =>
      simpa [exec] using
        (Result.Refines.refl
          (fail state .InvalidExpression : Result σ σ))

theorem exec_switch_succ_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat) (cond : EvmYul.Yul.Ast.Expr)
    (cases :
      List (Word × List EvmYul.Yul.Ast.Stmt))
    (default : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ)
    (hCond :
      Result.Refines
        (eval model sourcePrim fuel cond codeOverride state)
        (eval model targetPrim fuel cond codeOverride state))
    (hBody :
      ∀ condValue stateAfterCond,
        Result.Refines
          (exec model sourcePrim fuel
            (.Block
              (EvmYul.Yul.selectSwitchCase condValue default cases))
            codeOverride stateAfterCond)
          (exec model targetPrim fuel
            (.Block
              (EvmYul.Yul.selectSwitchCase condValue default cases))
            codeOverride stateAfterCond)) :
    Result.Refines
      (exec model sourcePrim fuel.succ
        (.Switch cond cases default) codeOverride state)
      (exec model targetPrim fuel.succ
        (.Switch cond cases default) codeOverride state) := by
  intro hObservable
  generalize hSourceCond :
    eval model sourcePrim fuel cond codeOverride state = sourceCond
  cases sourceCond with
  | error failure =>
      have hCondObservable :
          Result.Observable
            (.error failure : Result σ (σ × Word)) := by
        simpa only [exec, hSourceCond] using hObservable
      have hSourceCondObservable :
          Result.Observable
            (eval model sourcePrim fuel cond codeOverride state) := by
        rw [hSourceCond]
        exact hCondObservable
      have hTargetCond := hCond hSourceCondObservable
      rw [hSourceCond] at hTargetCond
      simpa only [exec, hSourceCond, hTargetCond]
  | ok result =>
      rcases result with ⟨stateAfterCond, condValue⟩
      have hSourceCondObservable :
          Result.Observable
            (eval model sourcePrim fuel cond codeOverride state) := by
        rw [hSourceCond]
        simp [Result.Observable]
      have hTargetCond := hCond hSourceCondObservable
      rw [hSourceCond] at hTargetCond
      have hBodyObservable :
          Result.Observable
            (exec model sourcePrim fuel
              (.Block
                (EvmYul.Yul.selectSwitchCase
                  condValue default cases))
              codeOverride stateAfterCond) := by
        simpa only [exec, hSourceCond, hTargetCond]
          using hObservable
      have hTargetBody :=
        hBody condValue stateAfterCond hBodyObservable
      simpa only [exec, hSourceCond, hTargetCond] using hTargetBody

theorem exec_for_succ_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat) (cond : EvmYul.Yul.Ast.Expr)
    (post body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ)
    (hLoop :
      Result.Refines
        (loop model sourcePrim fuel cond post body codeOverride state)
        (loop model targetPrim fuel cond post body codeOverride state)) :
    Result.Refines
      (exec model sourcePrim fuel.succ (.For cond post body)
        codeOverride state)
      (exec model targetPrim fuel.succ (.For cond post body)
        codeOverride state) := by
  simpa [exec] using hLoop

theorem exec_continue_succ_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ) :
    Result.Refines
      (exec model sourcePrim fuel.succ .Continue codeOverride state)
      (exec model targetPrim fuel.succ .Continue codeOverride state) := by
  simpa [exec] using
    (Result.Refines.refl
      (.ok
        (model.withSource state
          (EvmYul.Yul.State.setContinue (model.source state))) :
        Result σ σ))

theorem exec_break_succ_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ) :
    Result.Refines
      (exec model sourcePrim fuel.succ .Break codeOverride state)
      (exec model targetPrim fuel.succ .Break codeOverride state) := by
  simpa [exec] using
    (Result.Refines.refl
      (.ok
        (model.withSource state
          (EvmYul.Yul.State.setBreak (model.source state))) :
        Result σ σ))

theorem exec_leave_succ_refines
    {σ : Type} (model : StateModel σ)
    (sourcePrim targetPrim : PrimitiveSemantics σ)
    (fuel : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state : σ) :
    Result.Refines
      (exec model sourcePrim fuel.succ .Leave codeOverride state)
      (exec model targetPrim fuel.succ .Leave codeOverride state) := by
  simpa [exec] using
    (Result.Refines.refl
      (.ok
        (model.withSource state
          (EvmYul.Yul.State.setLeave (model.source state))) :
        Result σ σ))

end Effectful
end Source
end Yul
end EvmCompiler
