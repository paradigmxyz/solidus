import EvmCompiler.Yul.Compiler

namespace EvmCompiler
namespace Yul

/-!
Ordinary unchecked-compiler decompositions for individual Yul statements.

These equations expose the existing compiler to adjacent preservation proofs;
they do not define an alternate lowering.
-/

namespace Stmt

theorem toFunctionsListUncheckedFuel?_block_parts
    {fuel : Nat} {before after : Fresh.State}
    {body : List AstStmt}
    {lower : List Functions.Stmt}
    (hLower :
      toFunctionsListUncheckedFuel? fuel before (.Block body) =
        some (lower, after)) :
    ∃ previous lowerBody,
      fuel = previous + 1 ∧
      List.toBlockUncheckedFuel? previous before body =
        some (lowerBody, after) ∧
      lower = [.block lowerBody] := by
  cases fuel with
  | zero =>
      simp [toFunctionsListUncheckedFuel?] at hLower
  | succ previous =>
      cases hBody :
          List.toBlockUncheckedFuel? previous before body with
      | none =>
          simp [toFunctionsListUncheckedFuel?, hBody] at hLower
      | some result =>
          rcases result with ⟨lowerBody, final⟩
          simp [toFunctionsListUncheckedFuel?, hBody] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          exact ⟨previous, lowerBody, rfl, hBody, rfl⟩

theorem toFunctionsListUncheckedFuel?_block_of_toBlock
    {fuel : Nat} {before after : Fresh.State}
    {body : List AstStmt} {lowerBody : Functions.Block}
    (hLower :
      List.toBlockUncheckedFuel? fuel before body =
        some (lowerBody, after)) :
    toFunctionsListUncheckedFuel? (fuel + 1) before (.Block body) =
      some ([.block lowerBody], after) := by
  simp [toFunctionsListUncheckedFuel?, hLower]

theorem toFunctionsListUncheckedFuel?_if_parts
    {fuel : Nat} {before after : Fresh.State}
    {cond : AstExpr} {body : List AstStmt}
    {lower : List Functions.Stmt}
    (hLower :
      toFunctionsListUncheckedFuel? fuel before (.If cond body) =
        some (lower, after)) :
    ∃ previous preCond lowerCond middle lowerBody,
      fuel = previous + 1 ∧
      Expr.lower1Unchecked? before cond =
        some (preCond, lowerCond, middle) ∧
      List.toBlockUncheckedFuel? previous middle body =
        some (lowerBody, after) ∧
      lower = preCond ++ [.if_ lowerCond lowerBody] := by
  cases fuel with
  | zero =>
      simp [toFunctionsListUncheckedFuel?] at hLower
  | succ previous =>
      cases hCond : Expr.lower1Unchecked? before cond with
      | none =>
          simp [toFunctionsListUncheckedFuel?, hCond] at hLower
      | some condResult =>
          rcases condResult with ⟨preCond, lowerCond, middle⟩
          cases hBody :
              List.toBlockUncheckedFuel? previous middle body with
          | none =>
              simp [toFunctionsListUncheckedFuel?, hCond, hBody] at hLower
          | some bodyResult =>
              rcases bodyResult with ⟨lowerBody, final⟩
              simp [toFunctionsListUncheckedFuel?, hCond, hBody] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              exact
                ⟨previous, preCond, lowerCond, middle, lowerBody,
                  rfl, by simpa using hCond, by simpa using hBody, rfl⟩

theorem toFunctionsListUncheckedFuel?_let_none_parts
    {fuel : Nat} {before after : Fresh.State}
    {names : List EvmYul.Identifier}
    {lower : List Functions.Stmt}
    (hLower :
      toFunctionsListUncheckedFuel? fuel before (.Let names none) =
        some (lower, after)) :
    lower = initNames (identNames names) ∧
      after = before := by
  cases fuel with
  | zero =>
      simp [toFunctionsListUncheckedFuel?] at hLower
  | succ fuel =>
      simp [toFunctionsListUncheckedFuel?] at hLower
      exact ⟨hLower.1.symm, hLower.2.symm⟩

theorem toFunctionsListUncheckedFuel?_leave_parts
    {fuel : Nat} {before after : Fresh.State}
    {lower : List Functions.Stmt}
    (hLower :
      toFunctionsListUncheckedFuel? fuel before .Leave =
        some (lower, after)) :
    lower = [.leave] ∧ after = before := by
  cases fuel with
  | zero =>
      simp [toFunctionsListUncheckedFuel?] at hLower
  | succ fuel =>
      simp [toFunctionsListUncheckedFuel?] at hLower
      exact ⟨hLower.1.symm, hLower.2.symm⟩

theorem toFunctionsListUncheckedFuel?_continue_parts
    {fuel : Nat} {before after : Fresh.State}
    {lower : List Functions.Stmt}
    (hLower :
      toFunctionsListUncheckedFuel? fuel before .Continue =
        some (lower, after)) :
    lower = [.cont] ∧ after = before := by
  cases fuel with
  | zero =>
      simp [toFunctionsListUncheckedFuel?] at hLower
  | succ fuel =>
      simp [toFunctionsListUncheckedFuel?] at hLower
      exact ⟨hLower.1.symm, hLower.2.symm⟩

theorem toFunctionsListUncheckedFuel?_break_parts
    {fuel : Nat} {before after : Fresh.State}
    {lower : List Functions.Stmt}
    (hLower :
      toFunctionsListUncheckedFuel? fuel before .Break =
        some (lower, after)) :
    lower = [.brk] ∧ after = before := by
  cases fuel with
  | zero =>
      simp [toFunctionsListUncheckedFuel?] at hLower
  | succ fuel =>
      simp [toFunctionsListUncheckedFuel?] at hLower
      exact ⟨hLower.1.symm, hLower.2.symm⟩

theorem toFunctionsListUncheckedFuel?_let_one_parts
    {fuel : Nat} {before after : Fresh.State}
    {name : EvmYul.Identifier} {expr : AstExpr}
    {lower : List Functions.Stmt}
    (hNotFunctionCall :
      ∀ functionName functionArgs,
        expr ≠ .Call (.inr functionName) functionArgs)
    (hLower :
      toFunctionsListUncheckedFuel? fuel before
          (.Let [name] (some expr)) =
        some (lower, after)) :
    ∃ pre lowerValue,
      Expr.lower1Unchecked? before expr =
        some (pre, lowerValue, after) ∧
      lower =
        pre ++ [Functions.Stmt.let_ (identName name) lowerValue] := by
  cases fuel with
  | zero =>
      simp [toFunctionsListUncheckedFuel?] at hLower
  | succ fuel =>
      rw [toFunctionsListUncheckedFuel?_let_one_noncall
        fuel before name expr hNotFunctionCall] at hLower
      cases hValue : Expr.lower1Unchecked? before expr with
      | none =>
          simp [hValue] at hLower
      | some result =>
          rcases result with ⟨pre, lowerValue, final⟩
          simp [hValue] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          exact ⟨pre, lowerValue, rfl, rfl⟩

theorem toFunctionsListUncheckedFuel?_assign_one_parts
    {fuel : Nat} {before after : Fresh.State}
    {name : EvmYul.Identifier} {expr : AstExpr}
    {lower : List Functions.Stmt}
    (hNotFunctionCall :
      ∀ functionName functionArgs,
        expr ≠ .Call (.inr functionName) functionArgs)
    (hLower :
      toFunctionsListUncheckedFuel? fuel before
          (.Assign [name] expr) =
        some (lower, after)) :
    ∃ pre lowerValue,
      Expr.lower1Unchecked? before expr =
        some (pre, lowerValue, after) ∧
      lower =
        pre ++ [Functions.Stmt.assign (identName name) lowerValue] := by
  cases fuel with
  | zero =>
      simp [toFunctionsListUncheckedFuel?] at hLower
  | succ fuel =>
      rw [toFunctionsListUncheckedFuel?_assign_one_noncall
        fuel before name expr hNotFunctionCall] at hLower
      cases hValue : Expr.lower1Unchecked? before expr with
      | none =>
          simp [hValue] at hLower
      | some result =>
          rcases result with ⟨pre, lowerValue, final⟩
          simp [hValue] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          exact ⟨pre, lowerValue, rfl, rfl⟩

theorem toFunctionsListUncheckedFuel?_expr_primitive_parts
    {fuel : Nat} {before after : Fresh.State}
    {prim : EvmYul.Operation .Yul} {args : List AstExpr}
    {lower : List Functions.Stmt}
    (hNonterminal : Prim.terminal? prim = none)
    (hLower :
      toFunctionsListUncheckedFuel? fuel before
          (.ExprStmtCall (.Call (.inl prim) args)) =
        some (lower, after)) :
    ∃ pre lowerExpr,
      Expr.lower0Unchecked? before (.Call (.inl prim) args) =
        some (pre, lowerExpr, after) ∧
      lower = pre ++ [Functions.Stmt.expr lowerExpr] := by
  cases fuel with
  | zero =>
      simp [toFunctionsListUncheckedFuel?] at hLower
  | succ fuel =>
      simp only [toFunctionsListUncheckedFuel?] at hLower
      rw [hNonterminal] at hLower
      cases hExpr :
          Expr.lower0Unchecked? before (.Call (.inl prim) args) with
      | none =>
          simp [hExpr] at hLower
      | some result =>
          rcases result with ⟨pre, lowerExpr, final⟩
          simp [hExpr] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          exact ⟨pre, lowerExpr, rfl, rfl⟩

theorem toFunctionsListUncheckedFuel?_let_noncall_singleton
    {fuel : Nat} {before after : Fresh.State}
    {names : List EvmYul.Identifier} {expr : AstExpr}
    {lower : List Functions.Stmt}
    (hNotFunctionCall :
      ∀ functionName functionArgs,
        expr ≠ .Call (.inr functionName) functionArgs)
    (hLower :
      toFunctionsListUncheckedFuel? fuel before
          (.Let names (some expr)) =
        some (lower, after)) :
    ∃ name, names = [name] := by
  cases fuel with
  | zero => cases hLower
  | succ fuel =>
      cases names with
      | nil =>
          cases expr with
          | Lit value => cases hLower
          | Var name => cases hLower
          | Call callee args =>
              cases callee with
              | inl prim => cases hLower
              | inr functionName =>
                  exact (hNotFunctionCall functionName args rfl).elim
      | cons name rest =>
          cases rest with
          | nil => exact ⟨name, rfl⟩
          | cons next rest =>
              cases expr with
              | Lit value => cases hLower
              | Var varName => cases hLower
              | Call callee args =>
                  cases callee with
                  | inl prim => cases hLower
                  | inr functionName =>
                      exact (hNotFunctionCall functionName args rfl).elim

theorem toFunctionsListUncheckedFuel?_assign_noncall_singleton
    {fuel : Nat} {before after : Fresh.State}
    {names : List EvmYul.Identifier} {expr : AstExpr}
    {lower : List Functions.Stmt}
    (hNotFunctionCall :
      ∀ functionName functionArgs,
        expr ≠ .Call (.inr functionName) functionArgs)
    (hLower :
      toFunctionsListUncheckedFuel? fuel before (.Assign names expr) =
        some (lower, after)) :
    ∃ name, names = [name] := by
  cases fuel with
  | zero => cases hLower
  | succ fuel =>
      cases names with
      | nil =>
          cases expr with
          | Lit value => cases hLower
          | Var name => cases hLower
          | Call callee args =>
              cases callee with
              | inl prim => cases hLower
              | inr functionName =>
                  exact (hNotFunctionCall functionName args rfl).elim
      | cons name rest =>
          cases rest with
          | nil => exact ⟨name, rfl⟩
          | cons next rest =>
              cases expr with
              | Lit value => cases hLower
              | Var varName => cases hLower
              | Call callee args =>
                  cases callee with
                  | inl prim => cases hLower
                  | inr functionName =>
                      exact (hNotFunctionCall functionName args rfl).elim

end Stmt
end Yul
end EvmCompiler
