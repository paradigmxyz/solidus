import EvmCompiler.Yul.Compiler

namespace EvmCompiler
namespace Yul

/-!
Ordinary unchecked-compiler decompositions for individual Yul statements.

These equations expose the existing compiler to adjacent preservation proofs;
they do not define an alternate lowering.
-/

namespace Stmt

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

end Stmt
end Yul
end EvmCompiler
