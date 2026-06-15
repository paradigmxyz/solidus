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

end Stmt
end Yul
end EvmCompiler
