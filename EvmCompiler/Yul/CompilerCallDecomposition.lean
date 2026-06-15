import EvmCompiler.Yul.Compiler

namespace EvmCompiler
namespace Yul

/-!
Ordinary compiler decompositions for direct Yul function-call statements.

These lemmas expose the existing unchecked lowering without defining another
compiler or mentioning observer semantics.
-/

namespace Expr

theorem uncheckedCallArgsLowering_of_choice
    {state final : Fresh.State} {args : List AstExpr}
    {pre : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    (hLower :
      (if List.directCallArgsSafe? args then do
          let lowerArgs ← List.toLocals1? args
          some ([], lowerArgs, state)
        else
          List.lowerBound1Unchecked? state args) =
        some (pre, lowerArgs, final)) :
    UncheckedCallArgsLowering state args pre lowerArgs final := by
  cases args with
  | nil =>
      simp [List.directCallArgsSafe?, List.toLocals1?] at hLower
      rcases hLower with ⟨rfl, rfl, rfl⟩
      exact UncheckedCallArgsLowering.empty state
  | cons head tail =>
      simp [List.directCallArgsSafe?] at hLower
      exact
        UncheckedCallArgsLowering.bound
          (by simp)
          (List.uncheckedBoundLowering_of_lowerBound1Unchecked? hLower)

theorem UncheckedCallArgsLowering.stateExtends
    {state final : Fresh.State} {args : List AstExpr}
    {pre : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    (hLowering :
      UncheckedCallArgsLowering state args pre lowerArgs final) :
    Fresh.Extends state final := by
  cases hLowering with
  | empty =>
      exact Fresh.Extends.refl _
  | bound _hNonempty hBound =>
      exact
        hBound.stateExtends
          (fun hLower => lower1Unchecked?_stateExtends hLower)

end Expr

namespace Stmt

theorem toFunctionsListUncheckedFuel?_let_call
    (fuel : Nat) (state : Fresh.State)
    (names : List EvmYul.Identifier)
    (functionName : Name) (args : List AstExpr) :
    toFunctionsListUncheckedFuel? (fuel + 1) state
        (.Let names (some (.Call (.inr functionName) args))) =
      if ObjectBuiltin.unsupported? functionName then
        none
      else
        (if Expr.List.directCallArgsSafe? args then do
            let lowerArgs ← Expr.List.toLocals1? args
            some ([], lowerArgs, state)
          else
            Expr.List.lowerBound1Unchecked? state args).bind fun result =>
          some
            (initNames (identNames names) ++ result.1 ++
              [Functions.Stmt.call
                (identNames names) functionName result.2.1],
              result.2.2) := by
  cases names with
  | nil =>
      simp only [toFunctionsListUncheckedFuel?]
      by_cases hUnsupported : ObjectBuiltin.unsupported? functionName
      · simp [hUnsupported, identNames, initNames]
      · by_cases hDirect : Expr.List.directCallArgsSafe? args
        · cases hLocals : Expr.List.toLocals1? args <;>
            simp [hUnsupported, hDirect, hLocals, identNames, initNames]
        · simp [hUnsupported, hDirect, identNames, initNames]
  | cons name rest =>
      cases rest with
      | nil =>
          simp only [toFunctionsListUncheckedFuel?]
          by_cases hUnsupported : ObjectBuiltin.unsupported? functionName
          · simp [hUnsupported]
          · by_cases hDirect : Expr.List.directCallArgsSafe? args
            · cases hLocals : Expr.List.toLocals1? args <;>
                simp [hUnsupported, hDirect, hLocals]
            · simp [hUnsupported, hDirect]
      | cons next rest =>
          simp only [toFunctionsListUncheckedFuel?]
          by_cases hUnsupported : ObjectBuiltin.unsupported? functionName
          · simp [hUnsupported]
          · by_cases hDirect : Expr.List.directCallArgsSafe? args
            · cases hLocals : Expr.List.toLocals1? args <;>
                simp [hUnsupported, hDirect, hLocals]
            · simp [hUnsupported, hDirect]

theorem toFunctionsListUncheckedFuel?_assign_call
    (fuel : Nat) (state : Fresh.State)
    (names : List EvmYul.Identifier)
    (functionName : Name) (args : List AstExpr) :
    toFunctionsListUncheckedFuel? (fuel + 1) state
        (.Assign names (.Call (.inr functionName) args)) =
      if ObjectBuiltin.unsupported? functionName then
        none
      else
        (if Expr.List.directCallArgsSafe? args then do
            let lowerArgs ← Expr.List.toLocals1? args
            some ([], lowerArgs, state)
          else
            Expr.List.lowerBound1Unchecked? state args).bind fun result =>
          some
            (result.1 ++
              [Functions.Stmt.call
                (identNames names) functionName result.2.1],
              result.2.2) := by
  cases names with
  | nil =>
      simp only [toFunctionsListUncheckedFuel?]
      by_cases hUnsupported : ObjectBuiltin.unsupported? functionName
      · simp [hUnsupported, identNames]
      · by_cases hDirect : Expr.List.directCallArgsSafe? args
        · cases hLocals : Expr.List.toLocals1? args <;>
            simp [hUnsupported, hDirect, hLocals, identNames]
        · simp [hUnsupported, hDirect, identNames]
  | cons name rest =>
      cases rest with
      | nil =>
          simp only [toFunctionsListUncheckedFuel?]
          by_cases hUnsupported : ObjectBuiltin.unsupported? functionName
          · simp [hUnsupported]
          · by_cases hDirect : Expr.List.directCallArgsSafe? args
            · cases hLocals : Expr.List.toLocals1? args <;>
                simp [hUnsupported, hDirect, hLocals]
            · simp [hUnsupported, hDirect]
      | cons next rest =>
          simp only [toFunctionsListUncheckedFuel?]
          by_cases hUnsupported : ObjectBuiltin.unsupported? functionName
          · simp [hUnsupported]
          · by_cases hDirect : Expr.List.directCallArgsSafe? args
            · cases hLocals : Expr.List.toLocals1? args <;>
                simp [hUnsupported, hDirect, hLocals]
            · simp [hUnsupported, hDirect]

theorem toFunctionsListUncheckedFuel?_let_call_parts
    {fuel : Nat} {state final : Fresh.State}
    {names : List EvmYul.Identifier}
    {functionName : Name} {args : List AstExpr}
    {lower : List Functions.Stmt}
    (hLower :
      toFunctionsListUncheckedFuel? fuel state
          (.Let names (some (.Call (.inr functionName) args))) =
        some (lower, final)) :
    ∃ preArgs lowerArgs,
      Expr.UncheckedCallArgsLowering state args
        preArgs lowerArgs final ∧
      lower =
        initNames (identNames names) ++ preArgs ++
          [Functions.Stmt.call
            (identNames names) functionName lowerArgs] := by
  cases fuel with
  | zero =>
      simp [toFunctionsListUncheckedFuel?] at hLower
  | succ fuel =>
      rw [toFunctionsListUncheckedFuel?_let_call] at hLower
      by_cases hUnsupported :
          ObjectBuiltin.unsupported? functionName
      · simp [hUnsupported] at hLower
      · cases hArgs :
          (if Expr.List.directCallArgsSafe? args then do
              let lowerArgs ← Expr.List.toLocals1? args
              some ([], lowerArgs, state)
            else
              Expr.List.lowerBound1Unchecked? state args) with
        | none =>
            rw [hArgs] at hLower
            simp [hUnsupported] at hLower
        | some result =>
            rcases result with ⟨preArgs, lowerArgs, argsFinal⟩
            rw [hArgs] at hLower
            simp [hUnsupported] at hLower
            rcases hLower with ⟨rfl, rfl⟩
            exact
              ⟨preArgs, lowerArgs,
                Expr.uncheckedCallArgsLowering_of_choice hArgs,
                by simp [List.append_assoc]⟩

theorem toFunctionsListUncheckedFuel?_assign_call_parts
    {fuel : Nat} {state final : Fresh.State}
    {names : List EvmYul.Identifier}
    {functionName : Name} {args : List AstExpr}
    {lower : List Functions.Stmt}
    (hLower :
      toFunctionsListUncheckedFuel? fuel state
          (.Assign names (.Call (.inr functionName) args)) =
        some (lower, final)) :
    ∃ preArgs lowerArgs,
      Expr.UncheckedCallArgsLowering state args
        preArgs lowerArgs final ∧
      lower =
        preArgs ++
          [Functions.Stmt.call
            (identNames names) functionName lowerArgs] := by
  cases fuel with
  | zero =>
      simp [toFunctionsListUncheckedFuel?] at hLower
  | succ fuel =>
      rw [toFunctionsListUncheckedFuel?_assign_call] at hLower
      by_cases hUnsupported :
          ObjectBuiltin.unsupported? functionName
      · simp [hUnsupported] at hLower
      · cases hArgs :
          (if Expr.List.directCallArgsSafe? args then do
              let lowerArgs ← Expr.List.toLocals1? args
              some ([], lowerArgs, state)
            else
              Expr.List.lowerBound1Unchecked? state args) with
        | none =>
            rw [hArgs] at hLower
            simp [hUnsupported] at hLower
        | some result =>
            rcases result with ⟨preArgs, lowerArgs, argsFinal⟩
            rw [hArgs] at hLower
            simp [hUnsupported] at hLower
            rcases hLower with ⟨rfl, rfl⟩
            exact
              ⟨preArgs, lowerArgs,
                Expr.uncheckedCallArgsLowering_of_choice hArgs, rfl⟩

theorem toFunctionsListUncheckedFuel?_expr_call_parts
    {fuel : Nat} {state final : Fresh.State}
    {functionName : Name} {args : List AstExpr}
    {lower : List Functions.Stmt}
    (hLower :
      toFunctionsListUncheckedFuel? fuel state
          (.ExprStmtCall (.Call (.inr functionName) args)) =
        some (lower, final)) :
    ∃ preArgs lowerArgs,
      Expr.UncheckedCallArgsLowering state args
        preArgs lowerArgs final ∧
      lower =
        preArgs ++
          [Functions.Stmt.call [] functionName lowerArgs] := by
  cases fuel with
  | zero =>
      simp [toFunctionsListUncheckedFuel?] at hLower
  | succ fuel =>
      simp only [toFunctionsListUncheckedFuel?] at hLower
      by_cases hUnsupported :
          ObjectBuiltin.unsupported? functionName
      · simp [hUnsupported] at hLower
      · by_cases hDirect : Expr.List.directCallArgsSafe? args
        · cases hArgs : Expr.List.toLocals1? args with
          | none =>
              simp [hUnsupported, hDirect, hArgs] at hLower
          | some lowerArgs =>
              simp [hUnsupported, hDirect, hArgs] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              have hChoice :
                  (if Expr.List.directCallArgsSafe? args then do
                      let lowered ← Expr.List.toLocals1? args
                      some ([], lowered, state)
                    else
                      Expr.List.lowerBound1Unchecked? state args) =
                    some ([], lowerArgs, state) := by
                simp [hDirect, hArgs]
              exact
                ⟨[], lowerArgs,
                  Expr.uncheckedCallArgsLowering_of_choice hChoice, rfl⟩
        · cases hArgs :
            Expr.List.lowerBound1Unchecked? state args with
          | none =>
              simp [hUnsupported, hDirect, hArgs] at hLower
          | some result =>
              rcases result with ⟨preArgs, lowerArgs, argsFinal⟩
              simp [hUnsupported, hDirect, hArgs] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              have hChoice :
                  (if Expr.List.directCallArgsSafe? args then do
                      let lowered ← Expr.List.toLocals1? args
                      some ([], lowered, state)
                    else
                      Expr.List.lowerBound1Unchecked? state args) =
                    some (preArgs, lowerArgs, argsFinal) := by
                simp [hDirect, hArgs]
              exact
                ⟨preArgs, lowerArgs,
                  Expr.uncheckedCallArgsLowering_of_choice hChoice, rfl⟩

end Stmt

namespace Stmt.List

theorem toBlockUncheckedFuel?_singleton_let_call_parts
    {fuel : Nat} {state final : Fresh.State}
    {names : List EvmYul.Identifier}
    {functionName : Name} {args : List AstExpr}
    {lower : Functions.Block}
    (hLower :
      toBlockUncheckedFuel? fuel state
          [.Let names (some (.Call (.inr functionName) args))] =
        some (lower, final)) :
    ∃ preArgs lowerArgs,
      Expr.UncheckedCallArgsLowering state args
        preArgs lowerArgs final ∧
      lower =
        { stmts :=
            Stmt.initNames (identNames names) ++ preArgs ++
              [Functions.Stmt.call
                (identNames names) functionName lowerArgs] } := by
  obtain ⟨previous, lowerStmts, _hFuel, hList, hBlock⟩ :=
    toBlockUncheckedFuel?_parts hLower
  obtain
      ⟨stmtFuel, lowerStmt, middle, lowerRest,
        _hPrevious, hStmt, hRest, hStmts⟩ :=
    toFunctionsUncheckedFuel?_cons_parts hList
  cases stmtFuel with
  | zero =>
      simp [Stmt.toFunctionsListUncheckedFuel?] at hStmt
  | succ remaining =>
      rw [Stmt.toFunctionsListUncheckedFuel?_let_call] at hStmt
      by_cases hUnsupported :
          ObjectBuiltin.unsupported? functionName
      · simp [hUnsupported] at hStmt
      · cases hArgs :
          (if Expr.List.directCallArgsSafe? args then do
              let lowerArgs ← Expr.List.toLocals1? args
              some ([], lowerArgs, state)
            else
              Expr.List.lowerBound1Unchecked? state args) with
        | none =>
            rw [hArgs] at hStmt
            simp [hUnsupported] at hStmt
        | some result =>
            rcases result with ⟨preArgs, lowerArgs, argsFinal⟩
            rw [hArgs] at hStmt
            simp [hUnsupported] at hStmt
            rcases hStmt with ⟨rfl, rfl⟩
            obtain ⟨_restFuel, _hRestFuel, hLowerRest, hFinal⟩ :=
              toFunctionsUncheckedFuel?_nil_parts hRest
            subst lowerRest
            subst final
            refine
              ⟨preArgs, lowerArgs,
                Expr.uncheckedCallArgsLowering_of_choice hArgs, ?_⟩
            simpa [hStmts] using hBlock

theorem toBlockUncheckedFuel?_singleton_assign_call_parts
    {fuel : Nat} {state final : Fresh.State}
    {names : List EvmYul.Identifier}
    {functionName : Name} {args : List AstExpr}
    {lower : Functions.Block}
    (hLower :
      toBlockUncheckedFuel? fuel state
          [.Assign names (.Call (.inr functionName) args)] =
        some (lower, final)) :
    ∃ preArgs lowerArgs,
      Expr.UncheckedCallArgsLowering state args
        preArgs lowerArgs final ∧
      lower =
        { stmts :=
            preArgs ++
              [Functions.Stmt.call
                (identNames names) functionName lowerArgs] } := by
  obtain ⟨previous, lowerStmts, _hFuel, hList, hBlock⟩ :=
    toBlockUncheckedFuel?_parts hLower
  obtain
      ⟨stmtFuel, lowerStmt, middle, lowerRest,
        _hPrevious, hStmt, hRest, hStmts⟩ :=
    toFunctionsUncheckedFuel?_cons_parts hList
  cases stmtFuel with
  | zero =>
      simp [Stmt.toFunctionsListUncheckedFuel?] at hStmt
  | succ remaining =>
      rw [Stmt.toFunctionsListUncheckedFuel?_assign_call] at hStmt
      by_cases hUnsupported :
          ObjectBuiltin.unsupported? functionName
      · simp [hUnsupported] at hStmt
      · cases hArgs :
          (if Expr.List.directCallArgsSafe? args then do
              let lowerArgs ← Expr.List.toLocals1? args
              some ([], lowerArgs, state)
            else
              Expr.List.lowerBound1Unchecked? state args) with
        | none =>
            rw [hArgs] at hStmt
            simp [hUnsupported] at hStmt
        | some result =>
            rcases result with ⟨preArgs, lowerArgs, argsFinal⟩
            rw [hArgs] at hStmt
            simp [hUnsupported] at hStmt
            rcases hStmt with ⟨rfl, rfl⟩
            obtain ⟨_restFuel, _hRestFuel, hLowerRest, hFinal⟩ :=
              toFunctionsUncheckedFuel?_nil_parts hRest
            subst lowerRest
            subst final
            refine
              ⟨preArgs, lowerArgs,
                Expr.uncheckedCallArgsLowering_of_choice hArgs, ?_⟩
            simpa [hStmts] using hBlock

end Stmt.List
end Yul
end EvmCompiler
