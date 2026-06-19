import EvmCompiler.Yul.FunctionsInteractionTargetCost
import EvmCompiler.Yul.Compiler

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionCompilerCost

/-!
Source-syntax bounds for the recursive Functions target cost emitted by the
ordinary Yul compiler. These measures inspect no generated code and are used
only for private target meta-fuel accounting.
-/

mutual
  def expr : AstExpr → Nat
    | .Lit _ | .Var _ => 0
    | .Call _ args => exprList args + 4

  def exprList : List AstExpr → Nat
    | [] => 0
    | head :: tail => exprList tail + expr head + 2
end

/-- Every expression prelude emitted by unchecked lowering is bounded solely
by the source expression tree. The list theorem is the matching bound for the
compiler's right-to-left bounded-argument lowering. -/
theorem lowerUnchecked?_cost
    {results : Nat} {state final : Fresh.State}
    {source : AstExpr} {pre : List Functions.Stmt}
    {lower : Locals.Expr results}
    (hLower : Expr.lowerUnchecked? results state source =
      some (pre, lower, final)) :
    FunctionsInteractionTargetCost.list pre ≤ expr source := by
    induction results, state, source using Expr.lowerUnchecked?.induct
        (motive_2 := fun listState sources =>
          ∀ listPre listLower listFinal,
            Expr.List.lowerBound1Unchecked? listState sources =
                some (listPre, listLower, listFinal) →
              FunctionsInteractionTargetCost.list listPre ≤ exprList sources)
        generalizing pre final with
    | case1 state value =>
        simp [Expr.lowerUnchecked?] at hLower
        rw [hLower.1]
        simp [FunctionsInteractionTargetCost.list, expr]
    | case2 results state value hNe =>
        simp [Expr.lowerUnchecked?, hNe] at hLower
    | case3 state name =>
        simp [Expr.lowerUnchecked?] at hLower
        rw [hLower.1]
        simp [FunctionsInteractionTargetCost.list, expr]
    | case4 results state name hNe =>
        simp [Expr.lowerUnchecked?, hNe] at hLower
    | case5 results state functionName args hUnsupported =>
        simp [Expr.lowerUnchecked?, hUnsupported] at hLower
    | case6 state functionName args hSupported hDirect =>
        cases hArgs : Expr.List.toLocals1? args with
        | none =>
            simp [Expr.lowerUnchecked?, hSupported, hDirect, hArgs] at hLower
        | some lowerArgs =>
            cases hFresh : Fresh.fresh? state with
            | none =>
                simp [Expr.lowerUnchecked?, hSupported, hDirect, hArgs,
                  hFresh] at hLower
            | some result =>
                rcases result with ⟨tmp, stateAfter⟩
                simp [Expr.lowerUnchecked?, hSupported, hDirect, hArgs,
                  hFresh] at hLower
                rw [← hLower.1]
                simp [FunctionsInteractionTargetCost.list,
                  FunctionsInteractionTargetCost.stmt, expr]
    | case7 state functionName args hSupported hBound ih =>
        cases hArgs : Expr.List.lowerBound1Unchecked? state args with
        | none =>
            simp [Expr.lowerUnchecked?, hSupported, hBound, hArgs] at hLower
        | some result =>
            rcases result with ⟨preArgs, lowerArgs, stateAfterArgs⟩
            cases hFresh : Fresh.fresh? stateAfterArgs with
            | none =>
                simp [Expr.lowerUnchecked?, hSupported, hBound, hArgs,
                  hFresh] at hLower
            | some result =>
                rcases result with ⟨tmp, stateAfter⟩
                simp [Expr.lowerUnchecked?, hSupported, hBound, hArgs,
                  hFresh] at hLower
                rw [← hLower.1,
                  FunctionsInteractionTargetCost.list_append]
                have hPre := ih _ _ _ hArgs
                simp [FunctionsInteractionTargetCost.list,
                  FunctionsInteractionTargetCost.stmt, expr]
                omega
    | case8 results state functionName args hSupported hNe =>
        simp [Expr.lowerUnchecked?, hSupported, hNe] at hLower
    | case9 results state prim args ih =>
        cases hOp : Prim.toUncheckedBasicOp? prim with
        | none => simp [Expr.lowerUnchecked?, hOp] at hLower
        | some op =>
            cases hDirect : Expr.List.directPureArgsSafe? args with
            | false =>
                cases hArgs : Expr.List.lowerBound1Unchecked? state args with
                | none =>
                    simp [Expr.lowerUnchecked?, hOp, hDirect, hArgs] at hLower
                | some result =>
                    rcases result with ⟨preArgs, lowerArgs, stateAfterArgs⟩
                    cases hSeq : Expr.List.toStackSeq? lowerArgs
                        (Expressions.Structured.BasicOp.inputs op) with
                    | none =>
                        simp [Expr.lowerUnchecked?, hOp, hDirect, hArgs, hSeq]
                          at hLower
                    | some seq =>
                        by_cases hOutputs :
                            Expressions.Structured.BasicOp.outputs op = results
                        · simp [Expr.lowerUnchecked?, hOp, hDirect, hArgs, hSeq,
                            hOutputs] at hLower
                          rw [← hLower.1]
                          have hPre := ih _ _ _ hArgs
                          simp [expr]
                          omega
                        · simp [Expr.lowerUnchecked?, hOp, hDirect, hArgs, hSeq,
                            hOutputs] at hLower
            | true =>
                cases hArgs : Expr.List.toLocals1? args with
                | none =>
                    simp [Expr.lowerUnchecked?, hOp, hDirect, hArgs] at hLower
                | some lowerArgs =>
                    cases hSeq : Expr.List.toStackSeq? lowerArgs
                        (Expressions.Structured.BasicOp.inputs op) with
                    | none =>
                        simp [Expr.lowerUnchecked?, hOp, hDirect, hArgs, hSeq]
                          at hLower
                    | some seq =>
                        by_cases hOutputs :
                            Expressions.Structured.BasicOp.outputs op = results
                        · simp [Expr.lowerUnchecked?, hOp, hDirect, hArgs, hSeq,
                            hOutputs] at hLower
                          rw [hLower.1]
                          simp [FunctionsInteractionTargetCost.list, expr]
                        · simp [Expr.lowerUnchecked?, hOp, hDirect, hArgs, hSeq,
                            hOutputs] at hLower
    | case10 state =>
        rename_i listPre listLower listFinal hList
        simp [Expr.List.lowerBound1Unchecked?] at hList
        rw [hList.1]
        simp [FunctionsInteractionTargetCost.list, exprList]
    | case11 state source rest ihRest ihSource =>
        rename_i listPre listLower listFinal hList
        cases hRest : Expr.List.lowerBound1Unchecked? state rest with
        | none =>
            simp [Expr.List.lowerBound1Unchecked?, hRest] at hList
        | some restResult =>
            rcases restResult with ⟨preRest, lowerRest, stateAfterRest⟩
            cases hHead : Expr.lowerUnchecked? 1 stateAfterRest source with
            | none =>
                simp [Expr.List.lowerBound1Unchecked?, hRest, hHead] at hList
            | some headResult =>
                rcases headResult with ⟨preHead, lowerHead, stateAfterHead⟩
                by_cases hDeferred :
                    Expr.deferredBoundArgSafe? source = true ∧
                      lowerRest.length < 4
                · simp [Expr.List.lowerBound1Unchecked?, hRest, hHead,
                    hDeferred] at hList
                  rw [← hList.1,
                    FunctionsInteractionTargetCost.list_append]
                  have hRestCost := ihRest _ _ _ hRest
                  have hHeadCost := ihSource _ hHead
                  simp [exprList]
                  omega
                · cases hFresh : Fresh.fresh? stateAfterHead with
                  | none =>
                      simp [Expr.List.lowerBound1Unchecked?, hRest, hHead,
                        hDeferred, hFresh] at hList
                  | some freshResult =>
                      rcases freshResult with ⟨tmp, stateAfterFresh⟩
                      simp [Expr.List.lowerBound1Unchecked?, hRest, hHead,
                        hDeferred, hFresh] at hList
                      rw [← hList.1,
                        FunctionsInteractionTargetCost.list_append,
                        FunctionsInteractionTargetCost.list_append]
                      have hRestCost := ihRest _ _ _ hRest
                      have hHeadCost := ihSource _ hHead
                      simp [FunctionsInteractionTargetCost.list,
                        FunctionsInteractionTargetCost.stmt, exprList]
                      omega
theorem lower1Unchecked?_cost
    {state final : Fresh.State} {source : AstExpr}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    (hLower : Expr.lower1Unchecked? state source =
      some (pre, lower, final)) :
    FunctionsInteractionTargetCost.list pre ≤ expr source :=
  lowerUnchecked?_cost hLower

theorem lowerBound1Unchecked?_cost
    {state final : Fresh.State} {sources : List AstExpr}
    {pre : List Functions.Stmt} {lower : List (Locals.Expr 1)}
    (hLower : Expr.List.lowerBound1Unchecked? state sources =
      some (pre, lower, final)) :
    FunctionsInteractionTargetCost.list pre ≤ exprList sources := by
  induction sources generalizing state pre lower final with
  | nil =>
      simp [Expr.List.lowerBound1Unchecked?] at hLower
      rw [hLower.1]
      simp [FunctionsInteractionTargetCost.list, exprList]
  | cons source rest ih =>
      cases hRest : Expr.List.lowerBound1Unchecked? state rest with
      | none =>
          simp [Expr.List.lowerBound1Unchecked?, hRest] at hLower
      | some restResult =>
          rcases restResult with ⟨preRest, lowerRest, stateAfterRest⟩
          cases hHead : Expr.lowerUnchecked? 1 stateAfterRest source with
          | none =>
              simp [Expr.List.lowerBound1Unchecked?, hRest, hHead] at hLower
          | some headResult =>
              rcases headResult with ⟨preHead, lowerHead, stateAfterHead⟩
              by_cases hDeferred :
                  Expr.deferredBoundArgSafe? source = true ∧
                    lowerRest.length < 4
              · simp [Expr.List.lowerBound1Unchecked?, hRest, hHead,
                  hDeferred] at hLower
                rw [← hLower.1,
                  FunctionsInteractionTargetCost.list_append]
                have hRestCost := ih hRest
                have hHeadCost := lowerUnchecked?_cost hHead
                simp [exprList]
                omega
              · cases hFresh : Fresh.fresh? stateAfterHead with
                | none =>
                    simp [Expr.List.lowerBound1Unchecked?, hRest, hHead,
                      hDeferred, hFresh] at hLower
                | some freshResult =>
                    rcases freshResult with ⟨tmp, stateAfterFresh⟩
                    simp [Expr.List.lowerBound1Unchecked?, hRest, hHead,
                      hDeferred, hFresh] at hLower
                    rw [← hLower.1,
                      FunctionsInteractionTargetCost.list_append,
                      FunctionsInteractionTargetCost.list_append]
                    have hRestCost := ih hRest
                    have hHeadCost := lowerUnchecked?_cost hHead
                    simp [FunctionsInteractionTargetCost.list,
                      FunctionsInteractionTargetCost.stmt, exprList]
                    omega

mutual
  def stmt : AstStmt → Nat
    | .Block body => stmtList body + 2
    | .Let names none => 2 * names.length
    | .Let names (some value) => 2 * names.length + expr value + 2
    | .Assign _ value => expr value + 2
    | .ExprStmtCall value => expr value + 2
    | .Switch value cases defaultBody =>
        expr value + caseList cases + stmtList defaultBody + 3
    | .For cond post body =>
        expr cond + stmtList post + stmtList body + 6
    | .If cond body => expr cond + stmtList body + 2
    | .Continue | .Break | .Leave => 2

  def stmtList : List AstStmt → Nat
    | [] => 0
    | head :: tail => stmt head + stmtList tail

  def caseList : List (Word × List AstStmt) → Nat
    | [] => 0
    | (_, body) :: tail => stmtList body + caseList tail + 1
end

@[simp] theorem initNames_cost (names : List Name) :
    FunctionsInteractionTargetCost.list (Stmt.initNames names) =
      2 * names.length := by
  induction names with
  | nil => simp [Stmt.initNames, FunctionsInteractionTargetCost.list]
  | cons name names ih =>
      change
        FunctionsInteractionTargetCost.list
            (Functions.Stmt.let_ name (.lit Stmt.zero) ::
              Stmt.initNames names) =
          2 * (names.length + 1)
      simp [FunctionsInteractionTargetCost.list,
        FunctionsInteractionTargetCost.stmt, ih]
      omega

/-- The recursive target-syntax cost of every successful ordinary statement,
statement list, block, and switch-case lowering is bounded by source syntax. -/
theorem toFunctionsListUncheckedFuel?_cost
    {fuel : Nat} {before after : Fresh.State} {source : AstStmt}
    {lower : List Functions.Stmt}
    (hLower : Stmt.toFunctionsListUncheckedFuel? fuel before source =
      some (lower, after)) :
    FunctionsInteractionTargetCost.list lower ≤ stmt source := by
  induction fuel, before, source using
      Stmt.toFunctionsListUncheckedFuel?.induct
        (motive_2 := fun fuel before sources =>
          ∀ {lower after},
            Stmt.CaseList.toFunctionsUncheckedFuel? fuel before sources =
                some (lower, after) →
              FunctionsInteractionTargetCost.caseList lower ≤ caseList sources)
        (motive_3 := fun fuel before sources =>
          ∀ {lower after},
            Stmt.List.toBlockUncheckedFuel? fuel before sources =
                some (lower, after) →
              FunctionsInteractionTargetCost.block lower ≤ stmtList sources)
        (motive_4 := fun fuel before sources =>
          ∀ {lower after},
            Stmt.List.toFunctionsUncheckedFuel? fuel before sources =
                some (lower, after) →
              FunctionsInteractionTargetCost.list lower ≤ stmtList sources)
        generalizing lower after with
  | case1 =>
      simp [Stmt.toFunctionsListUncheckedFuel?] at hLower
  | case2 =>
      rename_i fuel before body ih
      cases hBody : Stmt.List.toBlockUncheckedFuel? fuel before body with
      | none => simp [Stmt.toFunctionsListUncheckedFuel?, hBody] at hLower
      | some result =>
          rcases result with ⟨lowerBody, middle⟩
          simp [Stmt.toFunctionsListUncheckedFuel?, hBody] at hLower
          rw [← hLower.1]
          have hCost := ih hBody
          simp [stmt, FunctionsInteractionTargetCost.list,
            FunctionsInteractionTargetCost.stmt]
          omega
  | case3 =>
      rename_i fuel before names
      simp [Stmt.toFunctionsListUncheckedFuel?] at hLower
      rw [← hLower.1]
      simp [stmt, identNames_eq_self]
  | case4 =>
      rename_i fuel before functionName args hUnsupported
      simp [Stmt.toFunctionsListUncheckedFuel?, hUnsupported] at hLower
  | case5 =>
      rename_i fuel before functionName args hSupported hDirect
      cases hArgs : Expr.List.toLocals1? args with
      | none =>
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hDirect, hArgs]
            at hLower
      | some lowerArgs =>
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hDirect, hArgs]
            at hLower
          rw [← hLower.1]
          simp [stmt, expr, FunctionsInteractionTargetCost.list,
            FunctionsInteractionTargetCost.stmt]
  | case6 =>
      rename_i fuel before functionName args hSupported hBound
      cases hArgs : Expr.List.lowerBound1Unchecked? before args with
      | none =>
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hBound, hArgs]
            at hLower
      | some result =>
          rcases result with ⟨preArgs, lowerArgs, middle⟩
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hBound, hArgs]
            at hLower
          rw [← hLower.1, FunctionsInteractionTargetCost.list_append]
          have hPre := lowerBound1Unchecked?_cost hArgs
          simp [stmt, expr, FunctionsInteractionTargetCost.list,
            FunctionsInteractionTargetCost.stmt]
          omega
  | case7 =>
      rename_i fuel before name functionName args hUnsupported
      simp [Stmt.toFunctionsListUncheckedFuel?, hUnsupported] at hLower
  | case8 =>
      rename_i fuel before name functionName args hSupported hDirect
      cases hArgs : Expr.List.toLocals1? args with
      | none =>
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hDirect, hArgs]
            at hLower
      | some lowerArgs =>
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hDirect, hArgs]
            at hLower
          rw [← hLower.1, FunctionsInteractionTargetCost.list_append]
          simp [stmt, expr, identNames_eq_self,
            FunctionsInteractionTargetCost.list,
            FunctionsInteractionTargetCost.stmt]
  | case9 =>
      rename_i fuel before name functionName args hSupported hBound
      cases hArgs : Expr.List.lowerBound1Unchecked? before args with
      | none =>
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hBound, hArgs]
            at hLower
      | some result =>
          rcases result with ⟨preArgs, lowerArgs, middle⟩
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hBound, hArgs]
            at hLower
          rw [← hLower.1, FunctionsInteractionTargetCost.list_append,
            FunctionsInteractionTargetCost.list_append]
          have hPre := lowerBound1Unchecked?_cost hArgs
          simp [stmt, expr, identNames_eq_self,
            FunctionsInteractionTargetCost.list,
            FunctionsInteractionTargetCost.stmt]
          omega
  | case10 =>
      rename_i fuel before name value hNotCall
      rw [Stmt.toFunctionsListUncheckedFuel?_let_one_noncall
        fuel before name value hNotCall] at hLower
      cases hValue : Expr.lower1Unchecked? before value with
      | none => simp [hValue] at hLower
      | some result =>
          rcases result with ⟨preValue, lowerValue, middle⟩
          simp [hValue] at hLower
          rw [← hLower.1, FunctionsInteractionTargetCost.list_append]
          have hPre := lower1Unchecked?_cost hValue
          simp [stmt, FunctionsInteractionTargetCost.list,
            FunctionsInteractionTargetCost.stmt]
          omega
  | case11 =>
      rename_i fuel before name next rest functionName args hUnsupported
      simp [Stmt.toFunctionsListUncheckedFuel?, hUnsupported] at hLower
  | case12 =>
      rename_i fuel before name next rest functionName args hSupported hDirect
      cases hArgs : Expr.List.toLocals1? args with
      | none =>
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hDirect, hArgs]
            at hLower
      | some lowerArgs =>
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hDirect, hArgs]
            at hLower
          rw [← hLower.1, FunctionsInteractionTargetCost.list_append]
          simp [stmt, expr, identNames_eq_self,
            FunctionsInteractionTargetCost.list,
            FunctionsInteractionTargetCost.stmt]
  | case13 =>
      rename_i fuel before name next rest functionName args hSupported hBound
      cases hArgs : Expr.List.lowerBound1Unchecked? before args with
      | none =>
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hBound, hArgs]
            at hLower
      | some result =>
          rcases result with ⟨preArgs, lowerArgs, middle⟩
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hBound, hArgs]
            at hLower
          rw [← hLower.1, FunctionsInteractionTargetCost.list_append,
            FunctionsInteractionTargetCost.list_append]
          have hPre := lowerBound1Unchecked?_cost hArgs
          simp [stmt, expr, identNames_eq_self,
            FunctionsInteractionTargetCost.list,
            FunctionsInteractionTargetCost.stmt]
          omega
  | case14 =>
      rename_i fuel before names value hNotEmpty hNotSingleCall
        hNotSingle hNotMultiCall
      cases names with
      | nil =>
          cases value with
          | Call callee args =>
              cases callee with
              | inl prim =>
                  change
                    (none : Option (List Functions.Stmt × Fresh.State)) =
                      some (lower, after) at hLower
                  cases hLower
              | inr functionName =>
                  exact (hNotEmpty functionName args rfl rfl).elim
          | _ =>
              change
                (none : Option (List Functions.Stmt × Fresh.State)) =
                  some (lower, after) at hLower
              cases hLower
      | cons name tail =>
          cases tail with
          | nil => exact (hNotSingle name rfl).elim
          | cons next rest =>
              cases value with
              | Call callee args =>
                  cases callee with
                  | inl prim =>
                      change
                        (none : Option (List Functions.Stmt × Fresh.State)) =
                          some (lower, after) at hLower
                      cases hLower
                  | inr functionName =>
                      exact
                        (hNotMultiCall name next rest functionName args
                          rfl rfl).elim
              | _ =>
                  change
                    (none : Option (List Functions.Stmt × Fresh.State)) =
                      some (lower, after) at hLower
                  cases hLower
  | case15 =>
      rename_i fuel before functionName args hUnsupported
      simp [Stmt.toFunctionsListUncheckedFuel?, hUnsupported] at hLower
  | case16 =>
      rename_i fuel before functionName args hSupported hDirect
      cases hArgs : Expr.List.toLocals1? args with
      | none =>
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hDirect, hArgs]
            at hLower
      | some lowerArgs =>
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hDirect, hArgs]
            at hLower
          rw [← hLower.1]
          simp [stmt, expr, FunctionsInteractionTargetCost.list,
            FunctionsInteractionTargetCost.stmt]
  | case17 =>
      rename_i fuel before functionName args hSupported hBound
      cases hArgs : Expr.List.lowerBound1Unchecked? before args with
      | none =>
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hBound, hArgs]
            at hLower
      | some result =>
          rcases result with ⟨preArgs, lowerArgs, middle⟩
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hBound, hArgs]
            at hLower
          rw [← hLower.1, FunctionsInteractionTargetCost.list_append]
          have hPre := lowerBound1Unchecked?_cost hArgs
          simp [stmt, expr, FunctionsInteractionTargetCost.list,
            FunctionsInteractionTargetCost.stmt]
          omega
  | case18 =>
      rename_i fuel before name functionName args hUnsupported
      simp [Stmt.toFunctionsListUncheckedFuel?, hUnsupported] at hLower
  | case19 =>
      rename_i fuel before name functionName args hSupported hDirect
      cases hArgs : Expr.List.toLocals1? args with
      | none =>
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hDirect, hArgs]
            at hLower
      | some lowerArgs =>
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hDirect, hArgs]
            at hLower
          rw [← hLower.1]
          simp [stmt, expr, FunctionsInteractionTargetCost.list,
            FunctionsInteractionTargetCost.stmt]
  | case20 =>
      rename_i fuel before name functionName args hSupported hBound
      cases hArgs : Expr.List.lowerBound1Unchecked? before args with
      | none =>
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hBound, hArgs]
            at hLower
      | some result =>
          rcases result with ⟨preArgs, lowerArgs, middle⟩
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hBound, hArgs]
            at hLower
          rw [← hLower.1, FunctionsInteractionTargetCost.list_append]
          have hPre := lowerBound1Unchecked?_cost hArgs
          simp [stmt, expr, FunctionsInteractionTargetCost.list,
            FunctionsInteractionTargetCost.stmt]
          omega
  | case21 =>
      rename_i fuel before name value hNotCall
      rw [Stmt.toFunctionsListUncheckedFuel?_assign_one_noncall
        fuel before name value hNotCall] at hLower
      cases hValue : Expr.lower1Unchecked? before value with
      | none => simp [hValue] at hLower
      | some result =>
          rcases result with ⟨preValue, lowerValue, middle⟩
          simp [hValue] at hLower
          rw [← hLower.1, FunctionsInteractionTargetCost.list_append]
          have hPre := lower1Unchecked?_cost hValue
          simp [stmt, FunctionsInteractionTargetCost.list,
            FunctionsInteractionTargetCost.stmt]
          omega
  | case22 =>
      rename_i fuel before name next rest functionName args hUnsupported
      simp [Stmt.toFunctionsListUncheckedFuel?, hUnsupported] at hLower
  | case23 =>
      rename_i fuel before name next rest functionName args hSupported hDirect
      cases hArgs : Expr.List.toLocals1? args with
      | none =>
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hDirect, hArgs]
            at hLower
      | some lowerArgs =>
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hDirect, hArgs]
            at hLower
          rw [← hLower.1]
          simp [stmt, expr, FunctionsInteractionTargetCost.list,
            FunctionsInteractionTargetCost.stmt]
  | case24 =>
      rename_i fuel before name next rest functionName args hSupported hBound
      cases hArgs : Expr.List.lowerBound1Unchecked? before args with
      | none =>
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hBound, hArgs]
            at hLower
      | some result =>
          rcases result with ⟨preArgs, lowerArgs, middle⟩
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hBound, hArgs]
            at hLower
          rw [← hLower.1, FunctionsInteractionTargetCost.list_append]
          have hPre := lowerBound1Unchecked?_cost hArgs
          simp [stmt, expr, FunctionsInteractionTargetCost.list,
            FunctionsInteractionTargetCost.stmt]
          omega
  | case25 =>
      rename_i fuel before names value hNotEmpty hNotSingleCall
        hNotSingle hNotMultiCall
      cases names with
      | nil =>
          cases value with
          | Call callee args =>
              cases callee with
              | inl prim =>
                  change
                    (none : Option (List Functions.Stmt × Fresh.State)) =
                      some (lower, after) at hLower
                  cases hLower
              | inr functionName =>
                  exact (hNotEmpty functionName args rfl rfl).elim
          | _ =>
              change
                (none : Option (List Functions.Stmt × Fresh.State)) =
                  some (lower, after) at hLower
              cases hLower
      | cons name tail =>
          cases tail with
          | nil => exact (hNotSingle name rfl).elim
          | cons next rest =>
              cases value with
              | Call callee args =>
                  cases callee with
                  | inl prim =>
                      change
                        (none : Option (List Functions.Stmt × Fresh.State)) =
                          some (lower, after) at hLower
                      cases hLower
                  | inr functionName =>
                      exact
                        (hNotMultiCall name next rest functionName args
                          rfl rfl).elim
              | _ =>
                  change
                    (none : Option (List Functions.Stmt × Fresh.State)) =
                      some (lower, after) at hLower
                  cases hLower
  | case26 =>
      rename_i fuel before functionName args hUnsupported
      simp [Stmt.toFunctionsListUncheckedFuel?, hUnsupported] at hLower
  | case27 =>
      rename_i fuel before functionName args hSupported hDirect
      cases hArgs : Expr.List.toLocals1? args with
      | none =>
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hDirect, hArgs]
            at hLower
      | some lowerArgs =>
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hDirect, hArgs]
            at hLower
          rw [← hLower.1]
          simp [stmt, expr, FunctionsInteractionTargetCost.list,
            FunctionsInteractionTargetCost.stmt]
  | case28 =>
      rename_i fuel before functionName args hSupported hBound
      cases hArgs : Expr.List.lowerBound1Unchecked? before args with
      | none =>
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hBound, hArgs]
            at hLower
      | some result =>
          rcases result with ⟨preArgs, lowerArgs, middle⟩
          simp [Stmt.toFunctionsListUncheckedFuel?, hSupported, hBound, hArgs]
            at hLower
          rw [← hLower.1, FunctionsInteractionTargetCost.list_append]
          have hPre := lowerBound1Unchecked?_cost hArgs
          simp [stmt, expr, FunctionsInteractionTargetCost.list,
            FunctionsInteractionTargetCost.stmt]
          omega
  | case29 =>
      rename_i fuel before prim args kind hTerminal
      cases hArgs : Expr.List.lowerBound1Unchecked? before args with
      | none =>
          simp [Stmt.toFunctionsListUncheckedFuel?, hTerminal, hArgs] at hLower
      | some result =>
          rcases result with ⟨preArgs, lowerArgs, middle⟩
          cases hSeq : Expr.List.toStackSeq? lowerArgs kind.argCount with
          | none =>
              simp [Stmt.toFunctionsListUncheckedFuel?, hTerminal, hArgs, hSeq]
                at hLower
          | some seq =>
              simp [Stmt.toFunctionsListUncheckedFuel?, hTerminal, hArgs, hSeq]
                at hLower
              rw [← hLower.1, FunctionsInteractionTargetCost.list_append]
              have hPre := lowerBound1Unchecked?_cost hArgs
              simp [stmt, expr, FunctionsInteractionTargetCost.list,
                FunctionsInteractionTargetCost.stmt]
              omega
  | case30 =>
      rename_i fuel before prim args hTerminal
      cases hExpr : Expr.lower0Unchecked? before (.Call (.inl prim) args) with
      | none =>
          simp [Stmt.toFunctionsListUncheckedFuel?, hTerminal, hExpr] at hLower
      | some result =>
          rcases result with ⟨preExpr, lowerExpr, middle⟩
          simp [Stmt.toFunctionsListUncheckedFuel?, hTerminal, hExpr] at hLower
          rw [← hLower.1, FunctionsInteractionTargetCost.list_append]
          have hPre := lowerUnchecked?_cost hExpr
          simp [stmt, FunctionsInteractionTargetCost.list,
            FunctionsInteractionTargetCost.stmt]
          omega
  | case31 =>
      rename_i fuel before value hNotFunctionCall hNotPrimitiveCall
      rw [Stmt.toFunctionsListUncheckedFuel?_expr_noncall
        fuel before value hNotFunctionCall hNotPrimitiveCall] at hLower
      cases hExpr : Expr.lower0Unchecked? before value with
      | none => simp [hExpr] at hLower
      | some result =>
          rcases result with ⟨preExpr, lowerExpr, middle⟩
          simp [hExpr] at hLower
          rw [← hLower.1, FunctionsInteractionTargetCost.list_append]
          have hPre := lowerUnchecked?_cost hExpr
          simp [stmt, FunctionsInteractionTargetCost.list,
            FunctionsInteractionTargetCost.stmt]
          omega
  | case32 =>
      rename_i fuel before scrutinee cases defaultBody ihCases ihDefault
      cases hScrutinee : Expr.lower1Unchecked? before scrutinee with
      | none =>
          simp [Stmt.toFunctionsListUncheckedFuel?, hScrutinee] at hLower
      | some scrutineeResult =>
          rcases scrutineeResult with
            ⟨preScrutinee, lowerScrutinee, afterScrutinee⟩
          cases hCases :
              Stmt.CaseList.toFunctionsUncheckedFuel?
                fuel afterScrutinee cases with
          | none =>
              simp [Stmt.toFunctionsListUncheckedFuel?, hScrutinee, hCases]
                at hLower
          | some casesResult =>
              rcases casesResult with ⟨lowerCases, afterCases⟩
              cases defaultBody with
              | nil =>
                  simp [Stmt.toFunctionsListUncheckedFuel?, hScrutinee, hCases]
                    at hLower
                  rw [← hLower.1,
                    FunctionsInteractionTargetCost.list_append]
                  have hPre := lower1Unchecked?_cost hScrutinee
                  have hCasesCost := ihCases _ hCases
                  simp [stmt, stmtList,
                    FunctionsInteractionTargetCost.list,
                    FunctionsInteractionTargetCost.stmt,
                    FunctionsInteractionTargetCost.optionBlock]
                  omega
              | cons defaultHead defaultTail =>
                  cases hDefault :
                      Stmt.List.toBlockUncheckedFuel? fuel afterCases
                        (defaultHead :: defaultTail) with
                  | none =>
                      simp [Stmt.toFunctionsListUncheckedFuel?, hScrutinee,
                        hCases, hDefault] at hLower
                  | some defaultResult =>
                      rcases defaultResult with
                        ⟨lowerDefault, afterDefault⟩
                      simp [Stmt.toFunctionsListUncheckedFuel?, hScrutinee,
                        hCases, hDefault] at hLower
                      rw [← hLower.1,
                        FunctionsInteractionTargetCost.list_append]
                      have hPre := lower1Unchecked?_cost hScrutinee
                      have hCasesCost := ihCases _ hCases
                      have hDefaultCost := ihDefault _ hDefault
                      simp [stmt, FunctionsInteractionTargetCost.list,
                        FunctionsInteractionTargetCost.stmt,
                        FunctionsInteractionTargetCost.optionBlock]
                      omega
  | case33 =>
      rename_i fuel before cond post body ihPost ihBody
      cases hCond : Expr.lower1Unchecked? before cond with
      | none => simp [Stmt.toFunctionsListUncheckedFuel?, hCond] at hLower
      | some condResult =>
          rcases condResult with ⟨preCond, lowerCond, afterCond⟩
          cases hPost :
              Stmt.List.toBlockUncheckedFuel? fuel afterCond post with
          | none =>
              simp [Stmt.toFunctionsListUncheckedFuel?, hCond, hPost] at hLower
          | some postResult =>
              rcases postResult with ⟨lowerPost, afterPost⟩
              cases hBody :
                  Stmt.List.toBlockUncheckedFuel? fuel afterPost body with
              | none =>
                  simp [Stmt.toFunctionsListUncheckedFuel?, hCond, hPost,
                    hBody] at hLower
              | some bodyResult =>
                  rcases bodyResult with ⟨lowerBody, afterBody⟩
                  simp [Stmt.toFunctionsListUncheckedFuel?, hCond, hPost,
                    hBody] at hLower
                  rw [← hLower.1]
                  have hPre := lower1Unchecked?_cost hCond
                  have hPostCost := ihPost _ hPost
                  have hBodyCost := ihBody _ hBody
                  have hPostListCost :
                      FunctionsInteractionTargetCost.list lowerPost.stmts ≤
                        stmtList post := by
                    simpa [FunctionsInteractionTargetCost.block] using hPostCost
                  have hBodyListCost :
                      FunctionsInteractionTargetCost.list lowerBody.stmts ≤
                        stmtList body := by
                    simpa [FunctionsInteractionTargetCost.block] using hBodyCost
                  simp [stmt, FunctionsInteractionTargetCost.list,
                    FunctionsInteractionTargetCost.stmt,
                    FunctionsInteractionTargetCost.block,
                    FunctionsInteractionTargetCost.list_append]
                  omega
  | case34 =>
      rename_i fuel before cond body ihBody
      cases hCond : Expr.lower1Unchecked? before cond with
      | none => simp [Stmt.toFunctionsListUncheckedFuel?, hCond] at hLower
      | some condResult =>
          rcases condResult with ⟨preCond, lowerCond, afterCond⟩
          cases hBody :
              Stmt.List.toBlockUncheckedFuel? fuel afterCond body with
          | none =>
              simp [Stmt.toFunctionsListUncheckedFuel?, hCond, hBody] at hLower
          | some bodyResult =>
              rcases bodyResult with ⟨lowerBody, afterBody⟩
              simp [Stmt.toFunctionsListUncheckedFuel?, hCond, hBody] at hLower
              rw [← hLower.1, FunctionsInteractionTargetCost.list_append]
              have hPre := lower1Unchecked?_cost hCond
              have hBodyCost := ihBody _ hBody
              simp [stmt, FunctionsInteractionTargetCost.list,
                FunctionsInteractionTargetCost.stmt]
              omega
  | case35 =>
      simp [Stmt.toFunctionsListUncheckedFuel?] at hLower
      rw [← hLower.1]
      simp [stmt, FunctionsInteractionTargetCost.list,
        FunctionsInteractionTargetCost.stmt]
  | case36 =>
      simp [Stmt.toFunctionsListUncheckedFuel?] at hLower
      rw [← hLower.1]
      simp [stmt, FunctionsInteractionTargetCost.list,
        FunctionsInteractionTargetCost.stmt]
  | case37 =>
      simp [Stmt.toFunctionsListUncheckedFuel?] at hLower
      rw [← hLower.1]
      simp [stmt, FunctionsInteractionTargetCost.list,
        FunctionsInteractionTargetCost.stmt]
  | case38 =>
      rename_i before cases lower after hLower
      simp [Stmt.CaseList.toFunctionsUncheckedFuel?] at hLower
  | case39 =>
      rename_i fuel before lower after hLower
      simp [Stmt.CaseList.toFunctionsUncheckedFuel?] at hLower
      rw [hLower.1]
      simp [FunctionsInteractionTargetCost.caseList, caseList]
  | case40 =>
      rename_i fuel before value body rest ihBody ihRest lower after hLower
      cases hBody : Stmt.List.toBlockUncheckedFuel? fuel before body with
      | none =>
          simp [Stmt.CaseList.toFunctionsUncheckedFuel?, hBody] at hLower
      | some bodyResult =>
          rcases bodyResult with ⟨lowerBody, afterBody⟩
          cases hRest :
              Stmt.CaseList.toFunctionsUncheckedFuel? fuel afterBody rest with
          | none =>
              simp [Stmt.CaseList.toFunctionsUncheckedFuel?, hBody, hRest]
                at hLower
          | some restResult =>
              rcases restResult with ⟨lowerRest, afterRest⟩
              simp [Stmt.CaseList.toFunctionsUncheckedFuel?, hBody, hRest]
                at hLower
              rw [← hLower.1]
              have hBodyCost := ihBody hBody
              have hRestCost := ihRest _ hRest
              simp [FunctionsInteractionTargetCost.caseList, caseList]
              omega
  | case41 =>
      rename_i before sources lower after hLower
      simp [Stmt.List.toBlockUncheckedFuel?] at hLower
  | case42 =>
      rename_i fuel before sources ih lower after hLower
      cases hSources :
          Stmt.List.toFunctionsUncheckedFuel? fuel before sources with
      | none =>
          simp [Stmt.List.toBlockUncheckedFuel?, hSources] at hLower
      | some sourcesResult =>
          rcases sourcesResult with ⟨lowerSources, afterSources⟩
          simp [Stmt.List.toBlockUncheckedFuel?, hSources] at hLower
          rw [← hLower.1]
          simpa [FunctionsInteractionTargetCost.block] using ih hSources
  | case43 =>
      rename_i before sources lower after hLower
      simp [Stmt.List.toFunctionsUncheckedFuel?] at hLower
  | case44 =>
      rename_i fuel before lower after hLower
      simp [Stmt.List.toFunctionsUncheckedFuel?] at hLower
      rw [hLower.1]
      simp [FunctionsInteractionTargetCost.list, stmtList]
  | case45 =>
      rename_i fuel before source rest ihSource ihRest lower after hLower
      cases hSource :
          Stmt.toFunctionsListUncheckedFuel? fuel before source with
      | none =>
          simp [Stmt.List.toFunctionsUncheckedFuel?, hSource] at hLower
      | some sourceResult =>
          rcases sourceResult with ⟨lowerSource, afterSource⟩
          cases hRest :
              Stmt.List.toFunctionsUncheckedFuel? fuel afterSource rest with
          | none =>
              simp [Stmt.List.toFunctionsUncheckedFuel?, hSource, hRest]
                at hLower
          | some restResult =>
              rcases restResult with ⟨lowerRest, afterRest⟩
              simp [Stmt.List.toFunctionsUncheckedFuel?, hSource, hRest]
                at hLower
              rw [← hLower.1,
                FunctionsInteractionTargetCost.list_append]
              have hSourceCost := ihSource hSource
              have hRestCost := ihRest _ hRest
              simp [stmtList]
              omega

/-- Block lowering inherits the statement theorem without exposing the
generated block at a source-facing boundary. -/
theorem toBlockUncheckedFuel?_cost
    {fuel : Nat} {before after : Fresh.State} {source : List AstStmt}
    {lower : Functions.Block}
    (hLower : Stmt.List.toBlockUncheckedFuel? fuel before source =
      some (lower, after)) :
    FunctionsInteractionTargetCost.block lower ≤ stmtList source := by
  have hStmt :
      Stmt.toFunctionsListUncheckedFuel? (fuel + 1) before (.Block source) =
        some ([Functions.Stmt.block lower], after) := by
    simp [Stmt.toFunctionsListUncheckedFuel?, hLower]
  have hCost := toFunctionsListUncheckedFuel?_cost hStmt
  simp [stmt, FunctionsInteractionTargetCost.list,
    FunctionsInteractionTargetCost.stmt] at hCost
  omega

/-- List lowering is bounded by the same source-only recursive expansion
measure, independently of the generated statements themselves. -/
theorem toFunctionsUncheckedFuel?_cost
    {fuel : Nat} {before after : Fresh.State} {source : List AstStmt}
    {lower : List Functions.Stmt}
    (hLower : Stmt.List.toFunctionsUncheckedFuel? fuel before source =
      some (lower, after)) :
    FunctionsInteractionTargetCost.list lower ≤ stmtList source := by
  have hBlock :
      Stmt.List.toBlockUncheckedFuel? (fuel + 1) before source =
        some ({ stmts := lower }, after) := by
    simp [Stmt.List.toBlockUncheckedFuel?, hLower]
  simpa [FunctionsInteractionTargetCost.block] using
    toBlockUncheckedFuel?_cost hBlock

end FunctionsInteractionCompilerCost
end Yul
end EvmCompiler
