import EvmCompiler.Functions.EffectSemanticsInversion
import EvmCompiler.Yul.Compiler

namespace EvmCompiler
namespace Yul
namespace Expr

/-!
Pass-owned decomposition facts for the Yul expression compiler.

Expression preludes contain only generated bindings and ordinary function
calls. Consequently, a successful Functions execution of such a prelude can
only return regularly or propagate a terminal halt; it cannot manufacture
structured statement control such as break, continue, or leave.
-/

inductive PreludeStmt : Functions.Stmt → Prop where
  | let_ (name : Name) (value : Functions.Expr 1) :
      PreludeStmt (.let_ name value)
  | call (targets : List Name) (functionName : Name)
      (args : List (Functions.Expr 1)) :
      PreludeStmt (.call targets functionName args)

def Prelude (stmts : List Functions.Stmt) : Prop :=
  ∀ stmt, stmt ∈ stmts → PreludeStmt stmt

namespace Prelude

theorem nil : Prelude [] := by
  intro stmt hMem
  simp at hMem

theorem append {left right : List Functions.Stmt}
    (hLeft : Prelude left) (hRight : Prelude right) :
    Prelude (left ++ right) := by
  intro stmt hMem
  rcases List.mem_append.mp hMem with hMem | hMem
  · exact hLeft stmt hMem
  · exact hRight stmt hMem

theorem let_ (name : Name) (value : Functions.Expr 1) :
    Prelude [.let_ name value] := by
  intro stmt hMem
  simp only [List.mem_singleton] at hMem
  subst stmt
  exact PreludeStmt.let_ _ _

theorem call (targets : List Name) (functionName : Name)
    (args : List (Functions.Expr 1)) :
    Prelude [.call targets functionName args] := by
  intro stmt hMem
  simp only [List.mem_singleton] at hMem
  subst stmt
  exact PreludeStmt.call _ _ _

theorem letCall (tmp : Name) (functionName : Name)
    (args : List (Functions.Expr 1)) :
    Prelude
      [.let_ tmp (.lit (EvmYul.UInt256.ofNat 0)),
        .call [tmp] functionName args] := by
  intro stmt hMem
  simp only [List.mem_cons, List.mem_singleton] at hMem
  rcases hMem with rfl | hMem
  · exact PreludeStmt.let_ _ _
  · rcases hMem with rfl | hMem
    · exact PreludeStmt.call _ _ _
    · simp at hMem

theorem stmt_run_regular_or_halt
    {σ : Type}
    (model : Functions.Source.Effectful.StateModel σ)
    (prim : Functions.Source.Effectful.PrimitiveSemantics σ)
    (program : Functions.Program)
    {ctx finalCtx : Functions.Source.Ctx}
    {fuel : Nat} {stmt : Functions.Stmt}
    {source : σ}
    {outcome : Functions.Source.Effectful.Outcome σ}
    (hPrelude : PreludeStmt stmt)
    (hRun :
      Functions.Source.Effectful.Stmt.run model prim program ctx fuel
          stmt source =
        .ok (outcome, finalCtx)) :
    outcome.mode = .regular ∨
      ∃ kind, outcome.mode = .halt kind := by
  cases hPrelude with
  | let_ name value =>
      unfold Functions.Source.Effectful.Stmt.run at hRun
      cases hEval :
          Functions.Source.Effectful.Expr.evalOne
            model prim value source with
      | error err =>
          simp [hEval] at hRun
      | ok evaluated =>
          rcases evaluated with ⟨afterValue, result⟩
          simp [hEval] at hRun
          rcases hRun with ⟨hOutcome, _hCtx⟩
          rw [← hOutcome]
          exact Or.inl rfl
  | call targets functionName args =>
      cases fuel with
      | zero =>
          simp [Functions.Source.Effectful.Stmt.run,
            Functions.Source.invalid, Structured.invalid] at hRun
      | succ previous =>
          rcases
              Functions.Source.Effectful.Stmt.run_call_cases
                model prim program hRun with
            hRegular | hHalt
          · rcases hRegular with ⟨final, hOutcome, _hCtx⟩
            rw [hOutcome]
            exact Or.inl rfl
          · rcases hHalt with ⟨kind, final, hOutcome, _hCtx⟩
            rw [hOutcome]
            exact Or.inr ⟨kind, rfl⟩

theorem runOpen_regular_or_halt
    {σ : Type}
    (model : Functions.Source.Effectful.StateModel σ)
    (prim : Functions.Source.Effectful.PrimitiveSemantics σ)
    (program : Functions.Program) :
    ∀ {stmts : List Functions.Stmt}
      {ctx finalCtx : Functions.Source.Ctx}
      {fuel : Nat} {source : σ}
      {outcome : Functions.Source.Effectful.Outcome σ},
      Prelude stmts →
      Functions.Source.Effectful.Block.runOpen
          model prim program ctx fuel { stmts := stmts } source =
        .ok (outcome, finalCtx) →
      outcome.mode = .regular ∨
        ∃ kind, outcome.mode = .halt kind := by
  intro stmts
  induction stmts with
  | nil =>
      intro ctx finalCtx fuel source outcome _hPrelude hRun
      obtain ⟨hOutcome, _hCtx⟩ :=
        Functions.Source.Effectful.Block.runOpen_nil_ok
          model prim program hRun
      rw [hOutcome]
      exact Or.inl rfl
  | cons head tail ih =>
      intro ctx finalCtx fuel source outcome hPrelude hRun
      cases fuel with
      | zero =>
          simp [Functions.Source.Effectful.Block.runOpen,
            Functions.Source.invalid, Structured.invalid] at hRun
      | succ previous =>
          rcases
              Functions.Source.Effectful.Block.runOpen_cons_cases
                model prim program hRun with
            hHeadRegular | hHeadNonregular
          · rcases hHeadRegular with
              ⟨middle, middleCtx, _hHead, hTail⟩
            apply ih
            · intro stmt hMem
              exact hPrelude stmt (by simp [hMem])
            · exact hTail
          · rcases hHeadNonregular with
              ⟨headOutcome, _headCtx, hHead, hHeadMode,
                hOutcome, _hFinalCtx⟩
            have hHeadPrelude : PreludeStmt head :=
              hPrelude head (by simp)
            rcases
                stmt_run_regular_or_halt model prim program
                  hHeadPrelude hHead with
              hHeadRegular | hHeadHalt
            · exact False.elim (hHeadMode hHeadRegular)
            · rcases hHeadHalt with ⟨kind, hKind⟩
              rw [hOutcome, hKind]
              exact Or.inr ⟨kind, rfl⟩

end Prelude

theorem lowerUnchecked?_prelude
      {results : Nat} {state final : Fresh.State}
      {expr : AstExpr} {pre : List Functions.Stmt}
      {lower : Locals.Expr results}
      (hLower :
        lowerUnchecked? results state expr =
          some (pre, lower, final)) :
      Prelude pre := by
    induction results, state, expr using lowerUnchecked?.induct
        (motive_2 := fun listState args =>
          ∀ listPre listLower listFinal,
            List.lowerBound1Unchecked? listState args =
                some (listPre, listLower, listFinal) →
              Prelude listPre)
        generalizing pre final with
    | case1 state value =>
        simp [lowerUnchecked?] at hLower
        rcases hLower with ⟨rfl, _hLower, _hFinal⟩
        exact Prelude.nil
    | case2 results state value hNe =>
        simp [lowerUnchecked?, hNe] at hLower
    | case3 state name =>
        simp [lowerUnchecked?] at hLower
        rcases hLower with ⟨rfl, _hLower, _hFinal⟩
        exact Prelude.nil
    | case4 results state name hNe =>
        simp [lowerUnchecked?, hNe] at hLower
    | case5 results state functionName args hUnsupported =>
        simp [lowerUnchecked?, hUnsupported] at hLower
    | case6 state functionName args hSupported hDirect =>
        cases hArgs : List.toLocals1? args with
        | none =>
            simp [lowerUnchecked?, hSupported, hDirect, hArgs] at hLower
        | some lowerArgs =>
            cases hFresh : Fresh.fresh? state with
            | none =>
                simp [lowerUnchecked?, hSupported, hDirect, hArgs, hFresh]
                  at hLower
            | some result =>
                rcases result with ⟨tmp, stateAfter⟩
                simp [lowerUnchecked?, hSupported, hDirect, hArgs, hFresh]
                  at hLower
                rw [← hLower.1]
                exact Prelude.letCall tmp functionName lowerArgs
    | case7 state functionName args hSupported hBound ih =>
        cases hArgs : List.lowerBound1Unchecked? state args with
        | none =>
            simp [lowerUnchecked?, hSupported, hBound, hArgs] at hLower
        | some result =>
            rcases result with ⟨preArgs, lowerArgs, stateAfterArgs⟩
            cases hFresh : Fresh.fresh? stateAfterArgs with
            | none =>
                simp [lowerUnchecked?, hSupported, hBound, hArgs, hFresh]
                  at hLower
            | some result =>
                rcases result with ⟨tmp, stateAfter⟩
                simp [lowerUnchecked?, hSupported, hBound, hArgs, hFresh]
                  at hLower
                rw [← hLower.1]
                exact
                  Prelude.append (ih _ _ _ hArgs)
                    (Prelude.letCall tmp functionName lowerArgs)
    | case8 results state functionName args hSupported hNe =>
        simp [lowerUnchecked?, hSupported, hNe] at hLower
    | case9 results state prim args ih =>
        cases hOp : Prim.toUncheckedBasicOp? prim with
        | none =>
            simp [lowerUnchecked?, hOp] at hLower
        | some op =>
            cases hDirect : List.directPureArgsSafe? args with
            | false =>
                cases hArgs : List.lowerBound1Unchecked? state args with
                | none =>
                    simp [lowerUnchecked?, hOp, hDirect, hArgs] at hLower
                | some result =>
                    rcases result with
                      ⟨preArgs, lowerArgs, stateAfterArgs⟩
                    cases hSeq :
                        List.toStackSeq? lowerArgs
                          (Expressions.Structured.BasicOp.inputs op) with
                    | none =>
                        simp [lowerUnchecked?, hOp, hDirect, hArgs, hSeq]
                          at hLower
                    | some seq =>
                        by_cases hOutputs :
                            Expressions.Structured.BasicOp.outputs op =
                              results
                        · simp [lowerUnchecked?, hOp, hDirect, hArgs, hSeq,
                            hOutputs] at hLower
                          rw [← hLower.1]
                          exact ih _ _ _ hArgs
                        · simp [lowerUnchecked?, hOp, hDirect, hArgs, hSeq,
                            hOutputs] at hLower
            | true =>
                cases hArgs : List.toLocals1? args with
                | none =>
                    simp [lowerUnchecked?, hOp, hDirect, hArgs] at hLower
                | some lowerArgs =>
                    cases hSeq :
                        List.toStackSeq? lowerArgs
                          (Expressions.Structured.BasicOp.inputs op) with
                    | none =>
                        simp [lowerUnchecked?, hOp, hDirect, hArgs, hSeq]
                          at hLower
                    | some seq =>
                        by_cases hOutputs :
                            Expressions.Structured.BasicOp.outputs op =
                              results
                        · simp [lowerUnchecked?, hOp, hDirect, hArgs, hSeq,
                            hOutputs] at hLower
                          rcases hLower with
                            ⟨rfl, _hLower, _hFinal⟩
                          exact Prelude.nil
                        · simp [lowerUnchecked?, hOp, hDirect, hArgs, hSeq,
                            hOutputs] at hLower
    | case10 state =>
        rename_i listPre listLower listFinal hList
        simp [List.lowerBound1Unchecked?] at hList
        rcases hList with ⟨rfl, _hLower, _hFinal⟩
        exact Prelude.nil
    | case11 state expr rest ihRest ihExpr =>
        rename_i listPre listLower listFinal hList
        cases hRest : List.lowerBound1Unchecked? state rest with
        | none =>
            simp [List.lowerBound1Unchecked?, hRest] at hList
        | some restResult =>
            rcases restResult with ⟨preRest, lowerRest, stateAfterRest⟩
            cases hHead : lowerUnchecked? 1 stateAfterRest expr with
            | none =>
                simp [List.lowerBound1Unchecked?, hRest, hHead] at hList
            | some headResult =>
                rcases headResult with
                  ⟨preHead, lowerHead, stateAfterHead⟩
                by_cases hDeferred :
                    deferredBoundArgSafe? expr = true ∧
                      lowerRest.length < 4
                · simp [List.lowerBound1Unchecked?, hRest, hHead,
                    hDeferred] at hList
                  rw [← hList.1]
                  exact
                    Prelude.append (ihRest _ _ _ hRest)
                      (ihExpr _ hHead)
                · cases hFresh : Fresh.fresh? stateAfterHead with
                  | none =>
                      simp [List.lowerBound1Unchecked?, hRest, hHead,
                        hDeferred, hFresh] at hList
                  | some freshResult =>
                      rcases freshResult with ⟨tmp, stateAfterFresh⟩
                      simp [List.lowerBound1Unchecked?, hRest, hHead,
                        hDeferred, hFresh] at hList
                      rw [← hList.1]
                      have hCombined :=
                        Prelude.append
                          (Prelude.append
                            (ihRest _ _ _ hRest) (ihExpr _ hHead))
                          (Prelude.let_ tmp lowerHead)
                      simpa [List.append_assoc] using hCombined

theorem lower1Unchecked?_prelude
    {state final : Fresh.State} {expr : AstExpr}
    {pre : List Functions.Stmt} {lower : Locals.Expr 1}
    (hLower :
      lower1Unchecked? state expr = some (pre, lower, final)) :
    Prelude pre := by
  exact lowerUnchecked?_prelude hLower

/-- Stable leaf arguments within the bounded direct window emit no generated
prelude. This is an inversion of the ordinary lowering algorithm, not an
alternate argument compiler. -/
theorem lowerBound1Unchecked?_direct_parts
    {state final : Fresh.State} {args : List AstExpr}
    {pre : List Functions.Stmt} {lower : List (Locals.Expr 1)}
    (hLower :
      List.lowerBound1Unchecked? state args = some (pre, lower, final))
    (hDirect : ∀ expr, expr ∈ args → deferredBoundArgSafe? expr = true)
    (hWindow : args.length < 5) :
    pre = [] ∧ final = state ∧ List.toLocals1? args = some lower := by
  induction args generalizing state pre lower final with
  | nil =>
      simp [List.lowerBound1Unchecked?] at hLower
      rcases hLower with ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, rfl, rfl⟩
  | cons expr rest ih =>
      cases hRest : List.lowerBound1Unchecked? state rest with
      | none =>
          simp [List.lowerBound1Unchecked?, hRest] at hLower
      | some restResult =>
          rcases restResult with ⟨preRest, lowerRest, stateRest⟩
          cases hHead : lowerUnchecked? 1 stateRest expr with
          | none =>
              simp [List.lowerBound1Unchecked?, hRest, hHead] at hLower
          | some headResult =>
              rcases headResult with ⟨preHead, lowerHead, stateHead⟩
              have hRestParts := ih hRest
                (fun item hMem => hDirect item (by simp [hMem]))
                (by simp only [List.length_cons] at hWindow; omega)
              rcases hRestParts with ⟨rfl, rfl, hRestDirect⟩
              have hExprDirect : deferredBoundArgSafe? expr = true :=
                hDirect expr (by simp)
              have hHeadParts :=
                lower1Unchecked?_deferred_parts hExprDirect
                  (by simpa [lower1Unchecked?] using hHead)
              rcases hHeadParts with ⟨rfl, rfl, hHeadDirect⟩
              have hRestLength : lowerRest.length < 4 := by
                have hLength :=
                  List.lowerBound1Unchecked?_length_lowerArgs_eq hRest
                rw [hLength]
                simp only [List.length_cons] at hWindow
                omega
              simp [List.lowerBound1Unchecked?, hRest, hHead,
                hExprDirect, hRestLength] at hLower
              rcases hLower with ⟨hPreEq, hLowerEq, hFinalEq⟩
              refine ⟨hPreEq, hFinalEq.symm, ?_⟩
              rw [← hLowerEq]
              simp [List.toLocals1?, hHeadDirect, hRestDirect]

theorem lower1Unchecked?_append_run_cases
    {σ : Type}
    (model : Functions.Source.Effectful.StateModel σ)
    (prim : Functions.Source.Effectful.PrimitiveSemantics σ)
    (program : Functions.Program)
    {before after : Fresh.State} {expr : AstExpr}
    {pre suffix : List Functions.Stmt} {lower : Locals.Expr 1}
    {ctx finalCtx : Functions.Source.Ctx} {fuel : Nat}
    {source : σ}
    {outcome : Functions.Source.Effectful.Outcome σ}
    (hLower :
      lower1Unchecked? before expr = some (pre, lower, after))
    (hRun :
      Functions.Source.Effectful.Block.runOpen
          model prim program ctx fuel
          { stmts := pre ++ suffix } source =
        .ok (outcome, finalCtx)) :
    (∃ middle middleCtx suffixFuel,
        Functions.Source.Effectful.Block.runOpen
            model prim program ctx fuel { stmts := pre } source =
          .ok
            (Functions.Source.Effectful.Outcome.regular middle,
              middleCtx) ∧
        Functions.Source.Effectful.Block.runOpen
            model prim program middleCtx suffixFuel
            { stmts := suffix } middle =
          .ok (outcome, finalCtx) ∧
        suffixFuel ≤ fuel) ∨
      (∃ kind preludeOutcome preludeCtx,
        Functions.Source.Effectful.Block.runOpen
            model prim program ctx fuel { stmts := pre } source =
          .ok (preludeOutcome, preludeCtx) ∧
        preludeOutcome.mode = .halt kind ∧
        outcome = preludeOutcome ∧
        finalCtx = preludeCtx) := by
  rcases
      Functions.Source.Effectful.Block.runOpen_append_bounded_cases
        model prim program hRun with
    hRegular | hNonregular
  · exact Or.inl hRegular
  · rcases hNonregular with
      ⟨preludeOutcome, preludeCtx, hPreludeRun,
        hPreludeNonregular, hOutcome, hFinalCtx⟩
    rcases
        Prelude.runOpen_regular_or_halt model prim program
          (lower1Unchecked?_prelude hLower) hPreludeRun with
      hPreludeRegular | hPreludeHalt
    · exact False.elim (hPreludeNonregular hPreludeRegular)
    · rcases hPreludeHalt with ⟨kind, hKind⟩
      exact
        Or.inr
          ⟨kind, preludeOutcome, preludeCtx, hPreludeRun,
            hKind, hOutcome, hFinalCtx⟩

end Expr
end Yul
end EvmCompiler
