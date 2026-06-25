import EvmCompiler.Solidity.FrontendOccurrence
import EvmCompiler.Solidity.RawAst

namespace EvmCompiler
namespace Solidity
namespace RawAst
namespace RawOccurrence

inductive ExprUserCall (functionName : Name)
    (args : List Raw.Expr) : Raw.Expr → Prop where
  | here :
      ExprUserCall functionName args
        (.functionCall functionName args)
  | callArg
      {callee : Name} {outerArgs : List Raw.Expr} {arg : Raw.Expr} :
      arg ∈ outerArgs →
        ExprUserCall functionName args arg →
          ExprUserCall functionName args (.functionCall callee outerArgs)

mutual
  inductive StmtUserCall (functionName : Name)
      (args : List Raw.Expr) : Raw.Stmt → Prop where
    | block {body : List Raw.Stmt} :
        StmtListUserCall functionName args body →
          StmtUserCall functionName args (.block body)
    | variableDeclarationValue
        {names : List Name} {value : Raw.Expr} :
        ExprUserCall functionName args value →
          StmtUserCall functionName args
            (.variableDeclaration names (some value))
    | assignmentValue {names : List Name} {value : Raw.Expr} :
        ExprUserCall functionName args value →
          StmtUserCall functionName args (.assignment names value)
    | expressionStatement {value : Raw.Expr} :
        ExprUserCall functionName args value →
          StmtUserCall functionName args (.expressionStatement value)
    | functionBody
        {name : Name} {params returns : List Name}
        {body : List Raw.Stmt} :
        StmtListUserCall functionName args body →
          StmtUserCall functionName args
            (.functionDefinition name params returns body)
    | switchScrutinee
        {scrutinee : Raw.Expr}
        {cases : List (Raw.SwitchCaseValue × List Raw.Stmt)}
        {defaultBody : List Raw.Stmt} :
        ExprUserCall functionName args scrutinee →
          StmtUserCall functionName args
            (.switch scrutinee cases defaultBody)
    | switchCase
        {scrutinee : Raw.Expr}
        {cases : List (Raw.SwitchCaseValue × List Raw.Stmt)}
        {defaultBody : List Raw.Stmt} :
        CaseListUserCall functionName args cases →
          StmtUserCall functionName args
            (.switch scrutinee cases defaultBody)
    | switchDefault
        {scrutinee : Raw.Expr}
        {cases : List (Raw.SwitchCaseValue × List Raw.Stmt)}
        {defaultBody : List Raw.Stmt} :
        StmtListUserCall functionName args defaultBody →
          StmtUserCall functionName args
            (.switch scrutinee cases defaultBody)
    | forPre
        {pre post body : List Raw.Stmt}
        {condition : Raw.Expr} :
        StmtListUserCall functionName args pre →
          StmtUserCall functionName args
            (.forLoop pre condition post body)
    | forCondition
        {pre post body : List Raw.Stmt}
        {condition : Raw.Expr} :
        ExprUserCall functionName args condition →
          StmtUserCall functionName args
            (.forLoop pre condition post body)
    | forPost
        {pre post body : List Raw.Stmt}
        {condition : Raw.Expr} :
        StmtListUserCall functionName args post →
          StmtUserCall functionName args
            (.forLoop pre condition post body)
    | forBody
        {pre post body : List Raw.Stmt}
        {condition : Raw.Expr} :
        StmtListUserCall functionName args body →
          StmtUserCall functionName args
            (.forLoop pre condition post body)
    | ifCondition {condition : Raw.Expr}
        {body : List Raw.Stmt} :
        ExprUserCall functionName args condition →
          StmtUserCall functionName args (.ifThen condition body)
    | ifBody {condition : Raw.Expr}
        {body : List Raw.Stmt} :
        StmtListUserCall functionName args body →
          StmtUserCall functionName args (.ifThen condition body)

  inductive StmtListUserCall (functionName : Name)
      (args : List Raw.Expr) : List Raw.Stmt → Prop where
    | head {stmt : Raw.Stmt} {rest : List Raw.Stmt} :
        StmtUserCall functionName args stmt →
          StmtListUserCall functionName args (stmt :: rest)
    | tail {stmt : Raw.Stmt} {rest : List Raw.Stmt} :
        StmtListUserCall functionName args rest →
          StmtListUserCall functionName args (stmt :: rest)

  inductive CaseListUserCall (functionName : Name)
      (args : List Raw.Expr) :
      List (Raw.SwitchCaseValue × List Raw.Stmt) → Prop where
    | head {value : Raw.SwitchCaseValue}
        {body : List Raw.Stmt}
        {rest : List (Raw.SwitchCaseValue × List Raw.Stmt)} :
        StmtListUserCall functionName args body →
          CaseListUserCall functionName args ((value, body) :: rest)
    | tail {head : Raw.SwitchCaseValue × List Raw.Stmt}
        {rest : List (Raw.SwitchCaseValue × List Raw.Stmt)} :
        CaseListUserCall functionName args rest →
          CaseListUserCall functionName args (head :: rest)
end

namespace StmtListUserCall

theorem exists_split_stmt
    {functionName : Name} {args : List Raw.Expr}
    {stmts : List Raw.Stmt}
    (hOccurrence : StmtListUserCall functionName args stmts) :
    ∃ (pre : List Raw.Stmt) (stmt : Raw.Stmt)
      (suffix : List Raw.Stmt),
      stmts = pre ++ stmt :: suffix ∧
        StmtUserCall functionName args stmt := by
  induction stmts with
  | nil =>
      cases hOccurrence
  | cons head rest ih =>
      cases hOccurrence with
      | head hStmt =>
          exact ⟨[], head, rest, rfl, hStmt⟩
      | tail hTail =>
          rcases ih hTail with ⟨pre, stmt, suffix, hSplit, hStmt⟩
          exact ⟨head :: pre, stmt, suffix, by simp [hSplit], hStmt⟩

theorem of_split_stmt
    {functionName : Name} {args : List Raw.Expr}
    {pre suffix : List Raw.Stmt} {stmt : Raw.Stmt}
    (hStmt : StmtUserCall functionName args stmt) :
    StmtListUserCall functionName args (pre ++ stmt :: suffix) := by
  induction pre with
  | nil =>
      exact StmtListUserCall.head hStmt
  | cons _ _ ih =>
      exact StmtListUserCall.tail ih

end StmtListUserCall

namespace Expr
namespace List

theorem elaborate_mem
    {rawExprs : List Raw.Expr} {frontendExprs : List Frontend.Expr}
    {state state' : Elab.State}
    (hElab :
      (Elab.Expr.List.elaborate rawExprs).run state =
        .ok (frontendExprs, state'))
    {rawExpr : Raw.Expr} (hMem : rawExpr ∈ rawExprs) :
    ∃ (frontendExpr : Frontend.Expr)
      (stateBefore stateAfter : Elab.State),
      (Elab.Expr.elaborate rawExpr).run stateBefore =
        .ok (frontendExpr, stateAfter) ∧
        frontendExpr ∈ frontendExprs := by
  induction rawExprs generalizing state state' frontendExprs with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      simp only [Elab.Expr.List.elaborate] at hElab
      cases hHead : (Elab.Expr.elaborate head).run state with
      | error err =>
          simp [hHead] at hElab
      | ok headResult =>
          rcases headResult with ⟨headExpr, stateAfterHead⟩
          cases hTail :
              (Elab.Expr.List.elaborate rest).run stateAfterHead with
          | error err =>
              simp [hHead, hTail] at hElab
          | ok tailResult =>
              rcases tailResult with ⟨tailExprs, stateAfterTail⟩
              simp [hHead, hTail] at hElab
              rcases hElab with ⟨rfl, rfl⟩
              simp only [List.mem_cons] at hMem ⊢
              rcases hMem with hHere | hRest
              · subst rawExpr
                exact
                  ⟨headExpr, state, stateAfterHead, hHead, Or.inl rfl⟩
              · rcases ih hTail hRest with
                  ⟨frontendExpr, stateBefore, stateAfter,
                    hExpr, hFrontendMem⟩
                exact
                  ⟨frontendExpr, stateBefore, stateAfter, hExpr,
                    Or.inr hFrontendMem⟩

end List
end Expr

namespace ExprUserCall

theorem elaborate_direct_user
    {functionName generated : Name} {rawArgs : List Raw.Expr}
    {frontendArgs : List Frontend.Expr}
    {frontendExpr : Frontend.Expr}
    {state stateAfterArgs state' : Elab.State}
    (hNotMemoryguard : functionName ≠ "memoryguard")
    (hNotClz : functionName ≠ "clz")
    (hKind : CallClass.classifyCall functionName = .user)
    (hArgs :
      (Elab.Expr.List.elaborate rawArgs).run state =
        .ok (frontendArgs, stateAfterArgs))
    (hResolve :
      Elab.resolveFunctionIn functionName stateAfterArgs.functionScopes =
        some generated)
    (hElab :
      (Elab.Expr.elaborate (.functionCall functionName rawArgs)).run state =
        .ok (frontendExpr, state')) :
    FrontendOccurrence.ExprUserCall generated frontendArgs frontendExpr := by
  simp [Elab.Expr.elaborate, hNotMemoryguard, hNotClz, hArgs,
    hKind, Elab.resolveFunction, hResolve] at hElab
  rcases hElab with ⟨rfl, _hState⟩
  exact FrontendOccurrence.ExprUserCall.here

theorem elaborate
    {functionName : Name} {rawArgs : List Raw.Expr}
    {rawExpr : Raw.Expr} {frontendExpr : Frontend.Expr}
    {state state' : Elab.State}
    (hOccurrence : ExprUserCall functionName rawArgs rawExpr)
    (hNotMemoryguard : functionName ≠ "memoryguard")
    (hNotClz : functionName ≠ "clz")
    (hKind : CallClass.classifyCall functionName = .user)
    (hElab :
      (Elab.Expr.elaborate rawExpr).run state =
        .ok (frontendExpr, state')) :
    ∃ (generated : Name) (frontendArgs : List Frontend.Expr),
      FrontendOccurrence.ExprUserCall generated frontendArgs frontendExpr := by
  induction hOccurrence generalizing frontendExpr state state' with
  | here =>
      cases hArgs :
          (Elab.Expr.List.elaborate rawArgs).run state with
      | error err =>
          simp [Elab.Expr.elaborate, hNotMemoryguard, hNotClz, hArgs]
            at hElab
      | ok argResult =>
          rcases argResult with ⟨frontendArgs, stateAfterArgs⟩
          cases hResolve :
              Elab.resolveFunctionIn functionName
                stateAfterArgs.functionScopes with
          | none =>
              simp [Elab.Expr.elaborate, hNotMemoryguard, hNotClz,
                hArgs, hKind, Elab.resolveFunction, hResolve]
                at hElab
              unfold Elab.throw at hElab
              cases hElab
          | some generated =>
              exact
                ⟨generated, frontendArgs,
                  elaborate_direct_user hNotMemoryguard hNotClz hKind
                    hArgs hResolve hElab⟩
  | @callArg callee outerArgs arg hMem _ ih =>
      by_cases hMemoryguard : callee = "memoryguard"
      · subst callee
        cases outerArgs with
        | nil =>
            simp [Elab.Expr.elaborate] at hElab
            unfold Elab.throw at hElab
            cases hElab
        | cons only rest =>
            cases rest with
            | nil =>
                cases hArg :
                    (Elab.Expr.elaborate only).run state with
                | error err =>
                    simp [Elab.Expr.elaborate, hArg] at hElab
                | ok argResult =>
                    rcases argResult with ⟨frontendArg, stateAfterArg⟩
                    simp [Elab.Expr.elaborate, hArg] at hElab
                    rcases hElab with ⟨rfl, rfl⟩
                    simp only [List.mem_singleton] at hMem
                    subst arg
                    rcases ih hArg with
                      ⟨generated, frontendArgs, hInner⟩
                    exact
                      ⟨generated, frontendArgs,
                        FrontendOccurrence.ExprUserCall.callArg
                          (by simp) hInner⟩
            | cons second rest =>
                simp [Elab.Expr.elaborate] at hElab
                unfold Elab.throw at hElab
                cases hElab
      · by_cases hClzOuter : callee = "clz"
        · subst callee
          cases outerArgs with
          | nil =>
              simp [Elab.Expr.elaborate] at hElab
              unfold Elab.throw at hElab
              cases hElab
          | cons only rest =>
              cases rest with
              | nil =>
                  cases hArg :
                      (Elab.Expr.elaborate only).run state with
                  | error err =>
                      simp [Elab.Expr.elaborate, hArg] at hElab
                  | ok argResult =>
                      rcases argResult with ⟨frontendArg, stateAfterArg⟩
                      cases hHelper :
                          Elab.ensureClzHelper.run stateAfterArg with
                      | error err =>
                          simp [Elab.Expr.elaborate, hArg, hHelper] at hElab
                      | ok helperResult =>
                          rcases helperResult with ⟨helper, stateAfterHelper⟩
                          simp [Elab.Expr.elaborate, hArg, hHelper] at hElab
                          rcases hElab with ⟨rfl, rfl⟩
                          simp only [List.mem_singleton] at hMem
                          subst arg
                          rcases ih hArg with
                            ⟨generated, frontendArgs, hInner⟩
                          exact
                            ⟨generated, frontendArgs,
                              FrontendOccurrence.ExprUserCall.callArg
                                (by simp) hInner⟩
              | cons second rest =>
                  simp [Elab.Expr.elaborate] at hElab
                  unfold Elab.throw at hElab
                  cases hElab
        · cases hOuterArgs :
              (Elab.Expr.List.elaborate outerArgs).run state with
          | error err =>
              simp [Elab.Expr.elaborate, hMemoryguard, hClzOuter,
                hOuterArgs] at hElab
          | ok outerResult =>
              rcases outerResult with ⟨frontendOuterArgs, stateAfterArgs⟩
              rcases RawOccurrence.Expr.List.elaborate_mem
                  hOuterArgs hMem with
                ⟨frontendArg, stateBeforeArg, stateAfterArg,
                  hArgElab, hFrontendMem⟩
              rcases ih hArgElab with
                ⟨generated, frontendArgs, hInner⟩
              cases hOuterKind : CallClass.classifyCall callee <;>
                try
                  (simp [Elab.Expr.elaborate, hMemoryguard, hClzOuter,
                    hOuterArgs, hOuterKind] at hElab
                   rcases hElab with ⟨rfl, rfl⟩
                   exact
                    ⟨generated, frontendArgs,
                      FrontendOccurrence.ExprUserCall.callArg
                        hFrontendMem hInner⟩)
              · cases hResolve :
                    Elab.resolveFunctionIn callee
                      stateAfterArgs.functionScopes with
                | none =>
                    simp [Elab.Expr.elaborate, hMemoryguard, hClzOuter,
                      hOuterArgs, hOuterKind, Elab.resolveFunction,
                      hResolve] at hElab
                    unfold Elab.throw at hElab
                    cases hElab
                | some resolved =>
                    simp [Elab.Expr.elaborate, hMemoryguard, hClzOuter,
                      hOuterArgs, hOuterKind, Elab.resolveFunction,
                      hResolve] at hElab
                    rcases hElab with ⟨rfl, rfl⟩
                    exact
                      ⟨generated, frontendArgs,
                        FrontendOccurrence.ExprUserCall.callArg
                          hFrontendMem hInner⟩

end ExprUserCall

end RawOccurrence
end RawAst
end Solidity
end EvmCompiler
