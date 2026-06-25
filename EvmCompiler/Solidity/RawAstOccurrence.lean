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

mutual
  inductive StmtElaborationOccurrence (functionName : Name)
      (args : List Frontend.Expr) : Frontend.Stmt → Prop where
    | executable {stmt : Frontend.Stmt} :
        FrontendOccurrence.StmtUserCall functionName args stmt →
          StmtElaborationOccurrence functionName args stmt
    | block {body : List Frontend.Stmt} :
        StmtListElaborationOccurrence functionName args body →
          StmtElaborationOccurrence functionName args (.block body)
    | functionBody
        {name : Name} {params returns : List Name}
        {body : List Frontend.Stmt} :
        StmtListElaborationOccurrence functionName args body →
          StmtElaborationOccurrence functionName args
            (.functionDef name params returns body)
    | switchCase
        {scrutinee : Frontend.Expr}
        {cases : List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
        {defaultBody : List Frontend.Stmt} :
        CaseListElaborationOccurrence functionName args cases →
          StmtElaborationOccurrence functionName args
            (.switch scrutinee cases defaultBody)
    | switchDefault
        {scrutinee : Frontend.Expr}
        {cases : List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
        {defaultBody : List Frontend.Stmt} :
        StmtListElaborationOccurrence functionName args defaultBody →
          StmtElaborationOccurrence functionName args
            (.switch scrutinee cases defaultBody)
    | forPre
        {pre post body : List Frontend.Stmt}
        {condition : Frontend.Expr} :
        StmtListElaborationOccurrence functionName args pre →
          StmtElaborationOccurrence functionName args
            (.forLoop pre condition post body)
    | forPost
        {pre post body : List Frontend.Stmt}
        {condition : Frontend.Expr} :
        StmtListElaborationOccurrence functionName args post →
          StmtElaborationOccurrence functionName args
            (.forLoop pre condition post body)
    | forBody
        {pre post body : List Frontend.Stmt}
        {condition : Frontend.Expr} :
        StmtListElaborationOccurrence functionName args body →
          StmtElaborationOccurrence functionName args
            (.forLoop pre condition post body)
    | ifBody {condition : Frontend.Expr}
        {body : List Frontend.Stmt} :
        StmtListElaborationOccurrence functionName args body →
          StmtElaborationOccurrence functionName args (.ifThen condition body)

  inductive StmtListElaborationOccurrence (functionName : Name)
      (args : List Frontend.Expr) : List Frontend.Stmt → Prop where
    | head {stmt : Frontend.Stmt} {rest : List Frontend.Stmt} :
        StmtElaborationOccurrence functionName args stmt →
          StmtListElaborationOccurrence functionName args (stmt :: rest)
    | tail {stmt : Frontend.Stmt} {rest : List Frontend.Stmt} :
        StmtListElaborationOccurrence functionName args rest →
          StmtListElaborationOccurrence functionName args (stmt :: rest)

  inductive CaseListElaborationOccurrence (functionName : Name)
      (args : List Frontend.Expr) :
      List (Frontend.SwitchCaseValue × List Frontend.Stmt) → Prop where
    | head {value : Frontend.SwitchCaseValue}
        {body : List Frontend.Stmt}
        {rest : List (Frontend.SwitchCaseValue × List Frontend.Stmt)} :
        StmtListElaborationOccurrence functionName args body →
          CaseListElaborationOccurrence functionName args
            ((value, body) :: rest)
    | tail {head : Frontend.SwitchCaseValue × List Frontend.Stmt}
        {rest : List (Frontend.SwitchCaseValue × List Frontend.Stmt)} :
        CaseListElaborationOccurrence functionName args rest →
          CaseListElaborationOccurrence functionName args (head :: rest)
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

namespace Stmt
namespace List

theorem elaborate_mem
    {rawStmts : List Raw.Stmt} {frontendStmts : List Frontend.Stmt}
    {state state' : Elab.State}
    (hElab :
      (Elab.Stmt.List.elaborate rawStmts).run state =
        .ok (frontendStmts, state'))
    {rawStmt : Raw.Stmt} (hMem : rawStmt ∈ rawStmts) :
    ∃ (frontendStmt : Frontend.Stmt)
      (stateBefore stateAfter : Elab.State),
      (Elab.Stmt.elaborate rawStmt).run stateBefore =
        .ok (frontendStmt, stateAfter) ∧
        frontendStmt ∈ frontendStmts := by
  induction rawStmts generalizing state state' frontendStmts with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      simp only [Elab.Stmt.List.elaborate] at hElab
      cases hHead : (Elab.Stmt.elaborate head).run state with
      | error err =>
          simp [hHead] at hElab
      | ok headResult =>
          rcases headResult with ⟨headStmt, stateAfterHead⟩
          cases hTail :
              (Elab.Stmt.List.elaborate rest).run stateAfterHead with
          | error err =>
              simp [hHead, hTail] at hElab
          | ok tailResult =>
              rcases tailResult with ⟨tailStmts, stateAfterTail⟩
              simp [hHead, hTail] at hElab
              rcases hElab with ⟨rfl, rfl⟩
              simp only [List.mem_cons] at hMem ⊢
              rcases hMem with hHere | hRest
              · subst rawStmt
                exact
                  ⟨headStmt, state, stateAfterHead, hHead, Or.inl rfl⟩
              · rcases ih hTail hRest with
                  ⟨frontendStmt, stateBefore, stateAfter,
                    hStmt, hFrontendMem⟩
                exact
                  ⟨frontendStmt, stateBefore, stateAfter, hStmt,
                    Or.inr hFrontendMem⟩

theorem elaborateBlock_elaborate_exists
    {rawStmts : List Raw.Stmt} {frontendStmts : List Frontend.Stmt}
    {state state' : Elab.State} {createsScope : Bool}
    (hElab :
      (Elab.Stmt.List.elaborateBlock rawStmts createsScope).run state =
        .ok (frontendStmts, state')) :
    ∃ (stateBefore stateAfter : Elab.State),
      (Elab.Stmt.List.elaborate rawStmts).run stateBefore =
        .ok (frontendStmts, stateAfter) := by
  unfold Elab.Stmt.List.elaborateBlock at hElab
  cases hCreate : createsScope
  · simp [hCreate] at hElab
    cases hScope :
        (Elab.Stmt.List.localFunctionScope rawStmts).run state with
    | error err =>
        simp [hScope] at hElab
    | ok scopeResult =>
        rcases scopeResult with ⟨scope, stateAfterScope⟩
        cases hPush :
            (Elab.pushFunctionScope scope).run stateAfterScope with
        | error err =>
            simp [hScope, hPush] at hElab
        | ok pushResult =>
            rcases pushResult with ⟨unitPush, stateAfterPush⟩
            cases hHoist :
                (Elab.Stmt.List.hoistLocalFunctions rawStmts scope).run
                  stateAfterPush with
            | error err =>
                simp [hScope, hPush, hHoist] at hElab
            | ok hoistResult =>
                rcases hoistResult with ⟨unitHoist, stateAfterHoist⟩
                cases hList :
                    (Elab.Stmt.List.elaborate rawStmts).run
                      stateAfterHoist with
                | error err =>
                    simp [hScope, hPush, hHoist, hList] at hElab
                | ok listResult =>
                    rcases listResult with ⟨frontendStmts', stateAfterList⟩
                    cases hPop :
                        Elab.popFunctionScope.run stateAfterList with
                    | error err =>
                        simp [hScope, hPush, hHoist, hList, hPop] at hElab
                    | ok popResult =>
                        rcases popResult with ⟨unitPop, stateAfterPop⟩
                        simp [hScope, hPush, hHoist, hList, hPop] at hElab
                        rcases hElab with ⟨rfl, _hState⟩
                        exact ⟨stateAfterHoist, stateAfterList, hList⟩
  · simp [hCreate] at hElab
    cases hIdent :
        Elab.pushIdentifierScope.run state with
    | error err =>
        simp [hIdent] at hElab
    | ok identResult =>
        rcases identResult with ⟨unitIdent, stateAfterIdent⟩
        cases hScope :
            (Elab.Stmt.List.localFunctionScope rawStmts).run
              stateAfterIdent with
        | error err =>
            simp [hIdent, hScope] at hElab
        | ok scopeResult =>
            rcases scopeResult with ⟨scope, stateAfterScope⟩
            cases hPush :
                (Elab.pushFunctionScope scope).run stateAfterScope with
            | error err =>
                simp [hIdent, hScope, hPush] at hElab
            | ok pushResult =>
                rcases pushResult with ⟨unitPush, stateAfterPush⟩
                cases hHoist :
                    (Elab.Stmt.List.hoistLocalFunctions rawStmts scope).run
                      stateAfterPush with
                | error err =>
                    simp [hIdent, hScope, hPush, hHoist] at hElab
                | ok hoistResult =>
                    rcases hoistResult with ⟨unitHoist, stateAfterHoist⟩
                    cases hList :
                        (Elab.Stmt.List.elaborate rawStmts).run
                          stateAfterHoist with
                    | error err =>
                        simp [hIdent, hScope, hPush, hHoist, hList] at hElab
                    | ok listResult =>
                        rcases listResult with
                          ⟨frontendStmts', stateAfterList⟩
                        cases hPop :
                            Elab.popFunctionScope.run stateAfterList with
                        | error err =>
                            simp [hIdent, hScope, hPush, hHoist, hList,
                              hPop] at hElab
                        | ok popResult =>
                            rcases popResult with ⟨unitPop, stateAfterPop⟩
                            cases hPopIdent :
                                Elab.popIdentifierScope.run stateAfterPop with
                            | error err =>
                                simp [hIdent, hScope, hPush, hHoist, hList,
                                  hPop, hPopIdent] at hElab
                            | ok identPopResult =>
                                rcases identPopResult with
                                  ⟨unitIdentPop, stateAfterIdentPop⟩
                                simp [hIdent, hScope, hPush, hHoist, hList,
                                  hPop, hPopIdent] at hElab
                                rcases hElab with ⟨rfl, _hState⟩
                                exact ⟨stateAfterHoist, stateAfterList, hList⟩

theorem elaborateForInitBlockWithScope_elaborate_exists
    {rawStmts : List Raw.Stmt} {frontendStmts : List Frontend.Stmt}
    {state state' : Elab.State}
    (hElab :
      (Elab.Stmt.List.elaborateForInitBlockWithScope rawStmts).run state =
        .ok (frontendStmts, state')) :
    ∃ (stateBefore stateAfter : Elab.State),
      (Elab.Stmt.List.elaborate rawStmts).run stateBefore =
        .ok (frontendStmts, stateAfter) := by
  unfold Elab.Stmt.List.elaborateForInitBlockWithScope at hElab
  cases hScope :
      (Elab.Stmt.List.localFunctionScope rawStmts).run state with
  | error err =>
      simp [hScope] at hElab
  | ok scopeResult =>
      rcases scopeResult with ⟨scope, stateAfterScope⟩
      cases hPush :
          (Elab.pushFunctionScope scope).run stateAfterScope with
      | error err =>
          simp [hScope, hPush] at hElab
      | ok pushResult =>
          rcases pushResult with ⟨unitPush, stateAfterPush⟩
          cases hHoist :
              (Elab.Stmt.List.hoistLocalFunctions rawStmts scope).run
                stateAfterPush with
          | error err =>
              simp [hScope, hPush, hHoist] at hElab
          | ok hoistResult =>
              rcases hoistResult with ⟨unitHoist, stateAfterHoist⟩
              cases hList :
                  (Elab.Stmt.List.elaborate rawStmts).run
                    stateAfterHoist with
              | error err =>
                  simp [hScope, hPush, hHoist, hList] at hElab
              | ok listResult =>
                  rcases listResult with ⟨frontendStmts', stateAfterList⟩
                  simp [hScope, hPush, hHoist, hList] at hElab
                  rcases hElab with ⟨rfl, _hState⟩
                  exact ⟨stateAfterHoist, stateAfterList, hList⟩

end List

namespace CaseList

theorem elaborate_mem
    {rawCases : List (Raw.SwitchCaseValue × List Raw.Stmt)}
    {frontendCases : List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
    {state state' : Elab.State}
    (hElab :
      (Elab.Stmt.CaseList.elaborate rawCases).run state =
        .ok (frontendCases, state'))
    {rawValue : Raw.SwitchCaseValue} {rawBody : List Raw.Stmt}
    (hMem : (rawValue, rawBody) ∈ rawCases) :
    ∃ (frontendValue : Frontend.SwitchCaseValue)
      (frontendBody : List Frontend.Stmt)
      (stateBeforeBody stateAfterBody : Elab.State),
      Elab.SwitchCaseValue.elaborate rawValue = .ok frontendValue ∧
        (Elab.Stmt.List.elaborateBlock rawBody true).run stateBeforeBody =
          .ok (frontendBody, stateAfterBody) ∧
        (frontendValue, frontendBody) ∈ frontendCases := by
  induction rawCases generalizing state state' frontendCases with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      rcases head with ⟨headValue, headBody⟩
      simp only [Elab.Stmt.CaseList.elaborate] at hElab
      cases hValue : Elab.SwitchCaseValue.elaborate headValue with
      | error err =>
          simp [hValue] at hElab
          unfold Elab.throw at hElab
          cases hElab
      | ok frontendValue =>
          cases hBody :
              (Elab.Stmt.List.elaborateBlock headBody true).run state with
          | error err =>
              simp [hValue, hBody] at hElab
          | ok bodyResult =>
              rcases bodyResult with ⟨frontendBody, stateAfterBody⟩
              cases hTail :
                  (Elab.Stmt.CaseList.elaborate rest).run
                    stateAfterBody with
              | error err =>
                  simp [hValue, hBody, hTail] at hElab
              | ok tailResult =>
                  rcases tailResult with ⟨tailCases, stateAfterTail⟩
                  simp [hValue, hBody, hTail] at hElab
                  rcases hElab with ⟨rfl, rfl⟩
                  simp only [List.mem_cons] at hMem ⊢
                  rcases hMem with hHere | hRest
                  · rcases hHere with ⟨rfl, rfl⟩
                    exact
                      ⟨frontendValue, frontendBody, state, stateAfterBody,
                        hValue, hBody, Or.inl rfl⟩
                  · rcases ih hTail hRest with
                      ⟨frontendValue, frontendBody, stateBeforeBody,
                        stateAfterBody, hValue, hBody, hFrontendMem⟩
                    exact
                      ⟨frontendValue, frontendBody, stateBeforeBody,
                        stateAfterBody, hValue, hBody,
                        Or.inr hFrontendMem⟩

end CaseList
end Stmt

namespace StmtListUserCall

theorem elaborate_exists_stmt
    {functionName : Name} {args : List Raw.Expr}
    {rawStmts : List Raw.Stmt} {frontendStmts : List Frontend.Stmt}
    {state state' : Elab.State}
    (hOccurrence : StmtListUserCall functionName args rawStmts)
    (hElab :
      (Elab.Stmt.List.elaborate rawStmts).run state =
        .ok (frontendStmts, state')) :
    ∃ (rawStmt : Raw.Stmt) (frontendStmt : Frontend.Stmt)
      (stateBefore stateAfter : Elab.State),
      StmtUserCall functionName args rawStmt ∧
        (Elab.Stmt.elaborate rawStmt).run stateBefore =
          .ok (frontendStmt, stateAfter) ∧
        frontendStmt ∈ frontendStmts := by
  rcases exists_split_stmt hOccurrence with
    ⟨pre, stmt, suffix, hSplit, hStmt⟩
  have hMem : stmt ∈ rawStmts := by
    subst rawStmts
    simp
  rcases Stmt.List.elaborate_mem hElab hMem with
    ⟨frontendStmt, stateBefore, stateAfter, hStmtElab, hFrontendMem⟩
  exact
    ⟨stmt, frontendStmt, stateBefore, stateAfter,
      hStmt, hStmtElab, hFrontendMem⟩

theorem elaborateBlock_exists_stmt
    {functionName : Name} {args : List Raw.Expr}
    {rawStmts : List Raw.Stmt} {frontendStmts : List Frontend.Stmt}
    {state state' : Elab.State} {createsScope : Bool}
    (hOccurrence : StmtListUserCall functionName args rawStmts)
    (hElab :
      (Elab.Stmt.List.elaborateBlock rawStmts createsScope).run state =
        .ok (frontendStmts, state')) :
    ∃ (rawStmt : Raw.Stmt) (frontendStmt : Frontend.Stmt)
      (stateBefore stateAfter : Elab.State),
      StmtUserCall functionName args rawStmt ∧
        (Elab.Stmt.elaborate rawStmt).run stateBefore =
          .ok (frontendStmt, stateAfter) ∧
        frontendStmt ∈ frontendStmts := by
  rcases Stmt.List.elaborateBlock_elaborate_exists hElab with
    ⟨stateBeforeList, stateAfterList, hList⟩
  exact elaborate_exists_stmt hOccurrence hList

theorem elaborateForInitBlockWithScope_exists_stmt
    {functionName : Name} {args : List Raw.Expr}
    {rawStmts : List Raw.Stmt} {frontendStmts : List Frontend.Stmt}
    {state state' : Elab.State}
    (hOccurrence : StmtListUserCall functionName args rawStmts)
    (hElab :
      (Elab.Stmt.List.elaborateForInitBlockWithScope rawStmts).run state =
        .ok (frontendStmts, state')) :
    ∃ (rawStmt : Raw.Stmt) (frontendStmt : Frontend.Stmt)
      (stateBefore stateAfter : Elab.State),
      StmtUserCall functionName args rawStmt ∧
        (Elab.Stmt.elaborate rawStmt).run stateBefore =
          .ok (frontendStmt, stateAfter) ∧
        frontendStmt ∈ frontendStmts := by
  rcases Stmt.List.elaborateForInitBlockWithScope_elaborate_exists
      hElab with
    ⟨stateBeforeList, stateAfterList, hList⟩
  exact elaborate_exists_stmt hOccurrence hList

end StmtListUserCall

namespace CaseListUserCall

theorem exists_split_case
    {functionName : Name} {args : List Raw.Expr}
    {cases : List (Raw.SwitchCaseValue × List Raw.Stmt)}
    (hOccurrence : CaseListUserCall functionName args cases) :
    ∃ (pre : List (Raw.SwitchCaseValue × List Raw.Stmt))
      (value : Raw.SwitchCaseValue) (body : List Raw.Stmt)
      (suffix : List (Raw.SwitchCaseValue × List Raw.Stmt)),
      cases = pre ++ (value, body) :: suffix ∧
        StmtListUserCall functionName args body := by
  induction cases with
  | nil =>
      cases hOccurrence
  | cons caseHead rest ih =>
      rcases caseHead with ⟨caseValue, caseBody⟩
      cases hOccurrence with
      | head hBody =>
          exact ⟨[], caseValue, caseBody, rest, rfl, hBody⟩
      | tail hTail =>
          rcases ih hTail with
            ⟨pre, value, body, suffix, hSplit, hBody⟩
          exact
            ⟨(caseValue, caseBody) :: pre, value, body, suffix,
              by simp [hSplit], hBody⟩

theorem elaborate_exists_case
    {functionName : Name} {args : List Raw.Expr}
    {rawCases : List (Raw.SwitchCaseValue × List Raw.Stmt)}
    {frontendCases : List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
    {state state' : Elab.State}
    (hOccurrence : CaseListUserCall functionName args rawCases)
    (hElab :
      (Elab.Stmt.CaseList.elaborate rawCases).run state =
        .ok (frontendCases, state')) :
    ∃ (rawValue : Raw.SwitchCaseValue) (rawBody : List Raw.Stmt)
      (frontendValue : Frontend.SwitchCaseValue)
      (frontendBody : List Frontend.Stmt)
      (stateBeforeBody stateAfterBody : Elab.State),
      StmtListUserCall functionName args rawBody ∧
        Elab.SwitchCaseValue.elaborate rawValue = .ok frontendValue ∧
        (Elab.Stmt.List.elaborateBlock rawBody true).run stateBeforeBody =
          .ok (frontendBody, stateAfterBody) ∧
        (frontendValue, frontendBody) ∈ frontendCases := by
  rcases exists_split_case hOccurrence with
    ⟨pre, value, body, suffix, hSplit, hBodyOccurrence⟩
  have hMem : (value, body) ∈ rawCases := by
    subst rawCases
    simp
  rcases Stmt.CaseList.elaborate_mem hElab hMem with
    ⟨frontendValue, frontendBody, stateBeforeBody, stateAfterBody,
      hValue, hBodyElab, hFrontendMem⟩
  exact
    ⟨value, body, frontendValue, frontendBody, stateBeforeBody,
      stateAfterBody, hBodyOccurrence, hValue, hBodyElab,
      hFrontendMem⟩

end CaseListUserCall

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
