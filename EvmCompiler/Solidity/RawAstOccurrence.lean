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

namespace Stmt

theorem assignment_elaborate_value_exists
    {names : List Name} {value : Raw.Expr}
    {frontendStmt : Frontend.Stmt} {state state' : Elab.State}
    (hElab :
      (Elab.Stmt.elaborate (.assignment names value)).run state =
        .ok (frontendStmt, state')) :
    ∃ (frontendValue : Frontend.Expr)
      (stateBeforeValue stateAfterValue : Elab.State),
      (Elab.Expr.elaborate value).run stateBeforeValue =
        .ok (frontendValue, stateAfterValue) ∧
        frontendStmt = .assign names frontendValue := by
  unfold Elab.Stmt.elaborate at hElab
  cases hVisible :
      (Elab.requireIdentifiersVisible names "assignment").run state with
  | error err =>
      simp [hVisible] at hElab
  | ok visibleResult =>
      rcases visibleResult with ⟨unitVisible, stateAfterVisible⟩
      cases hValue :
          (Elab.Expr.elaborate value).run stateAfterVisible with
      | error err =>
          simp [hVisible, hValue] at hElab
      | ok valueResult =>
          rcases valueResult with ⟨frontendValue, stateAfterValue⟩
          simp [hVisible, hValue] at hElab
          rcases hElab with ⟨rfl, _hState⟩
          exact
            ⟨frontendValue, stateAfterVisible, stateAfterValue,
              hValue, rfl⟩

theorem switch_elaborate_parts
    {scrutinee : Raw.Expr}
    {cases : List (Raw.SwitchCaseValue × List Raw.Stmt)}
    {defaultBody : List Raw.Stmt}
    {frontendStmt : Frontend.Stmt} {state state' : Elab.State}
    (hElab :
      (Elab.Stmt.elaborate (.switch scrutinee cases defaultBody)).run state =
        .ok (frontendStmt, state')) :
    ∃ (frontendScrutinee : Frontend.Expr)
      (frontendCases : List (Frontend.SwitchCaseValue × List Frontend.Stmt))
      (frontendDefault : List Frontend.Stmt)
      (stateAfterScrutinee stateAfterCases stateAfterDefault : Elab.State),
      (Elab.Expr.elaborate scrutinee).run state =
        .ok (frontendScrutinee, stateAfterScrutinee) ∧
        (Elab.Stmt.CaseList.elaborate cases).run stateAfterScrutinee =
          .ok (frontendCases, stateAfterCases) ∧
        (Elab.Stmt.List.elaborateBlock defaultBody true).run
          stateAfterCases =
          .ok (frontendDefault, stateAfterDefault) ∧
        frontendStmt =
          .switch frontendScrutinee frontendCases frontendDefault := by
  unfold Elab.Stmt.elaborate at hElab
  cases hScrutinee : (Elab.Expr.elaborate scrutinee).run state with
  | error err =>
      simp [hScrutinee] at hElab
  | ok scrutineeResult =>
      rcases scrutineeResult with
        ⟨frontendScrutinee, stateAfterScrutinee⟩
      cases hCases :
          (Elab.Stmt.CaseList.elaborate cases).run
            stateAfterScrutinee with
      | error err =>
          simp [hScrutinee, hCases] at hElab
      | ok caseResult =>
          rcases caseResult with ⟨frontendCases, stateAfterCases⟩
          cases hDefault :
              (Elab.Stmt.List.elaborateBlock defaultBody true).run
                stateAfterCases with
          | error err =>
              simp [hScrutinee, hCases, hDefault] at hElab
          | ok defaultResult =>
              rcases defaultResult with
                ⟨frontendDefault, stateAfterDefault⟩
              simp [hScrutinee, hCases, hDefault] at hElab
              rcases hElab with ⟨rfl, _hState⟩
              exact
                ⟨frontendScrutinee, frontendCases, frontendDefault,
                  stateAfterScrutinee, stateAfterCases, stateAfterDefault,
                  rfl, hCases, hDefault, rfl⟩

theorem ifThen_elaborate_parts
    {condition : Raw.Expr} {body : List Raw.Stmt}
    {frontendStmt : Frontend.Stmt} {state state' : Elab.State}
    (hElab :
      (Elab.Stmt.elaborate (.ifThen condition body)).run state =
        .ok (frontendStmt, state')) :
    ∃ (frontendCondition : Frontend.Expr)
      (frontendBody : List Frontend.Stmt)
      (stateAfterCondition stateAfterBody : Elab.State),
      (Elab.Expr.elaborate condition).run state =
        .ok (frontendCondition, stateAfterCondition) ∧
        (Elab.Stmt.List.elaborateBlock body true).run
          stateAfterCondition =
          .ok (frontendBody, stateAfterBody) ∧
        frontendStmt = .ifThen frontendCondition frontendBody := by
  unfold Elab.Stmt.elaborate at hElab
  cases hCondition : (Elab.Expr.elaborate condition).run state with
  | error err =>
      simp [hCondition] at hElab
  | ok conditionResult =>
      rcases conditionResult with
        ⟨frontendCondition, stateAfterCondition⟩
      cases hBody :
          (Elab.Stmt.List.elaborateBlock body true).run
            stateAfterCondition with
      | error err =>
          simp [hCondition, hBody] at hElab
      | ok bodyResult =>
          rcases bodyResult with ⟨frontendBody, stateAfterBody⟩
          simp [hCondition, hBody] at hElab
          rcases hElab with ⟨rfl, _hState⟩
          exact
            ⟨frontendCondition, frontendBody, stateAfterCondition,
              stateAfterBody, rfl, hBody, rfl⟩

theorem forLoop_elaborate_parts
    {pre post body : List Raw.Stmt} {condition : Raw.Expr}
    {frontendStmt : Frontend.Stmt} {state state' : Elab.State}
    (hElab :
      (Elab.Stmt.elaborate (.forLoop pre condition post body)).run state =
        .ok (frontendStmt, state')) :
    ∃ (frontendPre : List Frontend.Stmt)
      (frontendCondition : Frontend.Expr)
      (frontendPost frontendBody : List Frontend.Stmt)
      (stateBeforePre stateAfterPre stateAfterCondition stateAfterPost
        stateAfterBody : Elab.State),
      (if Elab.Stmt.List.hasImmediateFunctionDefinition pre then
          (Elab.Stmt.List.elaborateForInitBlockWithScope pre).run
            stateBeforePre
        else
          (Elab.Stmt.List.elaborateBlock pre false).run stateBeforePre) =
        .ok (frontendPre, stateAfterPre) ∧
        (Elab.Expr.elaborate condition).run stateAfterPre =
          .ok (frontendCondition, stateAfterCondition) ∧
        (Elab.Stmt.List.elaborateBlock post true).run
          stateAfterCondition =
          .ok (frontendPost, stateAfterPost) ∧
        (Elab.Stmt.List.elaborateBlock body true).run stateAfterPost =
          .ok (frontendBody, stateAfterBody) ∧
        frontendStmt =
          .forLoop frontendPre frontendCondition frontendPost frontendBody := by
  unfold Elab.Stmt.elaborate at hElab
  cases hPush : Elab.pushIdentifierScope.run state with
  | error err =>
      simp [hPush] at hElab
  | ok pushResult =>
      rcases pushResult with ⟨unitPush, stateAfterPush⟩
      cases hPreHas :
          Elab.Stmt.List.hasImmediateFunctionDefinition pre
      · cases hPre :
            (Elab.Stmt.List.elaborateBlock pre false).run
              stateAfterPush with
        | error err =>
            simp [hPush, hPreHas, hPre] at hElab
        | ok preResult =>
            rcases preResult with ⟨frontendPre, stateAfterPre⟩
            cases hCondition :
                (Elab.Expr.elaborate condition).run stateAfterPre with
            | error err =>
                simp [hPush, hPreHas, hPre, hCondition] at hElab
            | ok conditionResult =>
                rcases conditionResult with
                  ⟨frontendCondition, stateAfterCondition⟩
                cases hPost :
                    (Elab.Stmt.List.elaborateBlock post true).run
                      stateAfterCondition with
                | error err =>
                    simp [hPush, hPreHas, hPre, hCondition, hPost]
                      at hElab
                | ok postResult =>
                    rcases postResult with
                      ⟨frontendPost, stateAfterPost⟩
                    cases hBody :
                        (Elab.Stmt.List.elaborateBlock body true).run
                          stateAfterPost with
                    | error err =>
                        simp [hPush, hPreHas, hPre, hCondition, hPost,
                          hBody] at hElab
                    | ok bodyResult =>
                        rcases bodyResult with
                          ⟨frontendBody, stateAfterBody⟩
                        cases hPop :
                            Elab.popIdentifierScope.run stateAfterBody with
                        | error err =>
                            simp [hPush, hPreHas, hPre, hCondition, hPost,
                              hBody, hPop] at hElab
                        | ok popResult =>
                            rcases popResult with
                              ⟨unitPop, stateAfterPop⟩
                            simp [hPush, hPreHas, hPre, hCondition, hPost,
                              hBody, hPop] at hElab
                            rcases hElab with ⟨rfl, _hState⟩
                            exact
                              ⟨frontendPre, frontendCondition, frontendPost,
                                frontendBody, stateAfterPush, stateAfterPre,
                                stateAfterCondition, stateAfterPost,
                                stateAfterBody,
                                by simpa [hPreHas] using hPre,
                                hCondition, hPost, hBody, rfl⟩
      · cases hPre :
            (Elab.Stmt.List.elaborateForInitBlockWithScope pre).run
              stateAfterPush with
        | error err =>
            simp [hPush, hPreHas, hPre] at hElab
        | ok preResult =>
            rcases preResult with ⟨frontendPre, stateAfterPre⟩
            cases hCondition :
                (Elab.Expr.elaborate condition).run stateAfterPre with
            | error err =>
                simp [hPush, hPreHas, hPre, hCondition] at hElab
            | ok conditionResult =>
                rcases conditionResult with
                  ⟨frontendCondition, stateAfterCondition⟩
                cases hPost :
                    (Elab.Stmt.List.elaborateBlock post true).run
                      stateAfterCondition with
                | error err =>
                    simp [hPush, hPreHas, hPre, hCondition, hPost]
                      at hElab
                | ok postResult =>
                    rcases postResult with
                      ⟨frontendPost, stateAfterPost⟩
                    cases hBody :
                        (Elab.Stmt.List.elaborateBlock body true).run
                          stateAfterPost with
                    | error err =>
                        simp [hPush, hPreHas, hPre, hCondition, hPost,
                          hBody] at hElab
                    | ok bodyResult =>
                        rcases bodyResult with
                          ⟨frontendBody, stateAfterBody⟩
                        cases hPopFunction :
                            Elab.popFunctionScope.run stateAfterBody with
                        | error err =>
                            simp [hPush, hPreHas, hPre, hCondition, hPost,
                              hBody, hPopFunction] at hElab
                        | ok popFunctionResult =>
                            rcases popFunctionResult with
                              ⟨unitPopFunction, stateAfterPopFunction⟩
                            cases hPop :
                                Elab.popIdentifierScope.run
                                  stateAfterPopFunction with
                            | error err =>
                                simp [hPush, hPreHas, hPre, hCondition,
                                  hPost, hBody, hPopFunction, hPop]
                                  at hElab
                            | ok popResult =>
                                rcases popResult with
                                  ⟨unitPop, stateAfterPop⟩
                                simp [hPush, hPreHas, hPre, hCondition,
                                  hPost, hBody, hPopFunction, hPop]
                                  at hElab
                                rcases hElab with ⟨rfl, _hState⟩
                                exact
                                  ⟨frontendPre, frontendCondition,
                                    frontendPost, frontendBody,
                                    stateAfterPush, stateAfterPre,
                                    stateAfterCondition, stateAfterPost,
                                    stateAfterBody,
                                    by simpa [hPreHas] using hPre,
                                    hCondition, hPost, hBody, rfl⟩

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

namespace FunctionDef

theorem elaborate_bodyBlock_exists
    {params returns : List Name} {rawBody : List Raw.Stmt}
    {fn : Frontend.FunctionDef} {state state' : Elab.State}
    (hElab :
      (Elab.FunctionDef.elaborate params returns rawBody).run state =
        .ok (fn, state')) :
    ∃ (frontendBody : List Frontend.Stmt)
      (stateBeforeBody stateAfterBody : Elab.State),
      (Elab.Stmt.List.elaborateBlock rawBody true).run stateBeforeBody =
        .ok (frontendBody, stateAfterBody) ∧
        fn.body = frontendBody := by
  unfold Elab.FunctionDef.elaborate at hElab
  cases hPush : Elab.pushIdentifierScope.run state with
  | error err =>
      simp [hPush] at hElab
  | ok pushResult =>
      rcases pushResult with ⟨unitPush, stateAfterPush⟩
      cases hDeclare :
          (Elab.declareIdentifiers (params ++ returns)
            "function parameter/result").run stateAfterPush with
      | error err =>
          simp [hPush, hDeclare] at hElab
      | ok declareResult =>
          rcases declareResult with ⟨unitDeclare, stateAfterDeclare⟩
          cases hBody :
              (Elab.Stmt.List.elaborateBlock rawBody true).run
                stateAfterDeclare with
          | error err =>
              simp [hPush, hDeclare, hBody] at hElab
          | ok bodyResult =>
              rcases bodyResult with ⟨frontendBody, stateAfterBody⟩
              cases hPop :
                  Elab.popIdentifierScope.run stateAfterBody with
              | error err =>
                  simp [hPush, hDeclare, hBody, hPop] at hElab
              | ok popResult =>
                  rcases popResult with ⟨unitPop, stateAfterPop⟩
                  simp [hPush, hDeclare, hBody, hPop] at hElab
                  rcases hElab with ⟨rfl, _hState⟩
                  exact
                    ⟨frontendBody, stateAfterDeclare, stateAfterBody,
                      hBody, rfl⟩

end FunctionDef

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

mutual
  theorem StmtUserCall.elaborate
      {functionName : Name} {rawArgs : List Raw.Expr}
      {rawStmt : Raw.Stmt} {frontendStmt : Frontend.Stmt}
      {state state' : Elab.State}
      (hOccurrence : StmtUserCall functionName rawArgs rawStmt)
      (hNotMemoryguard : functionName ≠ "memoryguard")
      (hNotClz : functionName ≠ "clz")
      (hKind : CallClass.classifyCall functionName = .user)
      (hElab :
        (Elab.Stmt.elaborate rawStmt).run state =
          .ok (frontendStmt, state')) :
      ∃ (generated : Name) (frontendArgs : List Frontend.Expr),
        StmtElaborationOccurrence generated frontendArgs frontendStmt := by
    cases hOccurrence with
    | @block body hBody =>
        cases hBodyElab :
            (Elab.Stmt.List.elaborateBlock body true).run state with
        | error err =>
            simp [Elab.Stmt.elaborate, hBodyElab] at hElab
        | ok bodyResult =>
            rcases bodyResult with ⟨frontendBody, stateAfterBody⟩
            simp [Elab.Stmt.elaborate, hBodyElab] at hElab
            rcases hElab with ⟨rfl, _hState⟩
            rcases Stmt.List.elaborateBlock_elaborate_exists
                hBodyElab with
              ⟨stateBeforeList, stateAfterList, hList⟩
            rcases StmtListUserCall.elaborate hBody hNotMemoryguard
                hNotClz hKind hList with
              ⟨generated, frontendArgs, hFrontendBody⟩
            exact
              ⟨generated, frontendArgs,
                StmtElaborationOccurrence.block hFrontendBody⟩
    | @variableDeclarationValue names value hValue =>
        cases hValueElab : (Elab.Expr.elaborate value).run state with
        | error err =>
            simp [Elab.Stmt.elaborate, hValueElab] at hElab
        | ok valueResult =>
            rcases valueResult with ⟨frontendValue, stateAfterValue⟩
            cases hDeclare :
                (Elab.declareIdentifiers names "variable").run
                  stateAfterValue with
            | error err =>
                simp [Elab.Stmt.elaborate, hValueElab, hDeclare]
                  at hElab
            | ok declareResult =>
                rcases declareResult with
                  ⟨unitDeclare, stateAfterDeclare⟩
                simp [Elab.Stmt.elaborate, hValueElab, hDeclare]
                  at hElab
                rcases hElab with ⟨rfl, _hState⟩
                rcases ExprUserCall.elaborate hValue hNotMemoryguard
                    hNotClz hKind hValueElab with
                  ⟨generated, frontendArgs, hFrontendExpr⟩
                exact
                  ⟨generated, frontendArgs,
                    StmtElaborationOccurrence.executable
                      (FrontendOccurrence.StmtUserCall.letValue
                        hFrontendExpr)⟩
    | @assignmentValue names value hValue =>
        rcases Stmt.assignment_elaborate_value_exists hElab with
          ⟨frontendValue, stateBeforeValue, stateAfterValue,
            hValueElab, hStmtEq⟩
        subst frontendStmt
        rcases ExprUserCall.elaborate hValue hNotMemoryguard hNotClz
            hKind hValueElab with
          ⟨generated, frontendArgs, hFrontendExpr⟩
        exact
          ⟨generated, frontendArgs,
            StmtElaborationOccurrence.executable
              (FrontendOccurrence.StmtUserCall.assignValue
                hFrontendExpr)⟩
    | @expressionStatement value hValue =>
        cases hValueElab : (Elab.Expr.elaborate value).run state with
        | error err =>
            simp [Elab.Stmt.elaborate, hValueElab] at hElab
        | ok valueResult =>
            rcases valueResult with ⟨frontendValue, stateAfterValue⟩
            simp [Elab.Stmt.elaborate, hValueElab] at hElab
            rcases hElab with ⟨rfl, _hState⟩
            rcases ExprUserCall.elaborate hValue hNotMemoryguard hNotClz
                hKind hValueElab with
              ⟨generated, frontendArgs, hFrontendExpr⟩
            exact
              ⟨generated, frontendArgs,
                StmtElaborationOccurrence.executable
                  (FrontendOccurrence.StmtUserCall.exprStmt
                    hFrontendExpr)⟩
    | @functionBody name params returns body hBody =>
        cases hFn :
            (Elab.FunctionDef.elaborate params returns body).run state with
        | error err =>
            simp [Elab.Stmt.elaborate, hFn] at hElab
        | ok fnResult =>
            rcases fnResult with ⟨fn, stateAfterFn⟩
            simp [Elab.Stmt.elaborate, hFn] at hElab
            rcases hElab with ⟨rfl, _hState⟩
            rcases FunctionDef.elaborate_bodyBlock_exists hFn with
              ⟨frontendBody, stateBeforeBody, stateAfterBody,
                hBodyBlock, hFnBody⟩
            rcases Stmt.List.elaborateBlock_elaborate_exists
                hBodyBlock with
              ⟨stateBeforeList, stateAfterList, hList⟩
            rcases StmtListUserCall.elaborate hBody hNotMemoryguard
                hNotClz hKind hList with
              ⟨generated, frontendArgs, hFrontendBody⟩
            rw [hFnBody]
            exact
              ⟨generated, frontendArgs,
                StmtElaborationOccurrence.functionBody
                  hFrontendBody⟩
    | @switchScrutinee scrutinee cases defaultBody hScrutinee =>
        rcases Stmt.switch_elaborate_parts hElab with
          ⟨frontendScrutinee, frontendCases, frontendDefault,
            stateAfterScrutinee, stateAfterCases, stateAfterDefault,
            hScrutineeElab, hCasesElab, hDefaultElab, hStmtEq⟩
        subst frontendStmt
        rcases ExprUserCall.elaborate hScrutinee hNotMemoryguard
            hNotClz hKind hScrutineeElab with
          ⟨generated, frontendArgs, hFrontendExpr⟩
        exact
          ⟨generated, frontendArgs,
            StmtElaborationOccurrence.executable
              (FrontendOccurrence.StmtUserCall.switchScrutinee
                hFrontendExpr)⟩
    | @switchCase scrutinee cases defaultBody hCases =>
        rcases Stmt.switch_elaborate_parts hElab with
          ⟨frontendScrutinee, frontendCases, frontendDefault,
            stateAfterScrutinee, stateAfterCases, stateAfterDefault,
            hScrutineeElab, hCasesElab, hDefaultElab, hStmtEq⟩
        subst frontendStmt
        rcases CaseListUserCall.elaborate hCases hNotMemoryguard
            hNotClz hKind hCasesElab with
          ⟨generated, frontendArgs, hFrontendCases⟩
        exact
          ⟨generated, frontendArgs,
            StmtElaborationOccurrence.switchCase hFrontendCases⟩
    | @switchDefault scrutinee cases defaultBody hDefault =>
        rcases Stmt.switch_elaborate_parts hElab with
          ⟨frontendScrutinee, frontendCases, frontendDefault,
            stateAfterScrutinee, stateAfterCases, stateAfterDefault,
            hScrutineeElab, hCasesElab, hDefaultElab, hStmtEq⟩
        subst frontendStmt
        rcases Stmt.List.elaborateBlock_elaborate_exists hDefaultElab with
          ⟨stateBeforeList, stateAfterList, hList⟩
        rcases StmtListUserCall.elaborate hDefault hNotMemoryguard
            hNotClz hKind hList with
          ⟨generated, frontendArgs, hFrontendDefault⟩
        exact
          ⟨generated, frontendArgs,
            StmtElaborationOccurrence.switchDefault hFrontendDefault⟩
    | @forPre pre post body condition hPreOccurrence =>
        rcases Stmt.forLoop_elaborate_parts hElab with
          ⟨frontendPre, frontendCondition, frontendPost, frontendBody,
            stateBeforePre, stateAfterPre, stateAfterCondition,
            stateAfterPost, stateAfterBody, hPreElab, hConditionElab,
            hPostElab, hBodyElab, hStmtEq⟩
        subst frontendStmt
        have hPreList :
            ∃ (stateBeforeList stateAfterList : Elab.State),
              (Elab.Stmt.List.elaborate pre).run stateBeforeList =
                .ok (frontendPre, stateAfterList) := by
          cases hPreHas :
              Elab.Stmt.List.hasImmediateFunctionDefinition pre
          · have hBlock :
                (Elab.Stmt.List.elaborateBlock pre false).run
                  stateBeforePre =
                  .ok (frontendPre, stateAfterPre) := by
              simpa [hPreHas] using hPreElab
            exact Stmt.List.elaborateBlock_elaborate_exists hBlock
          · have hForInit :
                (Elab.Stmt.List.elaborateForInitBlockWithScope pre).run
                  stateBeforePre =
                  .ok (frontendPre, stateAfterPre) := by
              simpa [hPreHas] using hPreElab
            exact
              Stmt.List.elaborateForInitBlockWithScope_elaborate_exists
                hForInit
        rcases hPreList with ⟨stateBeforeList, stateAfterList, hList⟩
        rcases StmtListUserCall.elaborate hPreOccurrence hNotMemoryguard
            hNotClz hKind hList with
          ⟨generated, frontendArgs, hFrontendPre⟩
        exact
          ⟨generated, frontendArgs,
            StmtElaborationOccurrence.forPre hFrontendPre⟩
    | @forCondition pre post body condition hConditionOccurrence =>
        rcases Stmt.forLoop_elaborate_parts hElab with
          ⟨frontendPre, frontendCondition, frontendPost, frontendBody,
            stateBeforePre, stateAfterPre, stateAfterCondition,
            stateAfterPost, stateAfterBody, hPreElab, hConditionElab,
            hPostElab, hBodyElab, hStmtEq⟩
        subst frontendStmt
        rcases ExprUserCall.elaborate hConditionOccurrence hNotMemoryguard
            hNotClz hKind hConditionElab with
          ⟨generated, frontendArgs, hFrontendExpr⟩
        exact
          ⟨generated, frontendArgs,
            StmtElaborationOccurrence.executable
              (FrontendOccurrence.StmtUserCall.forCondition
                hFrontendExpr)⟩
    | @forPost pre post body condition hPostOccurrence =>
        rcases Stmt.forLoop_elaborate_parts hElab with
          ⟨frontendPre, frontendCondition, frontendPost, frontendBody,
            stateBeforePre, stateAfterPre, stateAfterCondition,
            stateAfterPost, stateAfterBody, hPreElab, hConditionElab,
            hPostElab, hBodyElab, hStmtEq⟩
        subst frontendStmt
        rcases Stmt.List.elaborateBlock_elaborate_exists hPostElab with
          ⟨stateBeforeList, stateAfterList, hList⟩
        rcases StmtListUserCall.elaborate hPostOccurrence hNotMemoryguard
            hNotClz hKind hList with
          ⟨generated, frontendArgs, hFrontendPost⟩
        exact
          ⟨generated, frontendArgs,
            StmtElaborationOccurrence.forPost hFrontendPost⟩
    | @forBody pre post body condition hBodyOccurrence =>
        rcases Stmt.forLoop_elaborate_parts hElab with
          ⟨frontendPre, frontendCondition, frontendPost, frontendBody,
            stateBeforePre, stateAfterPre, stateAfterCondition,
            stateAfterPost, stateAfterBody, hPreElab, hConditionElab,
            hPostElab, hBodyElab, hStmtEq⟩
        subst frontendStmt
        rcases Stmt.List.elaborateBlock_elaborate_exists hBodyElab with
          ⟨stateBeforeList, stateAfterList, hList⟩
        rcases StmtListUserCall.elaborate hBodyOccurrence hNotMemoryguard
            hNotClz hKind hList with
          ⟨generated, frontendArgs, hFrontendBody⟩
        exact
          ⟨generated, frontendArgs,
            StmtElaborationOccurrence.forBody hFrontendBody⟩
    | @ifCondition condition body hConditionOccurrence =>
        rcases Stmt.ifThen_elaborate_parts hElab with
          ⟨frontendCondition, frontendBody, stateAfterCondition,
            stateAfterBody, hConditionElab, hBodyElab, hStmtEq⟩
        subst frontendStmt
        rcases ExprUserCall.elaborate hConditionOccurrence hNotMemoryguard
            hNotClz hKind hConditionElab with
          ⟨generated, frontendArgs, hFrontendExpr⟩
        exact
          ⟨generated, frontendArgs,
            StmtElaborationOccurrence.executable
              (FrontendOccurrence.StmtUserCall.ifCondition
                hFrontendExpr)⟩
    | @ifBody condition body hBodyOccurrence =>
        rcases Stmt.ifThen_elaborate_parts hElab with
          ⟨frontendCondition, frontendBody, stateAfterCondition,
            stateAfterBody, hConditionElab, hBodyElab, hStmtEq⟩
        subst frontendStmt
        rcases Stmt.List.elaborateBlock_elaborate_exists hBodyElab with
          ⟨stateBeforeList, stateAfterList, hList⟩
        rcases StmtListUserCall.elaborate hBodyOccurrence hNotMemoryguard
            hNotClz hKind hList with
          ⟨generated, frontendArgs, hFrontendBody⟩
        exact
          ⟨generated, frontendArgs,
            StmtElaborationOccurrence.ifBody hFrontendBody⟩

  theorem StmtListUserCall.elaborate
      {functionName : Name} {rawArgs : List Raw.Expr}
      {rawStmts : List Raw.Stmt} {frontendStmts : List Frontend.Stmt}
      {state state' : Elab.State}
      (hOccurrence : StmtListUserCall functionName rawArgs rawStmts)
      (hNotMemoryguard : functionName ≠ "memoryguard")
      (hNotClz : functionName ≠ "clz")
      (hKind : CallClass.classifyCall functionName = .user)
      (hElab :
        (Elab.Stmt.List.elaborate rawStmts).run state =
          .ok (frontendStmts, state')) :
      ∃ (generated : Name) (frontendArgs : List Frontend.Expr),
        StmtListElaborationOccurrence generated frontendArgs frontendStmts := by
    cases hOccurrence with
    | @head stmt rest hStmtOccurrence =>
        simp only [Elab.Stmt.List.elaborate] at hElab
        cases hHead : (Elab.Stmt.elaborate stmt).run state with
        | error err =>
            simp [hHead] at hElab
        | ok headResult =>
            rcases headResult with ⟨frontendStmt, stateAfterHead⟩
            cases hTail :
                (Elab.Stmt.List.elaborate rest).run stateAfterHead with
            | error err =>
                simp [hHead, hTail] at hElab
            | ok tailResult =>
                rcases tailResult with ⟨frontendRest, stateAfterTail⟩
                simp [hHead, hTail] at hElab
                rcases hElab with ⟨rfl, _hState⟩
                rcases StmtUserCall.elaborate hStmtOccurrence
                    hNotMemoryguard hNotClz hKind hHead with
                  ⟨generated, frontendArgs, hFrontendStmt⟩
                exact
                  ⟨generated, frontendArgs,
                    StmtListElaborationOccurrence.head
                      hFrontendStmt⟩
    | @tail stmt rest hTailOccurrence =>
        simp only [Elab.Stmt.List.elaborate] at hElab
        cases hHead : (Elab.Stmt.elaborate stmt).run state with
        | error err =>
            simp [hHead] at hElab
        | ok headResult =>
            rcases headResult with ⟨frontendStmt, stateAfterHead⟩
            cases hTail :
                (Elab.Stmt.List.elaborate rest).run stateAfterHead with
            | error err =>
                simp [hHead, hTail] at hElab
            | ok tailResult =>
                rcases tailResult with ⟨frontendRest, stateAfterTail⟩
                simp [hHead, hTail] at hElab
                rcases hElab with ⟨rfl, _hState⟩
                rcases StmtListUserCall.elaborate hTailOccurrence
                    hNotMemoryguard hNotClz hKind hTail with
                  ⟨generated, frontendArgs, hFrontendTail⟩
                exact
                  ⟨generated, frontendArgs,
                    StmtListElaborationOccurrence.tail
                      hFrontendTail⟩

  theorem CaseListUserCall.elaborate
      {functionName : Name} {rawArgs : List Raw.Expr}
      {rawCases : List (Raw.SwitchCaseValue × List Raw.Stmt)}
      {frontendCases : List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
      {state state' : Elab.State}
      (hOccurrence : CaseListUserCall functionName rawArgs rawCases)
      (hNotMemoryguard : functionName ≠ "memoryguard")
      (hNotClz : functionName ≠ "clz")
      (hKind : CallClass.classifyCall functionName = .user)
      (hElab :
        (Elab.Stmt.CaseList.elaborate rawCases).run state =
          .ok (frontendCases, state')) :
      ∃ (generated : Name) (frontendArgs : List Frontend.Expr),
        CaseListElaborationOccurrence generated frontendArgs frontendCases := by
    cases hOccurrence with
    | @head value body rest hBodyOccurrence =>
        simp only [Elab.Stmt.CaseList.elaborate] at hElab
        cases hValue : Elab.SwitchCaseValue.elaborate value with
        | error err =>
            simp [hValue] at hElab
            unfold Elab.throw at hElab
            cases hElab
        | ok frontendValue =>
            cases hBody :
                (Elab.Stmt.List.elaborateBlock body true).run state with
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
                    rcases tailResult with
                      ⟨frontendRest, stateAfterTail⟩
                    simp [hValue, hBody, hTail] at hElab
                    rcases hElab with ⟨rfl, _hState⟩
                    rcases Stmt.List.elaborateBlock_elaborate_exists
                        hBody with
                      ⟨stateBeforeList, stateAfterList, hList⟩
                    rcases StmtListUserCall.elaborate hBodyOccurrence
                        hNotMemoryguard hNotClz hKind hList with
                      ⟨generated, frontendArgs, hFrontendBody⟩
                    exact
                      ⟨generated, frontendArgs,
                        CaseListElaborationOccurrence.head
                          hFrontendBody⟩
    | @tail head rest hTailOccurrence =>
        rcases head with ⟨value, body⟩
        simp only [Elab.Stmt.CaseList.elaborate] at hElab
        cases hValue : Elab.SwitchCaseValue.elaborate value with
        | error err =>
            simp [hValue] at hElab
            unfold Elab.throw at hElab
            cases hElab
        | ok frontendValue =>
            cases hBody :
                (Elab.Stmt.List.elaborateBlock body true).run state with
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
                    rcases tailResult with
                      ⟨frontendRest, stateAfterTail⟩
                    simp [hValue, hBody, hTail] at hElab
                    rcases hElab with ⟨rfl, _hState⟩
                    rcases CaseListUserCall.elaborate hTailOccurrence
                        hNotMemoryguard hNotClz hKind hTail with
                      ⟨generated, frontendArgs, hFrontendTail⟩
                    exact
                      ⟨generated, frontendArgs,
                        CaseListElaborationOccurrence.tail
                          hFrontendTail⟩
end

end RawOccurrence
end RawAst
end Solidity
end EvmCompiler
