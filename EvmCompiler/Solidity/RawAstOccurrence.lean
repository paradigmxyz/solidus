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

mutual
  inductive StmtElaborationRoute (functionName : Name)
      (args : List Frontend.Expr) : Frontend.Stmt → Prop where
    | current {stmt : Frontend.Stmt} :
        FrontendOccurrence.StmtUserCall functionName args stmt →
          StmtElaborationRoute functionName args stmt
    | functionBody
        {stmt : Frontend.Stmt}
        (contextName : Name) (contextFn : Frontend.FunctionDef) :
        FrontendOccurrence.StmtListUserCall functionName args
          contextFn.body →
          StmtElaborationRoute functionName args stmt

  inductive StmtListElaborationRoute (functionName : Name)
      (args : List Frontend.Expr) : List Frontend.Stmt → Prop where
    | current {stmts : List Frontend.Stmt} :
        FrontendOccurrence.StmtListUserCall functionName args stmts →
          StmtListElaborationRoute functionName args stmts
    | functionBody
        {stmts : List Frontend.Stmt}
        (contextName : Name) (contextFn : Frontend.FunctionDef) :
        FrontendOccurrence.StmtListUserCall functionName args
          contextFn.body →
          StmtListElaborationRoute functionName args stmts

  inductive CaseListElaborationRoute (functionName : Name)
      (args : List Frontend.Expr) :
      List (Frontend.SwitchCaseValue × List Frontend.Stmt) → Prop where
    | current {cases : List (Frontend.SwitchCaseValue × List Frontend.Stmt)} :
        FrontendOccurrence.CaseListUserCall functionName args cases →
          CaseListElaborationRoute functionName args cases
    | functionBody
        {cases : List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
        (contextName : Name) (contextFn : Frontend.FunctionDef) :
        FrontendOccurrence.StmtListUserCall functionName args
          contextFn.body →
          CaseListElaborationRoute functionName args cases
end

mutual
  theorem StmtElaborationOccurrence.route
      {functionName : Name} {args : List Frontend.Expr}
      {stmt : Frontend.Stmt}
      (hOccurrence :
        StmtElaborationOccurrence functionName args stmt) :
      StmtElaborationRoute functionName args stmt := by
    cases hOccurrence with
    | executable hStmt =>
        exact StmtElaborationRoute.current hStmt
    | block hBody =>
        cases StmtListElaborationOccurrence.route hBody with
        | current hCurrent =>
            exact
              StmtElaborationRoute.current
                (FrontendOccurrence.StmtUserCall.block hCurrent)
        | functionBody contextName contextFn hFunctionBody =>
            exact
              StmtElaborationRoute.functionBody contextName contextFn
                hFunctionBody
    | @functionBody name params returns body hBody =>
        cases StmtListElaborationOccurrence.route hBody with
        | current hCurrent =>
            exact
              StmtElaborationRoute.functionBody name
                ({ params := params, returns := returns, body := body } :
                  Frontend.FunctionDef)
                hCurrent
        | functionBody contextName contextFn hFunctionBody =>
            exact
              StmtElaborationRoute.functionBody contextName contextFn
                hFunctionBody
    | switchCase hCases =>
        cases CaseListElaborationOccurrence.route hCases with
        | current hCurrent =>
            exact
              StmtElaborationRoute.current
                (FrontendOccurrence.StmtUserCall.switchCase hCurrent)
        | functionBody contextName contextFn hFunctionBody =>
            exact
              StmtElaborationRoute.functionBody contextName contextFn
                hFunctionBody
    | switchDefault hDefault =>
        cases StmtListElaborationOccurrence.route hDefault with
        | current hCurrent =>
            exact
              StmtElaborationRoute.current
                (FrontendOccurrence.StmtUserCall.switchDefault hCurrent)
        | functionBody contextName contextFn hFunctionBody =>
            exact
              StmtElaborationRoute.functionBody contextName contextFn
                hFunctionBody
    | forPre hPre =>
        cases StmtListElaborationOccurrence.route hPre with
        | current hCurrent =>
            exact
              StmtElaborationRoute.current
                (FrontendOccurrence.StmtUserCall.forPre hCurrent)
        | functionBody contextName contextFn hFunctionBody =>
            exact
              StmtElaborationRoute.functionBody contextName contextFn
                hFunctionBody
    | forPost hPost =>
        cases StmtListElaborationOccurrence.route hPost with
        | current hCurrent =>
            exact
              StmtElaborationRoute.current
                (FrontendOccurrence.StmtUserCall.forPost hCurrent)
        | functionBody contextName contextFn hFunctionBody =>
            exact
              StmtElaborationRoute.functionBody contextName contextFn
                hFunctionBody
    | forBody hBody =>
        cases StmtListElaborationOccurrence.route hBody with
        | current hCurrent =>
            exact
              StmtElaborationRoute.current
                (FrontendOccurrence.StmtUserCall.forBody hCurrent)
        | functionBody contextName contextFn hFunctionBody =>
            exact
              StmtElaborationRoute.functionBody contextName contextFn
                hFunctionBody
    | ifBody hBody =>
        cases StmtListElaborationOccurrence.route hBody with
        | current hCurrent =>
            exact
              StmtElaborationRoute.current
                (FrontendOccurrence.StmtUserCall.ifBody hCurrent)
        | functionBody contextName contextFn hFunctionBody =>
            exact
              StmtElaborationRoute.functionBody contextName contextFn
                hFunctionBody

  theorem StmtListElaborationOccurrence.route
      {functionName : Name} {args : List Frontend.Expr}
      {stmts : List Frontend.Stmt}
      (hOccurrence :
        StmtListElaborationOccurrence functionName args stmts) :
      StmtListElaborationRoute functionName args stmts := by
    cases hOccurrence with
    | head hStmt =>
        cases StmtElaborationOccurrence.route hStmt with
        | current hCurrent =>
            exact
              StmtListElaborationRoute.current
                (FrontendOccurrence.StmtListUserCall.head hCurrent)
        | functionBody contextName contextFn hFunctionBody =>
            exact
              StmtListElaborationRoute.functionBody contextName contextFn
                hFunctionBody
    | tail hTail =>
        cases StmtListElaborationOccurrence.route hTail with
        | current hCurrent =>
            exact
              StmtListElaborationRoute.current
                (FrontendOccurrence.StmtListUserCall.tail hCurrent)
        | functionBody contextName contextFn hFunctionBody =>
            exact
              StmtListElaborationRoute.functionBody contextName contextFn
                hFunctionBody

  theorem CaseListElaborationOccurrence.route
      {functionName : Name} {args : List Frontend.Expr}
      {cases : List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
      (hOccurrence :
        CaseListElaborationOccurrence functionName args cases) :
      CaseListElaborationRoute functionName args cases := by
    cases hOccurrence with
    | head hBody =>
        cases StmtListElaborationOccurrence.route hBody with
        | current hCurrent =>
            exact
              CaseListElaborationRoute.current
                (FrontendOccurrence.CaseListUserCall.head hCurrent)
        | functionBody contextName contextFn hFunctionBody =>
            exact
              CaseListElaborationRoute.functionBody contextName contextFn
                hFunctionBody
    | tail hTail =>
        cases CaseListElaborationOccurrence.route hTail with
        | current hCurrent =>
            exact
              CaseListElaborationRoute.current
                (FrontendOccurrence.CaseListUserCall.tail hCurrent)
        | functionBody contextName contextFn hFunctionBody =>
            exact
              CaseListElaborationRoute.functionBody contextName contextFn
                hFunctionBody
end

inductive CodeElaborationRoute (state : Elab.State)
    (functionName : Name) (args : List Frontend.Expr)
    (dispatcher : List Frontend.Stmt) : Prop where
  | dispatcher :
      FrontendOccurrence.StmtListUserCall functionName args dispatcher →
        CodeElaborationRoute state functionName args dispatcher
  | functionBody
      (contextName : Name) (contextFn : Frontend.FunctionDef) :
      (contextName, contextFn) ∈ state.hoistedFunctions →
        FrontendOccurrence.StmtListUserCall functionName args
          contextFn.body →
          CodeElaborationRoute state functionName args dispatcher

inductive StmtCodeElaborationRoute (state : Elab.State)
    (functionName : Name) (args : List Frontend.Expr) :
    Frontend.Stmt → Prop where
  | current {stmt : Frontend.Stmt} :
      FrontendOccurrence.StmtUserCall functionName args stmt →
        StmtCodeElaborationRoute state functionName args stmt
  | functionBody
      {stmt : Frontend.Stmt}
      (contextName : Name) (contextFn : Frontend.FunctionDef) :
      (contextName, contextFn) ∈ state.hoistedFunctions →
        FrontendOccurrence.StmtListUserCall functionName args
          contextFn.body →
          StmtCodeElaborationRoute state functionName args stmt

inductive CaseListCodeElaborationRoute (state : Elab.State)
    (functionName : Name) (args : List Frontend.Expr) :
    List (Frontend.SwitchCaseValue × List Frontend.Stmt) → Prop where
  | current {cases : List (Frontend.SwitchCaseValue × List Frontend.Stmt)} :
      FrontendOccurrence.CaseListUserCall functionName args cases →
        CaseListCodeElaborationRoute state functionName args cases
  | functionBody
      {cases : List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
      (contextName : Name) (contextFn : Frontend.FunctionDef) :
      (contextName, contextFn) ∈ state.hoistedFunctions →
        FrontendOccurrence.StmtListUserCall functionName args
          contextFn.body →
          CaseListCodeElaborationRoute state functionName args cases

theorem frontendStmtListUserCall_of_mem
    {functionName : Frontend.Name} {args : List Frontend.Expr}
    {stmt : Frontend.Stmt} {stmts : List Frontend.Stmt}
    (hMem : stmt ∈ stmts)
    (hStmt :
      FrontendOccurrence.StmtUserCall functionName args stmt) :
    FrontendOccurrence.StmtListUserCall functionName args stmts := by
  induction stmts with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      simp only [List.mem_cons] at hMem
      rcases hMem with hHere | hTail
      · subst head
        exact FrontendOccurrence.StmtListUserCall.head hStmt
      · exact FrontendOccurrence.StmtListUserCall.tail (ih hTail)

namespace StmtCodeElaborationRoute

theorem retain
    {state state' : Elab.State} {functionName : Name}
    {args : List Frontend.Expr} {stmt : Frontend.Stmt}
    (hRoute : StmtCodeElaborationRoute state functionName args stmt)
    (hRetain :
      ∀ {entry : Name × Frontend.FunctionDef},
        entry ∈ state.hoistedFunctions →
          entry ∈ state'.hoistedFunctions) :
    StmtCodeElaborationRoute state' functionName args stmt := by
  cases hRoute with
  | current hCurrent =>
      exact StmtCodeElaborationRoute.current hCurrent
  | functionBody contextName contextFn hContext hBody =>
      exact
        StmtCodeElaborationRoute.functionBody contextName contextFn
          (hRetain hContext) hBody

theorem toCodeRoute_of_mem
    {state : Elab.State} {functionName : Name}
    {args : List Frontend.Expr} {stmt : Frontend.Stmt}
    {stmts : List Frontend.Stmt}
    (hMem : stmt ∈ stmts)
    (hRoute : StmtCodeElaborationRoute state functionName args stmt) :
    CodeElaborationRoute state functionName args stmts := by
  cases hRoute with
  | current hCurrent =>
      exact
        CodeElaborationRoute.dispatcher
          (frontendStmtListUserCall_of_mem hMem hCurrent)
  | functionBody contextName contextFn hContext hBody =>
      exact
        CodeElaborationRoute.functionBody contextName contextFn
          hContext hBody

theorem toCodeRoute_of_split
    {state : Elab.State} {functionName : Name}
    {args : List Frontend.Expr} {stmt : Frontend.Stmt}
    {pre suffix : List Frontend.Stmt}
    (hRoute : StmtCodeElaborationRoute state functionName args stmt) :
    CodeElaborationRoute state functionName args
      (pre ++ stmt :: suffix) := by
  exact toCodeRoute_of_mem (by simp) hRoute

end StmtCodeElaborationRoute

namespace CaseListCodeElaborationRoute

theorem retain
    {state state' : Elab.State} {functionName : Name}
    {args : List Frontend.Expr}
    {cases : List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
    (hRoute : CaseListCodeElaborationRoute state functionName args cases)
    (hRetain :
      ∀ {entry : Name × Frontend.FunctionDef},
        entry ∈ state.hoistedFunctions →
          entry ∈ state'.hoistedFunctions) :
    CaseListCodeElaborationRoute state' functionName args cases := by
  cases hRoute with
  | current hCurrent =>
      exact CaseListCodeElaborationRoute.current hCurrent
  | functionBody contextName contextFn hContext hBody =>
      exact
        CaseListCodeElaborationRoute.functionBody contextName contextFn
          (hRetain hContext) hBody

theorem toStmtRoute_switchCase
    {state : Elab.State} {functionName : Name}
    {args : List Frontend.Expr} {scrutinee : Frontend.Expr}
    {cases : List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
    {defaultBody : List Frontend.Stmt}
    (hRoute :
      CaseListCodeElaborationRoute state functionName args cases) :
    StmtCodeElaborationRoute state functionName args
      (.switch scrutinee cases defaultBody) := by
  cases hRoute with
  | current hCurrent =>
      exact
        StmtCodeElaborationRoute.current
          (FrontendOccurrence.StmtUserCall.switchCase hCurrent)
  | functionBody contextName contextFn hContext hBody =>
      exact
        StmtCodeElaborationRoute.functionBody contextName contextFn
          hContext hBody

end CaseListCodeElaborationRoute

namespace CodeElaborationRoute

theorem retain
    {state state' : Elab.State} {functionName : Name}
    {args : List Frontend.Expr} {dispatcher : List Frontend.Stmt}
    (hRoute : CodeElaborationRoute state functionName args dispatcher)
    (hRetain :
      ∀ {entry : Name × Frontend.FunctionDef},
        entry ∈ state.hoistedFunctions →
          entry ∈ state'.hoistedFunctions) :
    CodeElaborationRoute state' functionName args dispatcher := by
  cases hRoute with
  | dispatcher hDispatcher =>
      exact CodeElaborationRoute.dispatcher hDispatcher
  | functionBody contextName contextFn hContext hBody =>
      exact
        CodeElaborationRoute.functionBody contextName contextFn
          (hRetain hContext) hBody

theorem liftFunctionBody
    {state state' : Elab.State} {functionName : Name}
    {args : List Frontend.Expr} {dispatcher : List Frontend.Stmt}
    {contextGenerated : Name} {contextFn : Frontend.FunctionDef}
    (hContext : (contextGenerated, contextFn) ∈ state'.hoistedFunctions)
    (hRetain :
      ∀ {entry : Name × Frontend.FunctionDef},
        entry ∈ state.hoistedFunctions →
          entry ∈ state'.hoistedFunctions)
    (hRoute :
      CodeElaborationRoute state functionName args contextFn.body) :
    CodeElaborationRoute state' functionName args dispatcher := by
  cases hRoute with
  | dispatcher hBody =>
      exact
        CodeElaborationRoute.functionBody contextGenerated contextFn
          hContext hBody
  | functionBody innerGenerated innerFn hInner hBody =>
      exact
        CodeElaborationRoute.functionBody innerGenerated innerFn
          (hRetain hInner) hBody

theorem liftFunctionBodyStmt
    {state state' : Elab.State} {functionName : Name}
    {args : List Frontend.Expr} {stmt : Frontend.Stmt}
    {contextGenerated : Name} {contextFn : Frontend.FunctionDef}
    (hContext : (contextGenerated, contextFn) ∈ state'.hoistedFunctions)
    (hRetain :
      ∀ {entry : Name × Frontend.FunctionDef},
        entry ∈ state.hoistedFunctions →
          entry ∈ state'.hoistedFunctions)
    (hRoute :
      CodeElaborationRoute state functionName args contextFn.body) :
    StmtCodeElaborationRoute state' functionName args stmt := by
  cases hRoute with
  | dispatcher hBody =>
      exact
        StmtCodeElaborationRoute.functionBody contextGenerated contextFn
          hContext hBody
  | functionBody innerGenerated innerFn hInner hBody =>
      exact
        StmtCodeElaborationRoute.functionBody innerGenerated innerFn
          (hRetain hInner) hBody

theorem dispatcher_of_stmt_mem
    {state : Elab.State} {functionName : Name}
    {args : List Frontend.Expr} {stmt : Frontend.Stmt}
    {dispatcher : List Frontend.Stmt}
    (hMem : stmt ∈ dispatcher)
    (hStmt : FrontendOccurrence.StmtUserCall functionName args stmt) :
  CodeElaborationRoute state functionName args dispatcher :=
  CodeElaborationRoute.dispatcher
    (frontendStmtListUserCall_of_mem hMem hStmt)

theorem dispatcher_head
    {state : Elab.State} {functionName : Name}
    {args : List Frontend.Expr} {stmt : Frontend.Stmt}
    {rest : List Frontend.Stmt}
    (hStmt : FrontendOccurrence.StmtUserCall functionName args stmt) :
    CodeElaborationRoute state functionName args (stmt :: rest) :=
  CodeElaborationRoute.dispatcher
    (FrontendOccurrence.StmtListUserCall.head hStmt)

theorem dispatcher_tail
    {state : Elab.State} {functionName : Name}
    {args : List Frontend.Expr} {stmt : Frontend.Stmt}
    {rest : List Frontend.Stmt}
    (hRoute : CodeElaborationRoute state functionName args rest) :
    CodeElaborationRoute state functionName args (stmt :: rest) := by
  cases hRoute with
  | dispatcher hDispatcher =>
      exact
        CodeElaborationRoute.dispatcher
          (FrontendOccurrence.StmtListUserCall.tail hDispatcher)
  | functionBody contextName contextFn hContext hBody =>
      exact
        CodeElaborationRoute.functionBody contextName contextFn
          hContext hBody

end CodeElaborationRoute

namespace CodeElaborationRoute

theorem toStmtRoute_block
    {state : Elab.State} {functionName : Name}
    {args : List Frontend.Expr} {body : List Frontend.Stmt}
    (hRoute : CodeElaborationRoute state functionName args body) :
    StmtCodeElaborationRoute state functionName args (.block body) := by
  cases hRoute with
  | dispatcher hCurrent =>
      exact
        StmtCodeElaborationRoute.current
          (FrontendOccurrence.StmtUserCall.block hCurrent)
  | functionBody contextName contextFn hContext hBody =>
      exact
        StmtCodeElaborationRoute.functionBody contextName contextFn
          hContext hBody

theorem toStmtRoute_switchDefault
    {state : Elab.State} {functionName : Name}
    {args : List Frontend.Expr} {scrutinee : Frontend.Expr}
    {cases : List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
    {defaultBody : List Frontend.Stmt}
    (hRoute : CodeElaborationRoute state functionName args defaultBody) :
    StmtCodeElaborationRoute state functionName args
      (.switch scrutinee cases defaultBody) := by
  cases hRoute with
  | dispatcher hCurrent =>
      exact
        StmtCodeElaborationRoute.current
          (FrontendOccurrence.StmtUserCall.switchDefault hCurrent)
  | functionBody contextName contextFn hContext hBody =>
      exact
        StmtCodeElaborationRoute.functionBody contextName contextFn
          hContext hBody

theorem toStmtRoute_forPre
    {state : Elab.State} {functionName : Name}
    {args : List Frontend.Expr} {pre post body : List Frontend.Stmt}
    {condition : Frontend.Expr}
    (hRoute : CodeElaborationRoute state functionName args pre) :
    StmtCodeElaborationRoute state functionName args
      (.forLoop pre condition post body) := by
  cases hRoute with
  | dispatcher hCurrent =>
      exact
        StmtCodeElaborationRoute.current
          (FrontendOccurrence.StmtUserCall.forPre hCurrent)
  | functionBody contextName contextFn hContext hBody =>
      exact
        StmtCodeElaborationRoute.functionBody contextName contextFn
          hContext hBody

theorem toStmtRoute_forPost
    {state : Elab.State} {functionName : Name}
    {args : List Frontend.Expr} {pre post body : List Frontend.Stmt}
    {condition : Frontend.Expr}
    (hRoute : CodeElaborationRoute state functionName args post) :
    StmtCodeElaborationRoute state functionName args
      (.forLoop pre condition post body) := by
  cases hRoute with
  | dispatcher hCurrent =>
      exact
        StmtCodeElaborationRoute.current
          (FrontendOccurrence.StmtUserCall.forPost hCurrent)
  | functionBody contextName contextFn hContext hBody =>
      exact
        StmtCodeElaborationRoute.functionBody contextName contextFn
          hContext hBody

theorem toStmtRoute_forBody
    {state : Elab.State} {functionName : Name}
    {args : List Frontend.Expr} {pre post body : List Frontend.Stmt}
    {condition : Frontend.Expr}
    (hRoute : CodeElaborationRoute state functionName args body) :
    StmtCodeElaborationRoute state functionName args
      (.forLoop pre condition post body) := by
  cases hRoute with
  | dispatcher hCurrent =>
      exact
        StmtCodeElaborationRoute.current
          (FrontendOccurrence.StmtUserCall.forBody hCurrent)
  | functionBody contextName contextFn hContext hBody =>
      exact
        StmtCodeElaborationRoute.functionBody contextName contextFn
          hContext hBody

theorem toStmtRoute_ifBody
    {state : Elab.State} {functionName : Name}
    {args : List Frontend.Expr} {condition : Frontend.Expr}
    {body : List Frontend.Stmt}
    (hRoute : CodeElaborationRoute state functionName args body) :
    StmtCodeElaborationRoute state functionName args
      (.ifThen condition body) := by
  cases hRoute with
  | dispatcher hCurrent =>
      exact
        StmtCodeElaborationRoute.current
          (FrontendOccurrence.StmtUserCall.ifBody hCurrent)
  | functionBody contextName contextFn hContext hBody =>
      exact
        StmtCodeElaborationRoute.functionBody contextName contextFn
          hContext hBody

end CodeElaborationRoute

namespace StmtListElaborationRoute

theorem toCodeRoute
    {state : Elab.State} {functionName : Name}
    {args : List Frontend.Expr} {dispatcher : List Frontend.Stmt}
    (hRoute :
      StmtListElaborationRoute functionName args dispatcher)
    (hContextHoisted :
      ∀ {contextName : Name} {contextFn : Frontend.FunctionDef},
        FrontendOccurrence.StmtListUserCall functionName args
          contextFn.body →
        (contextName, contextFn) ∈ state.hoistedFunctions) :
    CodeElaborationRoute state functionName args dispatcher := by
  cases hRoute with
  | current hCurrent =>
      exact CodeElaborationRoute.dispatcher hCurrent
  | functionBody contextName contextFn hBody =>
      exact
        CodeElaborationRoute.functionBody contextName contextFn
          (hContextHoisted hBody) hBody

end StmtListElaborationRoute

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

theorem elaborate_split
    {pre suffix : List Raw.Stmt} {stmt : Raw.Stmt}
    {frontendStmts : List Frontend.Stmt}
    {state state' : Elab.State}
    (hElab :
      (Elab.Stmt.List.elaborate (pre ++ stmt :: suffix)).run state =
        .ok (frontendStmts, state')) :
    ∃ (frontendPre : List Frontend.Stmt)
      (frontendStmt : Frontend.Stmt)
      (frontendSuffix : List Frontend.Stmt)
      (stateBeforeStmt stateAfterStmt : Elab.State),
      (Elab.Stmt.List.elaborate pre).run state =
        .ok (frontendPre, stateBeforeStmt) ∧
        (Elab.Stmt.elaborate stmt).run stateBeforeStmt =
          .ok (frontendStmt, stateAfterStmt) ∧
        (Elab.Stmt.List.elaborate suffix).run stateAfterStmt =
          .ok (frontendSuffix, state') ∧
        frontendStmts = frontendPre ++ frontendStmt :: frontendSuffix := by
  induction pre generalizing state frontendStmts with
  | nil =>
      simp only [List.nil_append, Elab.Stmt.List.elaborate] at hElab
      cases hStmt : (Elab.Stmt.elaborate stmt).run state with
      | error err =>
          simp [hStmt] at hElab
      | ok stmtResult =>
          rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
          cases hSuffix :
              (Elab.Stmt.List.elaborate suffix).run stateAfterStmt with
          | error err =>
              simp [hStmt, hSuffix] at hElab
          | ok suffixResult =>
              rcases suffixResult with ⟨frontendSuffix, stateAfterSuffix⟩
              simp [hStmt, hSuffix] at hElab
              rcases hElab with ⟨rfl, rfl⟩
              exact
                ⟨[], frontendStmt, frontendSuffix, state, stateAfterStmt,
                  by
                    simp only [Elab.Stmt.List.elaborate]
                    change
                      (pure ([], state) :
                        DecodeM (List Frontend.Stmt × Elab.State)) =
                        Except.ok ([], state)
                    rfl,
                  hStmt, hSuffix, rfl⟩
  | cons head rest ih =>
      simp only [List.cons_append, Elab.Stmt.List.elaborate] at hElab
      cases hHead : (Elab.Stmt.elaborate head).run state with
      | error err =>
          simp [hHead] at hElab
      | ok headResult =>
          rcases headResult with ⟨frontendHead, stateAfterHead⟩
          cases hRest :
              (Elab.Stmt.List.elaborate (rest ++ stmt :: suffix)).run
                stateAfterHead with
          | error err =>
              simp [hHead, hRest] at hElab
          | ok restResult =>
              rcases restResult with ⟨frontendRest, stateAfterRest⟩
              simp [hHead, hRest] at hElab
              rcases hElab with ⟨rfl, rfl⟩
              rcases ih hRest with
                ⟨frontendPre, frontendStmt, frontendSuffix,
                  stateBeforeStmt, stateAfterStmt, hPre, hStmt,
                  hSuffix, hFrontend⟩
              refine
                ⟨frontendHead :: frontendPre, frontendStmt,
                  frontendSuffix, stateBeforeStmt, stateAfterStmt,
                  ?_, hStmt, hSuffix, ?_⟩
              · simp [Elab.Stmt.List.elaborate, hHead, hPre]
              · simp [hFrontend]

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

theorem elaborate_codeRoute_of_body
    {params returns : List Name} {rawBody : List Raw.Stmt}
    {fn : Frontend.FunctionDef} {state state' : Elab.State}
    {functionName : Name} {args : List Frontend.Expr}
    (hElab :
      (Elab.FunctionDef.elaborate params returns rawBody).run state =
        .ok (fn, state'))
    (hBodyRoute :
      ∀ {frontendBody : List Frontend.Stmt}
        {stateBeforeBody stateAfterBody : Elab.State},
        (Elab.Stmt.List.elaborateBlock rawBody true).run
          stateBeforeBody =
          .ok (frontendBody, stateAfterBody) →
        fn.body = frontendBody →
          CodeElaborationRoute stateAfterBody functionName args
            frontendBody) :
    CodeElaborationRoute state' functionName args fn.body := by
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
                  rcases hElab with ⟨rfl, rfl⟩
                  exact
                    CodeElaborationRoute.retain
                      (hBodyRoute hBody rfl)
                      (fun {entry} hMem => by
                        cases hScopes :
                            stateAfterBody.identifierScopes with
                        | nil =>
                            simp [Elab.popIdentifierScope, hScopes] at hPop
                            unfold Elab.throw at hPop
                            cases hPop
                        | cons head rest =>
                            simp [Elab.popIdentifierScope, hScopes] at hPop
                            rcases hPop with ⟨_hUnit, rfl⟩
                            exact hMem)

end FunctionDef

namespace Elab

theorem pushIdentifierScope_retains_hoisted
    {state state' : Elab.State}
    (hRun : Elab.pushIdentifierScope.run state = .ok ((), state'))
    {entry : Name × Frontend.FunctionDef}
    (hMem : entry ∈ state.hoistedFunctions) :
    entry ∈ state'.hoistedFunctions := by
  simp [Elab.pushIdentifierScope] at hRun
  rcases hRun with ⟨_hUnit, rfl⟩
  exact hMem

theorem popIdentifierScope_retains_hoisted
    {state state' : Elab.State}
    (hRun : Elab.popIdentifierScope.run state = .ok ((), state'))
    {entry : Name × Frontend.FunctionDef}
    (hMem : entry ∈ state.hoistedFunctions) :
    entry ∈ state'.hoistedFunctions := by
  rcases state with
    ⟨functionScopes, identifierScopes, hoistedFunctions, usedFunctionNames,
      nextGeneratedFunctionId, clzHelperName?, clzArgName?, clzReturnName?⟩
  unfold Elab.popIdentifierScope at hRun
  cases identifierScopes with
  | nil =>
      unfold Elab.throw at hRun
      simp at hRun
      change Except.error "internal frontend error: no identifier scope to pop" =
        Except.ok ((), state') at hRun
      cases hRun
  | cons scope rest =>
      simp at hRun
      rcases hRun with ⟨_hUnit, rfl⟩
      exact hMem

theorem pushFunctionScope_retains_hoisted
    {scope : List (Name × Name)}
    {state state' : Elab.State}
    (hRun : (Elab.pushFunctionScope scope).run state = .ok ((), state'))
    {entry : Name × Frontend.FunctionDef}
    (hMem : entry ∈ state.hoistedFunctions) :
    entry ∈ state'.hoistedFunctions := by
  simp [Elab.pushFunctionScope] at hRun
  rcases hRun with ⟨_hUnit, rfl⟩
  exact hMem

theorem popFunctionScope_retains_hoisted
    {state state' : Elab.State}
    (hRun : Elab.popFunctionScope.run state = .ok ((), state'))
    {entry : Name × Frontend.FunctionDef}
    (hMem : entry ∈ state.hoistedFunctions) :
    entry ∈ state'.hoistedFunctions := by
  rcases state with
    ⟨functionScopes, identifierScopes, hoistedFunctions, usedFunctionNames,
      nextGeneratedFunctionId, clzHelperName?, clzArgName?, clzReturnName?⟩
  unfold Elab.popFunctionScope at hRun
  cases functionScopes with
  | nil =>
      unfold Elab.throw at hRun
      simp at hRun
      change Except.error "internal frontend error: no function scope to pop" =
        Except.ok ((), state') at hRun
      cases hRun
  | cons scope rest =>
      simp at hRun
      rcases hRun with ⟨_hUnit, rfl⟩
      exact hMem

theorem declareIdentifiersLoop_retains_hoisted
    {description : String} {names seen seenOut : List Name}
    {state state' : Elab.State}
    (hRun :
      (Elab.declareIdentifiersLoop description names seen).run state =
        .ok (seenOut, state'))
    {entry : Name × Frontend.FunctionDef}
    (hMem : entry ∈ state.hoistedFunctions) :
    entry ∈ state'.hoistedFunctions := by
  induction names generalizing seen seenOut state state' with
  | nil =>
      simp [Elab.declareIdentifiersLoop] at hRun
      rcases hRun with ⟨_hSeen, rfl⟩
      exact hMem
  | cons name rest ih =>
      unfold Elab.declareIdentifiersLoop at hRun
      cases hBinding : Elab.bindingNameOk? name with
      | false =>
          unfold Elab.throw at hRun
          simp [hBinding] at hRun
          change Except.error
              (toString "invalid Yul " ++ toString description ++
                toString " name " ++ toString name) =
            Except.ok (seenOut, state') at hRun
          cases hRun
      | true =>
          cases hSeen : seen.contains name with
          | true =>
              have hSeenMem : name ∈ seen := by
                simpa using hSeen
              unfold Elab.throw at hRun
              simp [hBinding, hSeenMem] at hRun
              change Except.error
                  (toString "duplicate Yul " ++ toString description ++
                    toString " name " ++ toString name) =
                Except.ok (seenOut, state') at hRun
              cases hRun
          | false =>
              have hSeenNot : name ∉ seen := by
                simpa using hSeen
              cases hVisible :
                  Elab.identifierVisibleIn name state.identifierScopes with
              | true =>
                  unfold Elab.throw at hRun
                  simp [hBinding, hSeenNot, hVisible] at hRun
                  change Except.error
                      (toString "Yul " ++ toString description ++
                        toString " name " ++ toString name ++
                          toString " already taken in this scope") =
                    Except.ok (seenOut, state') at hRun
                  cases hRun
              | false =>
                  simp [hBinding, hSeenNot, hVisible] at hRun
                  exact ih hRun hMem

theorem declareIdentifiers_retains_hoisted
    {names : List Name} {description : String}
    {state state' : Elab.State}
    (hRun :
      (Elab.declareIdentifiers names description).run state =
        .ok ((), state'))
    {entry : Name × Frontend.FunctionDef}
    (hMem : entry ∈ state.hoistedFunctions) :
    entry ∈ state'.hoistedFunctions := by
  rcases state with
    ⟨functionScopes, identifierScopes, hoistedFunctions, usedFunctionNames,
      nextGeneratedFunctionId, clzHelperName?, clzArgName?, clzReturnName?⟩
  unfold Elab.declareIdentifiers at hRun
  cases identifierScopes with
  | nil =>
      cases hLoop :
          (Elab.declareIdentifiersLoop description names []).run
            { functionScopes := functionScopes
              identifierScopes := [[]]
              hoistedFunctions := hoistedFunctions
              usedFunctionNames := usedFunctionNames
              nextGeneratedFunctionId := nextGeneratedFunctionId
              clzHelperName? := clzHelperName?
              clzArgName? := clzArgName?
              clzReturnName? := clzReturnName? } with
      | error err =>
          simp [hLoop] at hRun
      | ok loopResult =>
          rcases loopResult with ⟨seen, stateAfterLoop⟩
          have hLoopMem :
              entry ∈ stateAfterLoop.hoistedFunctions :=
            declareIdentifiersLoop_retains_hoisted hLoop hMem
          cases hScopes : stateAfterLoop.identifierScopes with
          | nil =>
              simp [hLoop, hScopes] at hRun
              rcases hRun with ⟨_hUnit, rfl⟩
              exact hLoopMem
          | cons scope rest =>
              simp [hLoop, hScopes] at hRun
              rcases hRun with ⟨_hUnit, rfl⟩
              exact hLoopMem
  | cons initialScope initialRest =>
      cases hLoop :
          (Elab.declareIdentifiersLoop description names []).run
            { functionScopes := functionScopes
              identifierScopes := initialScope :: initialRest
              hoistedFunctions := hoistedFunctions
              usedFunctionNames := usedFunctionNames
              nextGeneratedFunctionId := nextGeneratedFunctionId
              clzHelperName? := clzHelperName?
              clzArgName? := clzArgName?
              clzReturnName? := clzReturnName? } with
      | error err =>
          simp [hLoop] at hRun
      | ok loopResult =>
          rcases loopResult with ⟨seen, stateAfterLoop⟩
          have hLoopMem :
              entry ∈ stateAfterLoop.hoistedFunctions :=
            declareIdentifiersLoop_retains_hoisted hLoop hMem
          cases hScopes : stateAfterLoop.identifierScopes with
          | nil =>
              simp [hLoop, hScopes] at hRun
              rcases hRun with ⟨_hUnit, rfl⟩
              exact hLoopMem
          | cons scope rest =>
              simp [hLoop, hScopes] at hRun
              rcases hRun with ⟨_hUnit, rfl⟩
              exact hLoopMem

theorem freshGeneratedFunctionNameFrom_retains_hoisted
    {stem : Name} {fuel : Nat} {name : Name}
    {state state' : Elab.State}
    (hRun :
      (Elab.freshGeneratedFunctionNameFrom stem fuel).run state =
        .ok (name, state'))
    {entry : Name × Frontend.FunctionDef}
    (hMem : entry ∈ state.hoistedFunctions) :
    entry ∈ state'.hoistedFunctions := by
  induction fuel generalizing name state state' with
  | zero =>
      unfold Elab.freshGeneratedFunctionNameFrom at hRun
      unfold Elab.throw at hRun
      change Except.error
          "could not allocate fresh generated Yul function name" =
        Except.ok (name, state') at hRun
      cases hRun
  | succ fuel ih =>
      unfold Elab.freshGeneratedFunctionNameFrom at hRun
      let candidate :=
        "__yul_gen_" ++ toString state.nextGeneratedFunctionId ++
          "_" ++ stem
      by_cases hUsed : candidate ∈ state.usedFunctionNames
      · simp [candidate, hUsed] at hRun
        have hMemNext :
            entry ∈
              ({ state with
                nextGeneratedFunctionId :=
                  state.nextGeneratedFunctionId + 1 } :
                Elab.State).hoistedFunctions := hMem
        exact ih hRun hMemNext
      · simp [candidate, hUsed] at hRun
        rcases hRun with ⟨rfl, rfl⟩
        exact hMem

theorem freshGeneratedFunctionName_retains_hoisted
    {base name : Name} {state state' : Elab.State}
    (hRun :
      (Elab.freshGeneratedFunctionName base).run state =
        .ok (name, state'))
    {entry : Name × Frontend.FunctionDef}
    (hMem : entry ∈ state.hoistedFunctions) :
    entry ∈ state'.hoistedFunctions := by
  unfold Elab.freshGeneratedFunctionName at hRun
  exact freshGeneratedFunctionNameFrom_retains_hoisted hRun hMem

theorem freshNonFunctionBindingNameFrom_retains_hoisted
    {stem : Name} {index fuel : Nat} {name : Name}
    {state state' : Elab.State}
    (hRun :
      (Elab.freshNonFunctionBindingNameFrom stem index fuel).run state =
        .ok (name, state'))
    {entry : Name × Frontend.FunctionDef}
    (hMem : entry ∈ state.hoistedFunctions) :
    entry ∈ state'.hoistedFunctions := by
  induction fuel generalizing index name state state' with
  | zero =>
      unfold Elab.freshNonFunctionBindingNameFrom at hRun
      unfold Elab.throw at hRun
      change Except.error
          "could not allocate fresh generated Yul binding name" =
        Except.ok (name, state') at hRun
      cases hRun
  | succ fuel ih =>
      unfold Elab.freshNonFunctionBindingNameFrom at hRun
      let candidate :=
        if index = 0 then "__yul_" ++ stem else
          "__yul_" ++ stem ++ "_" ++ toString index
      by_cases hUsed : candidate ∈ state.usedFunctionNames
      · simp [candidate, hUsed] at hRun
        exact ih hRun hMem
      · simp [candidate, hUsed] at hRun
        rcases hRun with ⟨rfl, rfl⟩
        exact hMem

theorem freshNonFunctionBindingName_retains_hoisted
    {base name : Name} {state state' : Elab.State}
    (hRun :
      (Elab.freshNonFunctionBindingName base).run state =
        .ok (name, state'))
    {entry : Name × Frontend.FunctionDef}
    (hMem : entry ∈ state.hoistedFunctions) :
    entry ∈ state'.hoistedFunctions := by
  unfold Elab.freshNonFunctionBindingName at hRun
  exact freshNonFunctionBindingNameFrom_retains_hoisted hRun hMem

theorem ensureClzHelper_retains_hoisted
    {helper : Name} {state state' : Elab.State}
    (hRun : Elab.ensureClzHelper.run state = .ok (helper, state'))
    {entry : Name × Frontend.FunctionDef}
    (hMem : entry ∈ state.hoistedFunctions) :
    entry ∈ state'.hoistedFunctions := by
  unfold Elab.ensureClzHelper at hRun
  cases hClz : state.clzHelperName? with
  | some existing =>
      simp [hClz] at hRun
      rcases hRun with ⟨rfl, rfl⟩
      exact hMem
  | none =>
      simp [hClz] at hRun
      cases hHelper :
          (Elab.freshGeneratedFunctionName "clz").run state with
      | error err =>
          simp [hHelper] at hRun
      | ok helperResult =>
          rcases helperResult with ⟨generatedHelper, stateAfterHelper⟩
          cases hArg :
              (Elab.freshNonFunctionBindingName "clz_arg").run
                stateAfterHelper with
          | error err =>
              simp [hHelper, hArg] at hRun
          | ok argResult =>
              rcases argResult with ⟨arg, stateAfterArg⟩
              cases hRet :
                  (Elab.freshNonFunctionBindingName "clz_ret").run
                    stateAfterArg with
              | error err =>
                  simp [hHelper, hArg, hRet] at hRun
              | ok retResult =>
                  rcases retResult with ⟨ret, stateAfterRet⟩
                  simp [hHelper, hArg, hRet] at hRun
                  rcases hRun with ⟨rfl, rfl⟩
                  have hHelperMem :
                      entry ∈ stateAfterHelper.hoistedFunctions :=
                    freshGeneratedFunctionName_retains_hoisted hHelper hMem
                  have hArgMem :
                      entry ∈ stateAfterArg.hoistedFunctions :=
                    freshNonFunctionBindingName_retains_hoisted hArg
                      hHelperMem
                  have hRetMem :
                      entry ∈ stateAfterRet.hoistedFunctions :=
                    freshNonFunctionBindingName_retains_hoisted hRet hArgMem
                  exact hRetMem

theorem localFunctionScope_retains_hoisted
    {rawStmts : List Raw.Stmt} {scope : List (Name × Name)}
    {state state' : Elab.State}
    (hRun :
      (Elab.Stmt.List.localFunctionScope rawStmts).run state =
        .ok (scope, state'))
    {entry : Name × Frontend.FunctionDef}
    (hMem : entry ∈ state.hoistedFunctions) :
    entry ∈ state'.hoistedFunctions := by
  induction rawStmts generalizing scope state state' with
  | nil =>
      simp [Elab.Stmt.List.localFunctionScope] at hRun
      rcases hRun with ⟨_hScope, rfl⟩
      exact hMem
  | cons head rest ih =>
      unfold Elab.Stmt.List.localFunctionScope at hRun
      cases head with
      | functionDefinition name params returns body =>
          cases hTail :
              (Elab.Stmt.List.localFunctionScope rest).run state with
          | error err =>
              simp [hTail] at hRun
          | ok tailResult =>
              rcases tailResult with ⟨tail, stateAfterTail⟩
              cases hDuplicate :
                  tail.any (fun entry => entry.fst == name) with
              | true =>
                  unfold Elab.throw at hRun
                  simp [hTail, hDuplicate] at hRun
                  change Except.error
                      (toString "duplicate Yul function " ++
                        toString name ++ toString " in block") =
                    Except.ok (scope, state') at hRun
                  cases hRun
              | false =>
                  cases hDeclare :
                      (Elab.declareIdentifiers [name] "function").run
                        stateAfterTail with
                  | error err =>
                      simp [hTail, hDuplicate, hDeclare] at hRun
                  | ok declareResult =>
                      rcases declareResult with ⟨unitDecl, stateAfterDeclare⟩
                      cases hFresh :
                          (Elab.freshGeneratedFunctionName name).run
                            stateAfterDeclare with
                      | error err =>
                          simp [hTail, hDuplicate, hDeclare, hFresh] at hRun
                      | ok freshResult =>
                          rcases freshResult with
                            ⟨generated, stateAfterFresh⟩
                          simp [hTail, hDuplicate, hDeclare, hFresh] at hRun
                          rcases hRun with ⟨rfl, rfl⟩
                          have hTailMem :
                              entry ∈ stateAfterTail.hoistedFunctions :=
                            ih hTail hMem
                          have hDeclareMem :
                              entry ∈ stateAfterDeclare.hoistedFunctions :=
                            declareIdentifiers_retains_hoisted hDeclare
                              hTailMem
                          exact
                            freshGeneratedFunctionName_retains_hoisted
                              hFresh hDeclareMem
      | block body =>
          exact ih hRun hMem
      | variableDeclaration names value? =>
          exact ih hRun hMem
      | assignment names value =>
          exact ih hRun hMem
      | expressionStatement expr =>
          exact ih hRun hMem
      | switch scrutinee cases defaultBody =>
          exact ih hRun hMem
      | forLoop pre condition post body =>
          exact ih hRun hMem
      | ifThen condition body =>
          exact ih hRun hMem
      | «break» =>
          exact ih hRun hMem
      | «continue» =>
          exact ih hRun hMem
      | «leave» =>
          exact ih hRun hMem

theorem localFunctionScope_lookup_of_mem
    {rawStmts : List Raw.Stmt} {scope : List (Name × Name)}
    {state state' : Elab.State}
    (hRun :
      (Elab.Stmt.List.localFunctionScope rawStmts).run state =
        .ok (scope, state'))
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    (hMem :
      Raw.Stmt.functionDefinition name params returns body ∈ rawStmts) :
    ∃ generated, Elab.lookupFunctionInScope name scope = some generated := by
  induction rawStmts generalizing scope state state' with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      unfold Elab.Stmt.List.localFunctionScope at hRun
      simp only [List.mem_cons] at hMem
      cases head with
      | functionDefinition headName headParams headReturns headBody =>
          cases hTail :
              (Elab.Stmt.List.localFunctionScope rest).run state with
          | error err =>
              simp [hTail] at hRun
          | ok tailResult =>
              rcases tailResult with ⟨tail, stateAfterTail⟩
              cases hDuplicate :
                  tail.any (fun entry => entry.fst == headName) with
              | true =>
                  unfold Elab.throw at hRun
                  simp [hTail, hDuplicate] at hRun
                  change Except.error
                      (toString "duplicate Yul function " ++
                        toString headName ++ toString " in block") =
                    Except.ok (scope, state') at hRun
                  cases hRun
              | false =>
                  cases hDeclare :
                      (Elab.declareIdentifiers [headName] "function").run
                        stateAfterTail with
                  | error err =>
                      simp [hTail, hDuplicate, hDeclare] at hRun
                  | ok declareResult =>
                      rcases declareResult with
                        ⟨unitDecl, stateAfterDeclare⟩
                      cases hFresh :
                          (Elab.freshGeneratedFunctionName headName).run
                            stateAfterDeclare with
                      | error err =>
                          simp [hTail, hDuplicate, hDeclare, hFresh]
                            at hRun
                      | ok freshResult =>
                          rcases freshResult with
                            ⟨generated, stateAfterFresh⟩
                          simp [hTail, hDuplicate, hDeclare, hFresh] at hRun
                          rcases hRun with ⟨rfl, rfl⟩
                          rcases hMem with hHere | hRest
                          · cases hHere
                            exact
                              ⟨generated,
                                by simp [Elab.lookupFunctionInScope]⟩
                          · by_cases hSame : headName = name
                            · subst headName
                              exact
                                ⟨generated,
                                  by simp [Elab.lookupFunctionInScope]⟩
                            · rcases ih hTail hRest with
                                ⟨tailGenerated, hLookup⟩
                              exact
                                ⟨tailGenerated,
                                  by
                                    simp [Elab.lookupFunctionInScope, hSame,
                                      hLookup]⟩
      | block body =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest
      | variableDeclaration names value? =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest
      | assignment names value =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest
      | expressionStatement expr =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest
      | switch scrutinee cases defaultBody =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest
      | forLoop pre condition post body =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest
      | ifThen condition body =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest
      | «break» =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest
      | «continue» =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest
      | «leave» =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest

theorem requireIdentifierVisible_retains_hoisted
    {name : Name} {what : String} {state state' : Elab.State}
    (hRun :
      (Elab.requireIdentifierVisible name what).run state =
        .ok ((), state'))
    {entry : Name × Frontend.FunctionDef}
    (hMem : entry ∈ state.hoistedFunctions) :
    entry ∈ state'.hoistedFunctions := by
  unfold Elab.requireIdentifierVisible Elab.identifierVisible at hRun
  cases hVisible :
      Elab.identifierVisibleIn name state.identifierScopes with
  | true =>
      simp [hVisible] at hRun
      rcases hRun with ⟨_hUnit, rfl⟩
      exact hMem
  | false =>
      simp [hVisible] at hRun
      unfold Elab.throw at hRun
      change Except.error
          (toString "unknown Yul identifier " ++ toString name ++
            toString " in " ++ toString what) =
        Except.ok ((), state') at hRun
      cases hRun

theorem requireIdentifiersVisible_retains_hoisted
    {names : List Name} {what : String} {state state' : Elab.State}
    (hRun :
      (Elab.requireIdentifiersVisible names what).run state =
        .ok ((), state'))
    {entry : Name × Frontend.FunctionDef}
    (hMem : entry ∈ state.hoistedFunctions) :
    entry ∈ state'.hoistedFunctions := by
  induction names generalizing state state' with
  | nil =>
      simp [Elab.requireIdentifiersVisible] at hRun
      rcases hRun with ⟨_hUnit, rfl⟩
      exact hMem
  | cons name rest ih =>
      unfold Elab.requireIdentifiersVisible at hRun
      cases hHead :
          (Elab.requireIdentifierVisible name what).run state with
      | error err =>
          simp [hHead] at hRun
      | ok headResult =>
          rcases headResult with ⟨unitHead, stateAfterHead⟩
          cases hTail :
              (Elab.requireIdentifiersVisible rest what).run
                stateAfterHead with
          | error err =>
              simp [hHead, hTail] at hRun
          | ok tailResult =>
              rcases tailResult with ⟨unitTail, stateAfterTail⟩
              simp [hHead, hTail] at hRun
              rcases hRun with ⟨_hUnit, rfl⟩
              have hHeadMem :
                  entry ∈ stateAfterHead.hoistedFunctions :=
                requireIdentifierVisible_retains_hoisted hHead hMem
              exact ih hTail hHeadMem

theorem resolveFunction_retains_hoisted
    {name resolved : Name} {state state' : Elab.State}
    (hRun : (Elab.resolveFunction name).run state = .ok (resolved, state'))
    {entry : Name × Frontend.FunctionDef}
    (hMem : entry ∈ state.hoistedFunctions) :
    entry ∈ state'.hoistedFunctions := by
  unfold Elab.resolveFunction at hRun
  cases hResolve :
      Elab.resolveFunctionIn name state.functionScopes with
  | some actual =>
      simp [hResolve] at hRun
      rcases hRun with ⟨rfl, rfl⟩
      exact hMem
  | none =>
      simp [hResolve] at hRun
      unfold Elab.throw at hRun
      change Except.error
          (toString "unknown Yul function " ++ toString name) =
        Except.ok (resolved, state') at hRun
      cases hRun

mutual
  def rawExprSize : Raw.Expr → Nat
    | .literal _ => 1
    | .identifier _ => 1
    | .functionCall _ args => rawExprListSize args + 1

  def rawExprListSize : List Raw.Expr → Nat
    | [] => 0
    | expr :: rest => rawExprSize expr + rawExprListSize rest + 1
end

mutual
  def rawStmtSize : Raw.Stmt → Nat
    | .block body => rawStmtListSize body + 1
    | .variableDeclaration _ none => 1
    | .variableDeclaration _ (some value) => rawExprSize value + 1
    | .assignment _ value => rawExprSize value + 1
    | .expressionStatement value => rawExprSize value + 1
    | .functionDefinition _ _ _ body => rawStmtListSize body + 1
    | .switch scrutinee cases defaultBody =>
        rawExprSize scrutinee + rawCaseListSize cases +
          rawStmtListSize defaultBody + 1
    | .forLoop pre condition post body =>
        rawStmtListSize pre + rawExprSize condition +
          rawStmtListSize post + rawStmtListSize body + 1
    | .ifThen condition body =>
        rawExprSize condition + rawStmtListSize body + 1
    | .break => 1
    | .continue => 1
    | .leave => 1

  def rawStmtListSize : List Raw.Stmt → Nat
    | [] => 0
    | stmt :: rest => rawStmtSize stmt + rawStmtListSize rest + 1

  def rawCaseListSize :
      List (Raw.SwitchCaseValue × List Raw.Stmt) → Nat
    | [] => 0
    | (_, body) :: rest =>
        rawStmtListSize body + rawCaseListSize rest + 1
end

mutual
  theorem Expr.elaborate_retains_hoisted
      {rawExpr : Raw.Expr} {frontendExpr : Frontend.Expr}
      {state state' : Elab.State}
      (hRun :
        (Elab.Expr.elaborate rawExpr).run state =
          .ok (frontendExpr, state'))
      {entry : Name × Frontend.FunctionDef}
      (hMem : entry ∈ state.hoistedFunctions) :
      entry ∈ state'.hoistedFunctions := by
    cases rawExpr with
    | literal literal =>
        cases literal <;>
          simp [Elab.Expr.elaborate, Elab.Literal.elaborate] at hRun
        all_goals
          rcases hRun with ⟨rfl, rfl⟩
          exact hMem
    | identifier name =>
        cases hRequire :
            (Elab.requireIdentifierVisible name "expression").run state with
        | error err =>
            simp [Elab.Expr.elaborate, hRequire] at hRun
        | ok requireResult =>
            rcases requireResult with ⟨unitRequire, stateAfterRequire⟩
            simp [Elab.Expr.elaborate, hRequire] at hRun
            rcases hRun with ⟨rfl, rfl⟩
            exact
              requireIdentifierVisible_retains_hoisted hRequire hMem
    | functionCall callee args =>
        by_cases hMemoryguard : callee = "memoryguard"
        · subst callee
          cases args with
          | nil =>
              simp [Elab.Expr.elaborate] at hRun
              unfold Elab.throw at hRun
              cases hRun
          | cons only rest =>
              cases rest with
              | nil =>
                  cases hArg :
                      (Elab.Expr.elaborate only).run state with
                  | error err =>
                      simp [Elab.Expr.elaborate, hArg] at hRun
                  | ok argResult =>
                      rcases argResult with ⟨frontendArg, stateAfterArg⟩
                      simp [Elab.Expr.elaborate, hArg] at hRun
                      rcases hRun with ⟨rfl, rfl⟩
                      exact Expr.elaborate_retains_hoisted hArg hMem
              | cons second rest =>
                  simp [Elab.Expr.elaborate] at hRun
                  unfold Elab.throw at hRun
                  cases hRun
        · by_cases hClz : callee = "clz"
          · subst callee
            cases args with
            | nil =>
                simp [Elab.Expr.elaborate] at hRun
                unfold Elab.throw at hRun
                cases hRun
            | cons only rest =>
                cases rest with
                | nil =>
                    cases hArg :
                        (Elab.Expr.elaborate only).run state with
                    | error err =>
                        simp [Elab.Expr.elaborate, hArg] at hRun
                    | ok argResult =>
                        rcases argResult with ⟨frontendArg, stateAfterArg⟩
                        cases hHelper :
                            Elab.ensureClzHelper.run stateAfterArg with
                        | error err =>
                            simp [Elab.Expr.elaborate, hArg, hHelper]
                              at hRun
                        | ok helperResult =>
                            rcases helperResult with
                              ⟨helper, stateAfterHelper⟩
                            simp [Elab.Expr.elaborate, hArg, hHelper]
                              at hRun
                            rcases hRun with ⟨rfl, rfl⟩
                            have hArgMem :
                                entry ∈ stateAfterArg.hoistedFunctions :=
                              Expr.elaborate_retains_hoisted hArg hMem
                            exact
                              ensureClzHelper_retains_hoisted hHelper
                                hArgMem
                | cons second rest =>
                    simp [Elab.Expr.elaborate] at hRun
                    unfold Elab.throw at hRun
                    cases hRun
          · cases hArgs :
                (Elab.Expr.List.elaborate args).run state with
            | error err =>
                simp [Elab.Expr.elaborate, hMemoryguard, hClz, hArgs]
                  at hRun
            | ok argsResult =>
                rcases argsResult with ⟨frontendArgs, stateAfterArgs⟩
                have hArgsMem :
                    entry ∈ stateAfterArgs.hoistedFunctions :=
                  Expr.List.elaborate_retains_hoisted hArgs hMem
                cases hKind : CallClass.classifyCall callee with
                | primitive =>
                    simp [Elab.Expr.elaborate, hMemoryguard, hClz, hArgs,
                      hKind] at hRun
                    rcases hRun with ⟨rfl, rfl⟩
                    exact hArgsMem
                | objectBuiltin =>
                    simp [Elab.Expr.elaborate, hMemoryguard, hClz, hArgs,
                      hKind] at hRun
                    rcases hRun with ⟨rfl, rfl⟩
                    exact hArgsMem
                | dialectBuiltin =>
                    simp [Elab.Expr.elaborate, hMemoryguard, hClz, hArgs,
                      hKind] at hRun
                    rcases hRun with ⟨rfl, rfl⟩
                    exact hArgsMem
                | user =>
                    cases hResolve :
                        (Elab.resolveFunction callee).run
                          stateAfterArgs with
                    | error err =>
                        simp [Elab.Expr.elaborate, hMemoryguard, hClz,
                          hArgs, hKind, hResolve] at hRun
                    | ok resolveResult =>
                        rcases resolveResult with
                          ⟨resolved, stateAfterResolve⟩
                        simp [Elab.Expr.elaborate, hMemoryguard, hClz,
                          hArgs, hKind, hResolve] at hRun
                        rcases hRun with ⟨rfl, rfl⟩
                        exact
                          resolveFunction_retains_hoisted hResolve
                            hArgsMem
  termination_by rawExprSize rawExpr
  decreasing_by
    all_goals simp_wf
    all_goals try subst_vars
    all_goals try simp [rawExprSize, rawExprListSize]
    all_goals omega

  theorem Expr.List.elaborate_retains_hoisted
      {rawExprs : List Raw.Expr} {frontendExprs : List Frontend.Expr}
      {state state' : Elab.State}
      (hRun :
        (Elab.Expr.List.elaborate rawExprs).run state =
          .ok (frontendExprs, state'))
      {entry : Name × Frontend.FunctionDef}
      (hMem : entry ∈ state.hoistedFunctions) :
      entry ∈ state'.hoistedFunctions := by
    cases rawExprs with
    | nil =>
        simp [Elab.Expr.List.elaborate] at hRun
        rcases hRun with ⟨rfl, rfl⟩
        exact hMem
    | cons head rest =>
        simp only [Elab.Expr.List.elaborate] at hRun
        cases hHead : (Elab.Expr.elaborate head).run state with
        | error err =>
            simp [hHead] at hRun
        | ok headResult =>
            rcases headResult with ⟨frontendHead, stateAfterHead⟩
            cases hTail :
                (Elab.Expr.List.elaborate rest).run stateAfterHead with
            | error err =>
                simp [hHead, hTail] at hRun
            | ok tailResult =>
                rcases tailResult with ⟨frontendTail, stateAfterTail⟩
                simp [hHead, hTail] at hRun
                rcases hRun with ⟨rfl, rfl⟩
                have hHeadMem :
                    entry ∈ stateAfterHead.hoistedFunctions :=
                  Expr.elaborate_retains_hoisted hHead hMem
                exact
                  Expr.List.elaborate_retains_hoisted hTail hHeadMem
  termination_by rawExprListSize rawExprs
  decreasing_by
    all_goals simp_wf
    all_goals try subst_vars
    all_goals try simp [rawExprSize, rawExprListSize]
    all_goals omega
end

def FunctionElaborateRetainsHoisted : Prop :=
  ∀ {params returns : List Name} {body : List Raw.Stmt}
    {fn : Frontend.FunctionDef} {state state' : Elab.State},
    (Elab.FunctionDef.elaborate params returns body).run state =
      .ok (fn, state') →
    ∀ {entry : Name × Frontend.FunctionDef},
      entry ∈ state.hoistedFunctions →
        entry ∈ state'.hoistedFunctions

def StmtListElaborateRetainsHoisted : Prop :=
  ∀ {rawStmts : List Raw.Stmt} {frontendStmts : List Frontend.Stmt}
    {state state' : Elab.State},
    (Elab.Stmt.List.elaborate rawStmts).run state =
      .ok (frontendStmts, state') →
    ∀ {entry : Name × Frontend.FunctionDef},
      entry ∈ state.hoistedFunctions →
        entry ∈ state'.hoistedFunctions

def StmtElaborateRetainsHoisted : Prop :=
  ∀ {rawStmt : Raw.Stmt} {frontendStmt : Frontend.Stmt}
    {state state' : Elab.State},
    (Elab.Stmt.elaborate rawStmt).run state =
      .ok (frontendStmt, state') →
    ∀ {entry : Name × Frontend.FunctionDef},
      entry ∈ state.hoistedFunctions →
        entry ∈ state'.hoistedFunctions

def CaseListElaborateRetainsHoisted : Prop :=
  ∀ {rawCases : List (Raw.SwitchCaseValue × List Raw.Stmt)}
    {frontendCases : List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
    {state state' : Elab.State},
    (Elab.Stmt.CaseList.elaborate rawCases).run state =
      .ok (frontendCases, state') →
    ∀ {entry : Name × Frontend.FunctionDef},
      entry ∈ state.hoistedFunctions →
        entry ∈ state'.hoistedFunctions

def StmtListElaborateBlockRetainsHoisted : Prop :=
  ∀ {rawStmts : List Raw.Stmt} {createsScope : Bool}
    {frontendStmts : List Frontend.Stmt} {state state' : Elab.State},
    (Elab.Stmt.List.elaborateBlock rawStmts createsScope).run state =
      .ok (frontendStmts, state') →
    ∀ {entry : Name × Frontend.FunctionDef},
      entry ∈ state.hoistedFunctions →
        entry ∈ state'.hoistedFunctions

def StmtListElaborateForInitRetainsHoisted : Prop :=
  ∀ {rawStmts : List Raw.Stmt} {frontendStmts : List Frontend.Stmt}
    {state state' : Elab.State},
    (Elab.Stmt.List.elaborateForInitBlockWithScope rawStmts).run state =
      .ok (frontendStmts, state') →
    ∀ {entry : Name × Frontend.FunctionDef},
      entry ∈ state.hoistedFunctions →
        entry ∈ state'.hoistedFunctions

theorem hoistLocalFunctions_retains_hoisted_of_function
    (hFunction : FunctionElaborateRetainsHoisted)
    {rawStmts : List Raw.Stmt} {scope : List (Name × Name)}
    {state state' : Elab.State}
    (hRun :
      (Elab.Stmt.List.hoistLocalFunctions rawStmts scope).run state =
        .ok ((), state'))
    {entry : Name × Frontend.FunctionDef}
    (hMem : entry ∈ state.hoistedFunctions) :
    entry ∈ state'.hoistedFunctions := by
  induction rawStmts generalizing state state' with
  | nil =>
      simp [Elab.Stmt.List.hoistLocalFunctions] at hRun
      rcases hRun with ⟨_hUnit, rfl⟩
      exact hMem
  | cons head rest ih =>
      unfold Elab.Stmt.List.hoistLocalFunctions at hRun
      cases head with
      | functionDefinition name params returns body =>
          cases hLookup : Elab.lookupFunctionInScope name scope with
          | none =>
              simp [hLookup] at hRun
              unfold Elab.throw at hRun
              cases hRun
          | some generated =>
              cases hFn :
                  (Elab.FunctionDef.elaborate params returns body).run state with
              | error err =>
                  simp [hLookup, hFn] at hRun
              | ok fnResult =>
                  rcases fnResult with ⟨fn, stateAfterFn⟩
                  let stateAfterStore : Elab.State :=
                    { stateAfterFn with
                      hoistedFunctions :=
                        (generated, fn) :: stateAfterFn.hoistedFunctions }
                  cases hTail :
                      (Elab.Stmt.List.hoistLocalFunctions rest scope).run
                        stateAfterStore with
                  | error err =>
                      simp [hLookup, hFn, stateAfterStore, hTail] at hRun
                  | ok tailResult =>
                      rcases tailResult with ⟨unitTail, stateAfterTail⟩
                      simp [hLookup, hFn, stateAfterStore, hTail] at hRun
                      rcases hRun with ⟨_hUnit, rfl⟩
                      have hFnMem :
                          entry ∈ stateAfterFn.hoistedFunctions :=
                        hFunction hFn hMem
                      have hStoreMem :
                          entry ∈ stateAfterStore.hoistedFunctions := by
                        simp [stateAfterStore, hFnMem]
                      exact ih hTail hStoreMem
      | block body =>
          exact ih hRun hMem
      | variableDeclaration names value? =>
          exact ih hRun hMem
      | assignment names value =>
          exact ih hRun hMem
      | expressionStatement value =>
          exact ih hRun hMem
      | switch scrutinee cases defaultBody =>
          exact ih hRun hMem
      | forLoop pre condition post body =>
          exact ih hRun hMem
      | ifThen condition body =>
          exact ih hRun hMem
      | «break» =>
          exact ih hRun hMem
      | «continue» =>
          exact ih hRun hMem
      | «leave» =>
          exact ih hRun hMem

theorem stmtListElaborate_retains_hoisted_of_stmt
    (hStmt : StmtElaborateRetainsHoisted) :
    StmtListElaborateRetainsHoisted := by
  intro rawStmts frontendStmts state state' hRun entry hMem
  induction rawStmts generalizing frontendStmts state state' with
  | nil =>
      simp [Elab.Stmt.List.elaborate] at hRun
      rcases hRun with ⟨rfl, rfl⟩
      exact hMem
  | cons head rest ih =>
      simp only [Elab.Stmt.List.elaborate] at hRun
      cases hHead : (Elab.Stmt.elaborate head).run state with
      | error err =>
          simp [hHead] at hRun
      | ok headResult =>
          rcases headResult with ⟨frontendHead, stateAfterHead⟩
          cases hTail :
              (Elab.Stmt.List.elaborate rest).run stateAfterHead with
          | error err =>
              simp [hHead, hTail] at hRun
          | ok tailResult =>
              rcases tailResult with ⟨frontendTail, stateAfterTail⟩
              simp [hHead, hTail] at hRun
              rcases hRun with ⟨rfl, rfl⟩
              have hHeadMem :
                  entry ∈ stateAfterHead.hoistedFunctions :=
                hStmt hHead hMem
              exact ih hTail hHeadMem

theorem caseListElaborate_retains_hoisted_of_block
    (hBlock : StmtListElaborateBlockRetainsHoisted) :
    CaseListElaborateRetainsHoisted := by
  intro rawCases frontendCases state state' hRun entry hMem
  induction rawCases generalizing frontendCases state state' with
  | nil =>
      simp [Elab.Stmt.CaseList.elaborate] at hRun
      rcases hRun with ⟨rfl, rfl⟩
      exact hMem
  | cons head rest ih =>
      rcases head with ⟨value, body⟩
      simp only [Elab.Stmt.CaseList.elaborate] at hRun
      cases hValue : Elab.SwitchCaseValue.elaborate value with
      | error err =>
          simp [hValue] at hRun
          unfold Elab.throw at hRun
          cases hRun
      | ok frontendValue =>
          cases hBody :
              (Elab.Stmt.List.elaborateBlock body true).run state with
          | error err =>
              simp [hValue, hBody] at hRun
          | ok bodyResult =>
              rcases bodyResult with ⟨frontendBody, stateAfterBody⟩
              cases hTail :
                  (Elab.Stmt.CaseList.elaborate rest).run
                    stateAfterBody with
              | error err =>
                  simp [hValue, hBody, hTail] at hRun
              | ok tailResult =>
                  rcases tailResult with ⟨frontendTail, stateAfterTail⟩
                  simp [hValue, hBody, hTail] at hRun
                  rcases hRun with ⟨rfl, rfl⟩
                  have hBodyMem :
                      entry ∈ stateAfterBody.hoistedFunctions :=
                    hBlock hBody hMem
                  exact ih hTail hBodyMem

theorem stmtElaborate_retains_hoisted_of_interfaces
    (hFunction : FunctionElaborateRetainsHoisted)
    (hBlock : StmtListElaborateBlockRetainsHoisted)
    (hForInit : StmtListElaborateForInitRetainsHoisted)
    (hCase : CaseListElaborateRetainsHoisted) :
    StmtElaborateRetainsHoisted := by
  intro rawStmt frontendStmt state state' hRun entry hMem
  cases rawStmt with
  | block body =>
      cases hBody :
          (Elab.Stmt.List.elaborateBlock body true).run state with
      | error err =>
          simp [Elab.Stmt.elaborate, hBody] at hRun
      | ok bodyResult =>
          rcases bodyResult with ⟨frontendBody, stateAfterBody⟩
          simp [Elab.Stmt.elaborate, hBody] at hRun
          rcases hRun with ⟨rfl, rfl⟩
          exact hBlock hBody hMem
  | variableDeclaration names value? =>
      cases value? with
      | none =>
          cases hDeclare :
              (Elab.declareIdentifiers names "variable").run state with
          | error err =>
              simp [Elab.Stmt.elaborate, hDeclare] at hRun
          | ok declareResult =>
              rcases declareResult with ⟨unitDeclare, stateAfterDeclare⟩
              simp [Elab.Stmt.elaborate, hDeclare] at hRun
              rcases hRun with ⟨rfl, rfl⟩
              exact declareIdentifiers_retains_hoisted hDeclare hMem
      | some value =>
          cases hValue : (Elab.Expr.elaborate value).run state with
          | error err =>
              simp [Elab.Stmt.elaborate, hValue] at hRun
          | ok valueResult =>
              rcases valueResult with ⟨frontendValue, stateAfterValue⟩
              cases hDeclare :
                  (Elab.declareIdentifiers names "variable").run
                    stateAfterValue with
              | error err =>
                  simp [Elab.Stmt.elaborate, hValue, hDeclare] at hRun
              | ok declareResult =>
                  rcases declareResult with
                    ⟨unitDeclare, stateAfterDeclare⟩
                  simp [Elab.Stmt.elaborate, hValue, hDeclare] at hRun
                  rcases hRun with ⟨rfl, rfl⟩
                  have hValueMem :
                      entry ∈ stateAfterValue.hoistedFunctions :=
                    Expr.elaborate_retains_hoisted hValue hMem
                  exact declareIdentifiers_retains_hoisted hDeclare hValueMem
  | assignment names value =>
      cases hRequire :
          (Elab.requireIdentifiersVisible names "assignment").run state with
      | error err =>
          simp [Elab.Stmt.elaborate, hRequire] at hRun
      | ok requireResult =>
          rcases requireResult with ⟨unitRequire, stateAfterRequire⟩
          cases hValue :
              (Elab.Expr.elaborate value).run stateAfterRequire with
          | error err =>
              simp [Elab.Stmt.elaborate, hRequire, hValue] at hRun
          | ok valueResult =>
              rcases valueResult with ⟨frontendValue, stateAfterValue⟩
              simp [Elab.Stmt.elaborate, hRequire, hValue] at hRun
              rcases hRun with ⟨rfl, rfl⟩
              have hRequireMem :
                  entry ∈ stateAfterRequire.hoistedFunctions :=
                requireIdentifiersVisible_retains_hoisted hRequire hMem
              exact Expr.elaborate_retains_hoisted hValue hRequireMem
  | expressionStatement value =>
      cases hValue : (Elab.Expr.elaborate value).run state with
      | error err =>
          simp [Elab.Stmt.elaborate, hValue] at hRun
      | ok valueResult =>
          rcases valueResult with ⟨frontendValue, stateAfterValue⟩
          simp [Elab.Stmt.elaborate, hValue] at hRun
          rcases hRun with ⟨rfl, rfl⟩
          exact Expr.elaborate_retains_hoisted hValue hMem
  | functionDefinition name params returns body =>
      cases hFn :
          (Elab.FunctionDef.elaborate params returns body).run state with
      | error err =>
          simp [Elab.Stmt.elaborate, hFn] at hRun
      | ok fnResult =>
          rcases fnResult with ⟨fn, stateAfterFn⟩
          simp [Elab.Stmt.elaborate, hFn] at hRun
          rcases hRun with ⟨rfl, rfl⟩
          exact hFunction hFn hMem
  | switch scrutinee cases defaultBody =>
      cases hScrutinee : (Elab.Expr.elaborate scrutinee).run state with
      | error err =>
          simp [Elab.Stmt.elaborate, hScrutinee] at hRun
      | ok scrutineeResult =>
          rcases scrutineeResult with
            ⟨frontendScrutinee, stateAfterScrutinee⟩
          cases hCases :
              (Elab.Stmt.CaseList.elaborate cases).run
                stateAfterScrutinee with
          | error err =>
              simp [Elab.Stmt.elaborate, hScrutinee, hCases] at hRun
          | ok casesResult =>
              rcases casesResult with ⟨frontendCases, stateAfterCases⟩
              cases hDefault :
                  (Elab.Stmt.List.elaborateBlock defaultBody true).run
                    stateAfterCases with
              | error err =>
                  simp [Elab.Stmt.elaborate, hScrutinee, hCases, hDefault]
                    at hRun
              | ok defaultResult =>
                  rcases defaultResult with
                    ⟨frontendDefault, stateAfterDefault⟩
                  simp [Elab.Stmt.elaborate, hScrutinee, hCases, hDefault]
                    at hRun
                  rcases hRun with ⟨rfl, rfl⟩
                  have hScrutineeMem :
                      entry ∈ stateAfterScrutinee.hoistedFunctions :=
                    Expr.elaborate_retains_hoisted hScrutinee hMem
                  have hCasesMem :
                      entry ∈ stateAfterCases.hoistedFunctions :=
                    hCase hCases hScrutineeMem
                  exact hBlock hDefault hCasesMem
  | forLoop pre condition post body =>
      cases hPush : Elab.pushIdentifierScope.run state with
      | error err =>
          simp [Elab.Stmt.elaborate, hPush] at hRun
      | ok pushResult =>
          rcases pushResult with ⟨unitPush, stateAfterPush⟩
          cases hPreHas :
              Elab.Stmt.List.hasImmediateFunctionDefinition pre with
          | false =>
              cases hPre :
                  (Elab.Stmt.List.elaborateBlock pre false).run
                    stateAfterPush with
              | error err =>
                  simp [Elab.Stmt.elaborate, hPush, hPreHas, hPre]
                    at hRun
              | ok preResult =>
                  rcases preResult with ⟨frontendPre, stateAfterPre⟩
                  cases hCondition :
                      (Elab.Expr.elaborate condition).run stateAfterPre with
                  | error err =>
                      simp [Elab.Stmt.elaborate, hPush, hPreHas, hPre,
                        hCondition] at hRun
                  | ok conditionResult =>
                      rcases conditionResult with
                        ⟨frontendCondition, stateAfterCondition⟩
                      cases hPost :
                          (Elab.Stmt.List.elaborateBlock post true).run
                            stateAfterCondition with
                      | error err =>
                          simp [Elab.Stmt.elaborate, hPush, hPreHas, hPre,
                            hCondition, hPost] at hRun
                      | ok postResult =>
                          rcases postResult with
                            ⟨frontendPost, stateAfterPost⟩
                          cases hBody :
                              (Elab.Stmt.List.elaborateBlock body true).run
                                stateAfterPost with
                          | error err =>
                              simp [Elab.Stmt.elaborate, hPush, hPreHas,
                                hPre, hCondition, hPost, hBody] at hRun
                          | ok bodyResult =>
                              rcases bodyResult with
                                ⟨frontendBody, stateAfterBody⟩
                              cases hPop :
                                  Elab.popIdentifierScope.run
                                    stateAfterBody with
                              | error err =>
                                  simp [Elab.Stmt.elaborate, hPush, hPreHas,
                                    hPre, hCondition, hPost, hBody, hPop]
                                    at hRun
                              | ok popResult =>
                                  rcases popResult with
                                    ⟨unitPop, stateAfterPop⟩
                                  simp [Elab.Stmt.elaborate, hPush, hPreHas,
                                    hPre, hCondition, hPost, hBody, hPop]
                                    at hRun
                                  rcases hRun with ⟨rfl, rfl⟩
                                  have hPushMem :
                                      entry ∈
                                        stateAfterPush.hoistedFunctions :=
                                    pushIdentifierScope_retains_hoisted
                                      hPush hMem
                                  have hPreMem :
                                      entry ∈ stateAfterPre.hoistedFunctions :=
                                    hBlock hPre hPushMem
                                  have hConditionMem :
                                      entry ∈
                                        stateAfterCondition.hoistedFunctions :=
                                    Expr.elaborate_retains_hoisted hCondition
                                      hPreMem
                                  have hPostMem :
                                      entry ∈ stateAfterPost.hoistedFunctions :=
                                    hBlock hPost hConditionMem
                                  have hBodyMem :
                                      entry ∈ stateAfterBody.hoistedFunctions :=
                                    hBlock hBody hPostMem
                                  exact
                                    popIdentifierScope_retains_hoisted hPop
                                      hBodyMem
          | true =>
              cases hPre :
                  (Elab.Stmt.List.elaborateForInitBlockWithScope pre).run
                    stateAfterPush with
              | error err =>
                  simp [Elab.Stmt.elaborate, hPush, hPreHas, hPre]
                    at hRun
              | ok preResult =>
                  rcases preResult with ⟨frontendPre, stateAfterPre⟩
                  cases hCondition :
                      (Elab.Expr.elaborate condition).run stateAfterPre with
                  | error err =>
                      simp [Elab.Stmt.elaborate, hPush, hPreHas, hPre,
                        hCondition] at hRun
                  | ok conditionResult =>
                      rcases conditionResult with
                        ⟨frontendCondition, stateAfterCondition⟩
                      cases hPost :
                          (Elab.Stmt.List.elaborateBlock post true).run
                            stateAfterCondition with
                      | error err =>
                          simp [Elab.Stmt.elaborate, hPush, hPreHas, hPre,
                            hCondition, hPost] at hRun
                      | ok postResult =>
                          rcases postResult with
                            ⟨frontendPost, stateAfterPost⟩
                          cases hBody :
                              (Elab.Stmt.List.elaborateBlock body true).run
                                stateAfterPost with
                          | error err =>
                              simp [Elab.Stmt.elaborate, hPush, hPreHas,
                                hPre, hCondition, hPost, hBody] at hRun
                          | ok bodyResult =>
                              rcases bodyResult with
                                ⟨frontendBody, stateAfterBody⟩
                              cases hPopFunction :
                                  Elab.popFunctionScope.run stateAfterBody with
                              | error err =>
                                  simp [Elab.Stmt.elaborate, hPush, hPreHas,
                                    hPre, hCondition, hPost, hBody,
                                    hPopFunction] at hRun
                              | ok popFunctionResult =>
                                  rcases popFunctionResult with
                                    ⟨unitPopFunction, stateAfterPopFunction⟩
                                  cases hPopIdentifier :
                                      Elab.popIdentifierScope.run
                                        stateAfterPopFunction with
                                  | error err =>
                                      simp [Elab.Stmt.elaborate, hPush,
                                        hPreHas, hPre, hCondition, hPost,
                                        hBody, hPopFunction, hPopIdentifier]
                                        at hRun
                                  | ok popIdentifierResult =>
                                      rcases popIdentifierResult with
                                        ⟨unitPopIdentifier,
                                          stateAfterPopIdentifier⟩
                                      simp [Elab.Stmt.elaborate, hPush,
                                        hPreHas, hPre, hCondition, hPost,
                                        hBody, hPopFunction, hPopIdentifier]
                                        at hRun
                                      rcases hRun with ⟨rfl, rfl⟩
                                      have hPushMem :
                                          entry ∈
                                            stateAfterPush.hoistedFunctions :=
                                        pushIdentifierScope_retains_hoisted
                                          hPush hMem
                                      have hPreMem :
                                          entry ∈
                                            stateAfterPre.hoistedFunctions :=
                                        hForInit hPre hPushMem
                                      have hConditionMem :
                                          entry ∈
                                            stateAfterCondition.hoistedFunctions :=
                                        Expr.elaborate_retains_hoisted
                                          hCondition hPreMem
                                      have hPostMem :
                                          entry ∈
                                            stateAfterPost.hoistedFunctions :=
                                        hBlock hPost hConditionMem
                                      have hBodyMem :
                                          entry ∈
                                            stateAfterBody.hoistedFunctions :=
                                        hBlock hBody hPostMem
                                      have hPopFunctionMem :
                                          entry ∈
                                            stateAfterPopFunction.hoistedFunctions :=
                                        popFunctionScope_retains_hoisted
                                          hPopFunction hBodyMem
                                      exact
                                        popIdentifierScope_retains_hoisted
                                          hPopIdentifier hPopFunctionMem
  | ifThen condition body =>
      cases hCondition :
          (Elab.Expr.elaborate condition).run state with
      | error err =>
          simp [Elab.Stmt.elaborate, hCondition] at hRun
      | ok conditionResult =>
          rcases conditionResult with
            ⟨frontendCondition, stateAfterCondition⟩
          cases hBody :
              (Elab.Stmt.List.elaborateBlock body true).run
                stateAfterCondition with
          | error err =>
              simp [Elab.Stmt.elaborate, hCondition, hBody] at hRun
          | ok bodyResult =>
              rcases bodyResult with ⟨frontendBody, stateAfterBody⟩
              simp [Elab.Stmt.elaborate, hCondition, hBody] at hRun
              rcases hRun with ⟨rfl, rfl⟩
              have hConditionMem :
                  entry ∈ stateAfterCondition.hoistedFunctions :=
                Expr.elaborate_retains_hoisted hCondition hMem
              exact hBlock hBody hConditionMem
  | «break» =>
      simp [Elab.Stmt.elaborate] at hRun
      rcases hRun with ⟨rfl, rfl⟩
      exact hMem
  | «continue» =>
      simp [Elab.Stmt.elaborate] at hRun
      rcases hRun with ⟨rfl, rfl⟩
      exact hMem
  | «leave» =>
      simp [Elab.Stmt.elaborate] at hRun
      rcases hRun with ⟨rfl, rfl⟩
      exact hMem

theorem elaborateBlock_retains_hoisted_of_interfaces
    (hFunction : FunctionElaborateRetainsHoisted)
    (hList : StmtListElaborateRetainsHoisted) :
    StmtListElaborateBlockRetainsHoisted := by
  intro rawStmts createsScope frontendStmts state state' hRun entry hMem
  unfold Elab.Stmt.List.elaborateBlock at hRun
  cases hCreate : createsScope
  · simp [hCreate] at hRun
    cases hScope :
        (Elab.Stmt.List.localFunctionScope rawStmts).run state with
    | error err =>
        simp [hScope] at hRun
    | ok scopeResult =>
        rcases scopeResult with ⟨scope, stateAfterScope⟩
        cases hPush :
            (Elab.pushFunctionScope scope).run stateAfterScope with
        | error err =>
            simp [hScope, hPush] at hRun
        | ok pushResult =>
            rcases pushResult with ⟨unitPush, stateAfterPush⟩
            cases hHoist :
                (Elab.Stmt.List.hoistLocalFunctions rawStmts scope).run
                  stateAfterPush with
            | error err =>
                simp [hScope, hPush, hHoist] at hRun
            | ok hoistResult =>
                rcases hoistResult with ⟨unitHoist, stateAfterHoist⟩
                cases hListRun :
                    (Elab.Stmt.List.elaborate rawStmts).run
                      stateAfterHoist with
                | error err =>
                    simp [hScope, hPush, hHoist, hListRun] at hRun
                | ok listResult =>
                    rcases listResult with
                      ⟨frontendStmts', stateAfterList⟩
                    cases hPop :
                        Elab.popFunctionScope.run stateAfterList with
                    | error err =>
                        simp [hScope, hPush, hHoist, hListRun, hPop]
                          at hRun
                    | ok popResult =>
                        rcases popResult with ⟨unitPop, stateAfterPop⟩
                        simp [hScope, hPush, hHoist, hListRun, hPop]
                          at hRun
                        rcases hRun with ⟨rfl, rfl⟩
                        have hScopeMem :
                            entry ∈ stateAfterScope.hoistedFunctions :=
                          localFunctionScope_retains_hoisted hScope hMem
                        have hPushMem :
                            entry ∈ stateAfterPush.hoistedFunctions :=
                          pushFunctionScope_retains_hoisted hPush hScopeMem
                        have hHoistMem :
                            entry ∈ stateAfterHoist.hoistedFunctions :=
                          hoistLocalFunctions_retains_hoisted_of_function
                            hFunction hHoist hPushMem
                        have hListMem :
                            entry ∈ stateAfterList.hoistedFunctions :=
                          hList hListRun hHoistMem
                        exact popFunctionScope_retains_hoisted hPop hListMem
  · simp [hCreate] at hRun
    cases hIdent :
        Elab.pushIdentifierScope.run state with
    | error err =>
        simp [hIdent] at hRun
    | ok identResult =>
        rcases identResult with ⟨unitIdent, stateAfterIdent⟩
        cases hScope :
            (Elab.Stmt.List.localFunctionScope rawStmts).run
              stateAfterIdent with
        | error err =>
            simp [hIdent, hScope] at hRun
        | ok scopeResult =>
            rcases scopeResult with ⟨scope, stateAfterScope⟩
            cases hPush :
                (Elab.pushFunctionScope scope).run stateAfterScope with
            | error err =>
                simp [hIdent, hScope, hPush] at hRun
            | ok pushResult =>
                rcases pushResult with ⟨unitPush, stateAfterPush⟩
                cases hHoist :
                    (Elab.Stmt.List.hoistLocalFunctions rawStmts scope).run
                      stateAfterPush with
                | error err =>
                    simp [hIdent, hScope, hPush, hHoist] at hRun
                | ok hoistResult =>
                    rcases hoistResult with ⟨unitHoist, stateAfterHoist⟩
                    cases hListRun :
                        (Elab.Stmt.List.elaborate rawStmts).run
                          stateAfterHoist with
                    | error err =>
                        simp [hIdent, hScope, hPush, hHoist, hListRun]
                          at hRun
                    | ok listResult =>
                        rcases listResult with
                          ⟨frontendStmts', stateAfterList⟩
                        cases hPop :
                            Elab.popFunctionScope.run stateAfterList with
                        | error err =>
                            simp [hIdent, hScope, hPush, hHoist, hListRun,
                              hPop] at hRun
                        | ok popResult =>
                            rcases popResult with
                              ⟨unitPop, stateAfterPop⟩
                            cases hPopIdent :
                                Elab.popIdentifierScope.run stateAfterPop with
                            | error err =>
                                simp [hIdent, hScope, hPush, hHoist,
                                  hListRun, hPop, hPopIdent] at hRun
                            | ok identPopResult =>
                                rcases identPopResult with
                                  ⟨unitIdentPop, stateAfterIdentPop⟩
                                simp [hIdent, hScope, hPush, hHoist,
                                  hListRun, hPop, hPopIdent] at hRun
                                rcases hRun with ⟨rfl, rfl⟩
                                have hIdentMem :
                                    entry ∈
                                      stateAfterIdent.hoistedFunctions :=
                                  pushIdentifierScope_retains_hoisted
                                    hIdent hMem
                                have hScopeMem :
                                    entry ∈
                                      stateAfterScope.hoistedFunctions :=
                                  localFunctionScope_retains_hoisted hScope
                                    hIdentMem
                                have hPushMem :
                                    entry ∈
                                      stateAfterPush.hoistedFunctions :=
                                  pushFunctionScope_retains_hoisted hPush
                                    hScopeMem
                                have hHoistMem :
                                    entry ∈
                                      stateAfterHoist.hoistedFunctions :=
                                  hoistLocalFunctions_retains_hoisted_of_function
                                    hFunction hHoist hPushMem
                                have hListMem :
                                    entry ∈
                                      stateAfterList.hoistedFunctions :=
                                  hList hListRun hHoistMem
                                have hPopMem :
                                    entry ∈
                                      stateAfterPop.hoistedFunctions :=
                                  popFunctionScope_retains_hoisted hPop
                                    hListMem
                                exact
                                  popIdentifierScope_retains_hoisted
                                    hPopIdent hPopMem

theorem elaborateForInitBlockWithScope_retains_hoisted_of_interfaces
    (hFunction : FunctionElaborateRetainsHoisted)
    (hList : StmtListElaborateRetainsHoisted) :
    StmtListElaborateForInitRetainsHoisted := by
  intro rawStmts frontendStmts state state' hRun entry hMem
  unfold Elab.Stmt.List.elaborateForInitBlockWithScope at hRun
  cases hScope :
      (Elab.Stmt.List.localFunctionScope rawStmts).run state with
  | error err =>
      simp [hScope] at hRun
  | ok scopeResult =>
      rcases scopeResult with ⟨scope, stateAfterScope⟩
      cases hPush :
          (Elab.pushFunctionScope scope).run stateAfterScope with
      | error err =>
          simp [hScope, hPush] at hRun
      | ok pushResult =>
          rcases pushResult with ⟨unitPush, stateAfterPush⟩
          cases hHoist :
              (Elab.Stmt.List.hoistLocalFunctions rawStmts scope).run
                stateAfterPush with
          | error err =>
              simp [hScope, hPush, hHoist] at hRun
          | ok hoistResult =>
              rcases hoistResult with ⟨unitHoist, stateAfterHoist⟩
              cases hListRun :
                  (Elab.Stmt.List.elaborate rawStmts).run
                    stateAfterHoist with
              | error err =>
                  simp [hScope, hPush, hHoist, hListRun] at hRun
              | ok listResult =>
                  rcases listResult with ⟨frontendStmts', stateAfterList⟩
                  simp [hScope, hPush, hHoist, hListRun] at hRun
                  rcases hRun with ⟨rfl, rfl⟩
                  have hScopeMem :
                      entry ∈ stateAfterScope.hoistedFunctions :=
                    localFunctionScope_retains_hoisted hScope hMem
                  have hPushMem :
                      entry ∈ stateAfterPush.hoistedFunctions :=
                    pushFunctionScope_retains_hoisted hPush hScopeMem
                  have hHoistMem :
                      entry ∈ stateAfterHoist.hoistedFunctions :=
                    hoistLocalFunctions_retains_hoisted_of_function
                      hFunction hHoist hPushMem
                  exact hList hListRun hHoistMem

theorem functionElaborate_retains_hoisted_of_block
    (hBlock : StmtListElaborateBlockRetainsHoisted) :
    FunctionElaborateRetainsHoisted := by
  intro params returns body fn state state' hRun entry hMem
  unfold Elab.FunctionDef.elaborate at hRun
  cases hPush : Elab.pushIdentifierScope.run state with
  | error err =>
      simp [hPush] at hRun
  | ok pushResult =>
      rcases pushResult with ⟨unitPush, stateAfterPush⟩
      cases hDeclare :
          (Elab.declareIdentifiers (params ++ returns)
            "function parameter/result").run stateAfterPush with
      | error err =>
          simp [hPush, hDeclare] at hRun
      | ok declareResult =>
          rcases declareResult with ⟨unitDeclare, stateAfterDeclare⟩
          cases hBody :
              (Elab.Stmt.List.elaborateBlock body true).run
                stateAfterDeclare with
          | error err =>
              simp [hPush, hDeclare, hBody] at hRun
          | ok bodyResult =>
              rcases bodyResult with ⟨frontendBody, stateAfterBody⟩
              cases hPop :
                  Elab.popIdentifierScope.run stateAfterBody with
              | error err =>
                  simp [hPush, hDeclare, hBody, hPop] at hRun
              | ok popResult =>
                  rcases popResult with ⟨unitPop, stateAfterPop⟩
                  simp [hPush, hDeclare, hBody, hPop] at hRun
                  rcases hRun with ⟨rfl, rfl⟩
                  have hPushMem :
                      entry ∈ stateAfterPush.hoistedFunctions :=
                    pushIdentifierScope_retains_hoisted hPush hMem
                  have hDeclareMem :
                      entry ∈ stateAfterDeclare.hoistedFunctions :=
                    declareIdentifiers_retains_hoisted hDeclare hPushMem
                  have hBodyMem :
                      entry ∈ stateAfterBody.hoistedFunctions :=
                    hBlock hBody hDeclareMem
                  exact popIdentifierScope_retains_hoisted hPop hBodyMem

structure RetainsHoistedBelow (fuel : Nat) : Prop where
  function :
    ∀ {params returns : List Name} {body : List Raw.Stmt}
      {fn : Frontend.FunctionDef} {state state' : Elab.State},
      rawStmtListSize body < fuel →
      (Elab.FunctionDef.elaborate params returns body).run state =
        .ok (fn, state') →
      ∀ {entry : Name × Frontend.FunctionDef},
        entry ∈ state.hoistedFunctions →
          entry ∈ state'.hoistedFunctions
  stmtList :
    ∀ {rawStmts : List Raw.Stmt} {frontendStmts : List Frontend.Stmt}
      {state state' : Elab.State},
      rawStmtListSize rawStmts < fuel →
      (Elab.Stmt.List.elaborate rawStmts).run state =
        .ok (frontendStmts, state') →
      ∀ {entry : Name × Frontend.FunctionDef},
        entry ∈ state.hoistedFunctions →
          entry ∈ state'.hoistedFunctions
  stmt :
    ∀ {rawStmt : Raw.Stmt} {frontendStmt : Frontend.Stmt}
      {state state' : Elab.State},
      rawStmtSize rawStmt < fuel →
      (Elab.Stmt.elaborate rawStmt).run state =
        .ok (frontendStmt, state') →
      ∀ {entry : Name × Frontend.FunctionDef},
        entry ∈ state.hoistedFunctions →
          entry ∈ state'.hoistedFunctions
  caseList :
    ∀ {rawCases : List (Raw.SwitchCaseValue × List Raw.Stmt)}
      {frontendCases : List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
      {state state' : Elab.State},
      rawCaseListSize rawCases < fuel →
      (Elab.Stmt.CaseList.elaborate rawCases).run state =
        .ok (frontendCases, state') →
      ∀ {entry : Name × Frontend.FunctionDef},
        entry ∈ state.hoistedFunctions →
          entry ∈ state'.hoistedFunctions
  block :
    ∀ {rawStmts : List Raw.Stmt} {createsScope : Bool}
      {frontendStmts : List Frontend.Stmt} {state state' : Elab.State},
      rawStmtListSize rawStmts < fuel →
      (Elab.Stmt.List.elaborateBlock rawStmts createsScope).run state =
        .ok (frontendStmts, state') →
      ∀ {entry : Name × Frontend.FunctionDef},
        entry ∈ state.hoistedFunctions →
          entry ∈ state'.hoistedFunctions
  forInit :
    ∀ {rawStmts : List Raw.Stmt} {frontendStmts : List Frontend.Stmt}
      {state state' : Elab.State},
      rawStmtListSize rawStmts < fuel →
      (Elab.Stmt.List.elaborateForInitBlockWithScope rawStmts).run state =
        .ok (frontendStmts, state') →
      ∀ {entry : Name × Frontend.FunctionDef},
        entry ∈ state.hoistedFunctions →
          entry ∈ state'.hoistedFunctions
  hoist :
    ∀ {rawStmts : List Raw.Stmt} {scope : List (Name × Name)}
      {state state' : Elab.State},
      rawStmtListSize rawStmts < fuel →
      (Elab.Stmt.List.hoistLocalFunctions rawStmts scope).run state =
        .ok ((), state') →
      ∀ {entry : Name × Frontend.FunctionDef},
        entry ∈ state.hoistedFunctions →
          entry ∈ state'.hoistedFunctions

theorem retainsHoistedBelow : (fuel : Nat) → RetainsHoistedBelow fuel
  | 0 => by
      exact
        { function := by
            intro params returns body fn state state' hSize hRun entry hMem
            omega
          stmtList := by
            intro rawStmts frontendStmts state state' hSize hRun entry hMem
            omega
          stmt := by
            intro rawStmt frontendStmt state state' hSize hRun entry hMem
            omega
          caseList := by
            intro rawCases frontendCases state state' hSize hRun entry hMem
            omega
          block := by
            intro rawStmts createsScope frontendStmts state state' hSize
              hRun entry hMem
            omega
          forInit := by
            intro rawStmts frontendStmts state state' hSize hRun entry hMem
            omega
          hoist := by
            intro rawStmts scope state state' hSize hRun entry hMem
            omega }
  | fuel + 1 => by
      let ih := retainsHoistedBelow fuel
      let hHoist :
          ∀ {rawStmts : List Raw.Stmt} {scope : List (Name × Name)}
            {state state' : Elab.State},
            rawStmtListSize rawStmts < fuel + 1 →
            (Elab.Stmt.List.hoistLocalFunctions rawStmts scope).run state =
              .ok ((), state') →
            ∀ {entry : Name × Frontend.FunctionDef},
              entry ∈ state.hoistedFunctions →
                entry ∈ state'.hoistedFunctions := by
        intro rawStmts scope state state' hSize hRun entry hMem
        cases rawStmts with
        | nil =>
            simp [Elab.Stmt.List.hoistLocalFunctions] at hRun
            rcases hRun with ⟨_hUnit, rfl⟩
            exact hMem
        | cons head rest =>
            have hRestSize : rawStmtListSize rest < fuel := by
              simp [rawStmtListSize] at hSize
              omega
            unfold Elab.Stmt.List.hoistLocalFunctions at hRun
            cases head with
            | functionDefinition name params returns body =>
                have hBodySize : rawStmtListSize body < fuel := by
                  simp [rawStmtListSize, rawStmtSize] at hSize
                  omega
                cases hLookup : Elab.lookupFunctionInScope name scope with
                | none =>
                    simp [hLookup] at hRun
                    unfold Elab.throw at hRun
                    cases hRun
                | some generated =>
                    cases hFn :
                        (Elab.FunctionDef.elaborate params returns body).run
                          state with
                    | error err =>
                        simp [hLookup, hFn] at hRun
                    | ok fnResult =>
                        rcases fnResult with ⟨fn, stateAfterFn⟩
                        let stateAfterStore : Elab.State :=
                          { stateAfterFn with
                            hoistedFunctions :=
                              (generated, fn) ::
                                stateAfterFn.hoistedFunctions }
                        cases hTail :
                            (Elab.Stmt.List.hoistLocalFunctions rest scope).run
                              stateAfterStore with
                        | error err =>
                            simp [hLookup, hFn, stateAfterStore, hTail]
                              at hRun
                        | ok tailResult =>
                            rcases tailResult with
                              ⟨unitTail, stateAfterTail⟩
                            simp [hLookup, hFn, stateAfterStore, hTail]
                              at hRun
                            rcases hRun with ⟨_hUnit, rfl⟩
                            have hFnMem :
                                entry ∈ stateAfterFn.hoistedFunctions :=
                              ih.function hBodySize hFn hMem
                            have hStoreMem :
                                entry ∈ stateAfterStore.hoistedFunctions := by
                              simp [stateAfterStore, hFnMem]
                            exact ih.hoist hRestSize hTail hStoreMem
            | block body =>
                exact ih.hoist hRestSize hRun hMem
            | variableDeclaration names value? =>
                exact ih.hoist hRestSize hRun hMem
            | assignment names value =>
                exact ih.hoist hRestSize hRun hMem
            | expressionStatement value =>
                exact ih.hoist hRestSize hRun hMem
            | switch scrutinee cases defaultBody =>
                exact ih.hoist hRestSize hRun hMem
            | forLoop pre condition post body =>
                exact ih.hoist hRestSize hRun hMem
            | ifThen condition body =>
                exact ih.hoist hRestSize hRun hMem
            | «break» =>
                exact ih.hoist hRestSize hRun hMem
            | «continue» =>
                exact ih.hoist hRestSize hRun hMem
            | «leave» =>
                exact ih.hoist hRestSize hRun hMem
      let hStmtList :
          ∀ {rawStmts : List Raw.Stmt} {frontendStmts : List Frontend.Stmt}
            {state state' : Elab.State},
            rawStmtListSize rawStmts < fuel + 1 →
            (Elab.Stmt.List.elaborate rawStmts).run state =
              .ok (frontendStmts, state') →
            ∀ {entry : Name × Frontend.FunctionDef},
              entry ∈ state.hoistedFunctions →
                entry ∈ state'.hoistedFunctions := by
        intro rawStmts frontendStmts state state' hSize hRun entry hMem
        cases rawStmts with
        | nil =>
            simp [Elab.Stmt.List.elaborate] at hRun
            rcases hRun with ⟨rfl, rfl⟩
            exact hMem
        | cons head rest =>
            have hHeadSize : rawStmtSize head < fuel := by
              simp [rawStmtListSize] at hSize
              omega
            have hRestSize : rawStmtListSize rest < fuel := by
              simp [rawStmtListSize] at hSize
              omega
            simp only [Elab.Stmt.List.elaborate] at hRun
            cases hHead : (Elab.Stmt.elaborate head).run state with
            | error err =>
                simp [hHead] at hRun
            | ok headResult =>
                rcases headResult with ⟨frontendHead, stateAfterHead⟩
                cases hTail :
                    (Elab.Stmt.List.elaborate rest).run stateAfterHead with
                | error err =>
                    simp [hHead, hTail] at hRun
                | ok tailResult =>
                    rcases tailResult with
                      ⟨frontendTail, stateAfterTail⟩
                    simp [hHead, hTail] at hRun
                    rcases hRun with ⟨rfl, rfl⟩
                    have hHeadMem :
                        entry ∈ stateAfterHead.hoistedFunctions :=
                      ih.stmt hHeadSize hHead hMem
                    exact ih.stmtList hRestSize hTail hHeadMem
      let hCaseList :
          ∀ {rawCases : List (Raw.SwitchCaseValue × List Raw.Stmt)}
            {frontendCases :
              List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
            {state state' : Elab.State},
            rawCaseListSize rawCases < fuel + 1 →
            (Elab.Stmt.CaseList.elaborate rawCases).run state =
              .ok (frontendCases, state') →
            ∀ {entry : Name × Frontend.FunctionDef},
              entry ∈ state.hoistedFunctions →
                entry ∈ state'.hoistedFunctions := by
        intro rawCases frontendCases state state' hSize hRun entry hMem
        cases rawCases with
        | nil =>
            simp [Elab.Stmt.CaseList.elaborate] at hRun
            rcases hRun with ⟨rfl, rfl⟩
            exact hMem
        | cons head rest =>
            rcases head with ⟨value, body⟩
            have hBodySize : rawStmtListSize body < fuel := by
              simp [rawCaseListSize] at hSize
              omega
            have hRestSize : rawCaseListSize rest < fuel := by
              simp [rawCaseListSize] at hSize
              omega
            simp only [Elab.Stmt.CaseList.elaborate] at hRun
            cases hValue : Elab.SwitchCaseValue.elaborate value with
            | error err =>
                simp [hValue] at hRun
                unfold Elab.throw at hRun
                cases hRun
            | ok frontendValue =>
                cases hBody :
                    (Elab.Stmt.List.elaborateBlock body true).run state with
                | error err =>
                    simp [hValue, hBody] at hRun
                | ok bodyResult =>
                    rcases bodyResult with
                      ⟨frontendBody, stateAfterBody⟩
                    cases hTail :
                        (Elab.Stmt.CaseList.elaborate rest).run
                          stateAfterBody with
                    | error err =>
                        simp [hValue, hBody, hTail] at hRun
                    | ok tailResult =>
                        rcases tailResult with
                          ⟨frontendTail, stateAfterTail⟩
                        simp [hValue, hBody, hTail] at hRun
                        rcases hRun with ⟨rfl, rfl⟩
                        have hBodyMem :
                            entry ∈ stateAfterBody.hoistedFunctions :=
                          ih.block hBodySize hBody hMem
                        exact ih.caseList hRestSize hTail hBodyMem
      let hStmt :
          ∀ {rawStmt : Raw.Stmt} {frontendStmt : Frontend.Stmt}
            {state state' : Elab.State},
            rawStmtSize rawStmt < fuel + 1 →
            (Elab.Stmt.elaborate rawStmt).run state =
              .ok (frontendStmt, state') →
            ∀ {entry : Name × Frontend.FunctionDef},
              entry ∈ state.hoistedFunctions →
                entry ∈ state'.hoistedFunctions := by
        intro rawStmt frontendStmt state state' hSize hRun entry hMem
        cases rawStmt with
        | block body =>
            have hBodySize : rawStmtListSize body < fuel := by
              simp [rawStmtSize] at hSize
              omega
            cases hBody :
                (Elab.Stmt.List.elaborateBlock body true).run state with
            | error err =>
                simp [Elab.Stmt.elaborate, hBody] at hRun
            | ok bodyResult =>
                rcases bodyResult with ⟨frontendBody, stateAfterBody⟩
                simp [Elab.Stmt.elaborate, hBody] at hRun
                rcases hRun with ⟨rfl, rfl⟩
                exact ih.block hBodySize hBody hMem
        | variableDeclaration names value? =>
            cases value? with
            | none =>
                cases hDeclare :
                    (Elab.declareIdentifiers names "variable").run state with
                | error err =>
                    simp [Elab.Stmt.elaborate, hDeclare] at hRun
                | ok declareResult =>
                    rcases declareResult with
                      ⟨unitDeclare, stateAfterDeclare⟩
                    simp [Elab.Stmt.elaborate, hDeclare] at hRun
                    rcases hRun with ⟨rfl, rfl⟩
                    exact declareIdentifiers_retains_hoisted hDeclare hMem
            | some value =>
                cases hValue : (Elab.Expr.elaborate value).run state with
                | error err =>
                    simp [Elab.Stmt.elaborate, hValue] at hRun
                | ok valueResult =>
                    rcases valueResult with ⟨frontendValue, stateAfterValue⟩
                    cases hDeclare :
                        (Elab.declareIdentifiers names "variable").run
                          stateAfterValue with
                    | error err =>
                        simp [Elab.Stmt.elaborate, hValue, hDeclare] at hRun
                    | ok declareResult =>
                        rcases declareResult with
                          ⟨unitDeclare, stateAfterDeclare⟩
                        simp [Elab.Stmt.elaborate, hValue, hDeclare] at hRun
                        rcases hRun with ⟨rfl, rfl⟩
                        have hValueMem :
                            entry ∈ stateAfterValue.hoistedFunctions :=
                          Expr.elaborate_retains_hoisted hValue hMem
                        exact
                          declareIdentifiers_retains_hoisted hDeclare
                            hValueMem
        | assignment names value =>
            cases hRequire :
                (Elab.requireIdentifiersVisible names "assignment").run
                  state with
            | error err =>
                simp [Elab.Stmt.elaborate, hRequire] at hRun
            | ok requireResult =>
                rcases requireResult with
                  ⟨unitRequire, stateAfterRequire⟩
                cases hValue :
                    (Elab.Expr.elaborate value).run stateAfterRequire with
                | error err =>
                    simp [Elab.Stmt.elaborate, hRequire, hValue] at hRun
                | ok valueResult =>
                    rcases valueResult with ⟨frontendValue, stateAfterValue⟩
                    simp [Elab.Stmt.elaborate, hRequire, hValue] at hRun
                    rcases hRun with ⟨rfl, rfl⟩
                    have hRequireMem :
                        entry ∈ stateAfterRequire.hoistedFunctions :=
                      requireIdentifiersVisible_retains_hoisted hRequire hMem
                    exact Expr.elaborate_retains_hoisted hValue hRequireMem
        | expressionStatement value =>
            cases hValue : (Elab.Expr.elaborate value).run state with
            | error err =>
                simp [Elab.Stmt.elaborate, hValue] at hRun
            | ok valueResult =>
                rcases valueResult with ⟨frontendValue, stateAfterValue⟩
                simp [Elab.Stmt.elaborate, hValue] at hRun
                rcases hRun with ⟨rfl, rfl⟩
                exact Expr.elaborate_retains_hoisted hValue hMem
        | functionDefinition name params returns body =>
            have hBodySize : rawStmtListSize body < fuel := by
              simp [rawStmtSize] at hSize
              omega
            cases hFn :
                (Elab.FunctionDef.elaborate params returns body).run
                  state with
            | error err =>
                simp [Elab.Stmt.elaborate, hFn] at hRun
            | ok fnResult =>
                rcases fnResult with ⟨fn, stateAfterFn⟩
                simp [Elab.Stmt.elaborate, hFn] at hRun
                rcases hRun with ⟨rfl, rfl⟩
                exact ih.function hBodySize hFn hMem
        | switch scrutinee cases defaultBody =>
            have hCasesSize : rawCaseListSize cases < fuel := by
              simp [rawStmtSize] at hSize
              omega
            have hDefaultSize : rawStmtListSize defaultBody < fuel := by
              simp [rawStmtSize] at hSize
              omega
            cases hScrutinee : (Elab.Expr.elaborate scrutinee).run state with
            | error err =>
                simp [Elab.Stmt.elaborate, hScrutinee] at hRun
            | ok scrutineeResult =>
                rcases scrutineeResult with
                  ⟨frontendScrutinee, stateAfterScrutinee⟩
                cases hCases :
                    (Elab.Stmt.CaseList.elaborate cases).run
                      stateAfterScrutinee with
                | error err =>
                    simp [Elab.Stmt.elaborate, hScrutinee, hCases] at hRun
                | ok casesResult =>
                    rcases casesResult with
                      ⟨frontendCases, stateAfterCases⟩
                    cases hDefault :
                        (Elab.Stmt.List.elaborateBlock defaultBody true).run
                          stateAfterCases with
                    | error err =>
                        simp [Elab.Stmt.elaborate, hScrutinee, hCases,
                          hDefault] at hRun
                    | ok defaultResult =>
                        rcases defaultResult with
                          ⟨frontendDefault, stateAfterDefault⟩
                        simp [Elab.Stmt.elaborate, hScrutinee, hCases,
                          hDefault] at hRun
                        rcases hRun with ⟨rfl, rfl⟩
                        have hScrutineeMem :
                            entry ∈
                              stateAfterScrutinee.hoistedFunctions :=
                          Expr.elaborate_retains_hoisted hScrutinee hMem
                        have hCasesMem :
                            entry ∈ stateAfterCases.hoistedFunctions :=
                          ih.caseList hCasesSize hCases hScrutineeMem
                        exact ih.block hDefaultSize hDefault hCasesMem
        | forLoop pre condition post body =>
            have hPreSize : rawStmtListSize pre < fuel := by
              simp [rawStmtSize] at hSize
              omega
            have hPostSize : rawStmtListSize post < fuel := by
              simp [rawStmtSize] at hSize
              omega
            have hBodySize : rawStmtListSize body < fuel := by
              simp [rawStmtSize] at hSize
              omega
            cases hPush : Elab.pushIdentifierScope.run state with
            | error err =>
                simp [Elab.Stmt.elaborate, hPush] at hRun
            | ok pushResult =>
                rcases pushResult with ⟨unitPush, stateAfterPush⟩
                cases hPreHas :
                    Elab.Stmt.List.hasImmediateFunctionDefinition pre with
                | false =>
                    cases hPre :
                        (Elab.Stmt.List.elaborateBlock pre false).run
                          stateAfterPush with
                    | error err =>
                        simp [Elab.Stmt.elaborate, hPush, hPreHas, hPre]
                          at hRun
                    | ok preResult =>
                        rcases preResult with
                          ⟨frontendPre, stateAfterPre⟩
                        cases hCondition :
                            (Elab.Expr.elaborate condition).run
                              stateAfterPre with
                        | error err =>
                            simp [Elab.Stmt.elaborate, hPush, hPreHas, hPre,
                              hCondition] at hRun
                        | ok conditionResult =>
                            rcases conditionResult with
                              ⟨frontendCondition, stateAfterCondition⟩
                            cases hPost :
                                (Elab.Stmt.List.elaborateBlock post true).run
                                  stateAfterCondition with
                            | error err =>
                                simp [Elab.Stmt.elaborate, hPush, hPreHas,
                                  hPre, hCondition, hPost] at hRun
                            | ok postResult =>
                                rcases postResult with
                                  ⟨frontendPost, stateAfterPost⟩
                                cases hBody :
                                    (Elab.Stmt.List.elaborateBlock body true).run
                                      stateAfterPost with
                                | error err =>
                                    simp [Elab.Stmt.elaborate, hPush, hPreHas,
                                      hPre, hCondition, hPost, hBody] at hRun
                                | ok bodyResult =>
                                    rcases bodyResult with
                                      ⟨frontendBody, stateAfterBody⟩
                                    cases hPop :
                                        Elab.popIdentifierScope.run
                                          stateAfterBody with
                                    | error err =>
                                        simp [Elab.Stmt.elaborate, hPush,
                                          hPreHas, hPre, hCondition, hPost,
                                          hBody, hPop] at hRun
                                    | ok popResult =>
                                        rcases popResult with
                                          ⟨unitPop, stateAfterPop⟩
                                        simp [Elab.Stmt.elaborate, hPush,
                                          hPreHas, hPre, hCondition, hPost,
                                          hBody, hPop] at hRun
                                        rcases hRun with ⟨rfl, rfl⟩
                                        have hPushMem :
                                            entry ∈
                                              stateAfterPush.hoistedFunctions :=
                                          pushIdentifierScope_retains_hoisted
                                            hPush hMem
                                        have hPreMem :
                                            entry ∈
                                              stateAfterPre.hoistedFunctions :=
                                          ih.block hPreSize hPre hPushMem
                                        have hConditionMem :
                                            entry ∈
                                              stateAfterCondition.hoistedFunctions :=
                                          Expr.elaborate_retains_hoisted
                                            hCondition hPreMem
                                        have hPostMem :
                                            entry ∈
                                              stateAfterPost.hoistedFunctions :=
                                          ih.block hPostSize hPost
                                            hConditionMem
                                        have hBodyMem :
                                            entry ∈
                                              stateAfterBody.hoistedFunctions :=
                                          ih.block hBodySize hBody hPostMem
                                        exact
                                          popIdentifierScope_retains_hoisted
                                            hPop hBodyMem
                | true =>
                    cases hPre :
                        (Elab.Stmt.List.elaborateForInitBlockWithScope pre).run
                          stateAfterPush with
                    | error err =>
                        simp [Elab.Stmt.elaborate, hPush, hPreHas, hPre]
                          at hRun
                    | ok preResult =>
                        rcases preResult with
                          ⟨frontendPre, stateAfterPre⟩
                        cases hCondition :
                            (Elab.Expr.elaborate condition).run
                              stateAfterPre with
                        | error err =>
                            simp [Elab.Stmt.elaborate, hPush, hPreHas, hPre,
                              hCondition] at hRun
                        | ok conditionResult =>
                            rcases conditionResult with
                              ⟨frontendCondition, stateAfterCondition⟩
                            cases hPost :
                                (Elab.Stmt.List.elaborateBlock post true).run
                                  stateAfterCondition with
                            | error err =>
                                simp [Elab.Stmt.elaborate, hPush, hPreHas,
                                  hPre, hCondition, hPost] at hRun
                            | ok postResult =>
                                rcases postResult with
                                  ⟨frontendPost, stateAfterPost⟩
                                cases hBody :
                                    (Elab.Stmt.List.elaborateBlock body true).run
                                      stateAfterPost with
                                | error err =>
                                    simp [Elab.Stmt.elaborate, hPush, hPreHas,
                                      hPre, hCondition, hPost, hBody] at hRun
                                | ok bodyResult =>
                                    rcases bodyResult with
                                      ⟨frontendBody, stateAfterBody⟩
                                    cases hPopFunction :
                                        Elab.popFunctionScope.run
                                          stateAfterBody with
                                    | error err =>
                                        simp [Elab.Stmt.elaborate, hPush,
                                          hPreHas, hPre, hCondition, hPost,
                                          hBody, hPopFunction] at hRun
                                    | ok popFunctionResult =>
                                        rcases popFunctionResult with
                                          ⟨unitPopFunction,
                                            stateAfterPopFunction⟩
                                        cases hPopIdentifier :
                                            Elab.popIdentifierScope.run
                                              stateAfterPopFunction with
                                        | error err =>
                                            simp [Elab.Stmt.elaborate, hPush,
                                              hPreHas, hPre, hCondition,
                                              hPost, hBody, hPopFunction,
                                              hPopIdentifier] at hRun
                                        | ok popIdentifierResult =>
                                            rcases popIdentifierResult with
                                              ⟨unitPopIdentifier,
                                                stateAfterPopIdentifier⟩
                                            simp [Elab.Stmt.elaborate, hPush,
                                              hPreHas, hPre, hCondition,
                                              hPost, hBody, hPopFunction,
                                              hPopIdentifier] at hRun
                                            rcases hRun with ⟨rfl, rfl⟩
                                            have hPushMem :
                                                entry ∈
                                                  stateAfterPush.hoistedFunctions :=
                                              pushIdentifierScope_retains_hoisted
                                                hPush hMem
                                            have hPreMem :
                                                entry ∈
                                                  stateAfterPre.hoistedFunctions :=
                                              ih.forInit hPreSize hPre
                                                hPushMem
                                            have hConditionMem :
                                                entry ∈
                                                  stateAfterCondition.hoistedFunctions :=
                                              Expr.elaborate_retains_hoisted
                                                hCondition hPreMem
                                            have hPostMem :
                                                entry ∈
                                                  stateAfterPost.hoistedFunctions :=
                                              ih.block hPostSize hPost
                                                hConditionMem
                                            have hBodyMem :
                                                entry ∈
                                                  stateAfterBody.hoistedFunctions :=
                                              ih.block hBodySize hBody
                                                hPostMem
                                            have hPopFunctionMem :
                                                entry ∈
                                                  stateAfterPopFunction.hoistedFunctions :=
                                              popFunctionScope_retains_hoisted
                                                hPopFunction hBodyMem
                                            exact
                                              popIdentifierScope_retains_hoisted
                                                hPopIdentifier hPopFunctionMem
        | ifThen condition body =>
            have hBodySize : rawStmtListSize body < fuel := by
              simp [rawStmtSize] at hSize
              omega
            cases hCondition :
                (Elab.Expr.elaborate condition).run state with
            | error err =>
                simp [Elab.Stmt.elaborate, hCondition] at hRun
            | ok conditionResult =>
                rcases conditionResult with
                  ⟨frontendCondition, stateAfterCondition⟩
                cases hBody :
                    (Elab.Stmt.List.elaborateBlock body true).run
                      stateAfterCondition with
                | error err =>
                    simp [Elab.Stmt.elaborate, hCondition, hBody] at hRun
                | ok bodyResult =>
                    rcases bodyResult with
                      ⟨frontendBody, stateAfterBody⟩
                    simp [Elab.Stmt.elaborate, hCondition, hBody] at hRun
                    rcases hRun with ⟨rfl, rfl⟩
                    have hConditionMem :
                        entry ∈ stateAfterCondition.hoistedFunctions :=
                      Expr.elaborate_retains_hoisted hCondition hMem
                    exact ih.block hBodySize hBody hConditionMem
        | «break» =>
            simp [Elab.Stmt.elaborate] at hRun
            rcases hRun with ⟨rfl, rfl⟩
            exact hMem
        | «continue» =>
            simp [Elab.Stmt.elaborate] at hRun
            rcases hRun with ⟨rfl, rfl⟩
            exact hMem
        | «leave» =>
            simp [Elab.Stmt.elaborate] at hRun
            rcases hRun with ⟨rfl, rfl⟩
            exact hMem
      let hBlock :
          ∀ {rawStmts : List Raw.Stmt} {createsScope : Bool}
            {frontendStmts : List Frontend.Stmt} {state state' : Elab.State},
            rawStmtListSize rawStmts < fuel + 1 →
            (Elab.Stmt.List.elaborateBlock rawStmts createsScope).run state =
              .ok (frontendStmts, state') →
            ∀ {entry : Name × Frontend.FunctionDef},
              entry ∈ state.hoistedFunctions →
                entry ∈ state'.hoistedFunctions := by
        intro rawStmts createsScope frontendStmts state state' hSize hRun
          entry hMem
        unfold Elab.Stmt.List.elaborateBlock at hRun
        cases hCreate : createsScope
        · simp [hCreate] at hRun
          cases hScope :
              (Elab.Stmt.List.localFunctionScope rawStmts).run state with
          | error err =>
              simp [hScope] at hRun
          | ok scopeResult =>
              rcases scopeResult with ⟨scope, stateAfterScope⟩
              cases hPush :
                  (Elab.pushFunctionScope scope).run stateAfterScope with
              | error err =>
                  simp [hScope, hPush] at hRun
              | ok pushResult =>
                  rcases pushResult with ⟨unitPush, stateAfterPush⟩
                  cases hHoistRun :
                      (Elab.Stmt.List.hoistLocalFunctions rawStmts scope).run
                        stateAfterPush with
                  | error err =>
                      simp [hScope, hPush, hHoistRun] at hRun
                  | ok hoistResult =>
                      rcases hoistResult with ⟨unitHoist, stateAfterHoist⟩
                      cases hListRun :
                          (Elab.Stmt.List.elaborate rawStmts).run
                            stateAfterHoist with
                      | error err =>
                          simp [hScope, hPush, hHoistRun, hListRun] at hRun
                      | ok listResult =>
                          rcases listResult with
                            ⟨frontendStmts', stateAfterList⟩
                          cases hPop :
                              Elab.popFunctionScope.run stateAfterList with
                          | error err =>
                              simp [hScope, hPush, hHoistRun, hListRun, hPop]
                                at hRun
                          | ok popResult =>
                              rcases popResult with
                                ⟨unitPop, stateAfterPop⟩
                              simp [hScope, hPush, hHoistRun, hListRun, hPop]
                                at hRun
                              rcases hRun with ⟨rfl, rfl⟩
                              have hScopeMem :
                                  entry ∈ stateAfterScope.hoistedFunctions :=
                                localFunctionScope_retains_hoisted hScope hMem
                              have hPushMem :
                                  entry ∈ stateAfterPush.hoistedFunctions :=
                                pushFunctionScope_retains_hoisted hPush
                                  hScopeMem
                              have hHoistMem :
                                  entry ∈ stateAfterHoist.hoistedFunctions :=
                                hHoist hSize hHoistRun hPushMem
                              have hListMem :
                                  entry ∈ stateAfterList.hoistedFunctions :=
                                hStmtList hSize hListRun hHoistMem
                              exact
                                popFunctionScope_retains_hoisted hPop
                                  hListMem
        · simp [hCreate] at hRun
          cases hIdent :
              Elab.pushIdentifierScope.run state with
          | error err =>
              simp [hIdent] at hRun
          | ok identResult =>
              rcases identResult with ⟨unitIdent, stateAfterIdent⟩
              cases hScope :
                  (Elab.Stmt.List.localFunctionScope rawStmts).run
                    stateAfterIdent with
              | error err =>
                  simp [hIdent, hScope] at hRun
              | ok scopeResult =>
                  rcases scopeResult with ⟨scope, stateAfterScope⟩
                  cases hPush :
                      (Elab.pushFunctionScope scope).run stateAfterScope with
                  | error err =>
                      simp [hIdent, hScope, hPush] at hRun
                  | ok pushResult =>
                      rcases pushResult with ⟨unitPush, stateAfterPush⟩
                      cases hHoistRun :
                          (Elab.Stmt.List.hoistLocalFunctions rawStmts scope).run
                            stateAfterPush with
                      | error err =>
                          simp [hIdent, hScope, hPush, hHoistRun] at hRun
                      | ok hoistResult =>
                          rcases hoistResult with
                            ⟨unitHoist, stateAfterHoist⟩
                          cases hListRun :
                              (Elab.Stmt.List.elaborate rawStmts).run
                                stateAfterHoist with
                          | error err =>
                              simp [hIdent, hScope, hPush, hHoistRun,
                                hListRun] at hRun
                          | ok listResult =>
                              rcases listResult with
                                ⟨frontendStmts', stateAfterList⟩
                              cases hPop :
                                  Elab.popFunctionScope.run
                                    stateAfterList with
                              | error err =>
                                  simp [hIdent, hScope, hPush, hHoistRun,
                                    hListRun, hPop] at hRun
                              | ok popResult =>
                                  rcases popResult with
                                    ⟨unitPop, stateAfterPop⟩
                                  cases hPopIdent :
                                      Elab.popIdentifierScope.run
                                        stateAfterPop with
                                  | error err =>
                                      simp [hIdent, hScope, hPush, hHoistRun,
                                        hListRun, hPop, hPopIdent] at hRun
                                  | ok identPopResult =>
                                      rcases identPopResult with
                                        ⟨unitIdentPop,
                                          stateAfterIdentPop⟩
                                      simp [hIdent, hScope, hPush, hHoistRun,
                                        hListRun, hPop, hPopIdent] at hRun
                                      rcases hRun with ⟨rfl, rfl⟩
                                      have hIdentMem :
                                          entry ∈
                                            stateAfterIdent.hoistedFunctions :=
                                        pushIdentifierScope_retains_hoisted
                                          hIdent hMem
                                      have hScopeMem :
                                          entry ∈
                                            stateAfterScope.hoistedFunctions :=
                                        localFunctionScope_retains_hoisted
                                          hScope hIdentMem
                                      have hPushMem :
                                          entry ∈
                                            stateAfterPush.hoistedFunctions :=
                                        pushFunctionScope_retains_hoisted
                                          hPush hScopeMem
                                      have hHoistMem :
                                          entry ∈
                                            stateAfterHoist.hoistedFunctions :=
                                        hHoist hSize hHoistRun hPushMem
                                      have hListMem :
                                          entry ∈
                                            stateAfterList.hoistedFunctions :=
                                        hStmtList hSize hListRun hHoistMem
                                      have hPopMem :
                                          entry ∈
                                            stateAfterPop.hoistedFunctions :=
                                        popFunctionScope_retains_hoisted hPop
                                          hListMem
                                      exact
                                        popIdentifierScope_retains_hoisted
                                          hPopIdent hPopMem
      let hForInit :
          ∀ {rawStmts : List Raw.Stmt} {frontendStmts : List Frontend.Stmt}
            {state state' : Elab.State},
            rawStmtListSize rawStmts < fuel + 1 →
            (Elab.Stmt.List.elaborateForInitBlockWithScope rawStmts).run
              state = .ok (frontendStmts, state') →
            ∀ {entry : Name × Frontend.FunctionDef},
              entry ∈ state.hoistedFunctions →
                entry ∈ state'.hoistedFunctions := by
        intro rawStmts frontendStmts state state' hSize hRun entry hMem
        unfold Elab.Stmt.List.elaborateForInitBlockWithScope at hRun
        cases hScope :
            (Elab.Stmt.List.localFunctionScope rawStmts).run state with
        | error err =>
            simp [hScope] at hRun
        | ok scopeResult =>
            rcases scopeResult with ⟨scope, stateAfterScope⟩
            cases hPush :
                (Elab.pushFunctionScope scope).run stateAfterScope with
            | error err =>
                simp [hScope, hPush] at hRun
            | ok pushResult =>
                rcases pushResult with ⟨unitPush, stateAfterPush⟩
                cases hHoistRun :
                    (Elab.Stmt.List.hoistLocalFunctions rawStmts scope).run
                      stateAfterPush with
                | error err =>
                    simp [hScope, hPush, hHoistRun] at hRun
                | ok hoistResult =>
                    rcases hoistResult with ⟨unitHoist, stateAfterHoist⟩
                    cases hListRun :
                        (Elab.Stmt.List.elaborate rawStmts).run
                          stateAfterHoist with
                    | error err =>
                        simp [hScope, hPush, hHoistRun, hListRun] at hRun
                    | ok listResult =>
                        rcases listResult with
                          ⟨frontendStmts', stateAfterList⟩
                        simp [hScope, hPush, hHoistRun, hListRun] at hRun
                        rcases hRun with ⟨rfl, rfl⟩
                        have hScopeMem :
                            entry ∈ stateAfterScope.hoistedFunctions :=
                          localFunctionScope_retains_hoisted hScope hMem
                        have hPushMem :
                            entry ∈ stateAfterPush.hoistedFunctions :=
                          pushFunctionScope_retains_hoisted hPush hScopeMem
                        have hHoistMem :
                            entry ∈ stateAfterHoist.hoistedFunctions :=
                          hHoist hSize hHoistRun hPushMem
                        exact hStmtList hSize hListRun hHoistMem
      let hFunction :
          ∀ {params returns : List Name} {body : List Raw.Stmt}
            {fn : Frontend.FunctionDef} {state state' : Elab.State},
            rawStmtListSize body < fuel + 1 →
            (Elab.FunctionDef.elaborate params returns body).run state =
              .ok (fn, state') →
            ∀ {entry : Name × Frontend.FunctionDef},
              entry ∈ state.hoistedFunctions →
                entry ∈ state'.hoistedFunctions := by
        intro params returns body fn state state' hSize hRun entry hMem
        unfold Elab.FunctionDef.elaborate at hRun
        cases hPush : Elab.pushIdentifierScope.run state with
        | error err =>
            simp [hPush] at hRun
        | ok pushResult =>
            rcases pushResult with ⟨unitPush, stateAfterPush⟩
            cases hDeclare :
                (Elab.declareIdentifiers (params ++ returns)
                  "function parameter/result").run stateAfterPush with
            | error err =>
                simp [hPush, hDeclare] at hRun
            | ok declareResult =>
                rcases declareResult with ⟨unitDeclare, stateAfterDeclare⟩
                cases hBody :
                    (Elab.Stmt.List.elaborateBlock body true).run
                      stateAfterDeclare with
                | error err =>
                    simp [hPush, hDeclare, hBody] at hRun
                | ok bodyResult =>
                    rcases bodyResult with ⟨frontendBody, stateAfterBody⟩
                    cases hPop :
                        Elab.popIdentifierScope.run stateAfterBody with
                    | error err =>
                        simp [hPush, hDeclare, hBody, hPop] at hRun
                    | ok popResult =>
                        rcases popResult with ⟨unitPop, stateAfterPop⟩
                        simp [hPush, hDeclare, hBody, hPop] at hRun
                        rcases hRun with ⟨rfl, rfl⟩
                        have hPushMem :
                            entry ∈ stateAfterPush.hoistedFunctions :=
                          pushIdentifierScope_retains_hoisted hPush hMem
                        have hDeclareMem :
                            entry ∈ stateAfterDeclare.hoistedFunctions :=
                          declareIdentifiers_retains_hoisted hDeclare
                            hPushMem
                        have hBodyMem :
                            entry ∈ stateAfterBody.hoistedFunctions :=
                          hBlock hSize hBody hDeclareMem
                        exact popIdentifierScope_retains_hoisted hPop
                          hBodyMem
      exact
        { function := hFunction
          stmtList := hStmtList
          stmt := hStmt
          caseList := hCaseList
          block := hBlock
          forInit := hForInit
          hoist := hHoist }

theorem hoistLocalFunctions_retains_hoisted
    {rawStmts : List Raw.Stmt} {scope : List (Name × Name)}
    {state state' : Elab.State}
    (hRun :
      (Elab.Stmt.List.hoistLocalFunctions rawStmts scope).run state =
        .ok ((), state'))
    {entry : Name × Frontend.FunctionDef}
    (hMem : entry ∈ state.hoistedFunctions) :
    entry ∈ state'.hoistedFunctions := by
  have hBelow := retainsHoistedBelow (rawStmtListSize rawStmts + 1)
  exact hBelow.hoist (Nat.lt_succ_self _) hRun hMem

theorem hoistLocalFunctions_function_mem
    {rawStmts : List Raw.Stmt} {scope : List (Name × Name)}
    {state state' : Elab.State}
    (hRun :
      (Elab.Stmt.List.hoistLocalFunctions rawStmts scope).run state =
        .ok ((), state'))
    {name generated : Name} {params returns : List Name}
    {body : List Raw.Stmt}
    (hMem :
      Raw.Stmt.functionDefinition name params returns body ∈ rawStmts)
    (hLookup : Elab.lookupFunctionInScope name scope = some generated) :
    ∃ (fn : Frontend.FunctionDef) (stateBefore stateAfter : Elab.State),
      (Elab.FunctionDef.elaborate params returns body).run stateBefore =
        .ok (fn, stateAfter) ∧
        (generated, fn) ∈ state'.hoistedFunctions := by
  induction rawStmts generalizing state state' generated hLookup with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      unfold Elab.Stmt.List.hoistLocalFunctions at hRun
      simp only [List.mem_cons] at hMem
      cases head with
      | functionDefinition headName headParams headReturns headBody =>
          cases hHeadLookup :
              Elab.lookupFunctionInScope headName scope with
          | none =>
              simp [hHeadLookup] at hRun
              unfold Elab.throw at hRun
              cases hRun
          | some headGenerated =>
              cases hFn :
                  (Elab.FunctionDef.elaborate headParams headReturns
                    headBody).run state with
              | error err =>
                  simp [hHeadLookup, hFn] at hRun
              | ok fnResult =>
                  rcases fnResult with ⟨headFn, stateAfterFn⟩
                  let stateAfterStore : Elab.State :=
                    { stateAfterFn with
                      hoistedFunctions :=
                        (headGenerated, headFn) ::
                          stateAfterFn.hoistedFunctions }
                  cases hTail :
                      (Elab.Stmt.List.hoistLocalFunctions rest scope).run
                        stateAfterStore with
                  | error err =>
                      simp [hHeadLookup, hFn, stateAfterStore, hTail]
                        at hRun
                  | ok tailResult =>
                      rcases tailResult with ⟨unitTail, stateAfterTail⟩
                      simp [hHeadLookup, hFn, stateAfterStore, hTail]
                        at hRun
                      rcases hRun with ⟨_hUnit, rfl⟩
                      rcases hMem with hHere | hRest
                      · cases hHere
                        have hGenerated : generated = headGenerated := by
                          cases hLookup.symm.trans hHeadLookup
                          rfl
                        subst generated
                        have hStoreMem :
                            (headGenerated, headFn) ∈
                              stateAfterStore.hoistedFunctions := by
                          simp [stateAfterStore]
                        have hFinalMem :=
                          hoistLocalFunctions_retains_hoisted hTail
                            hStoreMem
                        exact
                          ⟨headFn, state, stateAfterFn, hFn, hFinalMem⟩
                      · exact ih hTail hRest hLookup
      | block blockBody =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest hLookup
      | variableDeclaration names value? =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest hLookup
      | assignment names value =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest hLookup
      | expressionStatement value =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest hLookup
      | switch scrutinee cases defaultBody =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest hLookup
      | forLoop pre condition post body =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest hLookup
      | ifThen condition body =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest hLookup
      | «break» =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest hLookup
      | «continue» =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest hLookup
      | «leave» =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest hLookup

theorem hoistLocalFunctions_function_route_mem
    {rawStmts : List Raw.Stmt} {scope : List (Name × Name)}
    {state state' : Elab.State}
    (hRun :
      (Elab.Stmt.List.hoistLocalFunctions rawStmts scope).run state =
        .ok ((), state'))
    {name generated : Name} {params returns : List Name}
    {body : List Raw.Stmt}
    (hMem :
      Raw.Stmt.functionDefinition name params returns body ∈ rawStmts)
    (hLookup : Elab.lookupFunctionInScope name scope = some generated) :
    ∃ (fn : Frontend.FunctionDef) (stateBefore stateAfter : Elab.State),
      (Elab.FunctionDef.elaborate params returns body).run stateBefore =
        .ok (fn, stateAfter) ∧
        (generated, fn) ∈ state'.hoistedFunctions ∧
          ∀ {entry : Name × Frontend.FunctionDef},
            entry ∈ stateAfter.hoistedFunctions →
              entry ∈ state'.hoistedFunctions := by
  induction rawStmts generalizing state state' generated hLookup with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      unfold Elab.Stmt.List.hoistLocalFunctions at hRun
      simp only [List.mem_cons] at hMem
      cases head with
      | functionDefinition headName headParams headReturns headBody =>
          cases hHeadLookup :
              Elab.lookupFunctionInScope headName scope with
          | none =>
              simp [hHeadLookup] at hRun
              unfold Elab.throw at hRun
              cases hRun
          | some headGenerated =>
              cases hFn :
                  (Elab.FunctionDef.elaborate headParams headReturns
                    headBody).run state with
              | error err =>
                  simp [hHeadLookup, hFn] at hRun
              | ok fnResult =>
                  rcases fnResult with ⟨headFn, stateAfterFn⟩
                  let stateAfterStore : Elab.State :=
                    { stateAfterFn with
                      hoistedFunctions :=
                        (headGenerated, headFn) ::
                          stateAfterFn.hoistedFunctions }
                  cases hTail :
                      (Elab.Stmt.List.hoistLocalFunctions rest scope).run
                        stateAfterStore with
                  | error err =>
                      simp [hHeadLookup, hFn, stateAfterStore, hTail]
                        at hRun
                  | ok tailResult =>
                      rcases tailResult with ⟨unitTail, stateAfterTail⟩
                      simp [hHeadLookup, hFn, stateAfterStore, hTail]
                        at hRun
                      rcases hRun with ⟨_hUnit, rfl⟩
                      rcases hMem with hHere | hRest
                      · cases hHere
                        have hGenerated : generated = headGenerated := by
                          cases hLookup.symm.trans hHeadLookup
                          rfl
                        subst generated
                        have hStoreMem :
                            (headGenerated, headFn) ∈
                              stateAfterStore.hoistedFunctions := by
                          simp [stateAfterStore]
                        have hFinalMem :=
                          hoistLocalFunctions_retains_hoisted hTail
                            hStoreMem
                        have hRetain :
                            ∀ {entry : Name × Frontend.FunctionDef},
                              entry ∈ stateAfterFn.hoistedFunctions →
                                entry ∈ state'.hoistedFunctions := by
                          intro entry hEntry
                          have hStoreEntry :
                              entry ∈ stateAfterStore.hoistedFunctions := by
                            simp [stateAfterStore, hEntry]
                          exact
                            hoistLocalFunctions_retains_hoisted hTail
                              hStoreEntry
                        exact
                          ⟨headFn, state, stateAfterFn, hFn, hFinalMem,
                            hRetain⟩
                      · exact ih hTail hRest hLookup
      | block blockBody =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest hLookup
      | variableDeclaration names value? =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest hLookup
      | assignment names value =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest hLookup
      | expressionStatement value =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest hLookup
      | switch scrutinee cases defaultBody =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest hLookup
      | forLoop pre condition post body =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest hLookup
      | ifThen condition body =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest hLookup
      | «break» =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest hLookup
      | «continue» =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest hLookup
      | «leave» =>
          rcases hMem with hHere | hRest
          · cases hHere
          · exact ih hRun hRest hLookup

namespace Stmt

theorem elaborate_retains_hoisted
    {rawStmt : Raw.Stmt} {frontendStmt : Frontend.Stmt}
    {state state' : Elab.State}
    (hRun :
      (Elab.Stmt.elaborate rawStmt).run state =
        .ok (frontendStmt, state'))
    {entry : Name × Frontend.FunctionDef}
    (hMem : entry ∈ state.hoistedFunctions) :
    entry ∈ state'.hoistedFunctions := by
  have hBelow := retainsHoistedBelow (rawStmtSize rawStmt + 1)
  exact hBelow.stmt (Nat.lt_succ_self _) hRun hMem

theorem functionDefinition_codeRoute_of_hoist
    {rawStmts : List Raw.Stmt} {scope : List (Name × Name)}
    {stateBeforeHoist stateAfterHoist : Elab.State}
    (hHoist :
      (Elab.Stmt.List.hoistLocalFunctions rawStmts scope).run
        stateBeforeHoist =
        .ok ((), stateAfterHoist))
    {name generated : Name} {params returns : List Name}
    {body : List Raw.Stmt}
    (hMem :
      Raw.Stmt.functionDefinition name params returns body ∈ rawStmts)
    (hLookup : Elab.lookupFunctionInScope name scope = some generated)
    {frontendStmt : Frontend.Stmt}
    {stateBeforeStmt stateAfterStmt : Elab.State}
    (hStmt :
      (Elab.Stmt.elaborate
          (Raw.Stmt.functionDefinition name params returns body)).run
        stateBeforeStmt =
        .ok (frontendStmt, stateAfterStmt))
    (hRetainHoistToStmt :
      ∀ {entry : Name × Frontend.FunctionDef},
        entry ∈ stateAfterHoist.hoistedFunctions →
          entry ∈ stateBeforeStmt.hoistedFunctions)
    {functionName : Name} {args : List Frontend.Expr}
    (hBodyRoute :
      ∀ {fn : Frontend.FunctionDef}
        {stateBeforeFn stateAfterFn : Elab.State},
        (Elab.FunctionDef.elaborate params returns body).run
          stateBeforeFn =
          .ok (fn, stateAfterFn) →
        CodeElaborationRoute stateAfterFn functionName args fn.body) :
    StmtCodeElaborationRoute stateAfterStmt functionName args
      frontendStmt := by
  rcases
      RawOccurrence.Elab.hoistLocalFunctions_function_route_mem
        hHoist hMem hLookup with
    ⟨fn, stateBeforeFn, stateAfterFn, hFn, hContextHoist,
      hRetainFnToHoist⟩
  have hContextBefore :
      (generated, fn) ∈ stateBeforeStmt.hoistedFunctions :=
    hRetainHoistToStmt hContextHoist
  have hContextAfter :
      (generated, fn) ∈ stateAfterStmt.hoistedFunctions :=
    elaborate_retains_hoisted hStmt hContextBefore
  have hRetainFnToStmt :
      ∀ {entry : Name × Frontend.FunctionDef},
        entry ∈ stateAfterFn.hoistedFunctions →
          entry ∈ stateAfterStmt.hoistedFunctions := by
    intro entry hEntry
    exact
      elaborate_retains_hoisted hStmt
        (hRetainHoistToStmt (hRetainFnToHoist hEntry))
  exact
    CodeElaborationRoute.liftFunctionBodyStmt hContextAfter
      hRetainFnToStmt (hBodyRoute hFn)

namespace List

theorem elaborate_retains_hoisted
    {rawStmts : List Raw.Stmt} {frontendStmts : List Frontend.Stmt}
    {state state' : Elab.State}
    (hRun :
      (Elab.Stmt.List.elaborate rawStmts).run state =
        .ok (frontendStmts, state'))
    {entry : Name × Frontend.FunctionDef}
    (hMem : entry ∈ state.hoistedFunctions) :
    entry ∈ state'.hoistedFunctions := by
  have hBelow := retainsHoistedBelow (rawStmtListSize rawStmts + 1)
  exact hBelow.stmtList (Nat.lt_succ_self _) hRun hMem

theorem elaborate_codeRoute_of_split
    {pre suffix : List Raw.Stmt} {stmt : Raw.Stmt}
    {frontendStmts : List Frontend.Stmt}
    {state state' : Elab.State}
    {functionName : Name} {args : List Frontend.Expr}
    (hRun :
      (Elab.Stmt.List.elaborate (pre ++ stmt :: suffix)).run state =
        .ok (frontendStmts, state'))
    (hStmtRoute :
      ∀ {frontendStmt : Frontend.Stmt}
        {stateBeforeStmt stateAfterStmt : Elab.State},
        (Elab.Stmt.elaborate stmt).run stateBeforeStmt =
          .ok (frontendStmt, stateAfterStmt) →
        StmtCodeElaborationRoute stateAfterStmt functionName args
          frontendStmt) :
    CodeElaborationRoute state' functionName args frontendStmts := by
  rcases
      _root_.EvmCompiler.Solidity.RawAst.RawOccurrence.Stmt.List.elaborate_split
        hRun with
    ⟨frontendPre, frontendStmt, frontendSuffix, stateBeforeStmt,
      stateAfterStmt, hPre, hStmt, hSuffix, hFrontend⟩
  have hRouteAtStmt :
      StmtCodeElaborationRoute stateAfterStmt functionName args
        frontendStmt :=
    hStmtRoute hStmt
  have hRouteAtEnd :
      StmtCodeElaborationRoute state' functionName args frontendStmt :=
    StmtCodeElaborationRoute.retain hRouteAtStmt
      (fun {entry} hMem =>
        elaborate_retains_hoisted hSuffix hMem)
  rw [hFrontend]
  exact StmtCodeElaborationRoute.toCodeRoute_of_split hRouteAtEnd

theorem elaborate_codeRoute_of_split_context
    {pre suffix : List Raw.Stmt} {stmt : Raw.Stmt}
    {frontendStmts : List Frontend.Stmt}
    {state state' : Elab.State}
    {functionName : Name} {args : List Frontend.Expr}
    (hRun :
      (Elab.Stmt.List.elaborate (pre ++ stmt :: suffix)).run state =
        .ok (frontendStmts, state'))
    (hStmtRoute :
      ∀ {frontendPre : List Frontend.Stmt}
        {frontendStmt : Frontend.Stmt}
        {frontendSuffix : List Frontend.Stmt}
        {stateBeforeStmt stateAfterStmt : Elab.State},
        (Elab.Stmt.List.elaborate pre).run state =
          .ok (frontendPre, stateBeforeStmt) →
        (Elab.Stmt.elaborate stmt).run stateBeforeStmt =
          .ok (frontendStmt, stateAfterStmt) →
        (Elab.Stmt.List.elaborate suffix).run stateAfterStmt =
          .ok (frontendSuffix, state') →
        frontendStmts = frontendPre ++ frontendStmt :: frontendSuffix →
        StmtCodeElaborationRoute stateAfterStmt functionName args
          frontendStmt) :
    CodeElaborationRoute state' functionName args frontendStmts := by
  rcases
      _root_.EvmCompiler.Solidity.RawAst.RawOccurrence.Stmt.List.elaborate_split
        hRun with
    ⟨frontendPre, frontendStmt, frontendSuffix, stateBeforeStmt,
      stateAfterStmt, hPre, hStmt, hSuffix, hFrontend⟩
  have hRouteAtStmt :
      StmtCodeElaborationRoute stateAfterStmt functionName args
        frontendStmt :=
    hStmtRoute hPre hStmt hSuffix hFrontend
  have hRouteAtEnd :
      StmtCodeElaborationRoute state' functionName args frontendStmt :=
    StmtCodeElaborationRoute.retain hRouteAtStmt
      (fun {entry} hMem =>
        elaborate_retains_hoisted hSuffix hMem)
  rw [hFrontend]
  exact StmtCodeElaborationRoute.toCodeRoute_of_split hRouteAtEnd

theorem elaborate_codeRoute_of_functionDefinition_split
    {pre suffix : List Raw.Stmt}
    {name generated : Name} {params returns : List Name}
    {body : List Raw.Stmt}
    {scope : List (Name × Name)}
    {stateBeforeHoist stateAfterHoist state' : Elab.State}
    {frontendStmts : List Frontend.Stmt}
    {functionName : Name} {args : List Frontend.Expr}
    (hHoist :
      (Elab.Stmt.List.hoistLocalFunctions
          (pre ++
            Raw.Stmt.functionDefinition name params returns body ::
              suffix)
          scope).run stateBeforeHoist =
        .ok ((), stateAfterHoist))
    (hLookup : Elab.lookupFunctionInScope name scope = some generated)
    (hList :
      (Elab.Stmt.List.elaborate
          (pre ++
            Raw.Stmt.functionDefinition name params returns body ::
              suffix)).run stateAfterHoist =
        .ok (frontendStmts, state'))
    (hBodyRoute :
      ∀ {fn : Frontend.FunctionDef}
        {stateBeforeFn stateAfterFn : Elab.State},
        (Elab.FunctionDef.elaborate params returns body).run
          stateBeforeFn =
          .ok (fn, stateAfterFn) →
        CodeElaborationRoute stateAfterFn functionName args fn.body) :
    CodeElaborationRoute state' functionName args frontendStmts := by
  refine elaborate_codeRoute_of_split_context hList ?_
  intro frontendPre frontendStmt frontendSuffix stateBeforeStmt
    stateAfterStmt hPre hStmt hSuffix hFrontend
  exact
    _root_.EvmCompiler.Solidity.RawAst.RawOccurrence.Elab.Stmt.functionDefinition_codeRoute_of_hoist
      hHoist (by simp) hLookup hStmt
      (fun {entry} hMem =>
        elaborate_retains_hoisted hPre hMem)
      hBodyRoute

theorem elaborateBlock_retains_hoisted
    {rawStmts : List Raw.Stmt} {createsScope : Bool}
    {frontendStmts : List Frontend.Stmt} {state state' : Elab.State}
    (hRun :
      (Elab.Stmt.List.elaborateBlock rawStmts createsScope).run state =
        .ok (frontendStmts, state'))
    {entry : Name × Frontend.FunctionDef}
    (hMem : entry ∈ state.hoistedFunctions) :
    entry ∈ state'.hoistedFunctions := by
  have hBelow := retainsHoistedBelow (rawStmtListSize rawStmts + 1)
  exact hBelow.block (Nat.lt_succ_self _) hRun hMem

theorem elaborateBlock_codeRoute_of_list
    {rawStmts : List Raw.Stmt} {createsScope : Bool}
    {frontendStmts : List Frontend.Stmt} {state state' : Elab.State}
    {functionName : Name} {args : List Frontend.Expr}
    (hRun :
      (Elab.Stmt.List.elaborateBlock rawStmts createsScope).run state =
        .ok (frontendStmts, state'))
    (hListRoute :
      ∀ {stateBeforeList stateAfterList : Elab.State},
        (Elab.Stmt.List.elaborate rawStmts).run stateBeforeList =
          .ok (frontendStmts, stateAfterList) →
          CodeElaborationRoute stateAfterList functionName args
            frontendStmts) :
    CodeElaborationRoute state' functionName args frontendStmts := by
  unfold Elab.Stmt.List.elaborateBlock at hRun
  cases hCreate : createsScope
  · simp [hCreate] at hRun
    cases hScope :
        (Elab.Stmt.List.localFunctionScope rawStmts).run state with
    | error err =>
        simp [hScope] at hRun
    | ok scopeResult =>
        rcases scopeResult with ⟨scope, stateAfterScope⟩
        cases hPush :
            (Elab.pushFunctionScope scope).run stateAfterScope with
        | error err =>
            simp [hScope, hPush] at hRun
        | ok pushResult =>
            rcases pushResult with ⟨unitPush, stateAfterPush⟩
            cases hHoist :
                (Elab.Stmt.List.hoistLocalFunctions rawStmts scope).run
                  stateAfterPush with
            | error err =>
                simp [hScope, hPush, hHoist] at hRun
            | ok hoistResult =>
                rcases hoistResult with ⟨unitHoist, stateAfterHoist⟩
                cases hList :
                    (Elab.Stmt.List.elaborate rawStmts).run
                      stateAfterHoist with
                | error err =>
                    simp [hScope, hPush, hHoist, hList] at hRun
                | ok listResult =>
                    rcases listResult with
                      ⟨frontendStmts', stateAfterList⟩
                    cases hPop :
                        Elab.popFunctionScope.run stateAfterList with
                    | error err =>
                        simp [hScope, hPush, hHoist, hList, hPop] at hRun
                    | ok popResult =>
                        rcases popResult with ⟨unitPop, stateAfterPop⟩
                        simp [hScope, hPush, hHoist, hList, hPop] at hRun
                        rcases hRun with ⟨rfl, rfl⟩
                        exact
                          CodeElaborationRoute.retain
                            (hListRoute hList)
                            (fun hMem =>
                              popFunctionScope_retains_hoisted hPop hMem)
  · simp [hCreate] at hRun
    cases hIdent :
        Elab.pushIdentifierScope.run state with
    | error err =>
        simp [hIdent] at hRun
    | ok identResult =>
        rcases identResult with ⟨unitIdent, stateAfterIdent⟩
        cases hScope :
            (Elab.Stmt.List.localFunctionScope rawStmts).run
              stateAfterIdent with
        | error err =>
            simp [hIdent, hScope] at hRun
        | ok scopeResult =>
            rcases scopeResult with ⟨scope, stateAfterScope⟩
            cases hPush :
                (Elab.pushFunctionScope scope).run stateAfterScope with
            | error err =>
                simp [hIdent, hScope, hPush] at hRun
            | ok pushResult =>
                rcases pushResult with ⟨unitPush, stateAfterPush⟩
                cases hHoist :
                    (Elab.Stmt.List.hoistLocalFunctions rawStmts scope).run
                      stateAfterPush with
                | error err =>
                    simp [hIdent, hScope, hPush, hHoist] at hRun
                | ok hoistResult =>
                    rcases hoistResult with
                      ⟨unitHoist, stateAfterHoist⟩
                    cases hList :
                        (Elab.Stmt.List.elaborate rawStmts).run
                          stateAfterHoist with
                    | error err =>
                        simp [hIdent, hScope, hPush, hHoist, hList]
                          at hRun
                    | ok listResult =>
                        rcases listResult with
                          ⟨frontendStmts', stateAfterList⟩
                        cases hPop :
                            Elab.popFunctionScope.run stateAfterList with
                        | error err =>
                            simp [hIdent, hScope, hPush, hHoist, hList,
                              hPop] at hRun
                        | ok popResult =>
                            rcases popResult with
                              ⟨unitPop, stateAfterPop⟩
                            cases hPopIdent :
                                Elab.popIdentifierScope.run stateAfterPop with
                            | error err =>
                                simp [hIdent, hScope, hPush, hHoist, hList,
                                  hPop, hPopIdent] at hRun
                            | ok identPopResult =>
                                rcases identPopResult with
                                  ⟨unitIdentPop, stateAfterIdentPop⟩
                                simp [hIdent, hScope, hPush, hHoist, hList,
                                  hPop, hPopIdent] at hRun
                                rcases hRun with ⟨rfl, rfl⟩
                                exact
                                  CodeElaborationRoute.retain
                                    (hListRoute hList)
                                    (fun hMem =>
                                      popIdentifierScope_retains_hoisted
                                        hPopIdent
                                        (popFunctionScope_retains_hoisted
                                          hPop hMem))

theorem elaborateForInitBlockWithScope_retains_hoisted
    {rawStmts : List Raw.Stmt} {frontendStmts : List Frontend.Stmt}
    {state state' : Elab.State}
    (hRun :
      (Elab.Stmt.List.elaborateForInitBlockWithScope rawStmts).run state =
        .ok (frontendStmts, state'))
    {entry : Name × Frontend.FunctionDef}
    (hMem : entry ∈ state.hoistedFunctions) :
    entry ∈ state'.hoistedFunctions := by
  have hBelow := retainsHoistedBelow (rawStmtListSize rawStmts + 1)
  exact hBelow.forInit (Nat.lt_succ_self _) hRun hMem

theorem elaborateForInitBlockWithScope_codeRoute_of_list
    {rawStmts : List Raw.Stmt} {frontendStmts : List Frontend.Stmt}
    {state state' : Elab.State}
    {functionName : Name} {args : List Frontend.Expr}
    (hRun :
      (Elab.Stmt.List.elaborateForInitBlockWithScope rawStmts).run state =
        .ok (frontendStmts, state'))
    (hListRoute :
      ∀ {stateBeforeList stateAfterList : Elab.State},
        (Elab.Stmt.List.elaborate rawStmts).run stateBeforeList =
          .ok (frontendStmts, stateAfterList) →
          CodeElaborationRoute stateAfterList functionName args
            frontendStmts) :
    CodeElaborationRoute state' functionName args frontendStmts := by
  unfold Elab.Stmt.List.elaborateForInitBlockWithScope at hRun
  cases hScope :
      (Elab.Stmt.List.localFunctionScope rawStmts).run state with
  | error err =>
      simp [hScope] at hRun
  | ok scopeResult =>
      rcases scopeResult with ⟨scope, stateAfterScope⟩
      cases hPush :
          (Elab.pushFunctionScope scope).run stateAfterScope with
      | error err =>
          simp [hScope, hPush] at hRun
      | ok pushResult =>
          rcases pushResult with ⟨unitPush, stateAfterPush⟩
          cases hHoist :
              (Elab.Stmt.List.hoistLocalFunctions rawStmts scope).run
                stateAfterPush with
          | error err =>
              simp [hScope, hPush, hHoist] at hRun
          | ok hoistResult =>
              rcases hoistResult with ⟨unitHoist, stateAfterHoist⟩
              cases hList :
                  (Elab.Stmt.List.elaborate rawStmts).run
                    stateAfterHoist with
              | error err =>
                  simp [hScope, hPush, hHoist, hList] at hRun
              | ok listResult =>
                  rcases listResult with
                    ⟨frontendStmts', stateAfterList⟩
                  simp [hScope, hPush, hHoist, hList] at hRun
                  rcases hRun with ⟨rfl, rfl⟩
                  exact hListRoute hList

end List

namespace CaseList

theorem elaborate_retains_hoisted
    {rawCases : List (Raw.SwitchCaseValue × List Raw.Stmt)}
    {frontendCases : List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
    {state state' : Elab.State}
    (hRun :
      (Elab.Stmt.CaseList.elaborate rawCases).run state =
        .ok (frontendCases, state'))
    {entry : Name × Frontend.FunctionDef}
    (hMem : entry ∈ state.hoistedFunctions) :
    entry ∈ state'.hoistedFunctions := by
  have hBelow := retainsHoistedBelow (rawCaseListSize rawCases + 1)
  exact hBelow.caseList (Nat.lt_succ_self _) hRun hMem

end CaseList

end Stmt

namespace FunctionDef

theorem elaborate_retains_hoisted
    {params returns : List Name} {body : List Raw.Stmt}
    {fn : Frontend.FunctionDef} {state state' : Elab.State}
    (hRun :
      (Elab.FunctionDef.elaborate params returns body).run state =
        .ok (fn, state'))
    {entry : Name × Frontend.FunctionDef}
    (hMem : entry ∈ state.hoistedFunctions) :
    entry ∈ state'.hoistedFunctions := by
  have hBelow := retainsHoistedBelow (rawStmtListSize body + 1)
  exact hBelow.function (Nat.lt_succ_self _) hRun hMem

end FunctionDef

theorem elaborateCodeStmts_retains_dispatcher
    {rawStmts : List Raw.Stmt}
    {dispatcherAcc dispatcherOut : List Frontend.Stmt}
    {topFunctionsAcc topFunctionsOut : List (Name × Frontend.FunctionDef)}
    {state state' : Elab.State}
    (hElab :
      (Elab.elaborateCodeStmts rawStmts dispatcherAcc topFunctionsAcc).run
        state = .ok ((dispatcherOut, topFunctionsOut), state'))
    {stmt : Frontend.Stmt} (hMem : stmt ∈ dispatcherAcc) :
    stmt ∈ dispatcherOut := by
  induction rawStmts generalizing dispatcherAcc topFunctionsAcc state
      dispatcherOut topFunctionsOut state' with
  | nil =>
      simp [Elab.elaborateCodeStmts] at hElab
      rcases hElab with ⟨rfl, _hFunctions, _hState⟩
      exact hMem
  | cons head rest ih =>
      simp only [Elab.elaborateCodeStmts] at hElab
      cases head with
      | functionDefinition name params returns body =>
          cases hFn :
              (Elab.FunctionDef.elaborate params returns body).run state with
          | error err =>
              simp [hFn] at hElab
          | ok fnResult =>
              rcases fnResult with ⟨fn, stateAfterFn⟩
              simp [hFn] at hElab
              exact
                ih hElab hMem
      | block body =>
          cases hStmt : (Elab.Stmt.elaborate (.block body)).run state with
          | error err =>
              simp [hStmt] at hElab
          | ok stmtResult =>
              rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
              simp [hStmt] at hElab
              exact
                ih hElab (by simp [hMem])
      | variableDeclaration names value? =>
          cases hStmt :
              (Elab.Stmt.elaborate
                (.variableDeclaration names value?)).run state with
          | error err =>
              simp [hStmt] at hElab
          | ok stmtResult =>
              rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
              simp [hStmt] at hElab
              exact
                ih hElab (by simp [hMem])
      | assignment names value =>
          cases hStmt :
              (Elab.Stmt.elaborate (.assignment names value)).run state with
          | error err =>
              simp [hStmt] at hElab
          | ok stmtResult =>
              rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
              simp [hStmt] at hElab
              exact
                ih hElab (by simp [hMem])
      | expressionStatement value =>
          cases hStmt :
              (Elab.Stmt.elaborate (.expressionStatement value)).run state with
          | error err =>
              simp [hStmt] at hElab
          | ok stmtResult =>
              rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
              simp [hStmt] at hElab
              exact
                ih hElab (by simp [hMem])
      | switch scrutinee cases defaultBody =>
          cases hStmt :
              (Elab.Stmt.elaborate
                (.switch scrutinee cases defaultBody)).run state with
          | error err =>
              simp [hStmt] at hElab
          | ok stmtResult =>
              rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
              simp [hStmt] at hElab
              exact
                ih hElab (by simp [hMem])
      | forLoop pre condition post body =>
          cases hStmt :
              (Elab.Stmt.elaborate
                (.forLoop pre condition post body)).run state with
          | error err =>
              simp [hStmt] at hElab
          | ok stmtResult =>
              rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
              simp [hStmt] at hElab
              exact
                ih hElab (by simp [hMem])
      | ifThen condition body =>
          cases hStmt :
              (Elab.Stmt.elaborate (.ifThen condition body)).run state with
          | error err =>
              simp [hStmt] at hElab
          | ok stmtResult =>
              rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
              simp [hStmt] at hElab
              exact
                ih hElab (by simp [hMem])
      | «break» =>
          simp [Elab.Stmt.elaborate] at hElab
          exact ih hElab (by simp [hMem])
      | «continue» =>
          simp [Elab.Stmt.elaborate] at hElab
          exact ih hElab (by simp [hMem])
      | «leave» =>
          simp [Elab.Stmt.elaborate] at hElab
          exact ih hElab (by simp [hMem])

theorem elaborateCodeStmts_retains_topFunctions
    {rawStmts : List Raw.Stmt}
    {dispatcherAcc dispatcherOut : List Frontend.Stmt}
    {topFunctionsAcc topFunctionsOut : List (Name × Frontend.FunctionDef)}
    {state state' : Elab.State}
    (hElab :
      (Elab.elaborateCodeStmts rawStmts dispatcherAcc topFunctionsAcc).run
        state = .ok ((dispatcherOut, topFunctionsOut), state'))
    {entry : Name × Frontend.FunctionDef}
    (hMem : entry ∈ topFunctionsAcc) :
    entry ∈ topFunctionsOut := by
  induction rawStmts generalizing dispatcherAcc topFunctionsAcc state
      dispatcherOut topFunctionsOut state' with
  | nil =>
      simp [Elab.elaborateCodeStmts] at hElab
      rcases hElab with ⟨_hDispatcher, rfl, _hState⟩
      exact hMem
  | cons head rest ih =>
      simp only [Elab.elaborateCodeStmts] at hElab
      cases head with
      | functionDefinition name params returns body =>
          cases hFn :
              (Elab.FunctionDef.elaborate params returns body).run state with
          | error err =>
              simp [hFn] at hElab
          | ok fnResult =>
              rcases fnResult with ⟨fn, stateAfterFn⟩
              simp [hFn] at hElab
              exact
                ih hElab (by simp [hMem])
      | block body =>
          cases hStmt : (Elab.Stmt.elaborate (.block body)).run state with
          | error err =>
              simp [hStmt] at hElab
          | ok stmtResult =>
              rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
              simp [hStmt] at hElab
              exact ih hElab hMem
      | variableDeclaration names value? =>
          cases hStmt :
              (Elab.Stmt.elaborate
                (.variableDeclaration names value?)).run state with
          | error err =>
              simp [hStmt] at hElab
          | ok stmtResult =>
              rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
              simp [hStmt] at hElab
              exact ih hElab hMem
      | assignment names value =>
          cases hStmt :
              (Elab.Stmt.elaborate (.assignment names value)).run state with
          | error err =>
              simp [hStmt] at hElab
          | ok stmtResult =>
              rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
              simp [hStmt] at hElab
              exact ih hElab hMem
      | expressionStatement value =>
          cases hStmt :
              (Elab.Stmt.elaborate (.expressionStatement value)).run state with
          | error err =>
              simp [hStmt] at hElab
          | ok stmtResult =>
              rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
              simp [hStmt] at hElab
              exact ih hElab hMem
      | switch scrutinee cases defaultBody =>
          cases hStmt :
              (Elab.Stmt.elaborate
                (.switch scrutinee cases defaultBody)).run state with
          | error err =>
              simp [hStmt] at hElab
          | ok stmtResult =>
              rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
              simp [hStmt] at hElab
              exact ih hElab hMem
      | forLoop pre condition post body =>
          cases hStmt :
              (Elab.Stmt.elaborate
                (.forLoop pre condition post body)).run state with
          | error err =>
              simp [hStmt] at hElab
          | ok stmtResult =>
              rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
              simp [hStmt] at hElab
              exact ih hElab hMem
      | ifThen condition body =>
          cases hStmt :
              (Elab.Stmt.elaborate (.ifThen condition body)).run state with
          | error err =>
              simp [hStmt] at hElab
          | ok stmtResult =>
              rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
              simp [hStmt] at hElab
              exact ih hElab hMem
      | «break» =>
          simp [Elab.Stmt.elaborate] at hElab
          exact ih hElab hMem
      | «continue» =>
          simp [Elab.Stmt.elaborate] at hElab
          exact ih hElab hMem
      | «leave» =>
          simp [Elab.Stmt.elaborate] at hElab
          exact ih hElab hMem

theorem elaborateCodeStmts_function_mem
    {rawStmts : List Raw.Stmt}
    {dispatcherAcc dispatcherOut : List Frontend.Stmt}
    {topFunctionsAcc topFunctionsOut : List (Name × Frontend.FunctionDef)}
    {state state' : Elab.State}
    (hElab :
      (Elab.elaborateCodeStmts rawStmts dispatcherAcc topFunctionsAcc).run
        state = .ok ((dispatcherOut, topFunctionsOut), state'))
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    (hMem :
      Raw.Stmt.functionDefinition name params returns body ∈ rawStmts) :
    ∃ (fn : Frontend.FunctionDef) (stateBefore stateAfter : Elab.State),
      (Elab.FunctionDef.elaborate params returns body).run stateBefore =
        .ok (fn, stateAfter) ∧
        (name, fn) ∈ topFunctionsOut := by
  induction rawStmts generalizing dispatcherAcc topFunctionsAcc state
      dispatcherOut topFunctionsOut state' with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      simp only [Elab.elaborateCodeStmts] at hElab
      simp only [List.mem_cons] at hMem
      rcases hMem with hHere | hRest
      · subst head
        cases hFn :
            (Elab.FunctionDef.elaborate params returns body).run state with
        | error err =>
            simp [hFn] at hElab
        | ok fnResult =>
            rcases fnResult with ⟨fn, stateAfterFn⟩
            simp [hFn] at hElab
            have hRetained :
                (name, fn) ∈ topFunctionsOut :=
              elaborateCodeStmts_retains_topFunctions hElab (by simp)
            exact ⟨fn, state, stateAfterFn, hFn, hRetained⟩
      · cases head with
        | functionDefinition headName headParams headReturns headBody =>
            cases hFn :
                (Elab.FunctionDef.elaborate headParams headReturns
                  headBody).run state with
            | error err =>
                simp [hFn] at hElab
            | ok fnResult =>
                rcases fnResult with ⟨fn, stateAfterFn⟩
                simp [hFn] at hElab
                exact ih hElab hRest
        | block blockBody =>
            cases hStmt :
                (Elab.Stmt.elaborate (.block blockBody)).run state with
            | error err =>
                simp [hStmt] at hElab
            | ok stmtResult =>
                rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
                simp [hStmt] at hElab
                exact ih hElab hRest
        | variableDeclaration names value? =>
            cases hStmt :
                (Elab.Stmt.elaborate
                  (.variableDeclaration names value?)).run state with
            | error err =>
                simp [hStmt] at hElab
            | ok stmtResult =>
                rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
                simp [hStmt] at hElab
                exact ih hElab hRest
        | assignment names value =>
            cases hStmt :
                (Elab.Stmt.elaborate (.assignment names value)).run state with
            | error err =>
                simp [hStmt] at hElab
            | ok stmtResult =>
                rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
                simp [hStmt] at hElab
                exact ih hElab hRest
        | expressionStatement value =>
            cases hStmt :
                (Elab.Stmt.elaborate (.expressionStatement value)).run
                  state with
            | error err =>
                simp [hStmt] at hElab
            | ok stmtResult =>
                rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
                simp [hStmt] at hElab
                exact ih hElab hRest
        | switch scrutinee cases defaultBody =>
            cases hStmt :
                (Elab.Stmt.elaborate
                  (.switch scrutinee cases defaultBody)).run state with
            | error err =>
                simp [hStmt] at hElab
            | ok stmtResult =>
                rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
                simp [hStmt] at hElab
                exact ih hElab hRest
        | forLoop pre condition post body =>
            cases hStmt :
                (Elab.Stmt.elaborate
                  (.forLoop pre condition post body)).run state with
            | error err =>
                simp [hStmt] at hElab
            | ok stmtResult =>
                rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
                simp [hStmt] at hElab
                exact ih hElab hRest
        | ifThen condition body =>
            cases hStmt :
                (Elab.Stmt.elaborate (.ifThen condition body)).run state with
            | error err =>
                simp [hStmt] at hElab
            | ok stmtResult =>
                rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
                simp [hStmt] at hElab
                exact ih hElab hRest
        | «break» =>
            simp [Elab.Stmt.elaborate] at hElab
            exact ih hElab hRest
        | «continue» =>
            simp [Elab.Stmt.elaborate] at hElab
            exact ih hElab hRest
        | «leave» =>
            simp [Elab.Stmt.elaborate] at hElab
            exact ih hElab hRest

theorem elaborateCodeStmts_stmt_mem
    {rawStmts : List Raw.Stmt}
    {dispatcherAcc dispatcherOut : List Frontend.Stmt}
    {topFunctionsAcc topFunctionsOut : List (Name × Frontend.FunctionDef)}
    {state state' : Elab.State}
    (hElab :
      (Elab.elaborateCodeStmts rawStmts dispatcherAcc topFunctionsAcc).run
        state = .ok ((dispatcherOut, topFunctionsOut), state'))
    {rawStmt : Raw.Stmt} (hMem : rawStmt ∈ rawStmts)
    (hNotFunction :
      ∀ {name : Name} {params returns : List Name} {body : List Raw.Stmt},
        rawStmt ≠ Raw.Stmt.functionDefinition name params returns body) :
    ∃ (frontendStmt : Frontend.Stmt)
      (stateBefore stateAfter : Elab.State),
      (Elab.Stmt.elaborate rawStmt).run stateBefore =
        .ok (frontendStmt, stateAfter) ∧
        frontendStmt ∈ dispatcherOut := by
  induction rawStmts generalizing dispatcherAcc topFunctionsAcc state
      dispatcherOut topFunctionsOut state' with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      simp only [Elab.elaborateCodeStmts] at hElab
      simp only [List.mem_cons] at hMem
      rcases hMem with hHere | hRest
      · subst head
        cases rawStmt with
        | functionDefinition name params returns body =>
            exact False.elim (hNotFunction rfl)
        | block blockBody =>
            cases hStmt :
                (Elab.Stmt.elaborate (.block blockBody)).run state with
            | error err =>
                simp [hStmt] at hElab
            | ok stmtResult =>
                rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
                simp [hStmt] at hElab
                have hRetained :
                    frontendStmt ∈ dispatcherOut :=
                  elaborateCodeStmts_retains_dispatcher hElab (by simp)
                exact
                  ⟨frontendStmt, state, stateAfterStmt, hStmt, hRetained⟩
        | variableDeclaration names value? =>
            cases hStmt :
                (Elab.Stmt.elaborate
                  (.variableDeclaration names value?)).run state with
            | error err =>
                simp [hStmt] at hElab
            | ok stmtResult =>
                rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
                simp [hStmt] at hElab
                have hRetained :
                    frontendStmt ∈ dispatcherOut :=
                  elaborateCodeStmts_retains_dispatcher hElab (by simp)
                exact
                  ⟨frontendStmt, state, stateAfterStmt, hStmt, hRetained⟩
        | assignment names value =>
            cases hStmt :
                (Elab.Stmt.elaborate (.assignment names value)).run state with
            | error err =>
                simp [hStmt] at hElab
            | ok stmtResult =>
                rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
                simp [hStmt] at hElab
                have hRetained :
                    frontendStmt ∈ dispatcherOut :=
                  elaborateCodeStmts_retains_dispatcher hElab (by simp)
                exact
                  ⟨frontendStmt, state, stateAfterStmt, hStmt, hRetained⟩
        | expressionStatement value =>
            cases hStmt :
                (Elab.Stmt.elaborate (.expressionStatement value)).run
                  state with
            | error err =>
                simp [hStmt] at hElab
            | ok stmtResult =>
                rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
                simp [hStmt] at hElab
                have hRetained :
                    frontendStmt ∈ dispatcherOut :=
                  elaborateCodeStmts_retains_dispatcher hElab (by simp)
                exact
                  ⟨frontendStmt, state, stateAfterStmt, hStmt, hRetained⟩
        | switch scrutinee cases defaultBody =>
            cases hStmt :
                (Elab.Stmt.elaborate
                  (.switch scrutinee cases defaultBody)).run state with
            | error err =>
                simp [hStmt] at hElab
            | ok stmtResult =>
                rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
                simp [hStmt] at hElab
                have hRetained :
                    frontendStmt ∈ dispatcherOut :=
                  elaborateCodeStmts_retains_dispatcher hElab (by simp)
                exact
                  ⟨frontendStmt, state, stateAfterStmt, hStmt, hRetained⟩
        | forLoop pre condition post body =>
            cases hStmt :
                (Elab.Stmt.elaborate
                  (.forLoop pre condition post body)).run state with
            | error err =>
                simp [hStmt] at hElab
            | ok stmtResult =>
                rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
                simp [hStmt] at hElab
                have hRetained :
                    frontendStmt ∈ dispatcherOut :=
                  elaborateCodeStmts_retains_dispatcher hElab (by simp)
                exact
                  ⟨frontendStmt, state, stateAfterStmt, hStmt, hRetained⟩
        | ifThen condition body =>
            cases hStmt :
                (Elab.Stmt.elaborate (.ifThen condition body)).run state with
            | error err =>
                simp [hStmt] at hElab
            | ok stmtResult =>
                rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
                simp [hStmt] at hElab
                have hRetained :
                    frontendStmt ∈ dispatcherOut :=
                  elaborateCodeStmts_retains_dispatcher hElab (by simp)
                exact
                  ⟨frontendStmt, state, stateAfterStmt, hStmt, hRetained⟩
        | «break» =>
            simp [Elab.Stmt.elaborate] at hElab
            have hRetained :
                Frontend.Stmt.break ∈ dispatcherOut :=
              elaborateCodeStmts_retains_dispatcher hElab (by simp)
            exact
              ⟨Frontend.Stmt.break, state, state,
                by simp only [Elab.Stmt.elaborate]; rfl,
                hRetained⟩
        | «continue» =>
            simp [Elab.Stmt.elaborate] at hElab
            have hRetained :
                Frontend.Stmt.continue ∈ dispatcherOut :=
              elaborateCodeStmts_retains_dispatcher hElab (by simp)
            exact
              ⟨Frontend.Stmt.continue, state, state,
                by simp only [Elab.Stmt.elaborate]; rfl, hRetained⟩
        | «leave» =>
            simp [Elab.Stmt.elaborate] at hElab
            have hRetained :
                Frontend.Stmt.leave ∈ dispatcherOut :=
              elaborateCodeStmts_retains_dispatcher hElab (by simp)
            exact
              ⟨Frontend.Stmt.leave, state, state,
                by simp only [Elab.Stmt.elaborate]; rfl, hRetained⟩
      · cases head with
        | functionDefinition headName headParams headReturns headBody =>
            cases hFn :
                (Elab.FunctionDef.elaborate headParams headReturns
                  headBody).run state with
            | error err =>
                simp [hFn] at hElab
            | ok fnResult =>
                rcases fnResult with ⟨fn, stateAfterFn⟩
                simp [hFn] at hElab
                exact ih hElab hRest
        | block blockBody =>
            cases hStmt :
                (Elab.Stmt.elaborate (.block blockBody)).run state with
            | error err =>
                simp [hStmt] at hElab
            | ok stmtResult =>
                rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
                simp [hStmt] at hElab
                exact ih hElab hRest
        | variableDeclaration names value? =>
            cases hStmt :
                (Elab.Stmt.elaborate
                  (.variableDeclaration names value?)).run state with
            | error err =>
                simp [hStmt] at hElab
            | ok stmtResult =>
                rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
                simp [hStmt] at hElab
                exact ih hElab hRest
        | assignment names value =>
            cases hStmt :
                (Elab.Stmt.elaborate (.assignment names value)).run state with
            | error err =>
                simp [hStmt] at hElab
            | ok stmtResult =>
                rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
                simp [hStmt] at hElab
                exact ih hElab hRest
        | expressionStatement value =>
            cases hStmt :
                (Elab.Stmt.elaborate (.expressionStatement value)).run
                  state with
            | error err =>
                simp [hStmt] at hElab
            | ok stmtResult =>
                rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
                simp [hStmt] at hElab
                exact ih hElab hRest
        | switch scrutinee cases defaultBody =>
            cases hStmt :
                (Elab.Stmt.elaborate
                  (.switch scrutinee cases defaultBody)).run state with
            | error err =>
                simp [hStmt] at hElab
            | ok stmtResult =>
                rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
                simp [hStmt] at hElab
                exact ih hElab hRest
        | forLoop pre condition post body =>
            cases hStmt :
                (Elab.Stmt.elaborate
                  (.forLoop pre condition post body)).run state with
            | error err =>
                simp [hStmt] at hElab
            | ok stmtResult =>
                rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
                simp [hStmt] at hElab
                exact ih hElab hRest
        | ifThen condition body =>
            cases hStmt :
                (Elab.Stmt.elaborate (.ifThen condition body)).run state with
            | error err =>
                simp [hStmt] at hElab
            | ok stmtResult =>
                rcases stmtResult with ⟨frontendStmt, stateAfterStmt⟩
                simp [hStmt] at hElab
                exact ih hElab hRest
        | «break» =>
            simp [Elab.Stmt.elaborate] at hElab
            exact ih hElab hRest
        | «continue» =>
            simp [Elab.Stmt.elaborate] at hElab
            exact ih hElab hRest
        | «leave» =>
            simp [Elab.Stmt.elaborate] at hElab
            exact ih hElab hRest

theorem elaborateCodeCore_function_mem
    {rawStmts : List Raw.Stmt} {dispatcher : List Frontend.Stmt}
    {state : Elab.State}
    (hCore :
      Elab.elaborateCodeCore rawStmts = .ok (dispatcher, state))
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    (hMem :
      Raw.Stmt.functionDefinition name params returns body ∈ rawStmts) :
    ∃ (fn : Frontend.FunctionDef) (stateBefore stateAfter : Elab.State),
      (Elab.FunctionDef.elaborate params returns body).run stateBefore =
        .ok (fn, stateAfter) ∧
        (name, fn) ∈ state.hoistedFunctions := by
  unfold Elab.elaborateCodeCore Elab.elaborateCodeAction at hCore
  cases hPush : Elab.pushIdentifierScope.run {} with
  | error err =>
      simp [hPush] at hCore
  | ok pushResult =>
      rcases pushResult with ⟨unitPush, stateAfterPush⟩
      cases hCollect : (Elab.collectTopFunctions rawStmts).run
          stateAfterPush with
      | error err =>
          simp [hPush, hCollect] at hCore
      | ok collectResult =>
          rcases collectResult with ⟨topScope, stateAfterCollect⟩
          cases hPushFunctions :
              (Elab.pushFunctionScope topScope).run
                stateAfterCollect with
          | error err =>
              simp [hPush, hCollect, hPushFunctions] at hCore
          | ok pushFunctionsResult =>
              rcases pushFunctionsResult with
                ⟨unitPushFunctions, stateAfterPushFunctions⟩
              cases hLoop :
                  (Elab.elaborateCodeStmts rawStmts [] []).run
                    stateAfterPushFunctions with
              | error err =>
                  simp [hPush, hCollect, hPushFunctions, hLoop] at hCore
              | ok loopResult =>
                  rcases loopResult with
                    ⟨loopPair, stateAfterLoop⟩
                  rcases loopPair with
                    ⟨dispatcherRev, topFunctions⟩
                  cases hPopFunctions :
                      Elab.popFunctionScope.run stateAfterLoop with
                  | error err =>
                      simp [hPush, hCollect, hPushFunctions, hLoop,
                        hPopFunctions] at hCore
                  | ok popFunctionsResult =>
                      rcases popFunctionsResult with
                        ⟨unitPopFunctions, stateAfterPopFunctions⟩
                      cases hPopIdentifiers :
                          Elab.popIdentifierScope.run
                            stateAfterPopFunctions with
                      | error err =>
                          simp [hPush, hCollect, hPushFunctions, hLoop,
                            hPopFunctions, hPopIdentifiers] at hCore
                      | ok popIdentifiersResult =>
                          rcases popIdentifiersResult with
                            ⟨unitPopIdentifiers,
                              stateAfterPopIdentifiers⟩
                          simp [hPush, hCollect, hPushFunctions, hLoop,
                            hPopFunctions, hPopIdentifiers] at hCore
                          rcases hCore with ⟨rfl, rfl⟩
                          rcases elaborateCodeStmts_function_mem
                              hLoop hMem with
                            ⟨fn, stateBefore, stateAfter, hFn,
                              hTopMem⟩
                          exact
                            ⟨fn, stateBefore, stateAfter, hFn,
                              by simp [hTopMem]⟩

theorem elaborateCodeCore_stmt_mem
    {rawStmts : List Raw.Stmt} {dispatcher : List Frontend.Stmt}
    {state : Elab.State}
    (hCore :
      Elab.elaborateCodeCore rawStmts = .ok (dispatcher, state))
    {rawStmt : Raw.Stmt} (hMem : rawStmt ∈ rawStmts)
    (hNotFunction :
      ∀ {name : Name} {params returns : List Name} {body : List Raw.Stmt},
        rawStmt ≠ Raw.Stmt.functionDefinition name params returns body) :
    ∃ (frontendStmt : Frontend.Stmt)
      (stateBefore stateAfter : Elab.State),
      (Elab.Stmt.elaborate rawStmt).run stateBefore =
        .ok (frontendStmt, stateAfter) ∧
        frontendStmt ∈ dispatcher := by
  unfold Elab.elaborateCodeCore Elab.elaborateCodeAction at hCore
  cases hPush : Elab.pushIdentifierScope.run {} with
  | error err =>
      simp [hPush] at hCore
  | ok pushResult =>
      rcases pushResult with ⟨unitPush, stateAfterPush⟩
      cases hCollect : (Elab.collectTopFunctions rawStmts).run
          stateAfterPush with
      | error err =>
          simp [hPush, hCollect] at hCore
      | ok collectResult =>
          rcases collectResult with ⟨topScope, stateAfterCollect⟩
          cases hPushFunctions :
              (Elab.pushFunctionScope topScope).run
                stateAfterCollect with
          | error err =>
              simp [hPush, hCollect, hPushFunctions] at hCore
          | ok pushFunctionsResult =>
              rcases pushFunctionsResult with
                ⟨unitPushFunctions, stateAfterPushFunctions⟩
              cases hLoop :
                  (Elab.elaborateCodeStmts rawStmts [] []).run
                    stateAfterPushFunctions with
              | error err =>
                  simp [hPush, hCollect, hPushFunctions, hLoop] at hCore
              | ok loopResult =>
                  rcases loopResult with
                    ⟨loopPair, stateAfterLoop⟩
                  rcases loopPair with
                    ⟨dispatcherRev, topFunctions⟩
                  cases hPopFunctions :
                      Elab.popFunctionScope.run stateAfterLoop with
                  | error err =>
                      simp [hPush, hCollect, hPushFunctions, hLoop,
                        hPopFunctions] at hCore
                  | ok popFunctionsResult =>
                      rcases popFunctionsResult with
                        ⟨unitPopFunctions, stateAfterPopFunctions⟩
                      cases hPopIdentifiers :
                          Elab.popIdentifierScope.run
                            stateAfterPopFunctions with
                      | error err =>
                          simp [hPush, hCollect, hPushFunctions, hLoop,
                            hPopFunctions, hPopIdentifiers] at hCore
                      | ok popIdentifiersResult =>
                          rcases popIdentifiersResult with
                            ⟨unitPopIdentifiers,
                              stateAfterPopIdentifiers⟩
                          simp [hPush, hCollect, hPushFunctions, hLoop,
                            hPopFunctions, hPopIdentifiers] at hCore
                          rcases hCore with ⟨rfl, _hState⟩
                          rcases elaborateCodeStmts_stmt_mem hLoop hMem
                              hNotFunction with
                            ⟨frontendStmt, stateBefore, stateAfter,
                              hStmt, hDispatcherMem⟩
                          exact
                            ⟨frontendStmt, stateBefore, stateAfter,
                              hStmt, by simpa using hDispatcherMem⟩

end Elab

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

namespace StmtUserCall

theorem elaborate_route
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
      StmtElaborationRoute generated frontendArgs frontendStmt := by
  rcases StmtUserCall.elaborate hOccurrence hNotMemoryguard hNotClz
      hKind hElab with
    ⟨generated, frontendArgs, hFrontend⟩
  exact
    ⟨generated, frontendArgs,
      StmtElaborationOccurrence.route hFrontend⟩

end StmtUserCall

namespace StmtListUserCall

theorem elaborate_route
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
      StmtListElaborationRoute generated frontendArgs frontendStmts := by
  rcases StmtListUserCall.elaborate hOccurrence hNotMemoryguard hNotClz
      hKind hElab with
    ⟨generated, frontendArgs, hFrontend⟩
  exact
    ⟨generated, frontendArgs,
      StmtListElaborationOccurrence.route hFrontend⟩

end StmtListUserCall

namespace CaseListUserCall

theorem elaborate_route
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
      CaseListElaborationRoute generated frontendArgs frontendCases := by
  rcases CaseListUserCall.elaborate hOccurrence hNotMemoryguard hNotClz
      hKind hElab with
    ⟨generated, frontendArgs, hFrontend⟩
  exact
    ⟨generated, frontendArgs,
      CaseListElaborationOccurrence.route hFrontend⟩

end CaseListUserCall

end RawOccurrence
end RawAst
end Solidity
end EvmCompiler
