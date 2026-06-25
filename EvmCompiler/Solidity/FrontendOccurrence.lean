import EvmCompiler.Solidity.Frontend
import EvmCompiler.Yul.Occurrence

namespace EvmCompiler
namespace Solidity
namespace FrontendOccurrence

inductive ExprUserCall (functionName : Frontend.Name)
    (args : List Frontend.Expr) : Frontend.Expr → Prop where
  | here :
      ExprUserCall functionName args
        (.call .user functionName args)
  | callArg
      {kind : Frontend.CallKind} {callee : Frontend.Name}
      {outerArgs : List Frontend.Expr} {arg : Frontend.Expr} :
      arg ∈ outerArgs →
        ExprUserCall functionName args arg →
          ExprUserCall functionName args (.call kind callee outerArgs)

mutual
  inductive StmtUserCall (functionName : Frontend.Name)
      (args : List Frontend.Expr) : Frontend.Stmt → Prop where
    | block {body : List Frontend.Stmt} :
        StmtListUserCall functionName args body →
          StmtUserCall functionName args (.block body)
    | letValue {names : List Frontend.Name} {value : Frontend.Expr} :
        ExprUserCall functionName args value →
          StmtUserCall functionName args (.letDecl names (some value))
    | assignValue {names : List Frontend.Name} {value : Frontend.Expr} :
        ExprUserCall functionName args value →
          StmtUserCall functionName args (.assign names value)
    | exprStmt {value : Frontend.Expr} :
        ExprUserCall functionName args value →
          StmtUserCall functionName args (.exprStmt value)
    | switchScrutinee
        {scrutinee : Frontend.Expr}
        {cases : List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
        {defaultBody : List Frontend.Stmt} :
        ExprUserCall functionName args scrutinee →
          StmtUserCall functionName args
            (.switch scrutinee cases defaultBody)
    | switchCase
        {scrutinee : Frontend.Expr}
        {cases : List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
        {defaultBody : List Frontend.Stmt} :
        CaseListUserCall functionName args cases →
          StmtUserCall functionName args
            (.switch scrutinee cases defaultBody)
    | switchDefault
        {scrutinee : Frontend.Expr}
        {cases : List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
        {defaultBody : List Frontend.Stmt} :
        StmtListUserCall functionName args defaultBody →
          StmtUserCall functionName args
            (.switch scrutinee cases defaultBody)
    | forPre
        {pre post body : List Frontend.Stmt}
        {condition : Frontend.Expr} :
        StmtListUserCall functionName args pre →
          StmtUserCall functionName args
            (.forLoop pre condition post body)
    | forCondition
        {pre post body : List Frontend.Stmt}
        {condition : Frontend.Expr} :
        ExprUserCall functionName args condition →
          StmtUserCall functionName args
            (.forLoop pre condition post body)
    | forPost
        {pre post body : List Frontend.Stmt}
        {condition : Frontend.Expr} :
        StmtListUserCall functionName args post →
          StmtUserCall functionName args
            (.forLoop pre condition post body)
    | forBody
        {pre post body : List Frontend.Stmt}
        {condition : Frontend.Expr} :
        StmtListUserCall functionName args body →
          StmtUserCall functionName args
            (.forLoop pre condition post body)
    | ifCondition {condition : Frontend.Expr}
        {body : List Frontend.Stmt} :
        ExprUserCall functionName args condition →
          StmtUserCall functionName args (.ifThen condition body)
    | ifBody {condition : Frontend.Expr}
        {body : List Frontend.Stmt} :
        StmtListUserCall functionName args body →
          StmtUserCall functionName args (.ifThen condition body)

  inductive StmtListUserCall (functionName : Frontend.Name)
      (args : List Frontend.Expr) : List Frontend.Stmt → Prop where
    | head {stmt : Frontend.Stmt} {rest : List Frontend.Stmt} :
        StmtUserCall functionName args stmt →
          StmtListUserCall functionName args (stmt :: rest)
    | tail {stmt : Frontend.Stmt} {rest : List Frontend.Stmt} :
        StmtListUserCall functionName args rest →
          StmtListUserCall functionName args (stmt :: rest)

  inductive CaseListUserCall (functionName : Frontend.Name)
      (args : List Frontend.Expr) :
      List (Frontend.SwitchCaseValue × List Frontend.Stmt) → Prop where
    | head {value : Frontend.SwitchCaseValue}
        {body : List Frontend.Stmt}
        {rest : List (Frontend.SwitchCaseValue × List Frontend.Stmt)} :
        StmtListUserCall functionName args body →
          CaseListUserCall functionName args ((value, body) :: rest)
    | tail {head : Frontend.SwitchCaseValue × List Frontend.Stmt}
        {rest : List (Frontend.SwitchCaseValue × List Frontend.Stmt)} :
        CaseListUserCall functionName args rest →
          CaseListUserCall functionName args (head :: rest)
end

namespace StmtListUserCall

theorem exists_split_stmt
    {functionName : Frontend.Name} {args : List Frontend.Expr}
    {stmts : List Frontend.Stmt}
    (hOccurrence : StmtListUserCall functionName args stmts) :
    ∃ (pre : List Frontend.Stmt) (stmt : Frontend.Stmt)
      (suffix : List Frontend.Stmt),
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
    {functionName : Frontend.Name} {args : List Frontend.Expr}
    {pre suffix : List Frontend.Stmt} {stmt : Frontend.Stmt}
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

theorem toYul?_mem
    {exprs : List Frontend.Expr} {yulExprs : List Yul.AstExpr}
    (hConvert : Frontend.Expr.List.toYul? exprs = some yulExprs)
    {expr : Frontend.Expr} (hMem : expr ∈ exprs) :
    ∃ yulExpr,
      Frontend.Expr.toYul? expr = some yulExpr ∧
        yulExpr ∈ yulExprs := by
  induction exprs generalizing yulExprs with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      simp only [Frontend.Expr.List.toYul?] at hConvert
      cases hHead : Frontend.Expr.toYul? head with
      | none =>
          simp [hHead] at hConvert
      | some headYul =>
          cases hTail : Frontend.Expr.List.toYul? rest with
          | none =>
              simp [hHead, hTail] at hConvert
          | some tailYul =>
              simp [hHead, hTail] at hConvert
              subst yulExprs
              simp only [List.mem_cons] at hMem ⊢
              rcases hMem with hHere | hRest
              · subst expr
                exact ⟨headYul, hHead, Or.inl rfl⟩
              · rcases ih hTail hRest with
                  ⟨yulExpr, hExpr, hYulMem⟩
                exact ⟨yulExpr, hExpr, Or.inr hYulMem⟩

end List
end Expr

namespace ExprUserCall

theorem toYul?
    {functionName : Frontend.Name} {args : List Frontend.Expr}
    {expr : Frontend.Expr} {yulArgs : List Yul.AstExpr}
    {yulExpr : Yul.AstExpr}
    (hOccurrence : ExprUserCall functionName args expr)
    (hExpr : Frontend.Expr.toYul? expr = some yulExpr)
    (hArgs : Frontend.Expr.List.toYul? args = some yulArgs) :
    Yul.YulOccurrence.ExprUserCall functionName yulArgs yulExpr := by
  induction hOccurrence generalizing yulExpr with
  | here =>
      simp [Frontend.Expr.toYul?, hArgs] at hExpr
      subst yulExpr
      exact Yul.YulOccurrence.ExprUserCall.here
  | @callArg kind callee outerArgs arg hMem _ ih =>
      cases kind with
      | primitive =>
          cases hOp : Frontend.Primitive.ofName? callee with
          | none =>
              simp [Frontend.Expr.toYul?, hOp] at hExpr
          | some op =>
              cases hOuter :
                  Frontend.Expr.List.toYul? outerArgs with
              | none =>
                  simp [Frontend.Expr.toYul?, hOp, hOuter] at hExpr
              | some yulOuterArgs =>
                  simp [Frontend.Expr.toYul?, hOp, hOuter] at hExpr
                  subst yulExpr
                  rcases Expr.List.toYul?_mem hOuter hMem with
                    ⟨yulArg, hArg, hYulMem⟩
                  exact
                    Yul.YulOccurrence.ExprUserCall.callArg
                      hYulMem (ih hArg)
      | user =>
          cases hOuter : Frontend.Expr.List.toYul? outerArgs with
          | none =>
              simp [Frontend.Expr.toYul?, hOuter] at hExpr
          | some yulOuterArgs =>
              simp [Frontend.Expr.toYul?, hOuter] at hExpr
              subst yulExpr
              rcases Expr.List.toYul?_mem hOuter hMem with
                ⟨yulArg, hArg, hYulMem⟩
              exact
                Yul.YulOccurrence.ExprUserCall.callArg
                  hYulMem (ih hArg)
      | objectBuiltin =>
          simp [Frontend.Expr.toYul?] at hExpr
      | dialectBuiltin =>
          simp [Frontend.Expr.toYul?] at hExpr

end ExprUserCall

mutual
  theorem StmtUserCall.toYul?
      {functionName : Frontend.Name} {args : List Frontend.Expr}
      {stmt : Frontend.Stmt} {yulArgs : List Yul.AstExpr}
      {yulStmt : Yul.AstStmt}
      (hOccurrence : StmtUserCall functionName args stmt)
      (hStmt : Frontend.Stmt.toYul? stmt = some yulStmt)
      (hArgs : Frontend.Expr.List.toYul? args = some yulArgs) :
      Yul.YulOccurrence.StmtUserCall functionName yulArgs yulStmt := by
    cases hOccurrence with
    | block hBody =>
        simp [Frontend.Stmt.toYul?, Option.bind_eq_some_iff] at hStmt
        rcases hStmt with ⟨yulBody, hBodyConvert, hEq⟩
        subst yulStmt
        exact
          Yul.YulOccurrence.StmtUserCall.block
            (StmtListUserCall.toYul? hBody hBodyConvert hArgs)
    | letValue hValue =>
        simp [Frontend.Stmt.toYul?, Option.bind_eq_some_iff] at hStmt
        rcases hStmt with ⟨yulValue, hValueConvert, hEq⟩
        subst yulStmt
        exact
          Yul.YulOccurrence.StmtUserCall.letValue
            (ExprUserCall.toYul? hValue hValueConvert hArgs)
    | assignValue hValue =>
        simp [Frontend.Stmt.toYul?, Option.bind_eq_some_iff] at hStmt
        rcases hStmt with ⟨yulValue, hValueConvert, hEq⟩
        subst yulStmt
        exact
          Yul.YulOccurrence.StmtUserCall.assignValue
            (ExprUserCall.toYul? hValue hValueConvert hArgs)
    | exprStmt hValue =>
        simp [Frontend.Stmt.toYul?, Option.bind_eq_some_iff] at hStmt
        rcases hStmt with ⟨yulValue, hValueConvert, hEq⟩
        subst yulStmt
        exact
          Yul.YulOccurrence.StmtUserCall.exprStmt
            (ExprUserCall.toYul? hValue hValueConvert hArgs)
    | switchScrutinee hScrutinee =>
        simp [Frontend.Stmt.toYul?, Option.bind_eq_some_iff] at hStmt
        rcases hStmt with
          ⟨yulScrutinee, hScrutineeConvert, yulCases, hCasesConvert,
            yulDefault, hDefaultConvert, hEq⟩
        subst yulStmt
        exact
          Yul.YulOccurrence.StmtUserCall.switchScrutinee
            (ExprUserCall.toYul? hScrutinee hScrutineeConvert hArgs)
    | switchCase hCases =>
        simp [Frontend.Stmt.toYul?, Option.bind_eq_some_iff] at hStmt
        rcases hStmt with
          ⟨yulScrutinee, hScrutineeConvert, yulCases, hCasesConvert,
            yulDefault, hDefaultConvert, hEq⟩
        subst yulStmt
        exact
          Yul.YulOccurrence.StmtUserCall.switchCase
            (CaseListUserCall.toYul? hCases hCasesConvert hArgs)
    | switchDefault hDefault =>
        simp [Frontend.Stmt.toYul?, Option.bind_eq_some_iff] at hStmt
        rcases hStmt with
          ⟨yulScrutinee, hScrutineeConvert, yulCases, hCasesConvert,
            yulDefault, hDefaultConvert, hEq⟩
        subst yulStmt
        exact
          Yul.YulOccurrence.StmtUserCall.switchDefault
            (StmtListUserCall.toYul? hDefault hDefaultConvert hArgs)
    | forPre hPre =>
        simp [Frontend.Stmt.toYul?, Option.bind_eq_some_iff] at hStmt
        rcases hStmt with
          ⟨yulPre, hPreConvert, yulCondition, hConditionConvert,
            yulPost, hPostConvert, yulBody, hBodyConvert, hEq⟩
        have hPreOccurrence :
            Yul.YulOccurrence.StmtListUserCall functionName yulArgs yulPre :=
          StmtListUserCall.toYul? hPre hPreConvert hArgs
        cases yulPre with
        | nil =>
            cases hPreOccurrence
        | cons head tail =>
            simp at hEq
            subst yulStmt
            exact
              Yul.YulOccurrence.StmtUserCall.block
                (Yul.YulOccurrence.StmtListUserCall.append_right
                  [EvmYul.Yul.Ast.Stmt.For yulCondition yulPost yulBody]
                  hPreOccurrence)
    | forCondition hCondition =>
        simp [Frontend.Stmt.toYul?, Option.bind_eq_some_iff] at hStmt
        rcases hStmt with
          ⟨yulPre, hPreConvert, yulCondition, hConditionConvert,
            yulPost, hPostConvert, yulBody, hBodyConvert, hEq⟩
        have hYulCondition :
            Yul.YulOccurrence.ExprUserCall functionName yulArgs yulCondition :=
          ExprUserCall.toYul? hCondition hConditionConvert hArgs
        cases yulPre with
        | nil =>
            simp at hEq
            subst yulStmt
            exact Yul.YulOccurrence.StmtUserCall.forCondition hYulCondition
        | cons head tail =>
            simp at hEq
            subst yulStmt
            exact
              Yul.YulOccurrence.StmtUserCall.block
                (Yul.YulOccurrence.StmtListUserCall.of_split_stmt
                  (pre := head :: tail) (suffix := [])
                  (Yul.YulOccurrence.StmtUserCall.forCondition hYulCondition))
    | forPost hPost =>
        simp [Frontend.Stmt.toYul?, Option.bind_eq_some_iff] at hStmt
        rcases hStmt with
          ⟨yulPre, hPreConvert, yulCondition, hConditionConvert,
            yulPost, hPostConvert, yulBody, hBodyConvert, hEq⟩
        have hYulPost :
            Yul.YulOccurrence.StmtListUserCall functionName yulArgs yulPost :=
          StmtListUserCall.toYul? hPost hPostConvert hArgs
        cases yulPre with
        | nil =>
            simp at hEq
            subst yulStmt
            exact Yul.YulOccurrence.StmtUserCall.forPost hYulPost
        | cons head tail =>
            simp at hEq
            subst yulStmt
            exact
              Yul.YulOccurrence.StmtUserCall.block
                (Yul.YulOccurrence.StmtListUserCall.of_split_stmt
                  (pre := head :: tail) (suffix := [])
                  (Yul.YulOccurrence.StmtUserCall.forPost hYulPost))
    | forBody hBody =>
        simp [Frontend.Stmt.toYul?, Option.bind_eq_some_iff] at hStmt
        rcases hStmt with
          ⟨yulPre, hPreConvert, yulCondition, hConditionConvert,
            yulPost, hPostConvert, yulBody, hBodyConvert, hEq⟩
        have hYulBody :
            Yul.YulOccurrence.StmtListUserCall functionName yulArgs yulBody :=
          StmtListUserCall.toYul? hBody hBodyConvert hArgs
        cases yulPre with
        | nil =>
            simp at hEq
            subst yulStmt
            exact Yul.YulOccurrence.StmtUserCall.forBody hYulBody
        | cons head tail =>
            simp at hEq
            subst yulStmt
            exact
              Yul.YulOccurrence.StmtUserCall.block
                (Yul.YulOccurrence.StmtListUserCall.of_split_stmt
                  (pre := head :: tail) (suffix := [])
                  (Yul.YulOccurrence.StmtUserCall.forBody hYulBody))
    | ifCondition hCondition =>
        simp [Frontend.Stmt.toYul?, Option.bind_eq_some_iff] at hStmt
        rcases hStmt with
          ⟨yulCondition, hConditionConvert, yulBody, hBodyConvert, hEq⟩
        subst yulStmt
        exact
          Yul.YulOccurrence.StmtUserCall.ifCondition
            (ExprUserCall.toYul? hCondition hConditionConvert hArgs)
    | ifBody hBody =>
        simp [Frontend.Stmt.toYul?, Option.bind_eq_some_iff] at hStmt
        rcases hStmt with
          ⟨yulCondition, hConditionConvert, yulBody, hBodyConvert, hEq⟩
        subst yulStmt
        exact
          Yul.YulOccurrence.StmtUserCall.ifBody
            (StmtListUserCall.toYul? hBody hBodyConvert hArgs)

  theorem StmtListUserCall.toYul?
      {functionName : Frontend.Name} {args : List Frontend.Expr}
      {stmts : List Frontend.Stmt} {yulArgs : List Yul.AstExpr}
      {yulStmts : List Yul.AstStmt}
      (hOccurrence : StmtListUserCall functionName args stmts)
      (hStmts : Frontend.Stmt.List.toYul? stmts = some yulStmts)
      (hArgs : Frontend.Expr.List.toYul? args = some yulArgs) :
      Yul.YulOccurrence.StmtListUserCall functionName yulArgs yulStmts := by
    cases hOccurrence with
    | head hStmtOccurrence =>
        simp [Frontend.Stmt.List.toYul?, Option.bind_eq_some_iff] at hStmts
        rcases hStmts with
          ⟨yulStmt, hStmtConvert, yulRest, hRestConvert, hEq⟩
        subst yulStmts
        exact
          Yul.YulOccurrence.StmtListUserCall.head
            (StmtUserCall.toYul? hStmtOccurrence hStmtConvert hArgs)
    | tail hTail =>
        simp [Frontend.Stmt.List.toYul?, Option.bind_eq_some_iff] at hStmts
        rcases hStmts with
          ⟨yulStmt, hStmtConvert, yulRest, hRestConvert, hEq⟩
        subst yulStmts
        exact
          Yul.YulOccurrence.StmtListUserCall.tail
            (StmtListUserCall.toYul? hTail hRestConvert hArgs)

  theorem CaseListUserCall.toYul?
      {functionName : Frontend.Name} {args : List Frontend.Expr}
      {cases : List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
      {yulArgs : List Yul.AstExpr}
      {yulCases : List (Yul.Word × List Yul.AstStmt)}
      (hOccurrence : CaseListUserCall functionName args cases)
      (hCases : Frontend.Stmt.CaseList.toYul? cases = some yulCases)
      (hArgs : Frontend.Expr.List.toYul? args = some yulArgs) :
      Yul.YulOccurrence.CaseListUserCall functionName yulArgs yulCases := by
    cases hOccurrence with
    | head hBody =>
        simp [Frontend.Stmt.CaseList.toYul?, Option.bind_eq_some_iff]
          at hCases
        rcases hCases with
          ⟨yulValue, hValueConvert, yulBody, hBodyConvert,
            yulRest, hRestConvert, hEq⟩
        subst yulCases
        exact
          Yul.YulOccurrence.CaseListUserCall.head
            (StmtListUserCall.toYul? hBody hBodyConvert hArgs)
    | tail hTail =>
        simp [Frontend.Stmt.CaseList.toYul?, Option.bind_eq_some_iff]
          at hCases
        rcases hCases with
          ⟨yulValue, hValueConvert, yulBody, hBodyConvert,
            yulRest, hRestConvert, hEq⟩
        subst yulCases
        exact
          Yul.YulOccurrence.CaseListUserCall.tail
            (CaseListUserCall.toYul? hTail hRestConvert hArgs)
end

namespace FunctionDef

theorem bodyOccurrence_toYul?
    {functionName : Frontend.Name} {args : List Frontend.Expr}
    {fn : Frontend.FunctionDef} {params returns : List Frontend.Name}
    {body : List Yul.AstStmt} {yulArgs : List Yul.AstExpr}
    (hOccurrence : StmtListUserCall functionName args fn.body)
    (hFn : Frontend.FunctionDef.toYul? fn =
      some (.Def params returns body))
    (hArgs : Frontend.Expr.List.toYul? args = some yulArgs) :
    Yul.YulOccurrence.StmtListUserCall functionName yulArgs body := by
  simp [Frontend.FunctionDef.toYul?, Option.bind_eq_some_iff] at hFn
  rcases hFn with ⟨hBody, _hParams, _hReturns⟩
  exact StmtListUserCall.toYul? hOccurrence hBody hArgs

end FunctionDef

namespace Object

theorem dispatcherOccurrence_toOrdered?
    {functionName : Frontend.Name} {args : List Frontend.Expr}
    {object : Frontend.Object} {ordered : Yul.OrderedProgram}
    {yulArgs : List Yul.AstExpr}
    (hOccurrence :
      StmtListUserCall functionName args object.dispatcher)
    (hConvert : object.toSolcYulOrderedProgram? = some ordered)
    (hArgs : Frontend.Expr.List.toYul? args = some yulArgs) :
    Yul.YulOccurrence.StmtListUserCall functionName yulArgs
      [ordered.program.contract.dispatcher] := by
  unfold Frontend.Object.toSolcYulOrderedProgram? at hConvert
  cases hContract : object.toYulContractWithFunctionEntries? with
  | none =>
      simp [hContract] at hConvert
  | some result =>
      rcases result with ⟨contract, functions⟩
      cases hValid :
          Yul.SolcValidation.ContractOkWithEntries?
            object.dialectProfile contract functions <;>
        simp [hContract, hValid] at hConvert
      rcases hConvert with ⟨_hSpelling, hConvert⟩
      subst ordered
      unfold Frontend.Object.toYulContractWithFunctionEntries? at hContract
      cases hDispatcher :
          Frontend.Stmt.toYul? (.block object.dispatcher) with
      | none =>
          simp [hDispatcher] at hContract
      | some dispatcher =>
          cases hFunctions :
              Frontend.FunctionDef.List.toYul? object.functions with
          | none =>
              simp [hDispatcher, hFunctions] at hContract
          | some entries =>
              simp [hDispatcher, hFunctions] at hContract
              rcases hContract with ⟨rfl, rfl⟩
              exact
                Yul.YulOccurrence.StmtListUserCall.head
                  (StmtUserCall.toYul?
                    (StmtUserCall.block hOccurrence) hDispatcher hArgs)

end Object

end FrontendOccurrence
end Solidity
end EvmCompiler
