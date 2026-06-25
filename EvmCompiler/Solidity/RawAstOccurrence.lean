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

end RawOccurrence
end RawAst
end Solidity
end EvmCompiler
