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

end FrontendOccurrence
end Solidity
end EvmCompiler
