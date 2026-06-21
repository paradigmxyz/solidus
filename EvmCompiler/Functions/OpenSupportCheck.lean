import EvmCompiler.Functions.InteractionSemantics

namespace EvmCompiler
namespace Functions
namespace OpenSupportCheck

theorem and_parts {left right : Bool}
    (h : (left && right) = true) :
    left = true ∧ right = true := by
  simpa using h

mutual
  def expr? {results : Nat} : Locals.Expr results → Bool
    | .lit _ | .var _ => true
    | .code _ => false
    | .prim op args =>
        Locals.InteractionSemantics.Primitive.supportsOpen op && exprSeq? args

  def exprSeq? {results : Nat} : Locals.ExprSeq results → Bool
    | .nil => true
    | .cons head tail => expr? head && exprSeq? tail
end

theorem expr_of_check {results : Nat} {expr : Locals.Expr results}
    (hCheck : expr? expr = true) :
    Locals.InteractionSemantics.Expr.OpenSupported expr := by
  exact
    Locals.Expr.rec
      (motive_1 := fun _ expr =>
        expr? expr = true →
          Locals.InteractionSemantics.Expr.OpenSupported expr)
      (motive_2 := fun _ exprs =>
        exprSeq? exprs = true →
          Locals.InteractionSemantics.ExprSeq.OpenSupported exprs)
      (fun _ _ => True.intro)
      (fun _ _ => True.intro)
      (fun _ h => by simp [expr?] at h)
      (fun _ _ hArgs h => by
        have hParts := and_parts h
        exact ⟨hParts.1, hArgs hParts.2⟩)
      (fun _ => True.intro)
      (fun _ _ hHead hTail h => by
        have hParts := and_parts h
        exact ⟨hHead hParts.1, hTail hParts.2⟩)
      expr hCheck

theorem exprSeq_of_check {results : Nat} {exprs : Locals.ExprSeq results}
    (hCheck : exprSeq? exprs = true) :
    Locals.InteractionSemantics.ExprSeq.OpenSupported exprs := by
  exact
    Locals.ExprSeq.rec
      (motive_1 := fun _ expr =>
        expr? expr = true →
          Locals.InteractionSemantics.Expr.OpenSupported expr)
      (motive_2 := fun _ exprs =>
        exprSeq? exprs = true →
          Locals.InteractionSemantics.ExprSeq.OpenSupported exprs)
      (fun _ _ => True.intro)
      (fun _ _ => True.intro)
      (fun _ h => by simp [expr?] at h)
      (fun _ _ hArgs h => by
        have hParts := and_parts h
        exact ⟨hParts.1, hArgs hParts.2⟩)
      (fun _ => True.intro)
      (fun _ _ hHead hTail h => by
        have hParts := and_parts h
        exact ⟨hHead hParts.1, hTail hParts.2⟩)
      exprs hCheck

def argList? (args : List (Functions.Expr 1)) : Bool :=
  args.all expr?

theorem argList_of_check {args : List (Functions.Expr 1)}
    (hCheck : argList? args = true) :
    Functions.InteractionSemantics.ArgList.OpenSupported args := by
  intro expr hMem
  exact expr_of_check ((List.all_eq_true.mp hCheck) expr hMem)

mutual
  def block? : Functions.Block → Bool
    | ⟨stmts⟩ => stmtList? stmts

  def stmt? : Functions.Stmt → Bool
    | .expr expr => expr? expr
    | .let_ _ value | .assign _ value => expr? value
    | .block body => block? body
    | .if_ cond body => expr? cond && block? body
    | .switch scrutinee cases defaultBody =>
        expr? scrutinee && caseList? cases && default? defaultBody
    | .for_ init cond post body =>
        block? init && expr? cond && block? post && block? body
    | .brk | .cont | .leave | .terminal _ => true
    | .call _ _ args => argList? args
    | .terminalArgs _ args => exprSeq? args

  def stmtList? : List Functions.Stmt → Bool
    | [] => true
    | stmt :: rest => stmt? stmt && stmtList? rest

  def caseList? : List (Word × Functions.Block) → Bool
    | [] => true
    | (_, body) :: rest => block? body && caseList? rest

  def default? : Option Functions.Block → Bool
    | none => true
    | some body => block? body
end

theorem block_of_check {block : Functions.Block}
    (hCheck : block? block = true) :
    Functions.InteractionSemantics.Block.OpenSupported block := by
  exact
    Functions.Block.rec
      (motive_1 := fun block =>
        block? block = true →
          Functions.InteractionSemantics.Block.OpenSupported block)
      (motive_2 := fun stmt =>
        stmt? stmt = true →
          Functions.InteractionSemantics.Stmt.OpenSupported stmt)
      (motive_3 := fun stmts =>
        stmtList? stmts = true →
          Functions.InteractionSemantics.StmtList.OpenSupported stmts)
      (motive_4 := fun cases =>
        caseList? cases = true →
          Functions.InteractionSemantics.CaseList.OpenSupported cases)
      (motive_5 := fun body =>
        default? body = true →
          Functions.InteractionSemantics.Default.OpenSupported body)
      (motive_6 := fun pair =>
        block? pair.2 = true →
          Functions.InteractionSemantics.Block.OpenSupported pair.2)
      (fun _ hStmts h => hStmts h)
      (fun expr h => expr_of_check h)
      (fun _ value h => expr_of_check h)
      (fun _ value h => expr_of_check h)
      (fun _ hBody h => hBody h)
      (fun cond _ hBody h => by
        have hParts := and_parts h
        exact ⟨expr_of_check hParts.1, hBody hParts.2⟩)
      (fun scrutinee _ _ hCases hDefault h => by
        have hHead := and_parts h
        have hTail := and_parts hHead.1
        exact
          ⟨expr_of_check hTail.1, hCases hTail.2,
            hDefault hHead.2⟩)
      (fun _ cond _ _ hInit hPost hBody h => by
        have hBodyParts := and_parts h
        have hPostParts := and_parts hBodyParts.1
        have hCondParts := and_parts hPostParts.1
        exact
          ⟨hInit hCondParts.1, expr_of_check hCondParts.2,
            hPost hPostParts.2, hBody hBodyParts.2⟩)
      (fun _ => True.intro)
      (fun _ => True.intro)
      (fun _ => True.intro)
      (fun _ _ args h => argList_of_check h)
      (fun _ _ => True.intro)
      (fun _ args h => exprSeq_of_check h)
      (fun _ => True.intro)
      (fun _ _ hHead hTail h => by
        have hParts := and_parts h
        exact ⟨hHead hParts.1, hTail hParts.2⟩)
      (fun _ => True.intro)
      (fun _ _ hHead hTail h => by
        have hParts := and_parts h
        exact ⟨hHead hParts.1, hTail hParts.2⟩)
      (fun _ => True.intro)
      (fun _ hBody h => hBody h)
      (fun _ _ hBody h => hBody h)
      block hCheck

namespace Program

def openSupported? (program : Functions.Program) : Bool :=
  program.functions.all (fun fn => block? fn.body) && block? program.body

theorem openSupported_of_check {program : Functions.Program}
    (hCheck : openSupported? program = true) :
    Functions.InteractionSemantics.Program.OpenSupported program := by
  have hParts := and_parts hCheck
  constructor
  · intro fn hMem
    exact
      block_of_check
        ((List.all_eq_true.mp hParts.1) fn hMem)
  · exact block_of_check hParts.2

end Program

end OpenSupportCheck
end Functions
end EvmCompiler
