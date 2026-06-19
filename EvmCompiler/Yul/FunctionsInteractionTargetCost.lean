import EvmCompiler.Functions.SourceSemantics

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionTargetCost

/-!
Private target meta-fuel accounting for the adjacent Yul-to-Functions proof.
Unlike the source-owned dynamic budget, this measure follows ordinary compiler
output recursively so nested lexical/branch/loop blocks are not hidden behind
one outer statement. It never appears at the public compiler boundary.
-/

mutual
  def stmt : Functions.Stmt → Nat
    | .expr _ | .let_ _ _ | .assign _ _ | .brk | .cont | .leave |
        .call _ _ _ | .terminal _ | .terminalArgs _ _ => 1
    | .block body => block body + 1
    | .if_ _ body => block body + 1
    | .switch _ cases defaultBody =>
        caseList cases + optionBlock defaultBody + 1
    | .for_ init _ post body =>
        block init + block post + block body + 1
  termination_by statement => sizeOf statement
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def block (body : Functions.Block) : Nat :=
    list body.stmts
  termination_by sizeOf body
  decreasing_by
    cases body
    simp_wf

  def list : List Functions.Stmt → Nat
    | [] => 0
    | head :: tail => stmt head + list tail + 1
  termination_by stmts => sizeOf stmts
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | exact list_sizeOf_lt_sizeOf_of_mem (by assumption)
      | omega

  def caseList : List (Functions.Word × Functions.Block) → Nat
    | [] => 0
    | (_, body) :: tail => block body + caseList tail + 1
  termination_by cases => sizeOf cases
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def optionBlock : Option Functions.Block → Nat
    | none => 0
    | some body => block body + 1
  termination_by body => sizeOf body
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

@[simp] theorem block_mk (stmts : List Functions.Stmt) :
    block { stmts := stmts } = list stmts := by
  simp [block]

theorem list_append (left right : List Functions.Stmt) :
    list (left ++ right) = list left + list right := by
  induction left with
  | nil => simp [list]
  | cons head tail ih =>
      simp [list, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem length_le_list (stmts : List Functions.Stmt) :
    stmts.length ≤ list stmts := by
  induction stmts with
  | nil => simp [list]
  | cons head tail ih =>
      simp only [List.length_cons, list]
      omega

theorem nested_block_lt_singleton (body : Functions.Block) :
    block body < list [.block body] := by
  simp [list, stmt]
  omega

theorem nested_if_lt_singleton
    (cond : Functions.Expr 1) (body : Functions.Block) :
    block body < list [.if_ cond body] := by
  simp [list, stmt]
  omega

/-- The recursively measured cost of the branch selected by the ordinary
Functions switch semantics is bounded by the cost already charged to the
whole switch table. -/
theorem block_le_switchBranches_of_select_eq_some
    {value : Functions.Word}
    {cases : List (Functions.Word × Functions.Block)}
    {defaultBody : Option Functions.Block}
    {body : Functions.Block}
    (hSelect :
      Functions.Source.Switch.select value cases defaultBody = some body) :
    block body ≤ caseList cases + optionBlock defaultBody := by
  induction cases generalizing body with
  | nil =>
      cases defaultBody with
      | none => simp [Functions.Source.Switch.select] at hSelect
      | some defaultBlock =>
          simp [Functions.Source.Switch.select] at hSelect
          subst body
          simp [caseList, optionBlock]
  | cons head tail ih =>
      rcases head with ⟨caseValue, caseBody⟩
      by_cases hMatch : caseValue = value
      · simp [Functions.Source.Switch.select, hMatch] at hSelect
        subst body
        simp [caseList]
        omega
      · have hTail :
            Functions.Source.Switch.select value tail defaultBody =
              some body := by
          simpa [Functions.Source.Switch.select, hMatch] using hSelect
        have hBound := ih hTail
        simp only [caseList]
        omega

end FunctionsInteractionTargetCost
end Yul
end EvmCompiler
