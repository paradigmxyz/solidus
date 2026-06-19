import EvmCompiler.Yul.FunctionsInteractionFuel
import EvmYul.Yul.Interpreter

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionStaticCost

/-!
Source-owned static expansion bounds for the adjacent Yul-to-Functions pass.
These measures inspect only Yul syntax and never accept generated code or a
compiler certificate.
-/

mutual
  def expr : AstExpr → Nat
    | .Lit _ => 1
    | .Var _ => 1
    | .Call _ args => exprList args + 2

  def exprList : List AstExpr → Nat
    | [] => 0
    | head :: tail => expr head + exprList tail + 1
end

mutual
  def stmt : AstStmt → Nat
    | .Block body => stmtList body + 2
    | .Let names none => names.length + 1
    | .Let names (some value) => names.length + expr value + 4
    | .Assign names value => names.length + expr value + 4
    | .ExprStmtCall value => expr value + 2
    | .Switch scrutinee cases defaultBody =>
        expr scrutinee + Nat.max (caseList cases) (stmtList defaultBody) + 4
    | .For cond post body =>
        expr cond + Nat.max (stmtList post) (stmtList body) + 6
    | .If cond body => expr cond + stmtList body + 4
    | .Continue | .Break | .Leave => 2

  def stmtList : List AstStmt → Nat
    | [] => 1
    | head :: tail => Nat.max (stmt head) (stmtList tail) + 1

  def caseList : List (Word × List AstStmt) → Nat
    | [] => 1
    | (_value, body) :: tail =>
        Nat.max (stmtList body) (caseList tail) + 1
end

def functionDefinition : AstFunctionDefinition → Nat
  | .Def params returns body =>
      params.length + returns.length + stmtList body + 4

def functionList : List (Name × AstFunctionDefinition) → Nat
  | [] => 0
  | (_name, fn) :: tail =>
      Nat.max (functionDefinition fn) (functionList tail)

noncomputable def program (sourceProgram : Yul.Program) : Nat :=
  Nat.max
      (stmt sourceProgram.contract.dispatcher)
      (functionList (Contract.functionEntries sourceProgram.contract)) +
    8

noncomputable def bodyBudget
    (sourceProgram : Yul.Program) (body : List AstStmt)
    (sourceFuel : Nat) : Nat :=
  FunctionsInteractionFuel.executionBudgetFor
    (program sourceProgram) (stmtList body) sourceFuel

noncomputable def programBudget
    (sourceProgram : Yul.Program) (sourceFuel : Nat) : Nat :=
  FunctionsInteractionFuel.executionBudgetFor
    (program sourceProgram) (program sourceProgram) sourceFuel

theorem programBudget_child_add_eight_le
    (sourceProgram : Yul.Program) {childFuel parentFuel : Nat}
    (hFuel : childFuel < parentFuel) :
    programBudget sourceProgram childFuel + 8 ≤
      programBudget sourceProgram parentFuel := by
  unfold programBudget
  exact
    (FunctionsInteractionFuel.executionBudgetFor_add_eight_le_target_of_lt
      (program sourceProgram) (program sourceProgram) (by rfl) hFuel).trans
      (FunctionsInteractionFuel.targetBudgetFor_le_executionBudgetFor
        (program sourceProgram) (program sourceProgram) parentFuel)

theorem stmt_head_le_stmtList
    (head : AstStmt) (tail : List AstStmt) :
    stmt head ≤ stmtList (head :: tail) := by
  simp only [stmtList]
  exact (Nat.le_max_left _ _).trans (Nat.le_add_right _ 1)

theorem stmtList_tail_le_stmtList
    (head : AstStmt) (tail : List AstStmt) :
    stmtList tail ≤ stmtList (head :: tail) := by
  simp only [stmtList]
  exact (Nat.le_max_right _ _).trans (Nat.le_add_right _ 1)

theorem stmt_le_stmtList_of_mem
    {candidate : AstStmt} {stmts : List AstStmt}
    (hMem : candidate ∈ stmts) :
    stmt candidate ≤ stmtList stmts := by
  induction stmts with
  | nil => simp at hMem
  | cons head tail ih =>
      rcases List.mem_cons.mp hMem with hHere | hTail
      · subst candidate
        exact stmt_head_le_stmtList head tail
      · exact (ih hTail).trans (stmtList_tail_le_stmtList head tail)

theorem case_body_le_caseList_of_mem
    {value : Word} {body : List AstStmt}
    {cases : List (Word × List AstStmt)}
    (hMem : (value, body) ∈ cases) :
    stmtList body ≤ caseList cases := by
  induction cases with
  | nil => simp at hMem
  | cons head tail ih =>
      rcases head with ⟨headValue, headBody⟩
      simp only [List.mem_cons, Prod.mk.injEq] at hMem
      simp only [caseList]
      rcases hMem with hHere | hTail
      · rcases hHere with ⟨rfl, rfl⟩
        exact
          (Nat.le_max_left (stmtList body) (caseList tail)).trans
            (Nat.le_add_right _ 1)
      · exact
          (ih hTail).trans
            ((Nat.le_max_right (stmtList headBody) (caseList tail)).trans
              (Nat.le_add_right _ 1))

theorem stmtList_selectSwitchCase_le_max
    (value : Word) (defaultBody : List AstStmt)
    (cases : List (Word × List AstStmt)) :
    stmtList (EvmYul.Yul.selectSwitchCase value defaultBody cases) ≤
      Nat.max (caseList cases) (stmtList defaultBody) := by
  induction cases with
  | nil => simp [EvmYul.Yul.selectSwitchCase, caseList]
  | cons head tail ih =>
      rcases head with ⟨caseValue, body⟩
      simp only [EvmYul.Yul.selectSwitchCase, caseList]
      by_cases hMatch : caseValue = value
      · simp only [hMatch, ↓reduceIte]
        exact
          ((Nat.le_max_left (stmtList body) (caseList tail)).trans
            (Nat.le_add_right _ 1)).trans (Nat.le_max_left _ _)
      · simp only [hMatch, ↓reduceIte]
        have hCases :
            caseList tail ≤ Nat.max (stmtList body) (caseList tail) + 1 :=
          (Nat.le_max_right _ _).trans (Nat.le_add_right _ 1)
        have hOuter :
            Nat.max (caseList tail) (stmtList defaultBody) ≤
              Nat.max
                (Nat.max (stmtList body) (caseList tail) + 1)
                (stmtList defaultBody) :=
          Nat.max_le.mpr
            ⟨hCases.trans (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
        exact ih.trans hOuter

theorem functionDefinition_le_functionList_of_mem
    {name : Name} {fn : AstFunctionDefinition}
    {functions : List (Name × AstFunctionDefinition)}
    (hMem : (name, fn) ∈ functions) :
    functionDefinition fn ≤ functionList functions := by
  induction functions with
  | nil =>
      simp at hMem
  | cons head tail ih =>
      rcases head with ⟨headName, headFn⟩
      simp only [List.mem_cons, Prod.mk.injEq] at hMem
      simp only [functionList]
      rcases hMem with hHere | hTail
      · rcases hHere with ⟨rfl, rfl⟩
        exact Nat.le_max_left _ _
      · exact (ih hTail).trans (Nat.le_max_right _ _)

theorem function_le_program_of_lookup
    {sourceProgram : Yul.Program}
    {name : Name} {fn : AstFunctionDefinition}
    (hLookup :
      sourceProgram.contract.functions.lookup name = some fn) :
    functionDefinition fn ≤ program sourceProgram := by
  have hMem := Contract.functionEntries_mem_of_lookup hLookup
  have hList := functionDefinition_le_functionList_of_mem hMem
  unfold program
  have hMax :=
    Nat.le_max_right
      (stmt sourceProgram.contract.dispatcher)
      (functionList (Contract.functionEntries sourceProgram.contract))
  exact hList.trans (hMax.trans (Nat.le_add_right _ 8))

theorem dispatcher_le_program (sourceProgram : Yul.Program) :
    stmt sourceProgram.contract.dispatcher ≤ program sourceProgram := by
  unfold program
  exact
    (Nat.le_max_left _ _).trans (Nat.le_add_right _ 8)

theorem dispatcherList_le_program (sourceProgram : Yul.Program) :
    stmtList [sourceProgram.contract.dispatcher] ≤
      program sourceProgram := by
  let dispatcherCost := stmt sourceProgram.contract.dispatcher
  let functionCost :=
    functionList (Contract.functionEntries sourceProgram.contract)
  have hDispatcher :
      dispatcherCost ≤ Nat.max dispatcherCost functionCost :=
    Nat.le_max_left _ _
  have hMax :
      Nat.max dispatcherCost 1 ≤
        Nat.max dispatcherCost functionCost + 1 :=
    Nat.max_le.mpr
      ⟨hDispatcher.trans (Nat.le_add_right _ 1), by omega⟩
  simp only [stmtList]
  unfold program
  change Nat.max dispatcherCost 1 + 1 ≤
    Nat.max dispatcherCost functionCost + 8
  omega

theorem function_body_le_program_of_lookup
    {sourceProgram : Yul.Program}
    {name : Name}
    {params returns : List EvmYul.Identifier}
    {body : List AstStmt}
    (hLookup :
      sourceProgram.contract.functions.lookup name =
        some (.Def params returns body)) :
    stmtList body ≤ program sourceProgram := by
  have hFunction :=
    function_le_program_of_lookup
      (sourceProgram := sourceProgram) hLookup
  simp only [functionDefinition] at hFunction
  omega

end FunctionsInteractionStaticCost
end Yul
end EvmCompiler
