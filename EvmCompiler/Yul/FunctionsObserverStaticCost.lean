import EvmCompiler.Yul.FunctionsObserverFuel

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverStaticCost

/-!
Source-owned static expansion bounds for the Yul-to-Functions pass.

Source semantic fuel bounds dynamic recursion, but it does not bound the
number of Functions statements emitted by one Yul construct. These measures
conservatively account for that syntax-dependent expansion. They inspect only
the Yul AST and never accept a compiler artifact or replay witness.
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

def exprListBy (cost : AstExpr → Nat) : List AstExpr → Nat
  | [] => 0
  | head :: tail => cost head + exprListBy cost tail + 1

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

def calleeCost (sourceProgram : Yul.Program) (name : Name) : Nat :=
  match sourceProgram.contract.functions.lookup name with
  | none => 0
  | some fn => functionDefinition fn

mutual
  def runtimeExpr (sourceProgram : Yul.Program) : AstExpr → Nat
    | .Lit _ => 1
    | .Var _ => 1
    | .Call (.inl _) args =>
        runtimeExprList sourceProgram args + 2
    | .Call (.inr name) args =>
        runtimeExprList sourceProgram args +
          calleeCost sourceProgram name + 2

  def runtimeExprList
      (sourceProgram : Yul.Program) : List AstExpr → Nat
    | [] => 0
    | head :: tail =>
        runtimeExpr sourceProgram head +
          runtimeExprList sourceProgram tail + 1
end

mutual
  def runtimeStmt (sourceProgram : Yul.Program) : AstStmt → Nat
    | .Block body => runtimeStmtList sourceProgram body + 2
    | .Let names none => names.length + 1
    | .Let names (some value) =>
        names.length + runtimeExpr sourceProgram value + 4
    | .Assign names value =>
        names.length + runtimeExpr sourceProgram value + 4
    | .ExprStmtCall value =>
        runtimeExpr sourceProgram value + 2
    | .Switch scrutinee cases defaultBody =>
        runtimeExpr sourceProgram scrutinee +
          Nat.max
            (runtimeCaseList sourceProgram cases)
            (runtimeStmtList sourceProgram defaultBody) +
          4
    | .For cond post body =>
        runtimeExpr sourceProgram cond +
          Nat.max
            (runtimeStmtList sourceProgram post)
            (runtimeStmtList sourceProgram body) +
          6
    | .If cond body =>
        runtimeExpr sourceProgram cond +
          runtimeStmtList sourceProgram body + 4
    | .Continue | .Break | .Leave => 2

  def runtimeStmtList
      (sourceProgram : Yul.Program) : List AstStmt → Nat
    | [] => 1
    | head :: tail =>
        Nat.max
          (runtimeStmt sourceProgram head)
          (runtimeStmtList sourceProgram tail) +
        1

  def runtimeCaseList
      (sourceProgram : Yul.Program) :
      List (Word × List AstStmt) → Nat
    | [] => 1
    | (_value, body) :: tail =>
        Nat.max
          (runtimeStmtList sourceProgram body)
          (runtimeCaseList sourceProgram tail) +
        1
end

noncomputable def program (sourceProgram : Yul.Program) : Nat :=
  Nat.max
      (stmt sourceProgram.contract.dispatcher)
      (functionList
        (Contract.functionEntries sourceProgram.contract)) +
    8

noncomputable def programBudget
    (sourceProgram : Yul.Program) (sourceFuel : Nat) : Nat :=
  FunctionsObserverFuel.executionBudget
    (program sourceProgram) sourceFuel

theorem runtimeExprList_eq_exprListBy
    (sourceProgram : Yul.Program) (values : List AstExpr) :
    runtimeExprList sourceProgram values =
      exprListBy (runtimeExpr sourceProgram) values := by
  induction values with
  | nil =>
      rfl
  | cons head tail ih =>
      simp [runtimeExprList, exprListBy, ih]

theorem exprList_eq_exprListBy (values : List AstExpr) :
    exprList values = exprListBy expr values := by
  induction values with
  | nil =>
      rfl
  | cons head tail ih =>
      simp [exprList, exprListBy, ih]

theorem calleeCost_eq_functionDefinition_of_lookup
    {sourceProgram : Yul.Program}
    {name : Name} {fn : AstFunctionDefinition}
    (hLookup :
      sourceProgram.contract.functions.lookup name = some fn) :
    calleeCost sourceProgram name = functionDefinition fn := by
  simp [calleeCost, hLookup]

theorem function_body_le_calleeCost_of_lookup
    {sourceProgram : Yul.Program}
    {name : Name}
    {params returns : List EvmYul.Identifier}
    {body : List AstStmt}
    (hLookup :
      sourceProgram.contract.functions.lookup name =
        some (.Def params returns body)) :
    stmtList body ≤ calleeCost sourceProgram name := by
  rw [calleeCost_eq_functionDefinition_of_lookup hLookup]
  simp only [functionDefinition]
  omega

theorem expr_le_exprList_of_mem
    {candidate : AstExpr} {values : List AstExpr}
    (hMem : candidate ∈ values) :
    expr candidate ≤ exprList values := by
  induction values with
  | nil =>
      simp at hMem
  | cons head tail ih =>
      simp only [List.mem_cons] at hMem
      simp only [exprList]
      rcases hMem with rfl | hTail
      · omega
      · have hLe := ih hTail
        omega

theorem stmt_head_le_stmtList
    (head : AstStmt) (tail : List AstStmt) :
    stmt head ≤ stmtList (head :: tail) := by
  simp only [stmtList]
  have hMax := Nat.le_max_left (stmt head) (stmtList tail)
  exact hMax.trans (Nat.le_add_right _ 1)

theorem stmtList_tail_le_stmtList
    (head : AstStmt) (tail : List AstStmt) :
    stmtList tail ≤ stmtList (head :: tail) := by
  simp only [stmtList]
  have hMax := Nat.le_max_right (stmt head) (stmtList tail)
  exact hMax.trans (Nat.le_add_right _ 1)

theorem stmt_le_stmtList_of_mem
    {candidate : AstStmt} {stmts : List AstStmt}
    (hMem : candidate ∈ stmts) :
    stmt candidate ≤ stmtList stmts := by
  induction stmts with
  | nil =>
      simp at hMem
  | cons head tail ih =>
      rcases List.mem_cons.mp hMem with hHere | hTail
      · subst candidate
        exact stmt_head_le_stmtList head tail
      · exact
          (ih hTail).trans
            (stmtList_tail_le_stmtList head tail)

theorem case_body_le_caseList_of_mem
    {value : Word} {body : List AstStmt}
    {cases : List (Word × List AstStmt)}
    (hMem : (value, body) ∈ cases) :
    stmtList body ≤ caseList cases := by
  induction cases with
  | nil =>
      simp at hMem
  | cons head tail ih =>
      rcases head with ⟨headValue, headBody⟩
      simp only [List.mem_cons, Prod.mk.injEq] at hMem
      simp only [caseList]
      rcases hMem with hHere | hTail
      · rcases hHere with ⟨rfl, rfl⟩
        have hMax :=
          Nat.le_max_left (stmtList body) (caseList tail)
        exact hMax.trans (Nat.le_add_right _ 1)
      · have hLe := ih hTail
        have hMax :=
          Nat.le_max_right (stmtList headBody) (caseList tail)
        exact hLe.trans (hMax.trans (Nat.le_add_right _ 1))

theorem stmtList_selectSwitchCase_le_max
    (value : Word) (defaultBody : List AstStmt)
    (cases : List (Word × List AstStmt)) :
    stmtList
        (EvmYul.Yul.selectSwitchCase value defaultBody cases) ≤
      Nat.max (caseList cases) (stmtList defaultBody) := by
  induction cases with
  | nil =>
      simp [EvmYul.Yul.selectSwitchCase, caseList]
  | cons head tail ih =>
      rcases head with ⟨caseValue, body⟩
      simp only [EvmYul.Yul.selectSwitchCase, caseList]
      by_cases hMatch : caseValue = value
      · simp only [hMatch, ↓reduceIte]
        have hBody :
            stmtList body ≤
              Nat.max (stmtList body) (caseList tail) + 1 := by
          exact
            (Nat.le_max_left _ _).trans
              (Nat.le_add_right _ 1)
        exact hBody.trans (Nat.le_max_left _ _)
      · simp only [hMatch, ↓reduceIte]
        have hCases :
            caseList tail ≤
              Nat.max (stmtList body) (caseList tail) + 1 := by
          exact
            (Nat.le_max_right _ _).trans
              (Nat.le_add_right _ 1)
        have hOuter :
            Nat.max (caseList tail) (stmtList defaultBody) ≤
              Nat.max
                (Nat.max (stmtList body) (caseList tail) + 1)
                (stmtList defaultBody) := by
          exact
            Nat.max_le.mpr
              ⟨hCases.trans (Nat.le_max_left _ _),
                Nat.le_max_right _ _⟩
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

theorem dispatcher_le_program (sourceProgram : Yul.Program) :
    stmt sourceProgram.contract.dispatcher ≤ program sourceProgram := by
  unfold program
  have hMax :=
    Nat.le_max_left
      (stmt sourceProgram.contract.dispatcher)
      (functionList (Contract.functionEntries sourceProgram.contract))
  exact hMax.trans (Nat.le_add_right _ 8)

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
        Nat.max dispatcherCost functionCost + 1 := by
    exact
      Nat.max_le.mpr
        ⟨hDispatcher.trans (Nat.le_add_right _ 1), by omega⟩
  simp only [stmtList]
  unfold program
  change Nat.max dispatcherCost 1 + 1 ≤
    Nat.max dispatcherCost functionCost + 8
  omega

theorem function_le_program_of_lookup
    {sourceProgram : Yul.Program}
    {name : Name} {fn : AstFunctionDefinition}
    (hLookup :
      sourceProgram.contract.functions.lookup name = some fn) :
    functionDefinition fn ≤ program sourceProgram := by
  have hMem :=
    Contract.functionEntries_mem_of_lookup hLookup
  have hList :=
    functionDefinition_le_functionList_of_mem hMem
  unfold program
  have hMax :=
    Nat.le_max_right
      (stmt sourceProgram.contract.dispatcher)
      (functionList (Contract.functionEntries sourceProgram.contract))
  exact hList.trans (hMax.trans (Nat.le_add_right _ 8))

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

end FunctionsObserverStaticCost
end Yul
end EvmCompiler
