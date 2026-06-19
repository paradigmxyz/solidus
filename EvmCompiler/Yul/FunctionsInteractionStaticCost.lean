import EvmCompiler.Yul.FunctionsInteractionFuel
import EvmCompiler.Yul.FunctionsInteractionCompilerCost
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

def expansionFunctionDefinition : AstFunctionDefinition → Nat
  | .Def _params _returns body =>
      FunctionsInteractionCompilerCost.stmtList body

def expansionFunctionList : List (Name × AstFunctionDefinition) → Nat
  | [] => 0
  | (_name, fn) :: tail =>
      Nat.max (expansionFunctionDefinition fn) (expansionFunctionList tail)

noncomputable def program (sourceProgram : Yul.Program) : Nat :=
  Nat.max
      (stmt sourceProgram.contract.dispatcher)
      (functionList (Contract.functionEntries sourceProgram.contract)) +
    Nat.max
      (FunctionsInteractionCompilerCost.stmt
        sourceProgram.contract.dispatcher)
      (expansionFunctionList
        (Contract.functionEntries sourceProgram.contract)) +
    8

noncomputable def bodyBudget
    (sourceProgram : Yul.Program) (body : List AstStmt)
    (sourceFuel : Nat) : Nat :=
  FunctionsInteractionFuel.executionBudgetFor
    (program sourceProgram)
      (stmtList body + FunctionsInteractionCompilerCost.stmtList body + 1)
      sourceFuel

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

/-- One source-fuel step in a body budget pays for the previous whole-program
budget plus the complete source-bounded recursive cost of its generated
Functions list. -/
theorem programBudget_add_compilerCost_lt_bodyBudget_step
    (sourceProgram : Yul.Program) (body : List AstStmt) (fuel : Nat) :
    programBudget sourceProgram fuel +
        FunctionsInteractionCompilerCost.stmtList body + 1 <
      bodyBudget sourceProgram body (fuel + 1) := by
  unfold programBudget bodyBudget FunctionsInteractionFuel.executionBudgetFor
  simp only [FunctionsInteractionFuel.targetBudgetFor]
  let p := (program sourceProgram + 1) *
    FunctionsInteractionFuel.targetBudgetFor (program sourceProgram) fuel
  let c := FunctionsInteractionCompilerCost.stmtList body
  let r := stmtList body
  change p + c + 1 < (r + c + 2) * (16 * (p + 1))
  have hp : p ≤ (c + 2) * p := by
    simpa using Nat.mul_le_mul_right p (show 1 ≤ c + 2 by omega)
  have hFactor : p + c + 2 ≤ (r + c + 2) * (p + 1) := by
    calc
      p + c + 2 ≤ (c + 2) * p + (c + 2) := by omega
      _ = (c + 2) * (p + 1) := by simp [Nat.mul_add]
      _ ≤ (r + c + 2) * (p + 1) :=
        Nat.mul_le_mul_right (p + 1) (by omega)
  have hScaled := Nat.mul_le_mul_left 16 hFactor
  calc
    p + c + 1 < 16 * (p + c + 2) := by omega
    _ ≤ 16 * ((r + c + 2) * (p + 1)) := hScaled
    _ = (r + c + 2) * (16 * (p + 1)) := by ac_rfl

/-- A source-bounded generated cost that fits the program ceiling is absorbed
by one whole-program source-fuel step. -/
theorem programBudget_add_cost_lt_step
    (sourceProgram : Yul.Program) {cost fuel : Nat}
    (hCost : cost ≤ program sourceProgram) :
    programBudget sourceProgram fuel + cost + 1 <
      programBudget sourceProgram (fuel + 1) := by
  unfold programBudget FunctionsInteractionFuel.executionBudgetFor
  simp only [FunctionsInteractionFuel.targetBudgetFor]
  let g := program sourceProgram
  let t := FunctionsInteractionFuel.targetBudgetFor g fuel
  let p := (g + 1) * t
  change p + cost + 1 < (g + 1) * (16 * (p + 1))
  have ht : 16 ≤ t :=
    FunctionsInteractionFuel.targetBudgetFor_ge_sixteen g fuel
  have hScaled := Nat.mul_le_mul_left (g + 1) ht
  have hg : g ≤ p := by
    change g ≤ (g + 1) * t
    omega
  have hSmall : p + cost + 1 < 16 * (p + 1) := by omega
  have hLarge : 16 * (p + 1) ≤ (g + 1) * (16 * (p + 1)) := by
    simpa using
      Nat.mul_le_mul_right (16 * (p + 1)) (show 1 ≤ g + 1 by omega)
  exact hSmall.trans_le hLarge

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

theorem expansionFunctionDefinition_le_expansionFunctionList_of_mem
    {name : Name} {fn : AstFunctionDefinition}
    {functions : List (Name × AstFunctionDefinition)}
    (hMem : (name, fn) ∈ functions) :
    expansionFunctionDefinition fn ≤ expansionFunctionList functions := by
  induction functions with
  | nil => simp at hMem
  | cons head tail ih =>
      rcases head with ⟨headName, headFn⟩
      simp only [List.mem_cons, Prod.mk.injEq] at hMem
      simp only [expansionFunctionList]
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
  have hRuntime := hList.trans hMax
  exact hRuntime.trans (by
    simpa [Nat.add_assoc] using
      (Nat.le_add_right
        (Nat.max
          (stmt sourceProgram.contract.dispatcher)
          (functionList (Contract.functionEntries sourceProgram.contract)))
        (Nat.max
          (FunctionsInteractionCompilerCost.stmt
            sourceProgram.contract.dispatcher)
          (expansionFunctionList
            (Contract.functionEntries sourceProgram.contract)) + 8)))

theorem dispatcher_le_program (sourceProgram : Yul.Program) :
    stmt sourceProgram.contract.dispatcher ≤ program sourceProgram := by
  unfold program
  have hRuntime := Nat.le_max_left
    (stmt sourceProgram.contract.dispatcher)
    (functionList (Contract.functionEntries sourceProgram.contract))
  exact hRuntime.trans (by
    simpa [Nat.add_assoc] using
      (Nat.le_add_right
        (Nat.max
          (stmt sourceProgram.contract.dispatcher)
          (functionList (Contract.functionEntries sourceProgram.contract)))
        (Nat.max
          (FunctionsInteractionCompilerCost.stmt
            sourceProgram.contract.dispatcher)
          (expansionFunctionList
            (Contract.functionEntries sourceProgram.contract)) + 8)))

theorem expansion_dispatcher_le_program (sourceProgram : Yul.Program) :
    FunctionsInteractionCompilerCost.stmt
        sourceProgram.contract.dispatcher ≤
      program sourceProgram := by
  unfold program
  have hCompiler := Nat.le_max_left
    (FunctionsInteractionCompilerCost.stmt
      sourceProgram.contract.dispatcher)
    (expansionFunctionList
      (Contract.functionEntries sourceProgram.contract))
  have hLeft := Nat.le_add_left
    (Nat.max
      (FunctionsInteractionCompilerCost.stmt
        sourceProgram.contract.dispatcher)
      (expansionFunctionList
        (Contract.functionEntries sourceProgram.contract)))
    (Nat.max
      (stmt sourceProgram.contract.dispatcher)
      (functionList (Contract.functionEntries sourceProgram.contract)))
  exact hCompiler.trans (hLeft.trans (Nat.le_add_right _ 8))

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
    Nat.max dispatcherCost functionCost +
      Nat.max
        (FunctionsInteractionCompilerCost.stmt
          sourceProgram.contract.dispatcher)
        (expansionFunctionList
          (Contract.functionEntries sourceProgram.contract)) + 8
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

theorem expansion_function_body_le_program_of_lookup
    {sourceProgram : Yul.Program}
    {name : Name}
    {params returns : List EvmYul.Identifier}
    {body : List AstStmt}
    (hLookup :
      sourceProgram.contract.functions.lookup name =
        some (.Def params returns body)) :
    FunctionsInteractionCompilerCost.stmtList body ≤
      program sourceProgram := by
  have hMem := Contract.functionEntries_mem_of_lookup hLookup
  have hList :=
    expansionFunctionDefinition_le_expansionFunctionList_of_mem hMem
  simp only [expansionFunctionDefinition] at hList
  unfold program
  have hCompiler := hList.trans (Nat.le_max_right
    (FunctionsInteractionCompilerCost.stmt
      sourceProgram.contract.dispatcher)
    (expansionFunctionList
      (Contract.functionEntries sourceProgram.contract)))
  exact hCompiler.trans (by
    have hLeft := Nat.le_add_left
      (Nat.max
        (FunctionsInteractionCompilerCost.stmt
          sourceProgram.contract.dispatcher)
        (expansionFunctionList
          (Contract.functionEntries sourceProgram.contract)))
      (Nat.max
        (stmt sourceProgram.contract.dispatcher)
        (functionList (Contract.functionEntries sourceProgram.contract)))
    exact hLeft.trans (Nat.le_add_right _ 8))

theorem function_body_budget_cost_le_program_of_lookup
    {sourceProgram : Yul.Program}
    {name : Name}
    {params returns : List EvmYul.Identifier}
    {body : List AstStmt}
    (hLookup :
      sourceProgram.contract.functions.lookup name =
        some (.Def params returns body)) :
    stmtList body + FunctionsInteractionCompilerCost.stmtList body + 1 ≤
      program sourceProgram := by
  have hRuntimeMem := Contract.functionEntries_mem_of_lookup hLookup
  have hRuntimeList := functionDefinition_le_functionList_of_mem hRuntimeMem
  have hCompilerList :=
    expansionFunctionDefinition_le_expansionFunctionList_of_mem hRuntimeMem
  simp only [functionDefinition] at hRuntimeList
  simp only [expansionFunctionDefinition] at hCompilerList
  unfold program
  have hRuntime := hRuntimeList.trans (Nat.le_max_right
    (stmt sourceProgram.contract.dispatcher)
    (functionList (Contract.functionEntries sourceProgram.contract)))
  have hCompiler := hCompilerList.trans (Nat.le_max_right
    (FunctionsInteractionCompilerCost.stmt
      sourceProgram.contract.dispatcher)
    (expansionFunctionList
      (Contract.functionEntries sourceProgram.contract)))
  have hRuntimeBody : stmtList body ≤
      Nat.max
        (stmt sourceProgram.contract.dispatcher)
        (functionList (Contract.functionEntries sourceProgram.contract)) := by
    have hBodyDefinition :
        stmtList body ≤
          params.length + returns.length + stmtList body + 4 := by
      omega
    exact hBodyDefinition.trans hRuntime
  have hSum := Nat.add_le_add hRuntimeBody hCompiler
  calc
    stmtList body + FunctionsInteractionCompilerCost.stmtList body + 1 ≤
        Nat.max
            (stmt sourceProgram.contract.dispatcher)
            (functionList (Contract.functionEntries sourceProgram.contract)) +
          Nat.max
            (FunctionsInteractionCompilerCost.stmt
              sourceProgram.contract.dispatcher)
            (expansionFunctionList
              (Contract.functionEntries sourceProgram.contract)) + 1 :=
      Nat.add_le_add_right hSum 1
    _ ≤
        Nat.max
            (stmt sourceProgram.contract.dispatcher)
            (functionList (Contract.functionEntries sourceProgram.contract)) +
          Nat.max
            (FunctionsInteractionCompilerCost.stmt
              sourceProgram.contract.dispatcher)
            (expansionFunctionList
              (Contract.functionEntries sourceProgram.contract)) + 8 := by
      omega

end FunctionsInteractionStaticCost
end Yul
end EvmCompiler
