import EvmCompiler.Functions.Compiler
import EvmCompiler.Locals.Allocation
import EvmCompiler.Expressions.Compiler

/-!
Source-derived allocation recipes and frame-code primitives shared by
allocation planners and lowerers.

This module deliberately contains no standalone compiler backend. It records
lexical allocation state without emitting code, then exposes only the small
set of Structured fragments needed by the canonical mixed-location lowerer.
-/

namespace EvmCompiler
namespace Functions
namespace AllocationSupport

abbrev SlotEnv := List (Name × Nat)

structure FunSlots where
  name : Name
  params : List (Name × Nat)
  returns : List (Name × Nat)
  deriving DecidableEq, Repr

structure CompileState where
  env : SlotEnv
  nextSlot : Nat
  deriving DecidableEq, Repr

def word (n : Nat) : Word :=
  EvmYul.UInt256.ofNat n

def slotOffset (slot : Nat) : Word :=
  word (32 * slot)

def frameBytes (words : Nat) : Word :=
  word (32 * words)

def zeroWord : Word :=
  word 0

structure ScratchFrameConfig where
  allocatorCell : Nat
  firstFrame : Nat
  limit : Nat
  frameWords : Nat
  deriving DecidableEq, Repr

def scratchFrameConfig?
    (contract : MemoryContract.Contract)
    (frameWords : Nat) : Option ScratchFrameConfig := do
  let reservation ← contract.scratch?
  if reservation.WellFormed ∧
      reservation.HostAddressable ∧
      0 < reservation.words ∧
      frameWords ≤ reservation.usableWords then
    some
      { allocatorCell := reservation.allocatorCell
        firstFrame := reservation.frameBase
        limit := reservation.endExclusive
        frameWords := frameWords }
  else
    none

theorem scratchFrameConfig?_sound
    {contract : MemoryContract.Contract} {frameWords : Nat}
    {config : ScratchFrameConfig}
    (hConfig :
      scratchFrameConfig? contract frameWords = some config) :
    ∃ reservation,
      contract.scratch? = some reservation ∧
      config.allocatorCell = reservation.allocatorCell ∧
      config.firstFrame = reservation.frameBase ∧
      config.limit = reservation.endExclusive ∧
      config.frameWords = frameWords ∧
      reservation.WellFormed ∧
      reservation.HostAddressable ∧
      0 < reservation.words ∧
      frameWords ≤ reservation.usableWords := by
  unfold scratchFrameConfig? at hConfig
  cases hReservation : contract.scratch? with
  | none =>
      simp [hReservation] at hConfig
  | some reservation =>
      by_cases hWF : reservation.WellFormed
      · by_cases hPositive : 0 < reservation.words
        · by_cases hHost : reservation.HostAddressable
          · by_cases hFits : frameWords ≤ reservation.usableWords
            · simp [hReservation, hWF, hHost, hPositive, hFits] at hConfig
              subst config
              exact
                ⟨reservation, rfl, rfl, rfl, rfl, rfl,
                  hWF, hHost, hPositive, hFits⟩
            · simp [hReservation, hWF, hHost, hPositive, hFits] at hConfig
          · simp [hReservation, hWF, hHost] at hConfig
        · simp [hReservation, hWF, hPositive] at hConfig
      · simp [hReservation, hWF] at hConfig

def lookupSlot? (name : Name) : SlotEnv → Option Nat
  | [] => none
  | (candidate, slot) :: rest =>
      if candidate = name then some slot else lookupSlot? name rest

theorem mem_of_lookupSlot?_eq_some
    {env : SlotEnv} {name : Name} {slot : Nat}
    (hLookup : lookupSlot? name env = some slot) :
    (name, slot) ∈ env := by
  induction env with
  | nil =>
      simp [lookupSlot?] at hLookup
  | cons binding rest ih =>
      rcases binding with ⟨candidate, candidateSlot⟩
      by_cases hName : candidate = name
      · simp [lookupSlot?, hName] at hLookup
        subst candidate
        subst candidateSlot
        simp
      · have hTail :
            lookupSlot? name rest = some slot := by
          simpa [lookupSlot?, hName] using hLookup
        exact List.mem_cons_of_mem _ (ih hTail)

theorem lookupSlot?_eq_some_of_mem
    {env : SlotEnv} {name : Name} {slot : Nat}
    (hNodup : (env.map Prod.fst).Nodup)
    (hMem : (name, slot) ∈ env) :
    lookupSlot? name env = some slot := by
  induction env with
  | nil =>
      simp at hMem
  | cons binding rest ih =>
      rcases binding with ⟨candidate, candidateSlot⟩
      have hParts := List.nodup_cons.mp hNodup
      rcases List.mem_cons.mp hMem with hHead | hTail
      · cases hHead
        simp [lookupSlot?]
      · have hNe : candidate ≠ name := by
          intro hEq
          subst candidate
          exact hParts.1 (List.mem_map.mpr ⟨(name, slot), hTail, rfl⟩)
        simp [lookupSlot?, hNe, ih hParts.2 hTail]

def lookupFun? (name : Name) : List FunSlots → Option FunSlots
  | [] => none
  | fn :: rest => if fn.name = name then some fn else lookupFun? name rest

theorem lookupFun?_eq_some_facts
    {name : Name} {functions : List FunSlots} {slots : FunSlots}
    (hLookup : lookupFun? name functions = some slots) :
    slots ∈ functions ∧ slots.name = name := by
  induction functions with
  | nil =>
      simp [lookupFun?] at hLookup
  | cons head tail ih =>
      by_cases hName : head.name = name
      · simp [lookupFun?, hName] at hLookup
        subst slots
        exact ⟨by simp, hName⟩
      · have hTail :
          lookupFun? name tail = some slots := by
          simpa [lookupFun?, hName] using hLookup
        obtain ⟨hMem, hSlotsName⟩ := ih hTail
        exact ⟨by simp [hMem], hSlotsName⟩

def functionEnv (slots : FunSlots) : SlotEnv :=
  slots.returns ++ slots.params

def allocateName (name : Name) (state : CompileState) :
    Nat × CompileState :=
  (state.nextSlot,
    { env := (name, state.nextSlot) :: state.env
      nextSlot := state.nextSlot + 1 })

def allocateNames : List Name → CompileState →
    List (Name × Nat) × CompileState
  | [], state => ([], state)
  | name :: rest, state =>
      let (slot, state) := allocateName name state
      let (tail, state) := allocateNames rest state
      ((name, slot) :: tail, state)

def allocateFunctionSignatures : List FunDef → CompileState →
    List FunSlots × CompileState
  | [], state => ([], state)
  | fn :: rest, state =>
      let (params, state) := allocateNames fn.params state
      let (returns, state) := allocateNames fn.returns state
      let slots : FunSlots :=
        { name := fn.name, params := params, returns := returns }
      let (tail, state) := allocateFunctionSignatures rest state
      (slots :: tail, state)

namespace FunSlots

def Matches (slots : FunSlots) (fn : FunDef) : Prop :=
  slots.name = fn.name ∧
    slots.params.map Prod.fst = fn.params ∧
    slots.returns.map Prod.fst = fn.returns

end FunSlots

theorem allocateNames_names
    (names : List Name) (state : CompileState) :
    (allocateNames names state).1.map Prod.fst = names := by
  induction names generalizing state with
  | nil =>
      rfl
  | cons name rest ih =>
      simp [allocateNames, allocateName, ih]

theorem allocateFunctionSignatures_matches
    (functions : List FunDef) (state : CompileState) :
    List.Forall₂ (fun fn slots => slots.Matches fn) functions
      (allocateFunctionSignatures functions state).1 := by
  induction functions generalizing state with
  | nil =>
      exact .nil
  | cons fn rest ih =>
      let paramsResult := allocateNames fn.params state
      let params := paramsResult.1
      let afterParams := paramsResult.2
      let returnsResult := allocateNames fn.returns afterParams
      let returns := returnsResult.1
      let afterReturns := returnsResult.2
      let tailResult := allocateFunctionSignatures rest afterReturns
      change
        List.Forall₂ (fun fn slots => slots.Matches fn) (fn :: rest)
          ({ name := fn.name, params := params, returns := returns } ::
            tailResult.1)
      apply List.Forall₂.cons
      · exact
          ⟨rfl,
            by simpa [params, paramsResult] using
              allocateNames_names fn.params state,
            by simpa [returns, returnsResult, afterParams, paramsResult] using
              allocateNames_names fn.returns afterParams⟩
      · exact ih afterReturns

theorem lookupFun?_of_matches
    {functions : List FunDef} {slots : List FunSlots}
    {fn : FunDef}
    (hMatch :
      List.Forall₂ (fun fn slots => slots.Matches fn) functions slots)
    (hNames : (functions.map FunDef.name).Nodup)
    (hMem : fn ∈ functions) :
    ∃ fnSlots,
      lookupFun? fn.name slots = some fnSlots ∧
        fnSlots.Matches fn := by
  induction hMatch with
  | nil =>
      simp at hMem
  | @cons head headSlots functions slots hHead hTail ih =>
      have hHeadName : headSlots.name = head.name := hHead.1
      have hHeadFresh :
          head.name ∉ functions.map FunDef.name :=
        (List.nodup_cons.mp hNames).1
      have hTailNames :
          (functions.map FunDef.name).Nodup :=
        (List.nodup_cons.mp hNames).2
      rcases List.mem_cons.mp hMem with hEq | hTailMem
      · subst fn
        exact
          ⟨headSlots,
            by simp [lookupFun?, hHeadName],
            hHead⟩
      · have hNe : head.name ≠ fn.name := by
          intro hName
          apply hHeadFresh
          rw [hName]
          exact List.mem_map.mpr ⟨fn, hTailMem, rfl⟩
        obtain ⟨fnSlots, hLookup, hSlots⟩ :=
          ih hTailNames hTailMem
        exact
          ⟨fnSlots,
            by simp [lookupFun?, hHeadName, hNe, hLookup],
            hSlots⟩

/-- Reverse a slot lookup through the positional source/signature match. -/
theorem find?_of_lookupFun?_matches
    {functions : List FunDef} {slots : List FunSlots}
    {name : Name} {fnSlots : FunSlots}
    (hMatch :
      List.Forall₂ (fun fn slots => slots.Matches fn) functions slots)
    (hLookup : lookupFun? name slots = some fnSlots) :
    ∃ fn,
      Functions.Source.FunList.find? name functions = some fn ∧
        fnSlots.Matches fn := by
  induction hMatch with
  | nil =>
      simp [lookupFun?] at hLookup
  | @cons head headSlots functions slots hHead hTail ih =>
      by_cases hHeadName : headSlots.name = name
      · simp [lookupFun?, hHeadName] at hLookup
        subst fnSlots
        have hSourceName : head.name = name := by
          rw [← hHead.1]
          exact hHeadName
        exact
          ⟨head, by simp [Functions.Source.FunList.find?, hSourceName], hHead⟩
      · have hSourceNe : head.name ≠ name := by
          intro hEq
          apply hHeadName
          rw [hHead.1, hEq]
        have hTailLookup : lookupFun? name slots = some fnSlots := by
          simpa [lookupFun?, hHeadName] using hLookup
        obtain ⟨fn, hFind, hSlots⟩ := ih hTailLookup
        exact
          ⟨fn, by
            simpa [Functions.Source.FunList.find?, hSourceNe] using hFind,
            hSlots⟩

structure ScopedAllocation where
  scope : Locals.Allocation.ScopeId
  state : CompileState
  deriving DecidableEq, Repr

structure PlanningState where
  allocation : CompileState
  nextScope : Nat
  scopes : List ScopedAllocation
  deriving DecidableEq, Repr

mutual
  def planBlockOpen (current : Locals.Allocation.ScopeId)
      (state : PlanningState) (block : Block) : PlanningState :=
    match block with
    | ⟨stmts⟩ => planStmtList current state stmts

  def planBlockScoped (parent : Locals.Allocation.ScopeId)
      (state : PlanningState) (block : Block) : PlanningState :=
    let scope := Locals.Allocation.ScopeId.lexical parent state.nextScope
    let entered := { state with nextScope := state.nextScope + 1 }
    let planned := planBlockOpen scope entered block
    { allocation :=
        { env := state.allocation.env
          nextSlot := planned.allocation.nextSlot }
      nextScope := planned.nextScope
      scopes := { scope := scope, state := planned.allocation } :: planned.scopes }

  def planStmtList (current : Locals.Allocation.ScopeId) :
      PlanningState → List Stmt → PlanningState
    | state, [] => state
    | state, stmt :: rest =>
        planStmtList current (planStmt current state stmt) rest

  def planCases (current : Locals.Allocation.ScopeId) :
      PlanningState → List (Word × Block) → PlanningState
    | state, [] => state
    | state, (_, body) :: rest =>
        planCases current (planBlockScoped current state body) rest

  def planDefault (current : Locals.Allocation.ScopeId)
      (state : PlanningState) : Option Block → PlanningState
    | none => state
    | some body => planBlockScoped current state body

  def planStmt (current : Locals.Allocation.ScopeId)
      (state : PlanningState) : Stmt → PlanningState
    | .let_ name _ =>
        { state with allocation := (allocateName name state.allocation).2 }
    | .block body =>
        planBlockScoped current state body
    | .if_ _ body =>
        planBlockScoped current state body
    | .switch _ cases defaultBody =>
        planDefault current (planCases current state cases) defaultBody
    | .for_ init _ post body =>
        let loopScope :=
          Locals.Allocation.ScopeId.lexical current state.nextScope
        let entered := { state with nextScope := state.nextScope + 1 }
        let initState := planBlockOpen loopScope entered init
        let postState := planBlockScoped loopScope initState post
        let bodyState := planBlockScoped loopScope postState body
        { allocation :=
            { env := state.allocation.env
              nextSlot := bodyState.allocation.nextSlot }
          nextScope := bodyState.nextScope
          scopes :=
            { scope := loopScope, state := bodyState.allocation } ::
              bodyState.scopes }
    | _ => state
end

theorem planStmtList_append
    (current : Locals.Allocation.ScopeId)
    (state : PlanningState)
    (left right : List Stmt) :
    planStmtList current state (left ++ right) =
      planStmtList current (planStmtList current state left) right := by
  induction left generalizing state with
  | nil => simp [planStmtList]
  | cons stmt rest ih =>
      simp only [List.cons_append, planStmtList]
      exact ih (planStmt current state stmt)

mutual

private def planningBlockSize : Block → Nat
  | ⟨stmts⟩ => planningStmtListSize stmts + 1

private def planningStmtListSize : List Stmt → Nat
  | [] => 0
  | stmt :: rest =>
      planningStmtSize stmt + planningStmtListSize rest + 1

private def planningCasesSize : List (Word × Block) → Nat
  | [] => 0
  | (_, body) :: rest =>
      planningBlockSize body + planningCasesSize rest + 1

private def planningDefaultSize : Option Block → Nat
  | none => 0
  | some body => planningBlockSize body + 1

private def planningStmtSize : Stmt → Nat
  | .block body => planningBlockSize body + 1
  | .if_ _ body => planningBlockSize body + 1
  | .switch _ cases defaultBody =>
      planningCasesSize cases + planningDefaultSize defaultBody + 1
  | .for_ init _ post body =>
      planningBlockSize init + planningBlockSize post +
        planningBlockSize body + 1
  | _ => 0

end

mutual

theorem planBlockOpen_scopes_extension
    (block : Block) (current : Locals.Allocation.ScopeId)
    (state : PlanningState) :
    ∃ added,
      (planBlockOpen current state block).scopes =
        added ++ state.scopes := by
  rcases block with ⟨stmts⟩
  simpa [planBlockOpen] using
    planStmtList_scopes_extension stmts current state
termination_by (planningBlockSize block, 0)
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp [planningBlockSize]
  all_goals omega

theorem planBlockScoped_scopes_extension
    (block : Block) (parent : Locals.Allocation.ScopeId)
    (state : PlanningState) :
    ∃ added,
      (planBlockScoped parent state block).scopes =
        added ++ state.scopes := by
  let scope :=
    Locals.Allocation.ScopeId.lexical parent state.nextScope
  let entered := { state with nextScope := state.nextScope + 1 }
  obtain ⟨added, hAdded⟩ :=
    planBlockOpen_scopes_extension block scope entered
  refine
    ⟨{ scope := scope
       state := (planBlockOpen scope entered block).allocation } :: added,
      ?_⟩
  simp only [planBlockScoped]
  rw [hAdded]
  rfl
termination_by (planningBlockSize block, 1)
decreasing_by
  exact Prod.Lex.right _ (by omega)

theorem planStmtList_scopes_extension
    (stmts : List Stmt) (current : Locals.Allocation.ScopeId)
    (state : PlanningState) :
    ∃ added,
      (planStmtList current state stmts).scopes =
        added ++ state.scopes := by
  cases stmts with
  | nil =>
      exact ⟨[], by simp [planStmtList]⟩
  | cons stmt rest =>
      obtain ⟨headAdded, hHead⟩ :=
        planStmt_scopes_extension stmt current state
      obtain ⟨tailAdded, hTail⟩ :=
        planStmtList_scopes_extension rest current
          (planStmt current state stmt)
      refine ⟨tailAdded ++ headAdded, ?_⟩
      simp only [planStmtList]
      rw [hTail, hHead, List.append_assoc]
termination_by (planningStmtListSize stmts, 0)
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp [planningStmtListSize]
  all_goals omega

theorem planCases_scopes_extension
    (cases : List (Word × Block))
    (current : Locals.Allocation.ScopeId)
    (state : PlanningState) :
    ∃ added,
      (planCases current state cases).scopes =
        added ++ state.scopes := by
  cases cases with
  | nil =>
      exact ⟨[], by simp [planCases]⟩
  | cons head rest =>
      rcases head with ⟨value, body⟩
      obtain ⟨headAdded, hHead⟩ :=
        planBlockScoped_scopes_extension body current state
      obtain ⟨tailAdded, hTail⟩ :=
        planCases_scopes_extension rest current
          (planBlockScoped current state body)
      refine ⟨tailAdded ++ headAdded, ?_⟩
      simp only [planCases]
      rw [hTail, hHead, List.append_assoc]
termination_by (planningCasesSize cases, 0)
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp [planningCasesSize]
  all_goals omega

theorem planDefault_scopes_extension
    (body : Option Block) (current : Locals.Allocation.ScopeId)
    (state : PlanningState) :
    ∃ added,
      (planDefault current state body).scopes =
        added ++ state.scopes := by
  cases body with
  | none =>
      exact ⟨[], by simp [planDefault]⟩
  | some body =>
      simpa [planDefault] using
        planBlockScoped_scopes_extension body current state
termination_by (planningDefaultSize body, 0)
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp [planningDefaultSize]
  all_goals omega

theorem planStmt_scopes_extension
    (stmt : Stmt) (current : Locals.Allocation.ScopeId)
    (state : PlanningState) :
    ∃ added,
      (planStmt current state stmt).scopes =
        added ++ state.scopes := by
  cases stmt with
  | expr _ | let_ _ _ | assign _ _ | brk | cont | leave | call _ _ _
  | terminal _ | terminalArgs _ _ =>
      exact ⟨[], by simp [planStmt]⟩
  | block body =>
      simpa [planStmt] using
        planBlockScoped_scopes_extension body current state
  | if_ _ body =>
      simpa [planStmt] using
        planBlockScoped_scopes_extension body current state
  | switch _ cases defaultBody =>
      obtain ⟨caseAdded, hCases⟩ :=
        planCases_scopes_extension cases current state
      obtain ⟨defaultAdded, hDefault⟩ :=
        planDefault_scopes_extension defaultBody current
          (planCases current state cases)
      refine ⟨defaultAdded ++ caseAdded, ?_⟩
      simp only [planStmt]
      rw [hDefault, hCases, List.append_assoc]
  | for_ init _ post body =>
      let loopScope :=
        Locals.Allocation.ScopeId.lexical current state.nextScope
      let entered := { state with nextScope := state.nextScope + 1 }
      let initState := planBlockOpen loopScope entered init
      let postState := planBlockScoped loopScope initState post
      let bodyState := planBlockScoped loopScope postState body
      obtain ⟨initAdded, hInit⟩ :=
        planBlockOpen_scopes_extension init loopScope entered
      obtain ⟨postAdded, hPost⟩ :=
        planBlockScoped_scopes_extension post loopScope initState
      obtain ⟨bodyAdded, hBody⟩ :=
        planBlockScoped_scopes_extension body loopScope postState
      refine
        ⟨{ scope := loopScope, state := bodyState.allocation } ::
            (bodyAdded ++ postAdded ++ initAdded),
          ?_⟩
      simp only [planStmt]
      rw [hBody, hPost, hInit]
      simp [loopScope, entered, initState, postState, bodyState,
        List.append_assoc]
termination_by (planningStmtSize stmt, 0)
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp [planningStmtSize, planningBlockSize,
    planningStmtListSize, planningCasesSize, planningDefaultSize]
  all_goals omega

end

theorem mem_planStmtList_scopes_of_mem
    {entry : ScopedAllocation}
    (stmts : List Stmt) (current : Locals.Allocation.ScopeId)
    (state : PlanningState)
    (hEntry : entry ∈ state.scopes) :
    entry ∈ (planStmtList current state stmts).scopes := by
  obtain ⟨added, hScopes⟩ :=
    planStmtList_scopes_extension stmts current state
  rw [hScopes]
  exact List.mem_append_right _ hEntry

theorem mem_planCases_scopes_of_mem
    {entry : ScopedAllocation}
    (cases : List (Word × Block))
    (current : Locals.Allocation.ScopeId)
    (state : PlanningState)
    (hEntry : entry ∈ state.scopes) :
    entry ∈ (planCases current state cases).scopes := by
  obtain ⟨added, hScopes⟩ :=
    planCases_scopes_extension cases current state
  rw [hScopes]
  exact List.mem_append_right _ hEntry

theorem mem_planDefault_scopes_of_mem
    {entry : ScopedAllocation}
    (body : Option Block)
    (current : Locals.Allocation.ScopeId)
    (state : PlanningState)
    (hEntry : entry ∈ state.scopes) :
    entry ∈ (planDefault current state body).scopes := by
  obtain ⟨added, hScopes⟩ :=
    planDefault_scopes_extension body current state
  rw [hScopes]
  exact List.mem_append_right _ hEntry

theorem planBlockScoped_entry_mem
    (block : Block) (parent : Locals.Allocation.ScopeId)
    (state : PlanningState) :
    { scope := .lexical parent state.nextScope
      state :=
        (planBlockOpen (.lexical parent state.nextScope)
          { state with nextScope := state.nextScope + 1 }
          block).allocation } ∈
      (planBlockScoped parent state block).scopes := by
  simp [planBlockScoped]

theorem mem_planBlockScoped_scopes_of_open_mem
    {entry : ScopedAllocation}
    (block : Block) (parent : Locals.Allocation.ScopeId)
    (state : PlanningState)
    (hEntry :
      entry ∈
        (planBlockOpen (.lexical parent state.nextScope)
          { state with nextScope := state.nextScope + 1 }
          block).scopes) :
    entry ∈ (planBlockScoped parent state block).scopes := by
  simp only [planBlockScoped, List.mem_cons]
  exact Or.inr hEntry

private theorem planBlockScoped_env
    (parent : Locals.Allocation.ScopeId)
    (state : PlanningState) (block : Block) :
    (planBlockScoped parent state block).allocation.env =
      state.allocation.env := by
  simp [planBlockScoped]

private theorem planCases_env
    (current : Locals.Allocation.ScopeId) :
    ∀ (state : PlanningState) (cases : List (Word × Block)),
      (planCases current state cases).allocation.env =
        state.allocation.env
  | state, [] => by
      simp [planCases]
  | state, (_, body) :: rest => by
      simp only [planCases]
      rw [planCases_env current (planBlockScoped current state body) rest]
      exact planBlockScoped_env current state body

private theorem planDefault_env
    (current : Locals.Allocation.ScopeId)
    (state : PlanningState) :
    ∀ (body : Option Block),
      (planDefault current state body).allocation.env =
        state.allocation.env
  | none => by
      simp [planDefault]
  | some body => by
      simpa [planDefault] using planBlockScoped_env current state body

private theorem planStmt_env_extension
    (current : Locals.Allocation.ScopeId)
    (state : PlanningState) (stmt : Stmt) :
    ∃ added,
      (planStmt current state stmt).allocation.env =
        added ++ state.allocation.env := by
  cases stmt with
  | expr _ | assign _ _ | brk | cont | leave | call _ _ _
  | terminal _ | terminalArgs _ _ =>
      exact ⟨[], by simp [planStmt]⟩
  | let_ name _ =>
      exact
        ⟨[(name, state.allocation.nextSlot)],
          by simp [planStmt, allocateName]⟩
  | block body =>
      exact
        ⟨[], by
          simpa [planStmt] using planBlockScoped_env current state body⟩
  | if_ _ body =>
      exact
        ⟨[], by
          simpa [planStmt] using planBlockScoped_env current state body⟩
  | switch _ cases defaultBody =>
      refine ⟨[], ?_⟩
      simp only [planStmt, List.nil_append]
      rw [planDefault_env, planCases_env]
  | for_ init _ post body =>
      exact ⟨[], by simp [planStmt]⟩

theorem planStmt_allocation_env
    (current : Locals.Allocation.ScopeId)
    (state : PlanningState) (stmt : Stmt) :
    (planStmt current state stmt).allocation.env =
      match stmt with
      | .let_ name _ =>
          (name, state.allocation.nextSlot) :: state.allocation.env
      | _ => state.allocation.env := by
  cases stmt with
  | expr _ | assign _ _ | brk | cont | leave | call _ _ _
  | terminal _ | terminalArgs _ _ =>
      simp [planStmt]
  | let_ name _ =>
      simp [planStmt, allocateName]
  | block body =>
      simpa [planStmt] using planBlockScoped_env current state body
  | if_ _ body =>
      simpa [planStmt] using planBlockScoped_env current state body
  | switch _ cases defaultBody =>
      simp only [planStmt]
      rw [planDefault_env, planCases_env]
  | for_ init _ post body =>
      simp [planStmt]

private theorem planStmtList_env_extension
    (current : Locals.Allocation.ScopeId) :
    ∀ (state : PlanningState) (stmts : List Stmt),
      ∃ added,
        (planStmtList current state stmts).allocation.env =
          added ++ state.allocation.env
  | state, [] => ⟨[], by simp [planStmtList]⟩
  | state, stmt :: rest => by
      obtain ⟨headPrefix, hHead⟩ :=
        planStmt_env_extension current state stmt
      obtain ⟨tailPrefix, hTail⟩ :=
        planStmtList_env_extension current
          (planStmt current state stmt) rest
      refine ⟨tailPrefix ++ headPrefix, ?_⟩
      simp only [planStmtList]
      rw [hTail, hHead, List.append_assoc]

theorem planBlockOpen_env_extension
    (current : Locals.Allocation.ScopeId)
    (state : PlanningState) (block : Block) :
    ∃ added,
      (planBlockOpen current state block).allocation.env =
        added ++ state.allocation.env := by
  rcases block with ⟨stmts⟩
  simpa [planBlockOpen] using
    planStmtList_env_extension current state stmts

structure FunctionPlanResult where
  functions : List ScopedAllocation
  lexicalScopes : List ScopedAllocation
  state : CompileState
  deriving DecidableEq, Repr

structure AllocationRecipe where
  functionSlots : List FunSlots
  stateAfterSignatures : CompileState
  stateAfterFunctions : CompileState
  functions : List ScopedAllocation
  lexicalScopes : List ScopedAllocation
  main : CompileState
  frameWords : Nat
  deriving DecidableEq, Repr

def planFunctions (functionSlots : List FunSlots) :
    CompileState → List FunDef →
      Option FunctionPlanResult
  | state, [] =>
      some { functions := [], lexicalScopes := [], state := state }
  | state, fn :: rest => do
      if (fn.returns ++ fn.params).Nodup then pure () else none
      if fn.returns.length < 16 then pure () else none
      let slots ← lookupFun? fn.name functionSlots
      let bodyStart : CompileState :=
        { env := functionEnv slots, nextSlot := state.nextSlot }
      let bodyPlan :=
        planBlockOpen (.function fn.name)
          { allocation := bodyStart, nextScope := 0, scopes := [] }
          fn.body
      let stateAfter : CompileState :=
        { env := state.env, nextSlot := bodyPlan.allocation.nextSlot }
      let tail ← planFunctions functionSlots stateAfter rest
      some
        { functions :=
            { scope := .function fn.name, state := bodyPlan.allocation } ::
              tail.functions
          lexicalScopes := bodyPlan.scopes ++ tail.lexicalScopes
          state := tail.state }

theorem planFunctions_member_valid
    {functionSlots : List FunSlots}
    {state : CompileState} {functions : List FunDef}
    {result : FunctionPlanResult} {fn : FunDef}
    (hPlan :
      planFunctions functionSlots state functions = some result)
    (hMem : fn ∈ functions) :
    (fn.returns ++ fn.params).Nodup ∧
      fn.returns.length < 16 := by
  induction functions generalizing state result fn with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      by_cases hSignature :
          (head.returns ++ head.params).Nodup
      · by_cases hReturns : head.returns.length < 16
        · cases hSlots : lookupFun? head.name functionSlots with
          | none =>
              simp [planFunctions, hSignature, hReturns, hSlots] at hPlan
          | some slots =>
              let bodyStart : CompileState :=
                { env := functionEnv slots
                  nextSlot := state.nextSlot }
              let bodyPlan :=
                planBlockOpen (.function head.name)
                  { allocation := bodyStart, nextScope := 0, scopes := [] }
                  head.body
              let stateAfter : CompileState :=
                { env := state.env
                  nextSlot := bodyPlan.allocation.nextSlot }
              cases hTail :
                  planFunctions functionSlots stateAfter rest with
              | none =>
                  simp [planFunctions, hSignature, hReturns, hSlots,
                    bodyStart, bodyPlan, stateAfter, hTail] at hPlan
              | some tail =>
                  simp [planFunctions, hSignature, hReturns, hSlots,
                    bodyStart, bodyPlan, stateAfter, hTail] at hPlan
                  rcases List.mem_cons.mp hMem with hEq | hRest
                  · subst fn
                    exact ⟨hSignature, hReturns⟩
                  · exact ih hTail hRest
        · simp [planFunctions, hSignature, hReturns] at hPlan
      · simp [planFunctions, hSignature] at hPlan

theorem planFunctions_member_scope
    {functionSlots : List FunSlots}
    {state : CompileState} {functions : List FunDef}
    {result : FunctionPlanResult} {fn : FunDef}
    (hPlan :
      planFunctions functionSlots state functions = some result)
    (hMem : fn ∈ functions) :
    ∃ entry,
      entry ∈ result.functions ∧
        entry.scope = .function fn.name := by
  induction functions generalizing state result fn with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      by_cases hSignature :
          (head.returns ++ head.params).Nodup
      · by_cases hReturns : head.returns.length < 16
        · cases hSlots : lookupFun? head.name functionSlots with
          | none =>
              simp [planFunctions, hSignature, hReturns, hSlots] at hPlan
          | some slots =>
              let bodyStart : CompileState :=
                { env := functionEnv slots
                  nextSlot := state.nextSlot }
              let bodyPlan :=
                planBlockOpen (.function head.name)
                  { allocation := bodyStart, nextScope := 0, scopes := [] }
                  head.body
              let stateAfter : CompileState :=
                { env := state.env
                  nextSlot := bodyPlan.allocation.nextSlot }
              cases hTail :
                  planFunctions functionSlots stateAfter rest with
              | none =>
                  simp [planFunctions, hSignature, hReturns, hSlots,
                    bodyStart, bodyPlan, stateAfter, hTail] at hPlan
              | some tail =>
                  simp [planFunctions, hSignature, hReturns, hSlots,
                    bodyStart, bodyPlan, stateAfter, hTail] at hPlan
                  subst result
                  rcases List.mem_cons.mp hMem with hEq | hRest
                  · subst fn
                    refine
                      ⟨{ scope := .function head.name
                         state := bodyPlan.allocation },
                        ?_, rfl⟩
                    exact
                      List.mem_cons.mpr
                        (Or.inl (by simp [bodyPlan, bodyStart]))
                  · obtain ⟨entry, hEntry, hScope⟩ :=
                      ih hTail hRest
                    exact ⟨entry, by simp [hEntry], hScope⟩
        · simp [planFunctions, hSignature, hReturns] at hPlan
      · simp [planFunctions, hSignature] at hPlan

theorem planFunctions_member_entry
    {functionSlots : List FunSlots}
    {state : CompileState} {functions : List FunDef}
    {result : FunctionPlanResult} {fn : FunDef}
    (hPlan :
      planFunctions functionSlots state functions = some result)
    (hMem : fn ∈ functions) :
    ∃ slots entry added,
      lookupFun? fn.name functionSlots = some slots ∧
        entry ∈ result.functions ∧
        entry.scope = .function fn.name ∧
        entry.state.env = added ++ functionEnv slots := by
  induction functions generalizing state result fn with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      by_cases hSignature :
          (head.returns ++ head.params).Nodup
      · by_cases hReturns : head.returns.length < 16
        · cases hSlots : lookupFun? head.name functionSlots with
          | none =>
              simp [planFunctions, hSignature, hReturns, hSlots] at hPlan
          | some slots =>
              let bodyStart : CompileState :=
                { env := functionEnv slots
                  nextSlot := state.nextSlot }
              let bodyPlan :=
                planBlockOpen (.function head.name)
                  { allocation := bodyStart, nextScope := 0, scopes := [] }
                  head.body
              let stateAfter : CompileState :=
                { env := state.env
                  nextSlot := bodyPlan.allocation.nextSlot }
              cases hTail :
                  planFunctions functionSlots stateAfter rest with
              | none =>
                  simp [planFunctions, hSignature, hReturns, hSlots,
                    bodyStart, bodyPlan, stateAfter, hTail] at hPlan
              | some tail =>
                  simp [planFunctions, hSignature, hReturns, hSlots,
                    bodyStart, bodyPlan, stateAfter, hTail] at hPlan
                  subst result
                  rcases List.mem_cons.mp hMem with hEq | hRest
                  · subst fn
                    obtain ⟨added, hEnv⟩ :=
                      planBlockOpen_env_extension
                        (.function head.name)
                        { allocation := bodyStart
                          nextScope := 0
                          scopes := [] }
                        head.body
                    refine
                      ⟨slots,
                        { scope := .function head.name
                          state := bodyPlan.allocation },
                        added, hSlots, ?_, rfl, ?_⟩
                    · simp [bodyPlan, bodyStart]
                    · simpa [bodyPlan, bodyStart] using hEnv
                  · obtain
                      ⟨tailSlots, entry, added, hLookup, hEntry,
                        hScope, hEnv⟩ :=
                    ih hTail hRest
                    exact
                      ⟨tailSlots, entry, added, hLookup,
                        by simp [hEntry], hScope, hEnv⟩
        · simp [planFunctions, hSignature, hReturns] at hPlan
      · simp [planFunctions, hSignature] at hPlan

def planRecipeCore? (program : Program) :
    Option AllocationRecipe := do
  if (program.functions.map FunDef.name).Nodup then pure () else none
  let initial : CompileState := { env := [], nextSlot := 0 }
  let (functionSlots, stateAfterSignatures) :=
    allocateFunctionSignatures program.functions initial
  let functionPlan ←
    planFunctions functionSlots stateAfterSignatures program.functions
  let mainStart : CompileState :=
    { env := [], nextSlot := functionPlan.state.nextSlot }
  let mainPlan :=
    planBlockOpen .main
      { allocation := mainStart, nextScope := 0, scopes := [] }
      program.body
  some
    { functionSlots := functionSlots
      stateAfterSignatures := stateAfterSignatures
      stateAfterFunctions := functionPlan.state
      functions := functionPlan.functions
      lexicalScopes := mainPlan.scopes ++ functionPlan.lexicalScopes
      main := mainPlan.allocation
      frameWords := mainPlan.allocation.nextSlot }

/--
Successful recipe planning exposes the exact state-threaded function plan used
to populate the recipe's function entries and final function allocation state.
-/
theorem planRecipeCore?_functions
    {program : Program} {recipe : AllocationRecipe}
    (hPlan : planRecipeCore? program = some recipe) :
    ∃ functionPlan,
      planFunctions recipe.functionSlots recipe.stateAfterSignatures
          program.functions =
        some functionPlan ∧
      functionPlan.functions = recipe.functions ∧
      functionPlan.state = recipe.stateAfterFunctions := by
  unfold planRecipeCore? at hPlan
  by_cases hNames : (program.functions.map FunDef.name).Nodup
  · let initial : CompileState := { env := [], nextSlot := 0 }
    cases hSignatures :
        allocateFunctionSignatures program.functions initial with
    | mk functionSlots stateAfterSignatures =>
        cases hFunctions :
            planFunctions functionSlots stateAfterSignatures
              program.functions with
        | none =>
            simp [hNames, initial, hSignatures, hFunctions] at hPlan
        | some functionPlan =>
            simp [hNames, initial, hSignatures, hFunctions] at hPlan
            subst recipe
            exact ⟨functionPlan, hFunctions, rfl, rfl⟩
  · simp [hNames] at hPlan

/--
Successful recipe planning exposes the exact distinguished-main plan and the
fact that all main lexical scopes occupy the prefix of the shared recipe.
-/
theorem planRecipeCore?_main
    {program : Program} {recipe : AllocationRecipe}
    (hPlan : planRecipeCore? program = some recipe) :
    ∃ mainPlan,
      planBlockOpen .main
          {
            allocation :=
              { env := []
                nextSlot := recipe.stateAfterFunctions.nextSlot }
            nextScope := 0
            scopes := []
          }
          program.body =
        mainPlan ∧
      mainPlan.allocation = recipe.main ∧
      mainPlan.allocation.nextSlot = recipe.frameWords ∧
      (∀ entry,
        entry ∈ mainPlan.scopes →
          entry ∈ recipe.lexicalScopes) := by
  unfold planRecipeCore? at hPlan
  by_cases hNames : (program.functions.map FunDef.name).Nodup
  · let initial : CompileState := { env := [], nextSlot := 0 }
    cases hSignatures :
        allocateFunctionSignatures program.functions initial with
    | mk functionSlots stateAfterSignatures =>
        cases hFunctions :
            planFunctions functionSlots stateAfterSignatures
              program.functions with
        | none =>
            simp [hNames, initial, hSignatures, hFunctions] at hPlan
        | some functionPlan =>
            simp [hNames, initial, hSignatures, hFunctions] at hPlan
            subst recipe
            let mainStart : CompileState :=
              { env := [], nextSlot := functionPlan.state.nextSlot }
            let mainPlan :=
              planBlockOpen .main
                { allocation := mainStart, nextScope := 0, scopes := [] }
                program.body
            refine ⟨mainPlan, ?_, rfl, rfl, ?_⟩
            · rfl
            · intro entry hEntry
              exact List.mem_append_left _ hEntry
  · simp [hNames] at hPlan

/--
Every lexical scope produced while planning functions is retained in the
whole-program recipe after the main-program scopes are prepended.
-/
theorem planRecipeCore?_function_lexicalScopes
    {program : Program} {recipe : AllocationRecipe}
    (hPlan : planRecipeCore? program = some recipe) :
    ∃ functionPlan,
      planFunctions recipe.functionSlots recipe.stateAfterSignatures
          program.functions =
        some functionPlan ∧
      functionPlan.functions = recipe.functions ∧
      (∀ entry,
        entry ∈ functionPlan.lexicalScopes →
          entry ∈ recipe.lexicalScopes) := by
  unfold planRecipeCore? at hPlan
  by_cases hNames : (program.functions.map FunDef.name).Nodup
  · let initial : CompileState := { env := [], nextSlot := 0 }
    cases hSignatures :
        allocateFunctionSignatures program.functions initial with
    | mk functionSlots stateAfterSignatures =>
        cases hFunctions :
            planFunctions functionSlots stateAfterSignatures
              program.functions with
        | none =>
            simp [hNames, initial, hSignatures, hFunctions] at hPlan
        | some functionPlan =>
            simp [hNames, initial, hSignatures, hFunctions] at hPlan
            subst recipe
            refine ⟨functionPlan, hFunctions, rfl, ?_⟩
            intro entry hEntry
            exact List.mem_append_right _ hEntry
  · simp [hNames] at hPlan

theorem planRecipeCore?_lookupFun_matches
    {program : Program} {recipe : AllocationRecipe}
    {fn : FunDef}
    (hPlan : planRecipeCore? program = some recipe)
    (hMem : fn ∈ program.functions) :
    ∃ fnSlots,
      lookupFun? fn.name recipe.functionSlots = some fnSlots ∧
        fnSlots.Matches fn := by
  unfold planRecipeCore? at hPlan
  by_cases hNames : (program.functions.map FunDef.name).Nodup
  · let initial : CompileState := { env := [], nextSlot := 0 }
    cases hSignatures :
        allocateFunctionSignatures program.functions initial with
    | mk functionSlots stateAfterSignatures =>
        cases hFunctions :
            planFunctions functionSlots stateAfterSignatures
              program.functions with
        | none =>
            simp [hNames, initial, hSignatures, hFunctions] at hPlan
        | some functionPlan =>
            simp [hNames, initial, hSignatures, hFunctions] at hPlan
            subst recipe
            have hMatch :=
              allocateFunctionSignatures_matches
                program.functions initial
            rw [hSignatures] at hMatch
            exact lookupFun?_of_matches hMatch hNames hMem
  · simp [hNames] at hPlan

/-- Every checked recipe slot lookup comes from the corresponding real source
function and carries its exact signature match. -/
theorem planRecipeCore?_find?_of_lookupFun?
    {program : Program} {recipe : AllocationRecipe}
    {name : Name} {slots : FunSlots}
    (hPlan : planRecipeCore? program = some recipe)
    (hLookup : lookupFun? name recipe.functionSlots = some slots) :
    ∃ fn,
      Functions.Source.FunList.find? name program.functions = some fn ∧
        slots.Matches fn := by
  unfold planRecipeCore? at hPlan
  by_cases hNames : (program.functions.map FunDef.name).Nodup
  · let initial : CompileState := { env := [], nextSlot := 0 }
    cases hSignatures :
        allocateFunctionSignatures program.functions initial with
    | mk functionSlots stateAfterSignatures =>
        cases hFunctions :
            planFunctions functionSlots stateAfterSignatures
              program.functions with
        | none =>
            simp [hNames, initial, hSignatures, hFunctions] at hPlan
        | some functionPlan =>
            simp [hNames, initial, hSignatures, hFunctions] at hPlan
            subst recipe
            have hMatch :=
              allocateFunctionSignatures_matches program.functions initial
            rw [hSignatures] at hMatch
            exact find?_of_lookupFun?_matches hMatch hLookup
  · simp [hNames] at hPlan

theorem planRecipeCore?_function_signature_valid
    {program : Program} {recipe : AllocationRecipe}
    {fn : FunDef}
    (hPlan : planRecipeCore? program = some recipe)
    (hMem : fn ∈ program.functions) :
    (fn.returns ++ fn.params).Nodup ∧
      fn.returns.length < 16 := by
  unfold planRecipeCore? at hPlan
  by_cases hNames : (program.functions.map FunDef.name).Nodup
  · let initial : CompileState := { env := [], nextSlot := 0 }
    cases hSignatures :
        allocateFunctionSignatures program.functions initial with
    | mk functionSlots stateAfterSignatures =>
        cases hFunctions :
            planFunctions functionSlots stateAfterSignatures
              program.functions with
        | none =>
            simp [hNames, initial, hSignatures, hFunctions] at hPlan
        | some functionPlan =>
            exact planFunctions_member_valid hFunctions hMem
  · simp [hNames] at hPlan

theorem planRecipeCore?_function_scope
    {program : Program} {recipe : AllocationRecipe}
    {fn : FunDef}
    (hPlan : planRecipeCore? program = some recipe)
    (hMem : fn ∈ program.functions) :
    ∃ entry,
      entry ∈ recipe.functions ∧
        entry.scope = .function fn.name := by
  unfold planRecipeCore? at hPlan
  by_cases hNames : (program.functions.map FunDef.name).Nodup
  · let initial : CompileState := { env := [], nextSlot := 0 }
    cases hSignatures :
        allocateFunctionSignatures program.functions initial with
    | mk functionSlots stateAfterSignatures =>
        cases hFunctions :
            planFunctions functionSlots stateAfterSignatures
              program.functions with
        | none =>
            simp [hNames, initial, hSignatures, hFunctions] at hPlan
        | some functionPlan =>
            simp [hNames, initial, hSignatures, hFunctions] at hPlan
            subst recipe
            exact planFunctions_member_scope hFunctions hMem
  · simp [hNames] at hPlan

theorem planRecipeCore?_function_entry
    {program : Program} {recipe : AllocationRecipe}
    {fn : FunDef}
    (hPlan : planRecipeCore? program = some recipe)
    (hMem : fn ∈ program.functions) :
    ∃ slots entry added,
      lookupFun? fn.name recipe.functionSlots = some slots ∧
        slots.Matches fn ∧
        entry ∈ recipe.functions ∧
        entry.scope = .function fn.name ∧
        entry.state.env = added ++ functionEnv slots := by
  unfold planRecipeCore? at hPlan
  by_cases hNames : (program.functions.map FunDef.name).Nodup
  · let initial : CompileState := { env := [], nextSlot := 0 }
    cases hSignatures :
        allocateFunctionSignatures program.functions initial with
    | mk functionSlots stateAfterSignatures =>
        cases hFunctions :
            planFunctions functionSlots stateAfterSignatures
              program.functions with
        | none =>
            simp [hNames, initial, hSignatures, hFunctions] at hPlan
        | some functionPlan =>
            simp [hNames, initial, hSignatures, hFunctions] at hPlan
            subst recipe
            obtain
                ⟨slots, entry, added, hLookup, hEntry, hScope, hEnv⟩ :=
              planFunctions_member_entry hFunctions hMem
            have hMatch :=
              allocateFunctionSignatures_matches
                program.functions initial
            rw [hSignatures] at hMatch
            obtain ⟨matched, hMatched, hMatches⟩ :=
              lookupFun?_of_matches hMatch hNames hMem
            rw [hLookup] at hMatched
            have hSlots : slots = matched :=
              Option.some.inj hMatched
            subst matched
            exact
              ⟨slots, entry, added, hLookup, hMatches,
                hEntry, hScope, hEnv⟩
  · simp [hNames] at hPlan

def planRecipe? (maxFrameWords : Nat) (program : Program) :
    Option AllocationRecipe := do
  let recipe ← planRecipeCore? program
  if recipe.frameWords ≤ maxFrameWords then some recipe else none

theorem planRecipe?_core_and_frameWords_le
    {maxFrameWords : Nat} {program : Program}
    {recipe : AllocationRecipe}
    (hPlan : planRecipe? maxFrameWords program = some recipe) :
    planRecipeCore? program = some recipe ∧
      recipe.frameWords ≤ maxFrameWords := by
  unfold planRecipe? at hPlan
  cases hCore : planRecipeCore? program with
  | none =>
      simp [hCore] at hPlan
  | some planned =>
      by_cases hFits : planned.frameWords ≤ maxFrameWords
      · simp [hCore, hFits] at hPlan
        subst recipe
        exact ⟨rfl, hFits⟩
      · simp [hCore, hFits] at hPlan

def dupCode? (depth : Nat) : Option Structured.Code := do
  let op ← Locals.StackOp.dup? depth
  some [Structured.BasicInstr.op op]

def slotAddressCode? (valuesAboveBase slot : Nat) :
    Option Structured.Code := do
  let dup ← dupCode? (valuesAboveBase + 1)
  some
    (dup ++
      [ Structured.BasicInstr.push (slotOffset slot),
        Structured.BasicInstr.op .add ])

def storeTopSlotCode? (valuesAboveBase slot : Nat) :
    Option Structured.Code := do
  let addr ← slotAddressCode? valuesAboveBase slot
  some (addr ++ [Structured.BasicInstr.op .mstore])

def bindScratchBindingsCode (baseDepth : Nat)
    (bindings : SlotEnv) : Structured.Code :=
  bindings.map fun binding =>
    Structured.BasicInstr.bindScratch baseDepth binding.1 binding.2

mutual
  def compileNoVarExprCode? {results : Nat}
      (expr : Expr results) : Option Structured.Code :=
    match expr with
    | .lit value => some [Structured.BasicInstr.push value]
    | .var _name => none
    | .code code => some code
    | .prim op args => do
        let argsCode ← compileNoVarExprSeqCode? args
        some (argsCode ++ [Structured.BasicInstr.op op])

  def compileNoVarExprSeqCode? {results : Nat}
      (exprs : Locals.ExprSeq results) : Option Structured.Code :=
    match exprs with
    | .nil => some []
    | .cons head tail => do
        let headCode ← compileNoVarExprCode? head
        let tailCode ← compileNoVarExprSeqCode? tail
        some (headCode ++ tailCode)
end

def compilePreludeStmt? : Stmt → Option Expressions.Stmt
  | .expr expr => do
      let code ← compileNoVarExprCode? expr
      some (Expressions.Stmt.code code)
  | _ => none

def framePreallocCode : Nat → Structured.Code
  | 0 => []
  | slot + 1 =>
      [ Structured.BasicInstr.push zeroWord,
        Structured.BasicInstr.op .dup2,
        Structured.BasicInstr.push (slotOffset slot),
        Structured.BasicInstr.op .add,
        Structured.BasicInstr.op .mstore ]

def scratchAllocatorInitCode
    (config : ScratchFrameConfig) : Structured.Code :=
  [ Structured.BasicInstr.push (word config.firstFrame),
    Structured.BasicInstr.push (word config.allocatorCell),
    Structured.BasicInstr.op .mstore ]

def scratchFrameAcquireCode
    (config : ScratchFrameConfig) : Structured.Code :=
  [ Structured.BasicInstr.push (word config.allocatorCell),
    Structured.BasicInstr.op .mload,
    Structured.BasicInstr.op .dup1,
    Structured.BasicInstr.push (frameBytes config.frameWords),
    Structured.BasicInstr.op .add,
    Structured.BasicInstr.push (word config.allocatorCell),
    Structured.BasicInstr.op .mstore ] ++
      framePreallocCode config.frameWords

def scratchFrameReleaseCode
    (config : ScratchFrameConfig) : Structured.Code :=
  [ Structured.BasicInstr.push (frameBytes config.frameWords),
    Structured.BasicInstr.push (word config.allocatorCell),
    Structured.BasicInstr.op .mload,
    Structured.BasicInstr.op .sub,
    Structured.BasicInstr.push (word config.allocatorCell),
    Structured.BasicInstr.op .mstore ]

end AllocationSupport
end Functions
end EvmCompiler
