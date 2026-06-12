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

def lookupFun? (name : Name) : List FunSlots → Option FunSlots
  | [] => none
  | fn :: rest => if fn.name = name then some fn else lookupFun? name rest

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

def planRecipe? (maxFrameWords : Nat) (program : Program) :
    Option AllocationRecipe := do
  let recipe ← planRecipeCore? program
  if recipe.frameWords ≤ maxFrameWords then some recipe else none

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
  [ Structured.BasicInstr.push (word config.allocatorCell),
    Structured.BasicInstr.op .mload,
    Structured.BasicInstr.push (frameBytes config.frameWords),
    Structured.BasicInstr.op .sub,
    Structured.BasicInstr.push (word config.allocatorCell),
    Structured.BasicInstr.op .mstore ]

end AllocationSupport
end Functions
end EvmCompiler
