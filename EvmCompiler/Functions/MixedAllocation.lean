import EvmCompiler.Functions.AllocationSupport

namespace EvmCompiler
namespace Functions
namespace MixedAllocation

abbrev SlotSet := List Nat

def stackEntries (stackSlots : SlotSet)
    (env : AllocationSupport.SlotEnv) : AllocationSupport.SlotEnv :=
  env.filter fun binding => binding.2 ∈ stackSlots

def stackOrder (stackSlots : SlotSet)
    (env : AllocationSupport.SlotEnv) : List Name :=
  (stackEntries stackSlots env).map Prod.fst

def bindingLocation (stackEntries : AllocationSupport.SlotEnv)
    (binding : Name × Nat) :
    Locals.Allocation.LocalLocation :=
  match stackEntries.findIdx? (fun entry => entry = binding) with
  | some depth => .stack depth
  | none => .scratch binding.2

def bindings (stackEntries env : AllocationSupport.SlotEnv) :
    List Locals.Allocation.Binding :=
  env.map fun binding =>
    (binding.1, bindingLocation stackEntries binding)

def usesScratch (stackSlots : SlotSet)
    (env : AllocationSupport.SlotEnv) : Bool :=
  env.any fun binding => binding.2 ∉ stackSlots

def allocationOfState (frameWords : Nat)
    (stackEntries : AllocationSupport.SlotEnv)
    (state : AllocationSupport.CompileState) :
    Locals.Allocation.Plan where
  sourceScope := state.env.map Prod.fst
  stackOrder := stackEntries.map Prod.fst
  bindings := bindings stackEntries state.env
  scratchRegion? :=
    if stackEntries.length < state.env.length then
      some
        { base := .freeMemoryPointer
          words := frameWords }
    else
      none

namespace AllocationRecipe

def functionRoot? : Locals.Allocation.ScopeId → Option Name
  | .main => none
  | .function name => some name
  | .lexical parent _ => functionRoot? parent

def stackEntriesForScope (recipe : AllocationSupport.AllocationRecipe)
    (stackSlots : SlotSet) (scope : Locals.Allocation.ScopeId)
    (state : AllocationSupport.CompileState) :
    AllocationSupport.SlotEnv :=
  match functionRoot? scope with
  | none => stackEntries stackSlots state.env
  | some functionName =>
      match AllocationSupport.lookupFun? functionName recipe.functionSlots with
      | none => stackEntries stackSlots state.env
      | some slots =>
          let signature := AllocationSupport.functionEnv slots
          let locals :=
            state.env.take (state.env.length - signature.length)
          stackEntries stackSlots locals ++
            stackEntries stackSlots slots.returns.reverse ++
            stackEntries stackSlots slots.params.reverse

def scopeRoot : Locals.Allocation.ScopeId → Locals.Allocation.ScopeId
  | .main => .main
  | .function name => .function name
  | .lexical parent _ => scopeRoot parent

def scopedStates (recipe : AllocationSupport.AllocationRecipe) :
    List AllocationSupport.ScopedAllocation :=
  { scope := .main, state := recipe.main } ::
    recipe.functions ++ recipe.lexicalScopes

def rootUsesScratch (recipe : AllocationSupport.AllocationRecipe)
    (stackSlots : SlotSet) (root : Locals.Allocation.ScopeId) : Bool :=
  (scopedStates recipe).any fun entry =>
    decide (scopeRoot entry.scope = root) &&
      usesScratch stackSlots entry.state.env

def scopeExecutable? (recipe : AllocationSupport.AllocationRecipe)
    (stackSlots : SlotSet)
    (entry : AllocationSupport.ScopedAllocation) : Bool :=
  let stackCount :=
    (stackEntriesForScope recipe stackSlots entry.scope entry.state).length
  if rootUsesScratch recipe stackSlots (scopeRoot entry.scope) then
    stackCount < 15
  else
    stackCount ≤ 16

def functionEntriesExecutable?
    (recipe : AllocationSupport.AllocationRecipe)
    (stackSlots : SlotSet) (program : Program) : Bool :=
  program.functions.all fun fn =>
    if rootUsesScratch recipe stackSlots (.function fn.name) then
      fn.params.length < 16
    else
      fn.params.length ≤ 16

def executable? (recipe : AllocationSupport.AllocationRecipe)
    (stackSlots : SlotSet) (program : Program) : Bool :=
  (scopedStates recipe).all (scopeExecutable? recipe stackSlots) &&
    functionEntriesExecutable? recipe stackSlots program

def toMixedProgramPlan (recipe : AllocationSupport.AllocationRecipe)
    (stackSlots : SlotSet) : Locals.Allocation.ProgramPlan :=
  { scopes :=
      [{ scope := .main
         allocation :=
           allocationOfState recipe.frameWords
             (stackEntriesForScope recipe stackSlots .main recipe.main)
             recipe.main }] ++
      (recipe.functions.map fun fn =>
        { scope := fn.scope
          allocation :=
            allocationOfState recipe.frameWords
              (stackEntriesForScope recipe stackSlots fn.scope fn.state)
              fn.state }) ++
      (recipe.lexicalScopes.map fun entry =>
        { scope := entry.scope
          allocation :=
            allocationOfState recipe.frameWords
              (stackEntriesForScope recipe stackSlots entry.scope entry.state)
              entry.state }) }

end AllocationRecipe

def planAllocation? (maxFrameWords : Nat) (stackSlots : SlotSet)
    (program : Program) : Option Locals.Allocation.ProgramPlan := do
  if stackSlots.Nodup then pure () else none
  let recipe ← AllocationSupport.planRecipe? maxFrameWords program
  if AllocationRecipe.executable? recipe stackSlots program then
    pure ()
  else
    none
  let allocation := AllocationRecipe.toMixedProgramPlan recipe stackSlots
  if allocation.wellFormed? then some allocation else none

theorem planAllocation?_wellFormed
    {maxFrameWords : Nat} {stackSlots : SlotSet} {program : Program}
    {allocation : Locals.Allocation.ProgramPlan}
    (hPlan :
      planAllocation? maxFrameWords stackSlots program = some allocation) :
    allocation.WellFormed := by
  unfold planAllocation? at hPlan
  by_cases hSlots : stackSlots.Nodup
  · cases hRecipe :
        AllocationSupport.planRecipe? maxFrameWords program with
    | none =>
        simp [hSlots, hRecipe] at hPlan
    | some recipe =>
        simp [hSlots, hRecipe] at hPlan
        rcases hPlan with ⟨_, hWF, rfl⟩
        exact
          Locals.Allocation.ProgramPlan.wellFormed_of_check hWF
  · simp [hSlots] at hPlan

def planner (maxFrameWords : Nat) (stackSlots : SlotSet) :
    Locals.Allocation.Planner Program where
  plan? := planAllocation? maxFrameWords stackSlots

def firstStackSlots (count : Nat) : SlotSet :=
  List.range count

def planAllStack? (program : Program) :
    Option Locals.Allocation.ProgramPlan := do
  let recipe ← AllocationSupport.planRecipeCore? program
  planAllocation? recipe.frameWords
    (firstStackSlots recipe.frameWords) program

def allStackPlanner : Locals.Allocation.Planner Program where
  plan? := planAllStack?

def allScratchPlanner (maxFrameWords : Nat) :
    Locals.Allocation.Planner Program :=
  planner maxFrameWords []

namespace Examples

def function : FunDef :=
  { name := "f"
    params := ["p"]
    returns := ["r"]
    body :=
      { stmts :=
          [ .let_ "x" (.lit (AllocationSupport.word 1)),
            .assign "r" (.var "x") ] } }

def program : Program :=
  { functions := [function]
    body :=
      { stmts :=
          [.let_ "m" (.lit (AllocationSupport.word 2))] } }

def nestedProgram : Program :=
  { functions := []
    body :=
      { stmts :=
          [ .block
              { stmts :=
                  [.let_ "nested" (.lit (AllocationSupport.word 3))] } ] } }

def nestedStackAllocationExpected : Locals.Allocation.Plan :=
  { sourceScope := ["nested"]
    stackOrder := ["nested"]
    bindings := [("nested", .stack 0)]
    scratchRegion? := none }

def wideProgram : Program :=
  { functions := []
    body :=
      { stmts :=
          (List.range 17).map fun idx =>
            .let_ ("mixed_" ++ toString idx)
              (.lit (AllocationSupport.word idx)) } }

def mixedWidePlan : Option Locals.Allocation.ProgramPlan :=
  planAllocation? 17 (firstStackSlots 14) wideProgram

def mixedMainRecorded : Bool :=
  match mixedWidePlan with
  | none => false
  | some allocation =>
      match allocation.find? .main with
      | none => false
      | some main =>
          decide (main.stackOrder.length = 14) &&
            decide (main.scratchSlots = [16, 15, 14])

example : mixedMainRecorded = true := by
  native_decide

example :
    (planAllStack? nestedProgram).bind
        (fun allocation =>
          allocation.find? (.lexical .main 0)) =
      some nestedStackAllocationExpected := by
  native_decide

end Examples

end MixedAllocation
end Functions
end EvmCompiler
