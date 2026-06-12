import EvmCompiler.Functions.AllocationSupport

namespace EvmCompiler
namespace Functions
namespace MixedAllocation

abbrev SlotSet := List Nat

def stackEntries (stackSlots : SlotSet)
    (env : AllocationSupport.SlotEnv) : AllocationSupport.SlotEnv :=
  env.filter fun binding => binding.2 ∈ stackSlots

theorem mem_stackEntries_iff
    {stackSlots : SlotSet}
    {env : AllocationSupport.SlotEnv}
    {binding : Name × Nat} :
    binding ∈ stackEntries stackSlots env ↔
      binding ∈ env ∧ binding.2 ∈ stackSlots := by
  simp [stackEntries]

def stackOrder (stackSlots : SlotSet)
    (env : AllocationSupport.SlotEnv) : List Name :=
  (stackEntries stackSlots env).map Prod.fst

def bindingLocation (stackEntries : AllocationSupport.SlotEnv)
    (binding : Name × Nat) :
    Locals.Allocation.LocalLocation :=
  match stackEntries.findIdx? (fun entry => entry = binding) with
  | some depth => .stack depth
  | none => .scratch binding.2

theorem bindingLocation_stack_of_mem
    {entries : AllocationSupport.SlotEnv}
    {binding : Name × Nat}
    (hMem : binding ∈ entries) :
    ∃ depth,
      bindingLocation entries binding = .stack depth := by
  cases hFind :
      entries.findIdx? (fun entry => entry = binding) with
  | none =>
      have hAll :=
        List.findIdx?_eq_none_iff.mp hFind binding hMem
      simp at hAll
  | some depth =>
      exact ⟨depth, by simp [bindingLocation, hFind]⟩

theorem bindingLocation_scratch_of_not_mem
    {entries : AllocationSupport.SlotEnv}
    {binding : Name × Nat}
    (hNotMem : binding ∉ entries) :
    bindingLocation entries binding = .scratch binding.2 := by
  have hFind :
      entries.findIdx? (fun entry => entry = binding) = none := by
    apply List.findIdx?_eq_none_iff.mpr
    intro entry hEntry
    have hNe : entry ≠ binding := by
      intro hEq
      subst entry
      exact hNotMem hEntry
    simp [hNe]
  simp [bindingLocation, hFind]

def bindings (stackEntries env : AllocationSupport.SlotEnv) :
    List Locals.Allocation.Binding :=
  env.map fun binding =>
    (binding.1, bindingLocation stackEntries binding)

private theorem find_bindings_of_mem
    {entries env : AllocationSupport.SlotEnv}
    {name : Name} {slot : Nat}
    (hNodup : (env.map Prod.fst).Nodup)
    (hMem : (name, slot) ∈ env) :
    ((bindings entries env).find? fun binding =>
        decide (binding.1 = name)).map Prod.snd =
      some (bindingLocation entries (name, slot)) := by
  induction env with
  | nil =>
      exact False.elim (by simpa using hMem)
  | cons head tail ih =>
      have hNodup' :
          (head.1 :: tail.map Prod.fst).Nodup := by
        simpa only [List.map_cons] using hNodup
      have hTailNodup :
          (tail.map Prod.fst).Nodup :=
        (List.nodup_cons.mp hNodup').2
      rcases List.mem_cons.mp hMem with hHead | hTail
      · subst head
        simp [bindings]
      · have hNameNe : head.1 ≠ name := by
          intro hEq
          have hNameMem :
              name ∈ tail.map Prod.fst :=
            List.mem_map.mpr ⟨(name, slot), hTail, rfl⟩
          have hHeadFresh :=
            (List.nodup_cons.mp hNodup').1
          rw [hEq] at hHeadFresh
          exact hHeadFresh hNameMem
        simpa [bindings, hNameNe] using ih hTailNodup hTail

def usesScratch (stackSlots : SlotSet)
    (env : AllocationSupport.SlotEnv) : Bool :=
  env.any fun binding => binding.2 ∉ stackSlots

def scratchRegionBase
    (contract : MemoryContract.Contract) :
    Locals.Allocation.RegionBase :=
  match contract.scratch? with
  | none =>
      .freeMemoryPointer
  | some reservation =>
      .absolute reservation.frameBase

def allocationOfState (contract : MemoryContract.Contract)
    (frameWords : Nat)
    (stackEntries : AllocationSupport.SlotEnv)
    (state : AllocationSupport.CompileState) :
    Locals.Allocation.Plan where
  sourceScope := state.env.map Prod.fst
  stackOrder := stackEntries.map Prod.fst
  bindings := bindings stackEntries state.env
  scratchRegion? :=
    if stackEntries.length < state.env.length then
      some
        { base := scratchRegionBase contract
          words := frameWords }
    else
      none

theorem allocationOfState_location_of_mem
    {contract : MemoryContract.Contract}
    {frameWords : Nat}
    {entries : AllocationSupport.SlotEnv}
    {state : AllocationSupport.CompileState}
    {name : Name} {slot : Nat}
    (hNodup : (state.env.map Prod.fst).Nodup)
    (hMem : (name, slot) ∈ state.env) :
    (allocationOfState contract frameWords entries state).location? name =
      some (bindingLocation entries (name, slot)) := by
  simpa [allocationOfState, Locals.Allocation.Plan.location?] using
    find_bindings_of_mem (entries := entries) hNodup hMem

theorem allocationOfState_location_stack_of_entry
    {contract : MemoryContract.Contract}
    {frameWords : Nat}
    {entries : AllocationSupport.SlotEnv}
    {state : AllocationSupport.CompileState}
    {name : Name} {slot : Nat}
    (hNodup : (state.env.map Prod.fst).Nodup)
    (hMem : (name, slot) ∈ state.env)
    (hEntry : (name, slot) ∈ entries) :
    ∃ depth,
      (allocationOfState contract frameWords entries state).location? name =
        some (.stack depth) := by
  obtain ⟨depth, hLocation⟩ :=
    bindingLocation_stack_of_mem hEntry
  exact
    ⟨depth, by
      rw [allocationOfState_location_of_mem hNodup hMem, hLocation]⟩

theorem allocationOfState_location_scratch_of_not_entry
    {contract : MemoryContract.Contract}
    {frameWords : Nat}
    {entries : AllocationSupport.SlotEnv}
    {state : AllocationSupport.CompileState}
    {name : Name} {slot : Nat}
    (hNodup : (state.env.map Prod.fst).Nodup)
    (hMem : (name, slot) ∈ state.env)
    (hNotEntry : (name, slot) ∉ entries) :
    (allocationOfState contract frameWords entries state).location? name =
      some (.scratch slot) := by
  rw [allocationOfState_location_of_mem hNodup hMem]
  exact
    congrArg some
      (by simpa using bindingLocation_scratch_of_not_mem hNotEntry)

theorem allocationOfState_scratchRegion_of_wellFormed
    {contract : MemoryContract.Contract}
    {frameWords : Nat}
    {entries : AllocationSupport.SlotEnv}
    {state : AllocationSupport.CompileState}
    {name : Name} {slot : Nat}
    (hWF : (allocationOfState contract frameWords entries state).WellFormed)
    (hLocation :
      (allocationOfState contract frameWords entries state).location? name =
        some (.scratch slot)) :
    (allocationOfState contract frameWords entries state).scratchRegion? =
      some
        { base := scratchRegionBase contract
          words := frameWords } := by
  by_cases hScratch : entries.length < state.env.length
  · simp [allocationOfState, hScratch]
  · have hValid :=
      Locals.Allocation.Plan.bindingValid_of_wellFormed_of_location?_eq_some
        hWF hLocation
    simp [allocationOfState, hScratch,
      Locals.Allocation.Plan.BindingValid] at hValid

theorem allocationOfState_scratch_bound_of_wellFormed
    {contract : MemoryContract.Contract}
    {frameWords : Nat}
    {entries : AllocationSupport.SlotEnv}
    {state : AllocationSupport.CompileState}
    {name : Name} {slot : Nat}
    (hWF : (allocationOfState contract frameWords entries state).WellFormed)
    (hLocation :
      (allocationOfState contract frameWords entries state).location? name =
        some (.scratch slot)) :
    slot < frameWords := by
  exact
    Locals.Allocation.Plan.scratch_bound_of_wellFormed hWF hLocation
      (allocationOfState_scratchRegion_of_wellFormed hWF hLocation)

theorem allocationOfState_location_stack_of_mem
    {contract : MemoryContract.Contract}
    {frameWords : Nat} {stackSlots : SlotSet}
    {state : AllocationSupport.CompileState}
    {name : Name} {slot : Nat}
    (hNodup : (state.env.map Prod.fst).Nodup)
    (hMem : (name, slot) ∈ state.env)
    (hStack : slot ∈ stackSlots) :
    ∃ depth,
      (allocationOfState contract frameWords
          (stackEntries stackSlots state.env) state).location? name =
        some (.stack depth) := by
  have hEntry :
      (name, slot) ∈ stackEntries stackSlots state.env :=
    mem_stackEntries_iff.mpr ⟨hMem, hStack⟩
  obtain ⟨depth, hLocation⟩ :=
    bindingLocation_stack_of_mem hEntry
  exact
    ⟨depth, by
      rw [allocationOfState_location_of_mem hNodup hMem, hLocation]⟩

theorem allocationOfState_location_scratch_of_mem
    {contract : MemoryContract.Contract}
    {frameWords : Nat} {stackSlots : SlotSet}
    {state : AllocationSupport.CompileState}
    {name : Name} {slot : Nat}
    (hNodup : (state.env.map Prod.fst).Nodup)
    (hMem : (name, slot) ∈ state.env)
    (hScratch : slot ∉ stackSlots) :
    (allocationOfState contract frameWords
        (stackEntries stackSlots state.env) state).location? name =
      some (.scratch slot) := by
  have hNotEntry :
      (name, slot) ∉ stackEntries stackSlots state.env := by
    intro hEntry
    exact hScratch (mem_stackEntries_iff.mp hEntry).2
  rw [allocationOfState_location_of_mem hNodup hMem]
  exact
    congrArg some
      (by simpa using bindingLocation_scratch_of_not_mem hNotEntry)

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

theorem stackEntriesForScope_function_of_env_extension
    {recipe : AllocationSupport.AllocationRecipe}
    {stackSlots : SlotSet}
    {functionName : Name}
    {slots : AllocationSupport.FunSlots}
    {state : AllocationSupport.CompileState}
    {added : AllocationSupport.SlotEnv}
    (hLookup :
      AllocationSupport.lookupFun? functionName recipe.functionSlots =
        some slots)
    (hEnv :
      state.env = added ++ AllocationSupport.functionEnv slots) :
    stackEntriesForScope recipe stackSlots (.function functionName) state =
      stackEntries stackSlots added ++
        stackEntries stackSlots slots.returns.reverse ++
        stackEntries stackSlots slots.params.reverse := by
  simp [stackEntriesForScope, functionRoot?, hLookup, hEnv,
    AllocationSupport.functionEnv, stackEntries,
    List.filter_append, List.take_append]

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
    (stackSlots : SlotSet)
    (contract : MemoryContract.Contract) :
    Locals.Allocation.ProgramPlan :=
  { scopes :=
      [{ scope := .main
         allocation :=
           allocationOfState contract recipe.frameWords
             (stackEntriesForScope recipe stackSlots .main recipe.main)
             recipe.main }] ++
      (recipe.functions.map fun fn =>
        { scope := fn.scope
          allocation :=
            allocationOfState contract recipe.frameWords
              (stackEntriesForScope recipe stackSlots fn.scope fn.state)
              fn.state }) ++
      (recipe.lexicalScopes.map fun entry =>
        { scope := entry.scope
          allocation :=
            allocationOfState contract recipe.frameWords
              (stackEntriesForScope recipe stackSlots entry.scope entry.state)
              entry.state }) }

theorem toMixedProgramPlan_find_function_entry
    {recipe : AllocationSupport.AllocationRecipe}
    {stackSlots : SlotSet}
    {contract : MemoryContract.Contract}
    {entry : AllocationSupport.ScopedAllocation}
    (hWF :
      (toMixedProgramPlan recipe stackSlots contract).WellFormed)
    (hMem : entry ∈ recipe.functions) :
    (toMixedProgramPlan recipe stackSlots contract).find? entry.scope =
      some
        (allocationOfState contract recipe.frameWords
          (stackEntriesForScope recipe stackSlots entry.scope entry.state)
          entry.state) := by
  let scopePlan : Locals.Allocation.ScopePlan :=
    { scope := entry.scope
      allocation :=
        allocationOfState contract recipe.frameWords
          (stackEntriesForScope recipe stackSlots entry.scope entry.state)
          entry.state }
  have hScopeMem :
      scopePlan ∈
        (toMixedProgramPlan recipe stackSlots contract).scopes := by
    simp only [toMixedProgramPlan, List.mem_cons, List.mem_append,
      List.mem_map]
    exact
      Or.inl
        (Or.inr
          ⟨entry, hMem, by simp [scopePlan]⟩)
  exact
    Locals.Allocation.ProgramPlan.find?_of_mem_of_wellFormed
      hWF hScopeMem

end AllocationRecipe

def planAllocation? (maxFrameWords : Nat) (stackSlots : SlotSet)
    (program : Program) : Option Locals.Allocation.ProgramPlan := do
  if stackSlots.Nodup then pure () else none
  let recipe ← AllocationSupport.planRecipe? maxFrameWords program
  if AllocationRecipe.executable? recipe stackSlots program then
    pure ()
  else
    none
  let allocation :=
    AllocationRecipe.toMixedProgramPlan
      recipe stackSlots program.memoryContract
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

end Examples

end MixedAllocation
end Functions
end EvmCompiler
