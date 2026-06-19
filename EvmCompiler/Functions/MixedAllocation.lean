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

theorem not_mem_stackEntries_of_slot_not_mem
    {stackSlots : SlotSet}
    {env : AllocationSupport.SlotEnv}
    {name : Name} {slot : Nat}
    (hSlot : slot ∉ stackSlots) :
    (name, slot) ∉ stackEntries stackSlots env := by
  intro hMem
  exact hSlot (mem_stackEntries_iff.mp hMem).2

def stackOrder (stackSlots : SlotSet)
    (env : AllocationSupport.SlotEnv) : List Name :=
  (stackEntries stackSlots env).map Prod.fst

theorem stackOrder_nodup
    {stackSlots : SlotSet}
    {env : AllocationSupport.SlotEnv}
    (hNodup : (env.map Prod.fst).Nodup) :
    (stackOrder stackSlots env).Nodup := by
  induction env with
  | nil =>
      simp [stackOrder, stackEntries]
  | cons binding rest ih =>
      rcases binding with ⟨name, slot⟩
      have hNames :
          (name :: rest.map Prod.fst).Nodup := by
        simpa only [List.map_cons] using hNodup
      have hFresh := (List.nodup_cons.mp hNames).1
      have hRest := (List.nodup_cons.mp hNames).2
      by_cases hSlot : slot ∈ stackSlots
      · have hTailNodup := ih hRest
        have hNameFresh :
            name ∉ stackOrder stackSlots rest := by
          intro hName
          unfold stackOrder stackEntries at hName
          obtain ⟨binding, hBinding, hNameEq⟩ :=
            List.mem_map.mp hName
          have hRestMem : binding ∈ rest :=
            List.mem_of_mem_filter hBinding
          apply hFresh
          exact List.mem_map.mpr
            ⟨binding, hRestMem, hNameEq⟩
        simpa [stackOrder, stackEntries, hSlot] using
          List.nodup_cons.mpr ⟨hNameFresh, hTailNodup⟩
      · simpa [stackOrder, stackEntries, hSlot] using ih hRest

theorem mem_stackOrder_iff
    {stackSlots : SlotSet}
    {env : AllocationSupport.SlotEnv}
    {name : Name} :
    name ∈ stackOrder stackSlots env ↔
      ∃ slot, (name, slot) ∈ env ∧ slot ∈ stackSlots := by
  constructor
  · intro hMem
    obtain ⟨binding, hEntry, hName⟩ :=
      List.mem_map.mp hMem
    rcases binding with ⟨candidate, slot⟩
    simp at hName
    subst candidate
    exact
      ⟨slot, (mem_stackEntries_iff.mp hEntry).1,
        (mem_stackEntries_iff.mp hEntry).2⟩
  · rintro ⟨slot, hMem, hSlot⟩
    exact
      List.mem_map.mpr
        ⟨(name, slot), mem_stackEntries_iff.mpr ⟨hMem, hSlot⟩, rfl⟩

theorem stackOrder_append
    (stackSlots : SlotSet)
    (left right : AllocationSupport.SlotEnv) :
    stackOrder stackSlots (left ++ right) =
      stackOrder stackSlots left ++ stackOrder stackSlots right := by
  simp [stackOrder, stackEntries, List.filter_append]

theorem stackOrder_filter_names_self
    (stackSlots : SlotSet)
    (env : AllocationSupport.SlotEnv) :
    (stackOrder stackSlots env).filter
        (fun name => decide (name ∈ env.map Prod.fst)) =
      stackOrder stackSlots env := by
  apply List.filter_eq_self.mpr
  intro name hName
  obtain ⟨slot, hMem, _hSlot⟩ :=
    mem_stackOrder_iff.mp hName
  have hNameMap : name ∈ env.map Prod.fst :=
    List.mem_map.mpr ⟨(name, slot), hMem, rfl⟩
  simpa using hNameMap

theorem stackOrder_filter_names_eq_nil_of_nodup_append
    {stackSlots : SlotSet}
    {left right : AllocationSupport.SlotEnv}
    (hNodup :
      ((left ++ right).map Prod.fst).Nodup) :
    (stackOrder stackSlots left).filter
        (fun name => decide (name ∈ right.map Prod.fst)) =
      [] := by
  apply List.filter_eq_nil_iff.mpr
  intro name hName
  obtain ⟨slot, hMem, _hSlot⟩ :=
    mem_stackOrder_iff.mp hName
  have hLeftName : name ∈ left.map Prod.fst :=
    List.mem_map.mpr ⟨(name, slot), hMem, rfl⟩
  have hParts :
      (left.map Prod.fst ++ right.map Prod.fst).Nodup := by
    simpa [List.map_append] using hNodup
  have hDisjoint :
      List.Disjoint (left.map Prod.fst) (right.map Prod.fst) :=
    List.disjoint_of_nodup_append hParts
  have hNotRight : name ∉ right.map Prod.fst := fun hRightName =>
    (List.disjoint_left.mp hDisjoint) hLeftName hRightName
  simpa using hNotRight

theorem stackOrder_filter_names_eq_nil_of_disjoint
    {stackSlots : SlotSet}
    {env : AllocationSupport.SlotEnv}
    {names : List Name}
    (hDisjoint : List.Disjoint (env.map Prod.fst) names) :
    (stackOrder stackSlots env).filter
        (fun name => decide (name ∈ names)) =
      [] := by
  apply List.filter_eq_nil_iff.mpr
  intro name hName
  obtain ⟨slot, hMem, _hSlot⟩ :=
    mem_stackOrder_iff.mp hName
  have hEnvName : name ∈ env.map Prod.fst :=
    List.mem_map.mpr ⟨(name, slot), hMem, rfl⟩
  have hNotNames : name ∉ names := fun hNames =>
    (List.disjoint_left.mp hDisjoint) hEnvName hNames
  simpa using hNotNames

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

theorem allocationOfState_eq_of_env_eq
    {contract : MemoryContract.Contract}
    {frameWords : Nat}
    {leftEntries rightEntries : AllocationSupport.SlotEnv}
    {left right : AllocationSupport.CompileState}
    (hEntries : leftEntries = rightEntries)
    (hEnv : left.env = right.env) :
    allocationOfState contract frameWords leftEntries left =
      allocationOfState contract frameWords rightEntries right := by
  subst rightEntries
  cases left
  cases right
  simp only at hEnv
  subst hEnv
  rfl

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

theorem allocationOfState_parameter_stack_filter
    {contract : MemoryContract.Contract}
    {frameWords : Nat}
    {stackSlots : SlotSet}
    {state : AllocationSupport.CompileState}
    {added returns params processed pending : AllocationSupport.SlotEnv}
    (hEnv :
      state.env = added ++ returns ++ params)
    (hNodup : (state.env.map Prod.fst).Nodup)
    (hSplit : params = processed ++ pending) :
    ((allocationOfState contract frameWords
        (stackEntries stackSlots added ++
          stackEntries stackSlots returns.reverse ++
          stackEntries stackSlots params.reverse)
        state).stackOrder.filter
      (fun name => decide (name ∈ (processed.map Prod.fst).reverse))) =
      stackOrder stackSlots processed.reverse := by
  let addedNames := added.map Prod.fst
  let returnNames := returns.map Prod.fst
  let processedNames := processed.map Prod.fst
  let pendingNames := pending.map Prod.fst
  have hFull :
      (addedNames ++ returnNames ++ processedNames ++ pendingNames).Nodup := by
    simpa [addedNames, returnNames, processedNames, pendingNames,
      hEnv, hSplit, List.map_append, List.append_assoc] using hNodup
  have hAddedRest :
      (addedNames ++
        (returnNames ++ processedNames ++ pendingNames)).Nodup := by
    simpa [List.append_assoc] using hFull
  have hAddedParts := List.nodup_append.mp hAddedRest
  have hReturnRest :
      (returnNames ++ (processedNames ++ pendingNames)).Nodup :=
    by simpa [List.append_assoc] using hAddedParts.2.1
  have hReturnParts := List.nodup_append.mp hReturnRest
  have hProcessedPending :
      (processedNames ++ pendingNames).Nodup :=
    hReturnParts.2.1
  have hProcessedPendingParts :=
    List.nodup_append.mp hProcessedPending
  have hAddedProcessed :
      List.Disjoint addedNames processedNames := by
    apply List.disjoint_left.mpr
    intro name hAdded hProcessed
    exact
      hAddedParts.2.2 name hAdded name
        (by simp [hProcessed]) rfl
  have hReturnProcessed :
      List.Disjoint returnNames processedNames := by
    apply List.disjoint_left.mpr
    intro name hReturn hProcessed
    exact
      hReturnParts.2.2 name hReturn name
        (by simp [hProcessed]) rfl
  have hPendingProcessed :
      List.Disjoint pendingNames processedNames := by
    apply List.disjoint_left.mpr
    intro name hPending hProcessed
    exact
      hProcessedPendingParts.2.2 name hProcessed name hPending rfl
  have hAddedNil :=
    stackOrder_filter_names_eq_nil_of_disjoint
      (stackSlots := stackSlots)
      (env := added)
      (names := processedNames.reverse)
      (by
        apply List.disjoint_left.mpr
        intro name hAdded hProcessed
        exact
          (List.disjoint_left.mp hAddedProcessed)
            hAdded (by simpa using hProcessed))
  have hReturnsNil :=
    stackOrder_filter_names_eq_nil_of_disjoint
      (stackSlots := stackSlots)
      (env := returns.reverse)
      (names := processedNames.reverse)
      (by
        apply List.disjoint_left.mpr
        intro name hReturn hProcessed
        have hReturnName : name ∈ returnNames := by
          obtain ⟨binding, hBinding, hName⟩ :=
            List.mem_map.mp hReturn
          subst name
          exact
            List.mem_map.mpr
              ⟨binding, by simpa using hBinding, rfl⟩
        exact
          (List.disjoint_left.mp hReturnProcessed)
            hReturnName (by simpa using hProcessed))
  have hPendingNil :=
    stackOrder_filter_names_eq_nil_of_disjoint
      (stackSlots := stackSlots)
      (env := pending.reverse)
      (names := processedNames.reverse)
      (by
        apply List.disjoint_left.mpr
        intro name hPending hProcessed
        have hPendingName : name ∈ pendingNames := by
          obtain ⟨binding, hBinding, hName⟩ :=
            List.mem_map.mp hPending
          subst name
          exact
            List.mem_map.mpr
              ⟨binding, by simpa using hBinding, rfl⟩
        exact
          (List.disjoint_left.mp hPendingProcessed)
            hPendingName (by simpa using hProcessed))
  have hProcessedSelf :=
    stackOrder_filter_names_self stackSlots processed.reverse
  subst params
  simp only [allocationOfState, List.map_append]
  change
    ((stackOrder stackSlots added ++
        stackOrder stackSlots returns.reverse ++
        stackOrder stackSlots (processed ++ pending).reverse).filter
      (fun name => decide (name ∈ (processed.map Prod.fst).reverse))) =
      stackOrder stackSlots processed.reverse
  rw [List.filter_append, List.filter_append, List.reverse_append,
    stackOrder_append, List.filter_append]
  simp only [processedNames] at hAddedNil hReturnsNil hPendingNil
  rw [hAddedNil, hReturnsNil, hPendingNil]
  simpa [List.map_reverse] using hProcessedSelf

theorem allocationOfState_return_stack_filter
    {contract : MemoryContract.Contract}
    {frameWords : Nat}
    {stackSlots : SlotSet}
    {state : AllocationSupport.CompileState}
    {added returns params processed pending : AllocationSupport.SlotEnv}
    (hEnv :
      state.env = added ++ returns ++ params)
    (hNodup : (state.env.map Prod.fst).Nodup)
    (hSplit : returns = processed ++ pending) :
    ((allocationOfState contract frameWords
        (stackEntries stackSlots added ++
          stackEntries stackSlots returns.reverse ++
          stackEntries stackSlots params.reverse)
        state).stackOrder.filter
      (fun name =>
        decide
          (name ∈
            (processed.map Prod.fst).reverse ++
              (params.map Prod.fst).reverse))) =
      stackOrder stackSlots processed.reverse ++
        stackOrder stackSlots params.reverse := by
  let addedNames := added.map Prod.fst
  let processedNames := processed.map Prod.fst
  let pendingNames := pending.map Prod.fst
  let paramNames := params.map Prod.fst
  let liveNames := processedNames.reverse ++ paramNames.reverse
  have hFull :
      (addedNames ++ processedNames ++ pendingNames ++ paramNames).Nodup := by
    simpa [addedNames, processedNames, pendingNames, paramNames,
      hEnv, hSplit, List.map_append, List.append_assoc] using hNodup
  have hAddedRest :
      (addedNames ++
        (processedNames ++ pendingNames ++ paramNames)).Nodup := by
    simpa [List.append_assoc] using hFull
  have hAddedParts := List.nodup_append.mp hAddedRest
  have hReturnsParams :
      ((processedNames ++ pendingNames) ++ paramNames).Nodup := by
    simpa [List.append_assoc] using hAddedParts.2.1
  have hReturnsParts := List.nodup_append.mp hReturnsParams
  have hProcessedPending :
      (processedNames ++ pendingNames).Nodup :=
    hReturnsParts.1
  have hProcessedPendingParts :=
    List.nodup_append.mp hProcessedPending
  have hAddedLive :
      List.Disjoint addedNames liveNames := by
    apply List.disjoint_left.mpr
    intro name hAdded hLive
    have hLive' :
        name ∈ processedNames ∨ name ∈ paramNames := by
      simpa [liveNames] using hLive
    have hRest :
        name ∈ processedNames ++ pendingNames ++ paramNames := by
      rcases hLive' with hProcessed | hParam
      · simp [hProcessed]
      · simp [hParam]
    exact hAddedParts.2.2 name hAdded name hRest rfl
  have hPendingLive :
      List.Disjoint pendingNames liveNames := by
    apply List.disjoint_left.mpr
    intro name hPending hLive
    rcases List.mem_append.mp hLive with hProcessed | hParam
    · have hProcessed' : name ∈ processedNames := by
        simpa using hProcessed
      exact
        hProcessedPendingParts.2.2 name hProcessed'
          name hPending rfl
    · have hParam' : name ∈ paramNames := by
        simpa using hParam
      have hPendingInReturns :
          name ∈ processedNames ++ pendingNames := by
        simp [hPending]
      exact
        hReturnsParts.2.2 name hPendingInReturns
          name hParam' rfl
  have hAddedNil :=
    stackOrder_filter_names_eq_nil_of_disjoint
      (stackSlots := stackSlots)
      (env := added) (names := liveNames) hAddedLive
  have hPendingNil :=
    stackOrder_filter_names_eq_nil_of_disjoint
      (stackSlots := stackSlots)
      (env := pending.reverse) (names := liveNames)
      (by
        apply List.disjoint_left.mpr
        intro name hPending hLive
        have hPendingName : name ∈ pendingNames := by
          obtain ⟨binding, hBinding, hName⟩ :=
            List.mem_map.mp hPending
          subst name
          exact
            List.mem_map.mpr
              ⟨binding, by simpa using hBinding, rfl⟩
        exact
          (List.disjoint_left.mp hPendingLive)
            hPendingName hLive)
  have hProcessedSelf :
      (stackOrder stackSlots processed.reverse).filter
          (fun name => decide (name ∈ liveNames)) =
        stackOrder stackSlots processed.reverse := by
    apply List.filter_eq_self.mpr
    intro name hName
    obtain ⟨slot, hMem, _hSlot⟩ :=
      mem_stackOrder_iff.mp hName
    have hProcessedName : name ∈ processedNames.reverse := by
      have hMapped : name ∈ processed.reverse.map Prod.fst :=
        List.mem_map.mpr ⟨(name, slot), hMem, rfl⟩
      simpa [processedNames, List.map_reverse] using hMapped
    simpa [liveNames, hProcessedName]
  have hParamsSelf :
      (stackOrder stackSlots params.reverse).filter
          (fun name => decide (name ∈ liveNames)) =
        stackOrder stackSlots params.reverse := by
    apply List.filter_eq_self.mpr
    intro name hName
    obtain ⟨slot, hMem, _hSlot⟩ :=
      mem_stackOrder_iff.mp hName
    have hParamName : name ∈ paramNames.reverse := by
      have hMapped : name ∈ params.reverse.map Prod.fst :=
        List.mem_map.mpr ⟨(name, slot), hMem, rfl⟩
      simpa [paramNames, List.map_reverse] using hMapped
    simpa [liveNames, hParamName]
  subst returns
  simp only [allocationOfState, List.map_append]
  change
    List.filter
      (fun name =>
        decide
          (name ∈
            (processed.map Prod.fst).reverse ++
              (params.map Prod.fst).reverse))
      (stackOrder stackSlots added ++
        stackOrder stackSlots (processed ++ pending).reverse ++
        stackOrder stackSlots params.reverse) =
      stackOrder stackSlots processed.reverse ++
        stackOrder stackSlots params.reverse
  rw [List.filter_append, List.filter_append, List.reverse_append,
    stackOrder_append, List.filter_append]
  simp only [liveNames, processedNames, paramNames] at hAddedNil
  simp only [liveNames, processedNames, paramNames] at hPendingNil
  simp only [liveNames, processedNames, paramNames] at hProcessedSelf
  simp only [liveNames, processedNames, paramNames] at hParamsSelf
  rw [hAddedNil, hPendingNil, hProcessedSelf, hParamsSelf]
  simp

/--
The final function plan, restricted to the locals that have actually entered
scope, has exactly the stack order produced by those locals followed by the
function return/parameter prelude.

`future` contains declarations later in the same open function body. They are
present in the final allocation plan but absent from the current source scope.
-/
theorem allocationOfState_active_stack_filter
    {contract : MemoryContract.Contract}
    {frameWords : Nat}
    {stackSlots : SlotSet}
    {state : AllocationSupport.CompileState}
    {future locals returns params : AllocationSupport.SlotEnv}
    (hEnv :
      state.env = future ++ locals ++ returns ++ params)
    (hNodup : (state.env.map Prod.fst).Nodup) :
    ((allocationOfState contract frameWords
        (stackEntries stackSlots (future ++ locals) ++
          stackEntries stackSlots returns.reverse ++
          stackEntries stackSlots params.reverse)
        state).stackOrder.filter
      (fun name =>
        decide
          (name ∈
            locals.map Prod.fst ++
              (returns.map Prod.fst).reverse ++
              (params.map Prod.fst).reverse))) =
      stackOrder stackSlots locals ++
        stackOrder stackSlots returns.reverse ++
        stackOrder stackSlots params.reverse := by
  let futureNames := future.map Prod.fst
  let localsNames := locals.map Prod.fst
  let returnNames := returns.map Prod.fst
  let paramNames := params.map Prod.fst
  let liveNames :=
    localsNames ++ returnNames.reverse ++ paramNames.reverse
  have hFull :
      (futureNames ++ localsNames ++ returnNames ++ paramNames).Nodup := by
    simpa [futureNames, localsNames, returnNames, paramNames,
      hEnv, List.map_append, List.append_assoc] using hNodup
  have hFutureRest :
      List.Disjoint futureNames
        (localsNames ++ returnNames ++ paramNames) := by
    have hGrouped :
        (futureNames ++
          (localsNames ++ returnNames ++ paramNames)).Nodup := by
      simpa [List.append_assoc] using hFull
    exact List.disjoint_of_nodup_append hGrouped
  have hFutureLive :
      List.Disjoint futureNames liveNames := by
    apply List.disjoint_left.mpr
    intro name hFuture hLive
    have hParts :
        name ∈ localsNames ∨
          name ∈ returnNames ∨ name ∈ paramNames := by
      simpa [liveNames] using hLive
    have hRest :
        name ∈ localsNames ++ returnNames ++ paramNames := by
      rcases hParts with hLocal | hReturn | hParam
      · simp [hLocal]
      · simp [hReturn]
      · simp [hParam]
    exact (List.disjoint_left.mp hFutureRest) hFuture hRest
  have hFutureNil :=
    stackOrder_filter_names_eq_nil_of_disjoint
      (stackSlots := stackSlots) (env := future)
      (names := liveNames) hFutureLive
  have hLocalsSelf :
      (stackOrder stackSlots locals).filter
          (fun name => decide (name ∈ liveNames)) =
        stackOrder stackSlots locals := by
    apply List.filter_eq_self.mpr
    intro name hName
    obtain ⟨slot, hMem, _hSlot⟩ :=
      mem_stackOrder_iff.mp hName
    have hLocal : name ∈ localsNames :=
      List.mem_map.mpr ⟨(name, slot), hMem, rfl⟩
    simp [liveNames, hLocal]
  have hReturnsSelf :
      (stackOrder stackSlots returns.reverse).filter
          (fun name => decide (name ∈ liveNames)) =
        stackOrder stackSlots returns.reverse := by
    apply List.filter_eq_self.mpr
    intro name hName
    obtain ⟨slot, hMem, _hSlot⟩ :=
      mem_stackOrder_iff.mp hName
    have hReturn :
        name ∈ returnNames.reverse := by
      have hMapped : name ∈ returns.reverse.map Prod.fst :=
        List.mem_map.mpr ⟨(name, slot), hMem, rfl⟩
      simpa [returnNames, List.map_reverse] using hMapped
    simp [liveNames, hReturn]
  have hParamsSelf :
      (stackOrder stackSlots params.reverse).filter
          (fun name => decide (name ∈ liveNames)) =
        stackOrder stackSlots params.reverse := by
    apply List.filter_eq_self.mpr
    intro name hName
    obtain ⟨slot, hMem, _hSlot⟩ :=
      mem_stackOrder_iff.mp hName
    have hParam :
        name ∈ paramNames.reverse := by
      have hMapped : name ∈ params.reverse.map Prod.fst :=
        List.mem_map.mpr ⟨(name, slot), hMem, rfl⟩
      simpa [paramNames, List.map_reverse] using hMapped
    simp [liveNames, hParam]
  simp only [allocationOfState, List.map_append]
  change
    ((stackOrder stackSlots (future ++ locals) ++
        stackOrder stackSlots returns.reverse ++
        stackOrder stackSlots params.reverse).filter
      (fun name => decide (name ∈ liveNames))) =
      stackOrder stackSlots locals ++
        stackOrder stackSlots returns.reverse ++
        stackOrder stackSlots params.reverse
  rw [stackOrder_append, List.filter_append, List.filter_append,
    List.filter_append]
  rw [hFutureNil, hLocalsSelf, hReturnsSelf, hParamsSelf]
  simp

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

theorem stackEntriesForScope_eq_of_env_eq
    {recipe : AllocationSupport.AllocationRecipe}
    {stackSlots : SlotSet}
    {scope : Locals.Allocation.ScopeId}
    {left right : AllocationSupport.CompileState}
    (hEnv : left.env = right.env) :
    stackEntriesForScope recipe stackSlots scope left =
      stackEntriesForScope recipe stackSlots scope right := by
  unfold stackEntriesForScope
  split <;> simp only [hEnv]

theorem not_mem_stackEntriesForScope_of_slot_not_mem
    {recipe : AllocationSupport.AllocationRecipe}
    {stackSlots : SlotSet}
    {scope : Locals.Allocation.ScopeId}
    {state : AllocationSupport.CompileState}
    {name : Name} {slot : Nat}
    (hSlot : slot ∉ stackSlots) :
    (name, slot) ∉
      stackEntriesForScope recipe stackSlots scope state := by
  unfold stackEntriesForScope
  split
  · exact not_mem_stackEntries_of_slot_not_mem hSlot
  · split
    · exact not_mem_stackEntries_of_slot_not_mem hSlot
    · simp only [List.mem_append]
      intro hMem
      rcases hMem with hLocalOrReturn | hParam
      · rcases hLocalOrReturn with hLocal | hReturn
        · exact
            not_mem_stackEntries_of_slot_not_mem hSlot hLocal
        · exact
            not_mem_stackEntries_of_slot_not_mem hSlot hReturn
      · exact
          not_mem_stackEntries_of_slot_not_mem hSlot hParam

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

/--
The function-signature ordering used by a function scope is inherited by every
lexical scope rooted in that function.
-/
theorem stackEntriesForScope_of_functionRoot_env_extension
    {recipe : AllocationSupport.AllocationRecipe}
    {stackSlots : SlotSet}
    {scope : Locals.Allocation.ScopeId}
    {functionName : Name}
    {slots : AllocationSupport.FunSlots}
    {state : AllocationSupport.CompileState}
    {added : AllocationSupport.SlotEnv}
    (hRoot : functionRoot? scope = some functionName)
    (hLookup :
      AllocationSupport.lookupFun? functionName recipe.functionSlots =
        some slots)
    (hEnv :
      state.env = added ++ AllocationSupport.functionEnv slots) :
    stackEntriesForScope recipe stackSlots scope state =
      stackEntries stackSlots added ++
        stackEntries stackSlots slots.returns.reverse ++
        stackEntries stackSlots slots.params.reverse := by
  simp [stackEntriesForScope, hRoot, hLookup, hEnv,
    AllocationSupport.functionEnv, stackEntries,
    List.filter_append, List.take_append]

theorem mem_stackEntriesForScope_function_of_mem_of_slot_mem
    {recipe : AllocationSupport.AllocationRecipe}
    {stackSlots : SlotSet}
    {functionName : Name}
    {slots : AllocationSupport.FunSlots}
    {state : AllocationSupport.CompileState}
    {added : AllocationSupport.SlotEnv}
    {name : Name} {slot : Nat}
    (hLookup :
      AllocationSupport.lookupFun? functionName recipe.functionSlots =
        some slots)
    (hEnv :
      state.env = added ++ AllocationSupport.functionEnv slots)
    (hMem : (name, slot) ∈ state.env)
    (hSlot : slot ∈ stackSlots) :
    (name, slot) ∈
      stackEntriesForScope recipe stackSlots
        (.function functionName) state := by
  rw [stackEntriesForScope_function_of_env_extension hLookup hEnv]
  rw [hEnv] at hMem
  rcases List.mem_append.mp hMem with hAdded | hSignature
  · exact
      List.mem_append_left _
        (List.mem_append_left _
          (mem_stackEntries_iff.mpr ⟨hAdded, hSlot⟩))
  · rcases List.mem_append.mp hSignature with hReturn | hParam
    · exact
        List.mem_append_left _
          (List.mem_append_right _
            (mem_stackEntries_iff.mpr
              ⟨by simpa using hReturn, hSlot⟩))
    · exact
        List.mem_append_right _
          (mem_stackEntries_iff.mpr
            ⟨by simpa using hParam, hSlot⟩)

theorem mem_stackEntriesForScope_of_functionRoot_of_mem_of_slot_mem
    {recipe : AllocationSupport.AllocationRecipe}
    {stackSlots : SlotSet}
    {scope : Locals.Allocation.ScopeId}
    {functionName : Name}
    {slots : AllocationSupport.FunSlots}
    {state : AllocationSupport.CompileState}
    {added : AllocationSupport.SlotEnv}
    {name : Name} {slot : Nat}
    (hRoot : functionRoot? scope = some functionName)
    (hLookup :
      AllocationSupport.lookupFun? functionName recipe.functionSlots =
        some slots)
    (hEnv :
      state.env = added ++ AllocationSupport.functionEnv slots)
    (hMem : (name, slot) ∈ state.env)
    (hSlot : slot ∈ stackSlots) :
    (name, slot) ∈
      stackEntriesForScope recipe stackSlots scope state := by
  rw [stackEntriesForScope_of_functionRoot_env_extension
    hRoot hLookup hEnv]
  rw [hEnv] at hMem
  rcases List.mem_append.mp hMem with hAdded | hSignature
  · exact
      List.mem_append_left _
        (List.mem_append_left _
          (mem_stackEntries_iff.mpr ⟨hAdded, hSlot⟩))
  · rcases List.mem_append.mp hSignature with hReturn | hParam
    · exact
        List.mem_append_left _
          (List.mem_append_right _
            (mem_stackEntries_iff.mpr
              ⟨by simpa using hReturn, hSlot⟩))
    · exact
        List.mem_append_right _
          (mem_stackEntries_iff.mpr
            ⟨by simpa using hParam, hSlot⟩)

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

theorem toMixedProgramPlan_find_lexical_entry
    {recipe : AllocationSupport.AllocationRecipe}
    {stackSlots : SlotSet}
    {contract : MemoryContract.Contract}
    {entry : AllocationSupport.ScopedAllocation}
    (hWF :
      (toMixedProgramPlan recipe stackSlots contract).WellFormed)
    (hMem : entry ∈ recipe.lexicalScopes) :
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
      Or.inr
        ⟨entry, hMem, by simp [scopePlan]⟩
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

/-!
Pressure-aware candidate selection.

Recipe slot numbers are globally unique, but stack capacity is local to each
activation and lexical scope. `pressureStackSlots` indexes every recipe slot by
the scopes in which it is live, then greedily retains a slot only when doing so
keeps every affected scope below `cap`. Function return slots remain scratch
resident because the current TypedCfg procedure-exit shape owns returned words;
ordinary parameters and locals remain eligible.

This is only a candidate generator. `planPressure?` still runs the canonical
allocation checks, and the Objects compiler subsequently accepts a candidate
only when the complete existing lowering pipeline succeeds.
-/

def returnSlots (recipe : AllocationSupport.AllocationRecipe) : List Nat :=
  recipe.functionSlots.flatMap fun fn => fn.returns.map Prod.snd

def addScopeSlotOccurrences (scopeIndex : Nat)
    (env : AllocationSupport.SlotEnv)
    (occurrences : Array (List Nat)) : Array (List Nat) :=
  env.foldl
    (fun result binding =>
      result.modify binding.2 (fun scopes => scopeIndex :: scopes))
    occurrences

def slotScopeOccurrencesAux :
    List AllocationSupport.ScopedAllocation → Nat →
      Array (List Nat) → Array (List Nat)
  | [], _scopeIndex, occurrences => occurrences
  | entry :: rest, scopeIndex, occurrences =>
      slotScopeOccurrencesAux rest (scopeIndex + 1)
        (addScopeSlotOccurrences scopeIndex entry.state.env occurrences)

def slotScopeOccurrences
    (recipe : AllocationSupport.AllocationRecipe) : Array (List Nat) :=
  slotScopeOccurrencesAux (AllocationRecipe.scopedStates recipe) 0
    (Array.replicate recipe.frameWords [])

def pressureStackSlots
    (recipe : AllocationSupport.AllocationRecipe) (cap : Nat) : SlotSet :=
  let scopeStates := AllocationRecipe.scopedStates recipe
  let occurrences := slotScopeOccurrences recipe
  let candidates :=
    (List.range recipe.frameWords).filter fun slot =>
      slot ∉ returnSlots recipe
  let result :=
    candidates.foldl
      (fun result slot =>
        let indices := occurrences.getD slot []
        if indices.all fun index =>
            decide (result.2.getD index 0 < cap) then
          (slot :: result.1,
            indices.foldl
              (fun counts index =>
                counts.modify index (fun count => count + 1))
              result.2)
        else
          result)
      ([], Array.replicate scopeStates.length 0)
  result.1.reverse

def planPressure? (maxFrameWords cap : Nat) (program : Program) :
    Option Locals.Allocation.ProgramPlan := do
  let recipe ← AllocationSupport.planRecipe? maxFrameWords program
  planAllocation? maxFrameWords (pressureStackSlots recipe cap) program

theorem planPressure?_wellFormed
    {maxFrameWords cap : Nat} {program : Program}
    {allocation : Locals.Allocation.ProgramPlan}
    (hPlan : planPressure? maxFrameWords cap program = some allocation) :
    allocation.WellFormed := by
  unfold planPressure? at hPlan
  cases hRecipe : AllocationSupport.planRecipe? maxFrameWords program with
  | none => simp [hRecipe] at hPlan
  | some recipe =>
      exact planAllocation?_wellFormed (by simpa [hRecipe] using hPlan)

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
