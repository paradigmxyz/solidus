import EvmCompiler.Compiler.MemoryRelation
import EvmCompiler.Functions.AllocationSupport
import EvmCompiler.Functions.ObserverSemantics
import EvmCompiler.Structured.ObserverSemantics
import EvmYul.MachineStateOps

namespace EvmCompiler
namespace Functions
namespace AllocationObserverRelation

/-!
State and resource contracts for the adjacent Functions-to-allocated-
Expressions boundary.

The source owns named variables and the target realizes only the currently
live names through the checked allocation plan. Stack locations are indexed
from the top of the concrete EVM stack. Scratch locations are indexed from the
current activation's private frame base.

This module deliberately defines no lowering and no execution interpreter.
-/

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word
abbrev Plan := Locals.Allocation.Plan
abbrev Location := Locals.Allocation.LocalLocation
abbrev SourceState := Functions.ObserverSemantics.State
abbrev TargetState := Structured.ObserverSemantics.State

def scratchAddress (frameBase slot : Nat) : Nat :=
  frameBase + MemoryContract.wordBytes * slot

def currentStackOrder (plan : Plan) (live : List Locals.Name) :
    List Locals.Name :=
  plan.stackOrder.filter fun name => decide (name ∈ live)

theorem currentStackOrder_congr
    {plan : Plan} {left right : List Locals.Name}
    (hLive : ∀ name, name ∈ left ↔ name ∈ right) :
    currentStackOrder plan left = currentStackOrder plan right := by
  unfold currentStackOrder
  apply congrArg (fun predicate => plan.stackOrder.filter predicate)
  funext name
  by_cases hLeft : name ∈ left
  · have hRight : name ∈ right := (hLive name).mp hLeft
    simp [hLeft, hRight]
  · have hRight : name ∉ right := by
      intro hName
      exact hLeft ((hLive name).mpr hName)
    simp [hLeft, hRight]

theorem currentStackOrder_restrict
    {plan : Plan} {beforeLive afterLive : List Locals.Name}
    (hSubset : ∀ name, name ∈ afterLive → name ∈ beforeLive) :
    (currentStackOrder plan beforeLive).filter
        (fun name => decide (name ∈ afterLive)) =
      currentStackOrder plan afterLive := by
  unfold currentStackOrder
  rw [List.filter_filter]
  apply congrArg (fun predicate => plan.stackOrder.filter predicate)
  funext name
  by_cases hAfter : name ∈ afterLive
  · have hBefore : name ∈ beforeLive :=
      hSubset name hAfter
    simp [hAfter, hBefore]
  · simp [hAfter]

/--
Two allocation plans realize the same surviving locals.

Stack-location indices are plan-local metadata and may differ across lexical
scope plans; the filtered runtime order is required to agree. Scratch
locations instead retain their exact activation slot.
-/
inductive LocationAgrees : Location → Location → Prop where
  | stack (leftDepth rightDepth : Nat) :
      LocationAgrees (.stack leftDepth) (.stack rightDepth)
  | scratch (slot : Nat) :
      LocationAgrees (.scratch slot) (.scratch slot)

structure PlanAgreesOn
    (left right : Plan) (live : List Locals.Name) : Prop where
  stackOrder :
    currentStackOrder left live = currentStackOrder right live
  location :
    ∀ name,
      name ∈ live →
      ∃ leftLocation rightLocation,
        left.location? name = some leftLocation ∧
          right.location? name = some rightLocation ∧
          LocationAgrees leftLocation rightLocation

namespace PlanAgreesOn

theorem symm
    {left right : Plan} {live : List Locals.Name}
    (hAgree : PlanAgreesOn left right live) :
    PlanAgreesOn right left live := by
  refine ⟨hAgree.stackOrder.symm, ?_⟩
  intro name hLive
  obtain
      ⟨leftLocation, rightLocation,
        hLeft, hRight, hLocation⟩ :=
    hAgree.location name hLive
  refine ⟨rightLocation, leftLocation, hRight, hLeft, ?_⟩
  cases hLocation with
  | stack leftDepth rightDepth =>
      exact .stack rightDepth leftDepth
  | scratch slot =>
      exact .scratch slot

theorem mono
    {left right : Plan}
    {larger smaller : List Locals.Name}
    (hAgree : PlanAgreesOn left right larger)
    (hSubset : ∀ name, name ∈ smaller → name ∈ larger) :
    PlanAgreesOn left right smaller := by
  refine ⟨?_, ?_⟩
  · calc
      currentStackOrder left smaller =
          (currentStackOrder left larger).filter
            (fun name => decide (name ∈ smaller)) :=
        (currentStackOrder_restrict hSubset).symm
      _ =
          (currentStackOrder right larger).filter
            (fun name => decide (name ∈ smaller)) := by
        rw [hAgree.stackOrder]
      _ = currentStackOrder right smaller :=
        currentStackOrder_restrict hSubset
  · intro name hLive
    exact hAgree.location name (hSubset name hLive)

end PlanAgreesOn

/--
Every source local that is semantically live has already been initialized.

Allocation plans include declarations that may not have executed yet, so this
cannot be inferred from plan well-formedness alone. Recursive source execution
maintains it as a source-facing invariant.
-/
def LiveDefined (live : List Locals.Name) (source : Locals.Source.State) :
    Prop :=
  ∀ name, name ∈ live → ∃ value, source.vars name = some value

namespace LiveDefined

/--
A successful simultaneous lookup proves that every requested name is defined.
-/
theorem of_lookupMany
    {names : List Locals.Name} {source : Locals.Source.State}
    {values : List Word}
    (hLookup :
      Functions.Source.Store.lookupMany names source.vars =
        some values) :
    LiveDefined names source := by
  induction names generalizing values with
  | nil =>
      intro name hName
      simp at hName
  | cons head tail ih =>
      cases hHead : source.vars head with
      | none =>
          simp [Functions.Source.Store.lookupMany, hHead] at hLookup
      | some value =>
          cases hTail :
              Functions.Source.Store.lookupMany tail source.vars with
          | none =>
              simp [Functions.Source.Store.lookupMany, hHead, hTail] at hLookup
          | some tailValues =>
              simp [Functions.Source.Store.lookupMany, hHead, hTail] at hLookup
              subst values
              intro name hName
              rcases List.mem_cons.mp hName with hName | hName
              · subst name
                exact ⟨value, hHead⟩
              · exact ih hTail name hName

/--
Definedness composes across concatenated source scopes.
-/
theorem append
    {left right : List Locals.Name} {source : Locals.Source.State}
    (hLeft : LiveDefined left source)
    (hRight : LiveDefined right source) :
    LiveDefined (left ++ right) source := by
  intro name hName
  rcases List.mem_append.mp hName with hName | hName
  · exact hLeft name hName
  · exact hRight name hName

/--
Definedness is insensitive to the list orientation used by the runtime stack.
-/
theorem reverse
    {names : List Locals.Name} {source : Locals.Source.State}
    (hDefined : LiveDefined names source) :
    LiveDefined names.reverse source := by
  intro name hName
  exact hDefined name (by simpa using hName)

theorem congr_vars
    {live : List Locals.Name}
    {source final : Locals.Source.State}
    (hDefined : LiveDefined live source)
    (hVars : final.vars = source.vars) :
    LiveDefined live final := by
  intro name hLive
  rw [hVars]
  exact hDefined name hLive

theorem insert_preserves
    {live : List Locals.Name}
    {source : Locals.Source.State}
    {name : Locals.Name} {value : Word}
    (hDefined : LiveDefined live source) :
    LiveDefined live (source.insert name value) := by
  intro other hLive
  by_cases hName : other = name
  · subst other
    exact ⟨value, Locals.Source.Store.insert_self _ _ _⟩
  · obtain ⟨old, hOld⟩ := hDefined other hLive
    exact
      ⟨old, by
        simpa [Locals.Source.State.insert] using
          (Locals.Source.Store.insert_of_ne
            (store := source.vars) (name := name)
            (other := other) (value := value) hName).trans hOld⟩

theorem insert_cons
    {live : List Locals.Name}
    {source : Locals.Source.State}
    {name : Locals.Name} {value : Word}
    (hDefined : LiveDefined live source) :
    LiveDefined (name :: live) (source.insert name value) := by
  intro other hLive
  rcases List.mem_cons.mp hLive with hName | hLive
  · subst other
    exact ⟨value, Locals.Source.Store.insert_self _ _ _⟩
  · exact hDefined.insert_preserves other hLive

/--
Assigning a list of existing source locals cannot make any live local
undefined.
-/
theorem assignMany_preserves
    {live names : List Locals.Name}
    {values : List Word}
    {source : Locals.Source.State}
    {finalStore : Locals.Source.Store}
    (hDefined : LiveDefined live source)
    (hAssign :
      Functions.Source.Store.assignMany names values source.vars =
        some finalStore) :
    LiveDefined live (source.withVars finalStore) := by
  induction names generalizing values source with
  | nil =>
      cases values with
      | nil =>
          simp [Functions.Source.Store.assignMany] at hAssign
          subst finalStore
          simpa [Locals.Source.State.withVars] using hDefined
      | cons value values =>
          simp [Functions.Source.Store.assignMany] at hAssign
  | cons name names ih =>
      cases values with
      | nil =>
          simp [Functions.Source.Store.assignMany] at hAssign
      | cons value values =>
          change
            (if source.vars.contains name then
                Functions.Source.Store.assignMany names values
                  (Locals.Source.Store.insert source.vars name value)
              else none) =
              some finalStore at hAssign
          by_cases hContains : source.vars.contains name = true
          · simp [hContains] at hAssign
            have hTail :
                Functions.Source.Store.assignMany names values
                    (source.insert name value).vars =
                  some finalStore := by
              simpa [Locals.Source.State.insert] using hAssign
            exact
              ih (source := source.insert name value) (values := values)
                hDefined.insert_preserves hTail
          · simp [hContains] at hAssign

theorem restrictTo
    {beforeLive afterLive : List Locals.Name}
    {source : Locals.Source.State}
    (hDefined : LiveDefined beforeLive source)
    (hSubset : ∀ name, name ∈ afterLive → name ∈ beforeLive) :
    LiveDefined afterLive (source.restrictTo afterLive) := by
  intro name hLive
  obtain ⟨value, hValue⟩ :=
    hDefined name (hSubset name hLive)
  exact
    ⟨value, by
      simpa [Locals.Source.State.restrictTo] using
        (Locals.Source.Store.restrictTo_mem
          (scope := afterLive) (store := source.vars) hLive).trans hValue⟩

end LiveDefined

theorem lookupMany_of_liveDefined
    {live names : List Locals.Name} {source : Locals.Source.State}
    (hDefined : LiveDefined live source)
    (hSubset : ∀ name, name ∈ names → name ∈ live) :
    ∃ values,
      Functions.Source.Store.lookupMany names source.vars =
        some values := by
  induction names with
  | nil =>
      exact ⟨[], rfl⟩
  | cons name names ih =>
      obtain ⟨value, hValue⟩ :=
        hDefined name (hSubset name (by simp))
      obtain ⟨values, hValues⟩ :=
        ih (fun other hOther => hSubset other (by simp [hOther]))
      exact ⟨value :: values, by
        simp [Functions.Source.Store.lookupMany, hValue, hValues]⟩

theorem currentStackOrder_nodup
    {plan : Plan} {live : List Locals.Name}
    (hWF : plan.WellFormed) :
    (currentStackOrder plan live).Nodup := by
  rcases hWF with
    ⟨_hBindings, _hScope, _hLength,
      ⟨hStackNodup, _hStackScope⟩,
      _hValid, _hScratch, _hKeys, _hIntervals, _hCalls, _hReturns⟩
  exact hStackNodup.filter _

theorem mem_live_of_mem_currentStackOrder
    {plan : Plan} {live : List Locals.Name} {name : Locals.Name}
    (hMem : name ∈ currentStackOrder plan live) :
    name ∈ live := by
  simp [currentStackOrder] at hMem
  exact hMem.2

/--
Realization of the source store for names that are live at the current
semantic point.

Allocation plans describe an entire lexical scope, including declarations
that may not have executed yet. Their stack depths are therefore final-scope
depths, not necessarily current runtime depths. The current stack order is the
plan's final stack order filtered to names that are live at this semantic
point. This also handles function entry, whose source scope and concrete stack
use different list orientations.
-/
def StoreRel (plan : Plan) (live : List Locals.Name)
    (stackOffset frameBase : Nat) (source : Locals.Source.State)
    (target : Structured.RunState) : Prop :=
  ∀ name location,
    name ∈ live →
    plan.location? name = some location →
    match location with
    | .stack _ =>
        ∃ depth,
          Locals.Layout.lookupDepth?
              name (currentStackOrder plan live) =
            some (depth + 1) ∧
          target.evm.stack[stackOffset + depth]? = source.vars name
    | .scratch slot =>
        target.evm.toMachineState.lookupMemory
            (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) =
          (source.vars name).getD (EvmYul.UInt256.ofNat 0)

/--
The shared-state portion of allocation correctness.

Primitive-family proofs use this relation without acquiring ownership of the
allocation plan, concrete stack layout, or local-variable realization.
-/
structure SharedRel
    (contract : MemoryContract.Contract)
    (source target : EvmYul.SharedState .EVM) : Prop where
  machine :
    Compiler.MemoryRelation.MachineRel contract
      source.toMachineState target.toMachineState
  world :
    source.toState = target.toState

structure CoreRel
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name) (stackOffset frameBase : Nat)
    (source : Locals.Source.State) (target : Structured.RunState) :
    Prop where
  machine :
    Compiler.MemoryRelation.MachineRel contract
      source.shared.toMachineState
      target.evm.toMachineState
  world :
    source.shared.toState = target.evm.toSharedState.toState
  store : StoreRel plan live stackOffset frameBase source target

namespace SharedRel

theorem executionEnv_eq
    {contract : MemoryContract.Contract}
    {source target : EvmYul.SharedState .EVM}
    (hRel : SharedRel contract source target) :
    source.executionEnv = target.executionEnv :=
  congrArg EvmYul.State.executionEnv hRel.world

theorem replaceToState_same
    {contract : MemoryContract.Contract}
    {source target : EvmYul.SharedState .EVM}
    (hRel : SharedRel contract source target)
    (world : EvmYul.State .EVM) :
    SharedRel contract
      ({ source with toState := world } : EvmYul.SharedState .EVM)
      ({ target with toState := world } : EvmYul.SharedState .EVM) := by
  exact ⟨by simpa using hRel.machine, rfl⟩

end SharedRel

namespace CoreRel

theorem shared
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hRel :
      CoreRel contract plan live stackOffset frameBase source target) :
    SharedRel contract source.shared target.evm.toSharedState :=
  ⟨hRel.machine, hRel.world⟩

end CoreRel

structure StateRel {transcript : Trace}
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name) (stackOffset frameBase : Nat)
    (source : SourceState transcript) (target : TargetState transcript) :
    Prop where
  cursor : source.cursor = target.cursor
  core :
    CoreRel contract plan live stackOffset frameBase
      source.source target.source

namespace StoreRel

theorem restrict {plan : Plan} {smaller larger : List Locals.Name}
    {stackOffset frameBase : Nat} {source : Locals.Source.State}
    {target : Structured.RunState}
    (hRel : StoreRel plan larger stackOffset frameBase source target)
    (hSubset : ∀ name, name ∈ smaller → name ∈ larger)
    (hStackOrder :
      currentStackOrder plan smaller =
        currentStackOrder plan larger) :
    StoreRel plan smaller stackOffset frameBase source target := by
  intro name location hLive hLocation
  have hValue := hRel name location (hSubset name hLive) hLocation
  cases location with
  | stack planDepth =>
      rcases hValue with ⟨depth, hDepth, hValue⟩
      exact ⟨depth, by simpa [hStackOrder] using hDepth, hValue⟩
  | scratch slot =>
      exact hValue

theorem stack_at {plan : Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat} {source : Locals.Source.State}
    {target : Structured.RunState} {name : Locals.Name}
    {planDepth depth : Nat}
    (hRel : StoreRel plan live stackOffset frameBase source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hDepth :
      Locals.Layout.lookupDepth? name (currentStackOrder plan live) =
        some (depth + 1)) :
    target.evm.stack[stackOffset + depth]? = source.vars name :=
  by
    obtain ⟨actualDepth, hActualDepth, hValue⟩ :=
      hRel name (.stack planDepth) hLive hLocation
    rw [hDepth] at hActualDepth
    cases hActualDepth
    exact hValue

theorem scratch {plan : Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat} {source : Locals.Source.State}
    {target : Structured.RunState} {name : Locals.Name} {slot : Nat}
    (hRel : StoreRel plan live stackOffset frameBase source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot)) :
    target.evm.toMachineState.lookupMemory
        (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) =
      (source.vars name).getD (EvmYul.UInt256.ofNat 0) := by
  exact hRel name (.scratch slot) hLive hLocation

theorem rebase_prefix_of_lookup
    {plan : Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {source sourceFinal : Locals.Source.State}
    {target targetFinal : Structured.RunState}
    {oldPrefix newPrefix baseStack : List Word}
    (hRel :
      StoreRel plan live (stackOffset + oldPrefix.length) frameBase
        source target)
    (hOldStack : target.evm.stack = oldPrefix ++ baseStack)
    (hNewStack : targetFinal.evm.stack = newPrefix ++ baseStack)
    (hScratch :
      ∀ name slot,
        name ∈ live →
        plan.location? name = some (.scratch slot) →
        targetFinal.evm.toMachineState.lookupMemory
            (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) =
          target.evm.toMachineState.lookupMemory
            (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)))
    (hVars : sourceFinal.vars = source.vars) :
    StoreRel plan live (stackOffset + newPrefix.length) frameBase
      sourceFinal targetFinal := by
  intro name location hLive hLocation
  have hValue := hRel name location hLive hLocation
  cases location with
  | stack planDepth =>
      rcases hValue with ⟨depth, hDepth, hValue⟩
      refine ⟨depth, hDepth, ?_⟩
      change
        targetFinal.evm.stack[
            stackOffset + newPrefix.length + depth]? =
          sourceFinal.vars name
      change
        target.evm.stack[
            stackOffset + oldPrefix.length + depth]? =
          source.vars name at hValue
      rw [hOldStack] at hValue
      have hBase :
          baseStack[stackOffset + depth]? = source.vars name := by
        rw [show
            stackOffset + oldPrefix.length + depth =
              oldPrefix.length + (stackOffset + depth) by omega]
          at hValue
        rw [List.getElem?_append_right
          (Nat.le_add_right oldPrefix.length (stackOffset + depth))]
          at hValue
        simpa using hValue
      rw [hNewStack, hVars]
      rw [show
          stackOffset + newPrefix.length + depth =
            newPrefix.length + (stackOffset + depth) by omega]
      rw [List.getElem?_append_right
        (Nat.le_add_right newPrefix.length (stackOffset + depth))]
      simpa using hBase
  | scratch slot =>
      simpa [hScratch name slot hLive hLocation, hVars] using hValue

theorem rebase_prefix
    {plan : Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {source sourceFinal : Locals.Source.State}
    {target targetFinal : Structured.RunState}
    {oldPrefix newPrefix baseStack : List Word}
    (hRel :
      StoreRel plan live (stackOffset + oldPrefix.length) frameBase
        source target)
    (hOldStack : target.evm.stack = oldPrefix ++ baseStack)
    (hNewStack : targetFinal.evm.stack = newPrefix ++ baseStack)
    (hMachine :
      targetFinal.evm.toMachineState = target.evm.toMachineState)
    (hVars : sourceFinal.vars = source.vars) :
    StoreRel plan live (stackOffset + newPrefix.length) frameBase
      sourceFinal targetFinal := by
  apply rebase_prefix_of_lookup hRel hOldStack hNewStack _ hVars
  intro name slot hLive hLocation
  simp [hMachine]

theorem rebase_prefix_stack_only
    {plan : Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {source sourceFinal : Locals.Source.State}
    {target targetFinal : Structured.RunState}
    {oldPrefix newPrefix baseStack : List Word}
    (hOnly :
      ∀ name slot,
        name ∈ live →
        plan.location? name = some (.scratch slot) →
        False)
    (hRel :
      StoreRel plan live (stackOffset + oldPrefix.length) frameBase
        source target)
    (hOldStack : target.evm.stack = oldPrefix ++ baseStack)
    (hNewStack : targetFinal.evm.stack = newPrefix ++ baseStack)
    (hVars : sourceFinal.vars = source.vars) :
    StoreRel plan live (stackOffset + newPrefix.length) frameBase
      sourceFinal targetFinal := by
  apply
    rebase_prefix_of_lookup hRel hOldStack hNewStack
      (fun name slot hLive hLocation =>
        False.elim (hOnly name slot hLive hLocation))
      hVars

theorem transport_plan
    {left right : Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hRel :
      StoreRel left live stackOffset frameBase source target)
    (hAgree : PlanAgreesOn left right live) :
    StoreRel right live stackOffset frameBase source target := by
  intro name rightLocation hLive hRightLocation
  obtain
      ⟨leftLocation, agreedRightLocation,
        hLeftLocation, hAgreedRightLocation, hLocationAgree⟩ :=
    hAgree.location name hLive
  rw [hRightLocation] at hAgreedRightLocation
  cases hAgreedRightLocation
  cases hLocationAgree with
  | stack leftDepth rightDepth =>
      obtain ⟨depth, hDepth, hValue⟩ :=
        hRel name (.stack leftDepth) hLive hLeftLocation
      refine ⟨depth, ?_, hValue⟩
      rw [← hAgree.stackOrder]
      exact hDepth
  | scratch slot =>
      exact hRel name (.scratch slot) hLive hLeftLocation

end StoreRel

namespace StateRel

/--
Restricting the source store to exactly the live names already represented by
the target preserves the allocation relation.
-/
theorem restrict_source_live {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    (hRel :
      StateRel contract plan live stackOffset frameBase source target) :
    StateRel contract plan live stackOffset frameBase
      ((Functions.ObserverSemantics.stateModel transcript).restrictTo
        live source)
      target := by
  refine ⟨hRel.cursor, ?_⟩
  refine
    ⟨by
      simpa [Functions.ObserverSemantics.stateModel,
        Locals.ObserverSemantics.stateModel,
        Locals.Source.Effectful.StateModel.restrictTo,
        Locals.Source.State.restrictTo] using hRel.core.machine,
      by
        simpa [Functions.ObserverSemantics.stateModel,
          Locals.ObserverSemantics.stateModel,
          Locals.Source.Effectful.StateModel.restrictTo,
          Locals.Source.State.restrictTo] using hRel.core.world,
      ?_⟩
  intro name location hLive hLocation
  have hValue := hRel.core.store name location hLive hLocation
  cases location with
  | stack depth =>
      rcases hValue with ⟨actualDepth, hDepth, hStack⟩
      exact
        ⟨actualDepth, hDepth,
          by
            simpa [Functions.ObserverSemantics.stateModel,
              Locals.ObserverSemantics.stateModel,
              Locals.Source.Effectful.StateModel.restrictTo,
              Locals.Source.State.restrictTo,
              Locals.Source.Store.restrictTo, hLive] using hStack⟩
  | scratch slot =>
      simpa [Functions.ObserverSemantics.stateModel,
        Locals.ObserverSemantics.stateModel,
        Locals.Source.Effectful.StateModel.restrictTo,
        Locals.Source.State.restrictTo,
        Locals.Source.Store.restrictTo, hLive] using hValue

def pushTargetBy {transcript : Trace} (pcDelta : Nat) (value : Word)
    (target : TargetState transcript) : TargetState transcript :=
  target.withSource
    (target.source.withEVM
      (target.source.evm.replaceStackAndIncrPC
        (value :: target.source.evm.stack) (pcΔ := pcDelta)))

def pushTarget {transcript : Trace} (value : Word)
    (target : TargetState transcript) : TargetState transcript :=
  pushTargetBy 1 value target

def contractTargetBy {transcript : Trace} (pcDelta : Nat)
    (value : Word) (rest : List Word)
    (target : TargetState transcript) : TargetState transcript :=
  target.withSource
    (target.source.withEVM
      (target.source.evm.replaceStackAndIncrPC
        (value :: rest) (pcΔ := pcDelta)))

def mstoreTarget {transcript : Trace}
    (address value : Word) (rest : List Word)
    (target : TargetState transcript) : TargetState transcript :=
  target.withSource
    (target.source.withEVM
      (({ target.source.evm with
          toMachineState :=
            target.source.evm.toMachineState.mstore address value }).replaceStackAndIncrPC
        rest))

def replaceStackBy {transcript : Trace} (pcDelta : Nat)
    (stack : List Word) (target : TargetState transcript) :
    TargetState transcript :=
  target.withSource
    (target.source.withEVM
      (target.source.evm.replaceStackAndIncrPC stack (pcΔ := pcDelta)))

def popTarget {transcript : Trace}
    (stack : List Word) (target : TargetState transcript) :
    TargetState transcript :=
  target.withSource
    (target.source.withEVM
      { target.source.evm with stack := stack })

theorem mono {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {smaller larger : List Locals.Name} {stackOffset frameBase : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    (hRel :
      StateRel contract plan larger stackOffset frameBase source target)
    (hSubset : ∀ name, name ∈ smaller → name ∈ larger)
    (hStackOrder :
      currentStackOrder plan smaller =
        currentStackOrder plan larger) :
    StateRel contract plan smaller stackOffset frameBase source target :=
  ⟨hRel.cursor,
    ⟨hRel.core.machine, hRel.core.world,
      hRel.core.store.restrict hSubset hStackOrder⟩⟩

theorem transport_plan {transcript : Trace}
    {contract : MemoryContract.Contract}
    {left right : Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {source : SourceState transcript}
    {target : TargetState transcript}
    (hRel :
      StateRel contract left live stackOffset frameBase source target)
    (hAgree : PlanAgreesOn left right live) :
    StateRel contract right live stackOffset frameBase source target :=
  ⟨hRel.cursor,
    ⟨hRel.core.machine, hRel.core.world,
      hRel.core.store.transport_plan hAgree⟩⟩

/--
Discarding a prefix of stack-resident locals and restricting the source store
to the surviving live scope re-establishes the allocation relation at stack
offset zero.

This is the semantic core of plain Locals cleanup. The actual `POP` execution
and compiler equation are owned by the allocation cleanup module.
-/
theorem restrict_drop_stack_prefix {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {beforeLive afterLive dropped : List Locals.Name}
    {frameBase : Nat}
    {source : SourceState transcript}
    {target targetFinal : TargetState transcript}
    (hRel :
      StateRel contract plan beforeLive 0 frameBase source target)
    (hWF : plan.WellFormed)
    (hSubset : ∀ name, name ∈ afterLive → name ∈ beforeLive)
    (hOrder :
      currentStackOrder plan beforeLive =
        dropped ++ currentStackOrder plan afterLive)
    (hCursor : targetFinal.cursor = target.cursor)
    (hShared :
      targetFinal.source.evm.toSharedState =
        target.source.evm.toSharedState)
    (hStack :
      targetFinal.source.evm.stack =
        target.source.evm.stack.drop dropped.length) :
    StateRel contract plan afterLive 0 frameBase
      ((Functions.ObserverSemantics.stateModel transcript).restrictTo
        afterLive source)
      targetFinal := by
  let sourceFinal :=
    (Functions.ObserverSemantics.stateModel transcript).restrictTo
      afterLive source
  have hSourceCursor : sourceFinal.cursor = source.cursor := by
    rfl
  have hSourceShared :
      sourceFinal.source.shared = source.source.shared := by
    rfl
  refine ⟨?_, ?_⟩
  · rw [hSourceCursor, hCursor]
    exact hRel.cursor
  · refine ⟨?_, ?_, ?_⟩
    · rw [hSourceShared, hShared]
      exact hRel.core.machine
    · rw [hSourceShared, hShared]
      exact hRel.core.world
    · intro name location hAfterLive hLocation
      have hBeforeLive := hSubset name hAfterLive
      have hOld :=
        hRel.core.store name location hBeforeLive hLocation
      cases location with
      | scratch slot =>
          change
            targetFinal.source.evm.toMachineState.lookupMemory
                (EvmYul.UInt256.ofNat
                  (scratchAddress frameBase slot)) =
              (sourceFinal.source.vars name).getD
                (EvmYul.UInt256.ofNat 0)
          have hVars :
              sourceFinal.source.vars name = source.source.vars name := by
            simp [sourceFinal, Functions.ObserverSemantics.stateModel,
              Locals.ObserverSemantics.stateModel,
              Locals.Source.Effectful.StateModel.restrictTo,
              Locals.Source.State.restrictTo,
              Locals.Source.Store.restrictTo, hAfterLive]
          rw [hVars, hShared]
          exact hOld
      | stack planDepth =>
          rcases hOld with ⟨oldDepth, hOldDepth, hOldValue⟩
          have hNameBefore :
              name ∈ currentStackOrder plan beforeLive :=
            Locals.Layout.mem_of_lookupDepth?_eq_some hOldDepth
          have hPlanStack : name ∈ plan.stackOrder := by
            simp [currentStackOrder] at hNameBefore
            exact hNameBefore.1
          have hNameAfter :
              name ∈ currentStackOrder plan afterLive := by
            simp [currentStackOrder, hPlanStack, hAfterLive]
          obtain ⟨afterDepth, hAfterDepth⟩ :=
            Locals.Layout.exists_lookupDepth?_eq_some_of_mem hNameAfter
          have hBeforeNodup :=
            currentStackOrder_nodup (live := beforeLive) hWF
          rw [hOrder] at hBeforeNodup
          have hDisjoint :
              List.Disjoint dropped
                (currentStackOrder plan afterLive) :=
            List.disjoint_of_nodup_append hBeforeNodup
          have hNameNotDropped : name ∉ dropped := by
            intro hDropped
            exact
              (List.disjoint_left.mp hDisjoint)
                hDropped hNameAfter
          have hExpectedDepth :
              Locals.Layout.lookupDepth? name
                  (currentStackOrder plan beforeLive) =
                some (dropped.length + (afterDepth + 1)) := by
            rw [hOrder]
            exact
              Locals.Layout.lookupDepth?_append_of_not_mem
                hNameNotDropped hAfterDepth
          have hOldDepthEq :
              oldDepth = dropped.length + afterDepth := by
            rw [hExpectedDepth] at hOldDepth
            have :=
              Option.some.inj hOldDepth
            omega
          refine ⟨afterDepth, hAfterDepth, ?_⟩
          have hVars :
              sourceFinal.source.vars name = source.source.vars name := by
            simp [sourceFinal, Functions.ObserverSemantics.stateModel,
              Locals.ObserverSemantics.stateModel,
              Locals.Source.Effectful.StateModel.restrictTo,
              Locals.Source.State.restrictTo,
              Locals.Source.Store.restrictTo, hAfterLive]
          rw [hStack, hVars]
          simpa [List.getElem?_drop, hOldDepthEq,
            Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hOldValue

theorem push_target_by {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    (pcDelta : Nat) (value : Word)
    (hRel :
      StateRel contract plan live stackOffset frameBase source target) :
    StateRel contract plan live (stackOffset + 1) frameBase source
      (pushTargetBy pcDelta value target) := by
  refine ⟨hRel.cursor, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [pushTargetBy, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.core.machine
  · simpa [pushTargetBy, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.core.world
  · intro name location hLive hLocation
    have hValue :=
      hRel.core.store name location hLive hLocation
    cases location with
    | stack planDepth =>
        rcases hValue with ⟨depth, hDepth, hValue⟩
        refine ⟨depth, hDepth, ?_⟩
        change
          (value :: target.source.evm.stack)[stackOffset + 1 + depth]? =
            source.source.vars name
        rw [show stackOffset + 1 + depth =
            (stackOffset + depth) + 1 by omega]
        simpa using hValue
    | scratch slot =>
        simpa [pushTargetBy,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] using hValue

theorem push_target {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    (value : Word)
    (hRel :
      StateRel contract plan live stackOffset frameBase source target) :
    StateRel contract plan live (stackOffset + 1) frameBase source
      (pushTarget value target) := by
  exact push_target_by 1 value hRel

theorem pop_target {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {value : Word} {rest : List Word}
    (hRel :
      StateRel contract plan live (stackOffset + 1) frameBase
        source target)
    (hStack : target.source.evm.stack = value :: rest) :
    StateRel contract plan live stackOffset frameBase source
      (popTarget rest target) := by
  refine ⟨hRel.cursor, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [popTarget] using hRel.core.machine
  · simpa [popTarget] using hRel.core.world
  · intro name location hLive hLocation
    have hValue :=
      hRel.core.store name location hLive hLocation
    cases location with
    | stack planDepth =>
        rcases hValue with ⟨depth, hDepth, hValue⟩
        refine ⟨depth, hDepth, ?_⟩
        change rest[stackOffset + depth]? = source.source.vars name
        change
          target.source.evm.stack[stackOffset + 1 + depth]? =
            source.source.vars name at hValue
        rw [hStack] at hValue
        simpa [show stackOffset + 1 + depth =
            (stackOffset + depth) + 1 by omega] using hValue
    | scratch slot =>
        simpa [popTarget] using hValue

theorem contract_target_by {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {right left value : Word} {rest : List Word}
    (hRel :
      StateRel contract plan live (stackOffset + 2) frameBase
        source target)
    (hStack : target.source.evm.stack = right :: left :: rest)
    (pcDelta : Nat) :
    StateRel contract plan live (stackOffset + 1) frameBase source
      (contractTargetBy pcDelta value rest target) := by
  refine ⟨hRel.cursor, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [contractTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.core.machine
  · simpa [contractTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.core.world
  · intro name location hLive hLocation
    have hValue :=
      hRel.core.store name location hLive hLocation
    cases location with
    | stack planDepth =>
        rcases hValue with ⟨depth, hDepth, hValue⟩
        refine ⟨depth, hDepth, ?_⟩
        change
          (value :: rest)[stackOffset + 1 + depth]? =
            source.source.vars name
        change
          target.source.evm.stack[stackOffset + 2 + depth]? =
            source.source.vars name at hValue
        rw [hStack] at hValue
        have hRest :
            rest[stackOffset + depth]? = source.source.vars name := by
          simpa [show stackOffset + 2 + depth =
              (stackOffset + depth) + 2 by omega] using hValue
        simpa [show stackOffset + 1 + depth =
            (stackOffset + depth) + 1 by omega] using hRest
    | scratch slot =>
        simpa [contractTargetBy,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] using hValue

theorem replace_top_by {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {old value : Word} {rest : List Word}
    (hRel :
      StateRel contract plan live (stackOffset + 1) frameBase
        source target)
    (hStack : target.source.evm.stack = old :: rest)
    (pcDelta : Nat) :
    StateRel contract plan live (stackOffset + 1) frameBase source
      (contractTargetBy pcDelta value rest target) := by
  refine ⟨hRel.cursor, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [contractTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.core.machine
  · simpa [contractTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.core.world
  · intro name location hLive hLocation
    have hValue :=
      hRel.core.store name location hLive hLocation
    cases location with
    | stack planDepth =>
        rcases hValue with ⟨depth, hDepth, hValue⟩
        refine ⟨depth, hDepth, ?_⟩
        change
          (value :: rest)[stackOffset + 1 + depth]? =
            source.source.vars name
        change
          target.source.evm.stack[stackOffset + 1 + depth]? =
            source.source.vars name at hValue
        rw [hStack] at hValue
        simpa [show stackOffset + 1 + depth =
            (stackOffset + depth) + 1 by omega] using hValue
    | scratch slot =>
        simpa [contractTargetBy,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] using hValue

theorem consume_forward {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {kind : Assembly.ResourceObserver} {value : Word}
    {source source' : SourceState transcript}
    {target : TargetState transcript}
    (hRel :
      StateRel contract plan live stackOffset frameBase source target)
    (hConsume :
      Simulation.ResourceReplay.consume? kind source =
        some (value, source')) :
    ∃ target' : TargetState transcript,
      Simulation.ResourceReplay.consume? kind target =
          some (value, target') ∧
        StateRel contract plan live stackOffset frameBase
          source' target' := by
  obtain ⟨target', hTarget, hCursor, hCore⟩ :=
    Simulation.ResourceReplay.consume?_rel
      hRel.cursor hRel.core hConsume
  exact ⟨target', hTarget, hCursor, hCore⟩

theorem consume_backward {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {kind : Assembly.ResourceObserver} {value : Word}
    {source : SourceState transcript}
    {target target' : TargetState transcript}
    (hRel :
      StateRel contract plan live stackOffset frameBase source target)
    (hConsume :
      Simulation.ResourceReplay.consume? kind target =
        some (value, target')) :
    ∃ source' : SourceState transcript,
      Simulation.ResourceReplay.consume? kind source =
          some (value, source') ∧
        StateRel contract plan live stackOffset frameBase
          source' target' := by
  obtain ⟨source', hSource, hCursor, hCore⟩ :=
    Simulation.ResourceReplay.consume?_rel
      (rel := fun target source =>
        CoreRel contract plan live stackOffset frameBase source target)
      hRel.cursor.symm hRel.core hConsume
  exact ⟨source', hSource, hCursor.symm, hCore⟩

/--
A stack declaration consumes the expression result at the top of the target
stack and turns it into the new live named local.

This is the representation-neutral core of declaration preservation. The
scratch-frame wrapper additionally shifts its hidden frame-pointer depth.
-/
theorem declare_stack_live
    {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {beforeLive afterLive : List Locals.Name}
    {frameBase planDepth : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {value : Word} {rest : List Word}
    (hRel :
      StateRel contract plan beforeLive 1 frameBase source target)
    (hStack : target.source.evm.stack = value :: rest)
    (hAfter :
      ∀ other, other ∈ afterLive →
        other = name ∨ other ∈ beforeLive)
    (hNameAfter : name ∈ afterLive)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hStackOrder :
      currentStackOrder plan afterLive =
        name :: currentStackOrder plan beforeLive) :
    StateRel contract plan afterLive 0 frameBase
      (source.withSource (source.source.insert name value)) target := by
  refine ⟨?_, ?_⟩
  · simpa [Simulation.ResourceReplay.State.withSource] using hRel.cursor
  · refine ⟨?_, ?_, ?_⟩
    · simpa [Simulation.ResourceReplay.State.withSource,
        Locals.Source.State.insert] using hRel.core.machine
    · simpa [Simulation.ResourceReplay.State.withSource,
        Locals.Source.State.insert] using hRel.core.world
    · intro other location hOtherAfter hOtherLocation
      by_cases hName : other = name
      · subst other
        cases location with
        | stack otherPlanDepth =>
            rw [hLocation] at hOtherLocation
            cases hOtherLocation
            refine ⟨0, ?_, ?_⟩
            · simp [hStackOrder, Locals.Layout.lookupDepth?,
                Locals.Layout.lookupDepthFrom]
            · rw [hStack]
              simp [Simulation.ResourceReplay.State.withSource,
                Locals.Source.State.insert]
        | scratch slot =>
            rw [hLocation] at hOtherLocation
            simp at hOtherLocation
      · have hOtherBefore : other ∈ beforeLive := by
          rcases hAfter other hOtherAfter with hEq | hBefore
          · exact False.elim (hName hEq)
          · exact hBefore
        have hOld :=
          hRel.core.store other location hOtherBefore hOtherLocation
        cases location with
        | stack otherPlanDepth =>
            rcases hOld with ⟨depth, hDepth, hValue⟩
            refine ⟨depth + 1, ?_, ?_⟩
            · rw [hStackOrder]
              simpa [Nat.add_assoc] using
                (Locals.Layout.lookupDepth?_cons_of_ne
                  (Ne.symm hName) hDepth)
            · simpa [Simulation.ResourceReplay.State.withSource,
                Locals.Source.State.insert,
                Locals.Source.Store.insert_of_ne hName,
                Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hValue
        | scratch slot =>
            change
              target.source.evm.toMachineState.lookupMemory
                  (EvmYul.UInt256.ofNat
                    (scratchAddress frameBase slot)) =
                (Locals.Source.Store.insert
                  source.source.vars name value other).getD
                    (EvmYul.UInt256.ofNat 0)
            rw [Locals.Source.Store.insert_of_ne hName]
            exact hOld

/--
Replace one live stack local with the expression result currently above the
local stack.

The dynamic depth is measured in `currentStackOrder`, not in the final
allocation plan. This is the state-level meaning of the compiler's
`SWAP depth; POP` assignment sequence.
-/
theorem assign_stack_live
    {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {frameBase planDepth depth : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {value old : Word} {rest : List Word}
    (hRel :
      StateRel contract plan live 1 frameBase source target)
    (hStack : target.source.evm.stack = value :: rest)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hDepth :
      Locals.Layout.lookupDepth? name (currentStackOrder plan live) =
        some (depth + 1))
    (hOld : source.source.vars name = some old) :
    StateRel contract plan live 0 frameBase
      (source.withSource (source.source.insert name value))
      (replaceStackBy 2 (rest.set depth value) target) := by
  have hAssigned :=
    hRel.core.store.stack_at hLive hLocation hDepth
  rw [hStack, hOld] at hAssigned
  have hRestAssigned : rest[depth]? = some old := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hAssigned
  have hDepthBound : depth < rest.length :=
    List.getElem?_eq_some_iff.mp hRestAssigned |>.1
  refine ⟨?_, ?_⟩
  · simpa [replaceStackBy, Simulation.ResourceReplay.State.withSource] using
      hRel.cursor
  · refine ⟨?_, ?_, ?_⟩
    · simpa [replaceStackBy, Simulation.ResourceReplay.State.withSource,
        Locals.Source.State.insert,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] using hRel.core.machine
    · simpa [replaceStackBy, Simulation.ResourceReplay.State.withSource,
        Locals.Source.State.insert,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] using hRel.core.world
    · intro other location hOtherLive hOtherLocation
      have hPrevious :=
        hRel.core.store other location hOtherLive hOtherLocation
      cases location with
      | stack otherPlanDepth =>
          rcases hPrevious with
            ⟨otherDepth, hOtherDepth, hOtherValue⟩
          refine ⟨otherDepth, hOtherDepth, ?_⟩
          simp only [replaceStackBy,
            Simulation.ResourceReplay.State.withSource,
            Locals.Source.State.insert,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC, Nat.zero_add]
          change
            (rest.set depth value)[otherDepth]? =
              Locals.Source.Store.insert
                source.source.vars name value other
          by_cases hName : other = name
          · subst other
            rw [hDepth] at hOtherDepth
            cases hOtherDepth
            rw [List.getElem?_set_eq_of_lt value hDepthBound]
            exact
              (Locals.Source.Store.insert_self
                source.source.vars name value).symm
          · have hDepthNe : depth ≠ otherDepth := by
              intro hEq
              have hOtherName :
                  other = name :=
                Locals.Layout.name_eq_of_lookupDepth?_eq_some
                  (by simpa [hEq] using hOtherDepth) hDepth
              exact hName hOtherName
            change
              target.source.evm.stack[1 + otherDepth]? =
                source.source.vars other at hOtherValue
            rw [hStack] at hOtherValue
            have hRestOther :
                rest[otherDepth]? = source.source.vars other := by
              simpa [show 1 + otherDepth = otherDepth + 1 by omega] using
                hOtherValue
            rw [List.getElem?_set_of_lt' value rest hDepthBound]
            simp [hDepthNe, hRestOther,
              Locals.Source.Store.insert_of_ne hName]
      | scratch slot =>
          change
            target.source.evm.toMachineState.lookupMemory
                (EvmYul.UInt256.ofNat
                  (scratchAddress frameBase slot)) =
              (Locals.Source.Store.insert
                source.source.vars name value other).getD
                (EvmYul.UInt256.ofNat 0)
          have hName : other ≠ name := by
            intro hEq
            subst other
            rw [hLocation] at hOtherLocation
            simp at hOtherLocation
          rw [Locals.Source.Store.insert_of_ne hName]
          exact hPrevious

/--
Assign a stack-resident local while an arbitrary temporary prefix remains
above the local layout.

The assigned value is the top stack item. `stackOffset` counts the other
temporary values retained after the compiler's `SWAP`/`POP` sequence.
-/
theorem assign_stack_live_at
    {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase planDepth depth : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {value old : Word} {rest : List Word}
    (hRel :
      StateRel contract plan live (stackOffset + 1) frameBase source target)
    (hStack : target.source.evm.stack = value :: rest)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hDepth :
      Locals.Layout.lookupDepth? name (currentStackOrder plan live) =
        some (depth + 1))
    (hOld : source.source.vars name = some old) :
    StateRel contract plan live stackOffset frameBase
      (source.withSource (source.source.insert name value))
      (replaceStackBy 2 (rest.set (stackOffset + depth) value) target) := by
  have hAssigned :=
    hRel.core.store.stack_at hLive hLocation hDepth
  rw [hStack, hOld] at hAssigned
  have hRestAssigned :
      rest[stackOffset + depth]? = some old := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hAssigned
  have hDepthBound : stackOffset + depth < rest.length :=
    List.getElem?_eq_some_iff.mp hRestAssigned |>.1
  refine ⟨?_, ?_⟩
  · simpa [replaceStackBy, Simulation.ResourceReplay.State.withSource] using
      hRel.cursor
  · refine ⟨?_, ?_, ?_⟩
    · simpa [replaceStackBy, Simulation.ResourceReplay.State.withSource,
        Locals.Source.State.insert,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] using hRel.core.machine
    · simpa [replaceStackBy, Simulation.ResourceReplay.State.withSource,
        Locals.Source.State.insert,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] using hRel.core.world
    · intro other location hOtherLive hOtherLocation
      have hPrevious :=
        hRel.core.store other location hOtherLive hOtherLocation
      cases location with
      | stack otherPlanDepth =>
          rcases hPrevious with
            ⟨otherDepth, hOtherDepth, hOtherValue⟩
          refine ⟨otherDepth, hOtherDepth, ?_⟩
          simp only [replaceStackBy,
            Simulation.ResourceReplay.State.withSource,
            Locals.Source.State.insert,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
          change
            (rest.set (stackOffset + depth) value)[
                stackOffset + otherDepth]? =
              Locals.Source.Store.insert
                source.source.vars name value other
          by_cases hName : other = name
          · subst other
            rw [hDepth] at hOtherDepth
            cases hOtherDepth
            rw [List.getElem?_set_eq_of_lt value hDepthBound]
            exact
              (Locals.Source.Store.insert_self
                source.source.vars name value).symm
          · have hDepthNe : depth ≠ otherDepth := by
              intro hEq
              have hOtherName :
                  other = name :=
                Locals.Layout.name_eq_of_lookupDepth?_eq_some
                  (by simpa [hEq] using hOtherDepth) hDepth
              exact hName hOtherName
            change
              target.source.evm.stack[
                  (stackOffset + 1) + otherDepth]? =
                source.source.vars other at hOtherValue
            rw [hStack] at hOtherValue
            have hRestOther :
                rest[stackOffset + otherDepth]? =
                  source.source.vars other := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                hOtherValue
            rw [List.getElem?_set_of_lt' value rest hDepthBound]
            simp [hDepthNe, hRestOther,
              Locals.Source.Store.insert_of_ne hName]
      | scratch slot =>
          change
            target.source.evm.toMachineState.lookupMemory
                (EvmYul.UInt256.ofNat
                  (scratchAddress frameBase slot)) =
              (Locals.Source.Store.insert
                source.source.vars name value other).getD
                (EvmYul.UInt256.ofNat 0)
          have hName : other ≠ name := by
            intro hEq
            subst other
            rw [hLocation] at hOtherLocation
            simp at hOtherLocation
          rw [Locals.Source.Store.insert_of_ne hName]
          exact hPrevious

end StateRel

/--
Additional realization facts for an activation that owns a scratch frame.

The hidden frame pointer is below any temporary expression results by
`stackOffset + frameDepth`. Frame acquisition preallocates every frame word,
so reads of compiler-owned slots do not subsequently change `MSIZE`.
-/
structure ScratchStateRel {transcript : Trace}
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name) (stackOffset frameBase frameDepth frameWords : Nat)
    (source : SourceState transcript) (target : TargetState transcript) :
    Prop where
  base :
    StateRel contract plan live stackOffset frameBase source target
  framePointer :
    target.source.evm.stack[stackOffset + frameDepth]? =
      some (EvmYul.UInt256.ofNat frameBase)
  frameActive :
    frameBase + MemoryContract.wordBytes * frameWords ≤
      target.source.evm.activeWords.toNat * MemoryContract.wordBytes
  frameAllocated :
    frameBase + MemoryContract.wordBytes * frameWords ≤
      target.source.evm.toMachineState.memory.size
  frameNoWrap :
    frameBase + MemoryContract.wordBytes * frameWords <
      EvmYul.UInt256.size
  frameHostAddressable :
    frameBase + MemoryContract.wordBytes * frameWords <
      USize.size
  activeNoWrap :
    target.source.evm.activeWords.toNat * MemoryContract.wordBytes <
      EvmYul.UInt256.size
  frameReserved :
    ∃ reservation,
      contract.scratch? = some reservation ∧
        reservation.containsRegion frameBase frameWords
  scratchBound :
    ∀ name slot,
      name ∈ live →
      plan.location? name = some (.scratch slot) →
      slot < frameWords

/--
Result relation for a compiled expression or expression sequence.

The produced source values occupy exactly the new concrete target stack
prefix, in EVM top-first order, and the incoming stack is preserved as the
suffix. `StateRel` simultaneously advances the local-location offset by the
number of produced values.
-/
structure ExprResultRel {transcript : Trace}
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name) (stackOffset frameBase resultCount : Nat)
    (source : SourceState transcript)
    (targetInitial targetFinal : TargetState transcript)
    (values : List Word) : Prop where
  state :
    StateRel contract plan live (stackOffset + resultCount) frameBase
      source targetFinal
  valuesLength :
    values.length = resultCount
  stack :
    targetFinal.source.evm.stack =
      values.reverse ++ targetInitial.source.evm.stack

/--
Expression-result relation retaining the additional active scratch-frame
invariants needed by spilled variable reads and writes.
-/
structure ScratchExprResultRel {transcript : Trace}
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name)
    (stackOffset frameBase frameDepth frameWords resultCount : Nat)
    (source : SourceState transcript)
    (targetInitial targetFinal : TargetState transcript)
    (values : List Word) : Prop where
  state :
    ScratchStateRel contract plan live
      (stackOffset + resultCount) frameBase frameDepth frameWords
      source targetFinal
  valuesLength :
    values.length = resultCount
  stack :
    targetFinal.source.evm.stack =
      values.reverse ++ targetInitial.source.evm.stack

namespace ExprResultRel

theorem nil {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    (hRel :
      StateRel contract plan live stackOffset frameBase source target) :
    ExprResultRel contract plan live stackOffset frameBase 0
      source target target [] := by
  exact ⟨by simpa using hRel, rfl, by simp⟩

theorem append {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {sourceHead sourceFinal : SourceState transcript}
    {targetInitial targetHead targetFinal : TargetState transcript}
    {headCount tailCount : Nat}
    {headValues tailValues : List Word}
    (hHead :
      ExprResultRel contract plan live stackOffset frameBase headCount
        sourceHead targetInitial targetHead headValues)
    (hTail :
      ExprResultRel contract plan live
        (stackOffset + headCount) frameBase tailCount
        sourceFinal targetHead targetFinal tailValues) :
    ExprResultRel contract plan live stackOffset frameBase
      (headCount + tailCount)
      sourceFinal targetInitial targetFinal (headValues ++ tailValues) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [Nat.add_assoc] using hTail.state
  · simp [List.length_append, hHead.valuesLength, hTail.valuesLength]
  · rw [hTail.stack, hHead.stack]
    simp [List.reverse_append, List.append_assoc]

end ExprResultRel

namespace ScratchExprResultRel

theorem nil {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source target) :
    ScratchExprResultRel contract plan live stackOffset frameBase
      frameDepth frameWords 0 source target target [] := by
  exact ⟨by simpa using hRel, rfl, by simp⟩

theorem append {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {sourceHead sourceFinal : SourceState transcript}
    {targetInitial targetHead targetFinal : TargetState transcript}
    {headCount tailCount : Nat}
    {headValues tailValues : List Word}
    (hHead :
      ScratchExprResultRel contract plan live stackOffset frameBase
        frameDepth frameWords headCount
        sourceHead targetInitial targetHead headValues)
    (hTail :
      ScratchExprResultRel contract plan live
        (stackOffset + headCount) frameBase
        frameDepth frameWords tailCount
        sourceFinal targetHead targetFinal tailValues) :
    ScratchExprResultRel contract plan live stackOffset frameBase
      frameDepth frameWords (headCount + tailCount)
      sourceFinal targetInitial targetFinal
      (headValues ++ tailValues) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [Nat.add_assoc] using hTail.state
  · simp [List.length_append, hHead.valuesLength, hTail.valuesLength]
  · rw [hTail.stack, hHead.stack]
    simp [List.reverse_append, List.append_assoc]

end ScratchExprResultRel

namespace ScratchStateRel

theorem transport_plan {transcript : Trace}
    {contract : MemoryContract.Contract}
    {left right : Plan} {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript}
    {target : TargetState transcript}
    (hRel :
      ScratchStateRel contract left live stackOffset frameBase
        frameDepth frameWords source target)
    (hAgree : PlanAgreesOn left right live) :
    ScratchStateRel contract right live stackOffset frameBase
      frameDepth frameWords source target := by
  refine
    ⟨hRel.base.transport_plan hAgree, hRel.framePointer,
      hRel.frameActive, hRel.frameAllocated, hRel.frameNoWrap,
      hRel.frameHostAddressable, hRel.activeNoWrap,
      hRel.frameReserved, ?_⟩
  intro name slot hLive hRightLocation
  obtain
      ⟨leftLocation, rightLocation,
        hLeftLocation, hAgreedRightLocation, hLocationAgree⟩ :=
    hAgree.location name hLive
  rw [hRightLocation] at hAgreedRightLocation
  cases hAgreedRightLocation
  cases hLocationAgree with
  | scratch agreedSlot =>
      exact hRel.scratchBound name slot hLive hLeftLocation

theorem rebase_prefix {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source sourceFinal : SourceState transcript}
    {target targetFinal : TargetState transcript}
    {oldPrefix newPrefix baseStack : List Word}
    (hRel :
      ScratchStateRel contract plan live
        (stackOffset + oldPrefix.length) frameBase
        frameDepth frameWords source target)
    (hBase :
      StateRel contract plan live
        (stackOffset + newPrefix.length) frameBase
        sourceFinal targetFinal)
    (hOldStack :
      target.source.evm.stack = oldPrefix ++ baseStack)
    (hNewStack :
      targetFinal.source.evm.stack = newPrefix ++ baseStack)
    (hMachine :
      targetFinal.source.evm.toMachineState =
        target.source.evm.toMachineState) :
    ScratchStateRel contract plan live
      (stackOffset + newPrefix.length) frameBase
      frameDepth frameWords sourceFinal targetFinal := by
  refine ⟨hBase, ?_, ?_, ?_, hRel.frameNoWrap,
    hRel.frameHostAddressable, ?_, hRel.frameReserved,
    hRel.scratchBound⟩
  · have hPointer := hRel.framePointer
    rw [hOldStack] at hPointer
    have hBasePointer :
        baseStack[stackOffset + frameDepth]? =
          some (EvmYul.UInt256.ofNat frameBase) := by
      rw [show
          stackOffset + oldPrefix.length + frameDepth =
            oldPrefix.length + (stackOffset + frameDepth) by omega]
        at hPointer
      rw [List.getElem?_append_right
        (Nat.le_add_right oldPrefix.length
          (stackOffset + frameDepth))] at hPointer
      simpa using hPointer
    rw [hNewStack]
    rw [show
        stackOffset + newPrefix.length + frameDepth =
          newPrefix.length + (stackOffset + frameDepth) by omega]
    rw [List.getElem?_append_right
      (Nat.le_add_right newPrefix.length
        (stackOffset + frameDepth))]
    simpa using hBasePointer
  · simpa [hMachine] using hRel.frameActive
  · simpa [hMachine] using hRel.frameAllocated
  · simpa [hMachine] using hRel.activeNoWrap

/--
Rebase a scratch activation across a target-only permutation or removal of a
stack prefix. The source store and shared EVM state are unchanged.
-/
theorem rebase_prefix_same_source {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript}
    {target targetFinal : TargetState transcript}
    {oldPrefix newPrefix baseStack : List Word}
    (hRel :
      ScratchStateRel contract plan live
        (stackOffset + oldPrefix.length) frameBase
        frameDepth frameWords source target)
    (hCursor : targetFinal.cursor = target.cursor)
    (hShared :
      targetFinal.source.evm.toSharedState =
        target.source.evm.toSharedState)
    (hOldStack :
      target.source.evm.stack = oldPrefix ++ baseStack)
    (hNewStack :
      targetFinal.source.evm.stack = newPrefix ++ baseStack) :
    ScratchStateRel contract plan live
      (stackOffset + newPrefix.length) frameBase
      frameDepth frameWords source targetFinal := by
  have hMachine :
      targetFinal.source.evm.toMachineState =
        target.source.evm.toMachineState := by
    exact congrArg EvmYul.SharedState.toMachineState hShared
  have hBase :
      StateRel contract plan live
        (stackOffset + newPrefix.length) frameBase
        source targetFinal := by
    refine ⟨?_, ?_⟩
    · rw [hCursor]
      exact hRel.base.cursor
    · refine ⟨?_, ?_, ?_⟩
      · rw [hMachine]
        exact hRel.base.core.machine
      · rw [hShared]
        exact hRel.base.core.world
      · exact
          hRel.base.core.store.rebase_prefix
            hOldStack hNewStack hMachine rfl
  exact
    hRel.rebase_prefix hBase hOldStack hNewStack hMachine

theorem rebase_prefix_mono {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source sourceFinal : SourceState transcript}
    {target targetFinal : TargetState transcript}
    {oldPrefix newPrefix baseStack : List Word}
    (hRel :
      ScratchStateRel contract plan live
        (stackOffset + oldPrefix.length) frameBase
        frameDepth frameWords source target)
    (hBase :
      StateRel contract plan live
        (stackOffset + newPrefix.length) frameBase
        sourceFinal targetFinal)
    (hOldStack :
      target.source.evm.stack = oldPrefix ++ baseStack)
    (hNewStack :
      targetFinal.source.evm.stack = newPrefix ++ baseStack)
    (hMemory :
      target.source.evm.toMachineState.memory.size ≤
        targetFinal.source.evm.toMachineState.memory.size)
    (hActive :
      target.source.evm.activeWords.toNat ≤
        targetFinal.source.evm.activeWords.toNat)
    (hActiveNoWrap :
      targetFinal.source.evm.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size) :
    ScratchStateRel contract plan live
      (stackOffset + newPrefix.length) frameBase
      frameDepth frameWords sourceFinal targetFinal := by
  refine ⟨hBase, ?_, ?_, ?_, hRel.frameNoWrap,
    hRel.frameHostAddressable, hActiveNoWrap, hRel.frameReserved,
    hRel.scratchBound⟩
  · have hPointer := hRel.framePointer
    rw [hOldStack] at hPointer
    have hBasePointer :
        baseStack[stackOffset + frameDepth]? =
          some (EvmYul.UInt256.ofNat frameBase) := by
      rw [show
          stackOffset + oldPrefix.length + frameDepth =
            oldPrefix.length + (stackOffset + frameDepth) by omega]
        at hPointer
      rw [List.getElem?_append_right
        (Nat.le_add_right oldPrefix.length
          (stackOffset + frameDepth))] at hPointer
      simpa using hPointer
    rw [hNewStack]
    rw [show
        stackOffset + newPrefix.length + frameDepth =
          newPrefix.length + (stackOffset + frameDepth) by omega]
    rw [List.getElem?_append_right
      (Nat.le_add_right newPrefix.length
        (stackOffset + frameDepth))]
    simpa using hBasePointer
  · exact hRel.frameActive.trans
      (Nat.mul_le_mul_right MemoryContract.wordBytes hActive)
  · exact hRel.frameAllocated.trans hMemory

theorem of_wellFormed
    {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {regionBase : Locals.Allocation.RegionBase}
    {source : SourceState transcript} {target : TargetState transcript}
    (hBase :
      StateRel contract plan live stackOffset frameBase source target)
    (hFramePointer :
      target.source.evm.stack[stackOffset + frameDepth]? =
        some (EvmYul.UInt256.ofNat frameBase))
    (hFrameActive :
      frameBase + MemoryContract.wordBytes * frameWords ≤
        target.source.evm.activeWords.toNat * MemoryContract.wordBytes)
    (hFrameAllocated :
      frameBase + MemoryContract.wordBytes * frameWords ≤
        target.source.evm.toMachineState.memory.size)
    (hFrameNoWrap :
      frameBase + MemoryContract.wordBytes * frameWords <
        EvmYul.UInt256.size)
    (hFrameHostAddressable :
      frameBase + MemoryContract.wordBytes * frameWords <
        USize.size)
    (hActiveNoWrap :
      target.source.evm.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (hFrameReserved :
      ∃ reservation,
        contract.scratch? = some reservation ∧
          reservation.containsRegion frameBase frameWords)
    (hWF : plan.WellFormed)
    (hRegion :
      plan.scratchRegion? =
        some
          { base := regionBase
            words := frameWords }) :
    ScratchStateRel contract plan live stackOffset frameBase
      frameDepth frameWords source target :=
  ⟨hBase, hFramePointer, hFrameActive, hFrameAllocated,
    hFrameNoWrap, hFrameHostAddressable, hActiveNoWrap,
    hFrameReserved, fun name slot _hLive hLocation =>
      plan.scratch_bound_of_wellFormed hWF hLocation hRegion⟩

theorem scratchAddress_reserved_of_bound {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {slot : Nat}
    {reservation : MemoryContract.ScratchReservation}
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source target)
    (hSlot : slot < frameWords)
    (hReservation : contract.scratch? = some reservation) :
    reservation.containsRegion (scratchAddress frameBase slot) 1 := by
  obtain ⟨owned, hOwned, hFrame⟩ := hRel.frameReserved
  have hOwnedEq : owned = reservation := by
    rw [hReservation] at hOwned
    exact (Option.some.inj hOwned).symm
  subst owned
  have hSucc : slot + 1 ≤ frameWords :=
    Nat.succ_le_iff.mpr hSlot
  constructor
  · exact hFrame.1.trans
      (Nat.le_add_right frameBase (MemoryContract.wordBytes * slot))
  · calc
      scratchAddress frameBase slot + MemoryContract.wordBytes * 1 =
          frameBase + MemoryContract.wordBytes * (slot + 1) := by
            simp [scratchAddress, Nat.mul_add, Nat.add_assoc]
      _ ≤ frameBase + MemoryContract.wordBytes * frameWords :=
        Nat.add_le_add_left
          (Nat.mul_le_mul_left MemoryContract.wordBytes hSucc) frameBase
      _ ≤ reservation.endExclusive := hFrame.2

theorem scratchAddress_reserved {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {slot : Nat}
    {reservation : MemoryContract.ScratchReservation}
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot))
    (hReservation : contract.scratch? = some reservation) :
    reservation.containsRegion (scratchAddress frameBase slot) 1 :=
  hRel.scratchAddress_reserved_of_bound
    (hRel.scratchBound name slot hLive hLocation) hReservation

theorem scratchAddress_end_le_active {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {slot : Nat}
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot)) :
    scratchAddress frameBase slot + MemoryContract.wordBytes ≤
      target.source.evm.activeWords.toNat *
        MemoryContract.wordBytes := by
  have hSlot := hRel.scratchBound name slot hLive hLocation
  have hSucc : slot + 1 ≤ frameWords :=
    Nat.succ_le_iff.mpr hSlot
  calc
    scratchAddress frameBase slot + MemoryContract.wordBytes =
        frameBase + MemoryContract.wordBytes * (slot + 1) := by
          simp [scratchAddress, Nat.mul_add, Nat.add_assoc]
    _ ≤ frameBase + MemoryContract.wordBytes * frameWords :=
      Nat.add_le_add_left
        (Nat.mul_le_mul_left MemoryContract.wordBytes hSucc) frameBase
    _ ≤ target.source.evm.activeWords.toNat *
        MemoryContract.wordBytes :=
      hRel.frameActive

theorem scratchAddress_end_lt_size {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {slot : Nat}
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot)) :
    scratchAddress frameBase slot + MemoryContract.wordBytes <
      EvmYul.UInt256.size := by
  have hSlot := hRel.scratchBound name slot hLive hLocation
  have hSucc : slot + 1 ≤ frameWords :=
    Nat.succ_le_iff.mpr hSlot
  exact
    lt_of_le_of_lt
      (show
        scratchAddress frameBase slot + MemoryContract.wordBytes ≤
          frameBase + MemoryContract.wordBytes * frameWords by
        calc
          scratchAddress frameBase slot + MemoryContract.wordBytes =
              frameBase + MemoryContract.wordBytes * (slot + 1) := by
                simp [scratchAddress, Nat.mul_add, Nat.add_assoc]
          _ ≤ frameBase + MemoryContract.wordBytes * frameWords :=
            Nat.add_le_add_left
              (Nat.mul_le_mul_left MemoryContract.wordBytes hSucc)
              frameBase)
      hRel.frameNoWrap

theorem scratchAddress_end_le_memory {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {slot : Nat}
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot)) :
    scratchAddress frameBase slot + MemoryContract.wordBytes ≤
      target.source.evm.toMachineState.memory.size := by
  have hSlot := hRel.scratchBound name slot hLive hLocation
  have hSucc : slot + 1 ≤ frameWords :=
    Nat.succ_le_iff.mpr hSlot
  calc
    scratchAddress frameBase slot + MemoryContract.wordBytes =
        frameBase + MemoryContract.wordBytes * (slot + 1) := by
          simp [scratchAddress, Nat.mul_add, Nat.add_assoc]
    _ ≤ frameBase + MemoryContract.wordBytes * frameWords :=
      Nat.add_le_add_left
        (Nat.mul_le_mul_left MemoryContract.wordBytes hSucc) frameBase
    _ ≤ target.source.evm.toMachineState.memory.size :=
      hRel.frameAllocated

theorem scratchAddress_end_lt_hostSize {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {slot : Nat}
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot)) :
    scratchAddress frameBase slot + MemoryContract.wordBytes <
      USize.size := by
  have hSlot := hRel.scratchBound name slot hLive hLocation
  have hSucc : slot + 1 ≤ frameWords :=
    Nat.succ_le_iff.mpr hSlot
  exact
    lt_of_le_of_lt
      (show
        scratchAddress frameBase slot + MemoryContract.wordBytes ≤
          frameBase + MemoryContract.wordBytes * frameWords by
        calc
          scratchAddress frameBase slot + MemoryContract.wordBytes =
              frameBase + MemoryContract.wordBytes * (slot + 1) := by
                simp [scratchAddress, Nat.mul_add, Nat.add_assoc]
          _ ≤ frameBase + MemoryContract.wordBytes * frameWords :=
            Nat.add_le_add_left
              (Nat.mul_le_mul_left MemoryContract.wordBytes hSucc)
              frameBase)
      hRel.frameHostAddressable

theorem mload_machine_eq {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {slot : Nat}
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot)) :
    target.source.evm.toMachineState.mload
        (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) =
      (target.source.evm.toMachineState.lookupMemory
          (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)),
        target.source.evm.toMachineState) := by
  have hEndActive :=
    hRel.scratchAddress_end_le_active hLive hLocation
  have hEndLt :=
    hRel.scratchAddress_end_lt_size hLive hLocation
  have hAddressLt :
      scratchAddress frameBase slot < EvmYul.UInt256.size :=
    lt_of_lt_of_le
      (Nat.lt_add_of_pos_right
        (by decide : 0 < MemoryContract.wordBytes))
      (Nat.le_of_lt hEndLt)
  have hAddressToNat :
      (EvmYul.UInt256.ofNat
        (scratchAddress frameBase slot)).toNat =
          scratchAddress frameBase slot :=
    EvmYul.UInt256.toNat_ofNat_of_lt hAddressLt
  exact
    Compiler.MemoryRelation.mload_eq_lookup_of_end_le
      target.source.evm.toMachineState
      (scratchAddress frameBase slot)
      hAddressToNat
      (by simpa [MemoryContract.wordBytes] using hEndActive)

theorem mono {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {smaller larger : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    (hRel :
      ScratchStateRel contract plan larger stackOffset frameBase
        frameDepth frameWords source target)
    (hSubset : ∀ name, name ∈ smaller → name ∈ larger)
    (hStackOrder :
      currentStackOrder plan smaller =
        currentStackOrder plan larger) :
    ScratchStateRel contract plan smaller stackOffset frameBase
      frameDepth frameWords source target :=
  ⟨hRel.base.mono hSubset hStackOrder, hRel.framePointer, hRel.frameActive,
    hRel.frameAllocated, hRel.frameNoWrap,
    hRel.frameHostAddressable, hRel.activeNoWrap,
    hRel.frameReserved,
    fun name slot hLive hLocation =>
      hRel.scratchBound name slot (hSubset name hLive) hLocation⟩

theorem push_target_by {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    (pcDelta : Nat) (value : Word)
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source target) :
    ScratchStateRel contract plan live (stackOffset + 1) frameBase
      frameDepth frameWords source
      (StateRel.pushTargetBy pcDelta value target) := by
  refine
    ⟨hRel.base.push_target_by pcDelta value, ?_, ?_, ?_,
      hRel.frameNoWrap, hRel.frameHostAddressable, ?_,
      hRel.frameReserved, hRel.scratchBound⟩
  · change
      (value :: target.source.evm.stack)[stackOffset + 1 + frameDepth]? =
        some (EvmYul.UInt256.ofNat frameBase)
    rw [show stackOffset + 1 + frameDepth =
        (stackOffset + frameDepth) + 1 by omega]
    simpa using hRel.framePointer
  · simpa [StateRel.pushTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.frameActive
  · simpa [StateRel.pushTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.frameAllocated
  · simpa [StateRel.pushTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.activeNoWrap

theorem push_target {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    (value : Word)
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source target) :
    ScratchStateRel contract plan live (stackOffset + 1) frameBase
      frameDepth frameWords source
      (StateRel.pushTarget value target) := by
  exact hRel.push_target_by 1 value

theorem pop_target {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {value : Word} {rest : List Word}
    (hRel :
      ScratchStateRel contract plan live (stackOffset + 1) frameBase
        frameDepth frameWords source target)
    (hStack : target.source.evm.stack = value :: rest) :
    ScratchStateRel contract plan live stackOffset frameBase
      frameDepth frameWords source (StateRel.popTarget rest target) := by
  refine
    ⟨hRel.base.pop_target hStack, ?_, ?_, ?_,
      hRel.frameNoWrap, hRel.frameHostAddressable, ?_,
      hRel.frameReserved, hRel.scratchBound⟩
  · change
      rest[stackOffset + frameDepth]? =
        some (EvmYul.UInt256.ofNat frameBase)
    have hPointer := hRel.framePointer
    rw [hStack] at hPointer
    simpa [show stackOffset + 1 + frameDepth =
        (stackOffset + frameDepth) + 1 by omega] using hPointer
  · simpa [StateRel.popTarget] using hRel.frameActive
  · simpa [StateRel.popTarget] using hRel.frameAllocated
  · simpa [StateRel.popTarget] using hRel.activeNoWrap

theorem contract_target_by {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {right left value : Word} {rest : List Word}
    (hRel :
      ScratchStateRel contract plan live (stackOffset + 2) frameBase
        frameDepth frameWords source target)
    (hStack : target.source.evm.stack = right :: left :: rest)
    (pcDelta : Nat) :
    ScratchStateRel contract plan live (stackOffset + 1) frameBase
      frameDepth frameWords source
      (StateRel.contractTargetBy pcDelta value rest target) := by
  refine
    ⟨hRel.base.contract_target_by hStack pcDelta, ?_, ?_, ?_,
      hRel.frameNoWrap, hRel.frameHostAddressable, ?_,
      hRel.frameReserved, hRel.scratchBound⟩
  · change
      (value :: rest)[stackOffset + 1 + frameDepth]? =
        some (EvmYul.UInt256.ofNat frameBase)
    have hPointer := hRel.framePointer
    rw [hStack] at hPointer
    have hRest :
        rest[stackOffset + frameDepth]? =
          some (EvmYul.UInt256.ofNat frameBase) := by
      simpa [show stackOffset + 2 + frameDepth =
          (stackOffset + frameDepth) + 2 by omega] using hPointer
    simpa [show stackOffset + 1 + frameDepth =
        (stackOffset + frameDepth) + 1 by omega] using hRest
  · simpa [StateRel.contractTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.frameActive
  · simpa [StateRel.contractTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.frameAllocated
  · simpa [StateRel.contractTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.activeNoWrap

theorem replace_top_by {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {old value : Word} {rest : List Word}
    (hRel :
      ScratchStateRel contract plan live (stackOffset + 1) frameBase
        frameDepth frameWords source target)
    (hStack : target.source.evm.stack = old :: rest)
    (pcDelta : Nat) :
    ScratchStateRel contract plan live (stackOffset + 1) frameBase
      frameDepth frameWords source
      (StateRel.contractTargetBy pcDelta value rest target) := by
  refine
    ⟨hRel.base.replace_top_by hStack pcDelta, ?_, ?_, ?_,
      hRel.frameNoWrap, hRel.frameHostAddressable, ?_,
      hRel.frameReserved, hRel.scratchBound⟩
  · change
      (value :: rest)[stackOffset + 1 + frameDepth]? =
        some (EvmYul.UInt256.ofNat frameBase)
    have hPointer := hRel.framePointer
    rw [hStack] at hPointer
    simpa [show stackOffset + 1 + frameDepth =
        (stackOffset + frameDepth) + 1 by omega] using hPointer
  · simpa [StateRel.contractTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.frameActive
  · simpa [StateRel.contractTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.frameAllocated
  · simpa [StateRel.contractTargetBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.activeNoWrap

/--
A newly declared stack local consumes the expression result at the top of the
stack. Existing stack locals move one slot deeper, while the hidden scratch
frame pointer moves from `frameDepth` to `frameDepth + 1`.

`hStackOrder` is the allocation-owned transition fact: among names live after
the declaration, the new stack binding is first and the previous current order
is retained behind it.
-/
theorem declare_stack_live
    {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {beforeLive afterLive : List Locals.Name}
    {frameBase frameDepth frameWords planDepth : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {value : Word} {rest : List Word}
    (hRel :
      ScratchStateRel contract plan beforeLive 1 frameBase
        frameDepth frameWords source target)
    (hStack : target.source.evm.stack = value :: rest)
    (hAfter :
      ∀ other, other ∈ afterLive →
        other = name ∨ other ∈ beforeLive)
    (hNameAfter : name ∈ afterLive)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hStackOrder :
      currentStackOrder plan afterLive =
        name :: currentStackOrder plan beforeLive) :
    ScratchStateRel contract plan afterLive 0 frameBase
      (frameDepth + 1) frameWords
      (source.withSource (source.source.insert name value)) target := by
  refine
    { base := ?_
      framePointer := ?_
      frameActive := hRel.frameActive
      frameAllocated := hRel.frameAllocated
      frameNoWrap := hRel.frameNoWrap
      frameHostAddressable := hRel.frameHostAddressable
      activeNoWrap := hRel.activeNoWrap
      frameReserved := hRel.frameReserved
      scratchBound := ?_ }
  · refine ⟨?_, ?_⟩
    · simpa [Simulation.ResourceReplay.State.withSource] using
        hRel.base.cursor
    · refine ⟨?_, ?_, ?_⟩
      · simpa [Simulation.ResourceReplay.State.withSource,
          Locals.Source.State.insert] using hRel.base.core.machine
      · simpa [Simulation.ResourceReplay.State.withSource,
          Locals.Source.State.insert] using hRel.base.core.world
      · intro other location hOtherAfter hOtherLocation
        by_cases hName : other = name
        · subst other
          cases location with
          | stack otherPlanDepth =>
              rw [hLocation] at hOtherLocation
              cases hOtherLocation
              refine ⟨0, ?_, ?_⟩
              · simp [hStackOrder, Locals.Layout.lookupDepth?,
                  Locals.Layout.lookupDepthFrom]
              · rw [hStack]
                simp [Simulation.ResourceReplay.State.withSource,
                  Locals.Source.State.insert]
          | scratch slot =>
              rw [hLocation] at hOtherLocation
              simp at hOtherLocation
        · have hOtherBefore : other ∈ beforeLive := by
            rcases hAfter other hOtherAfter with hEq | hBefore
            · exact False.elim (hName hEq)
            · exact hBefore
          have hOld :=
            hRel.base.core.store other location
              hOtherBefore hOtherLocation
          cases location with
          | stack otherPlanDepth =>
              rcases hOld with ⟨depth, hDepth, hValue⟩
              refine ⟨depth + 1, ?_, ?_⟩
              · rw [hStackOrder]
                simpa [Nat.add_assoc] using
                  (Locals.Layout.lookupDepth?_cons_of_ne
                    (Ne.symm hName) hDepth)
              · simpa [Simulation.ResourceReplay.State.withSource,
                  Locals.Source.State.insert,
                  Locals.Source.Store.insert_of_ne hName,
                  Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hValue
          | scratch slot =>
              change
                target.source.evm.toMachineState.lookupMemory
                    (EvmYul.UInt256.ofNat
                      (scratchAddress frameBase slot)) =
                  (Locals.Source.Store.insert
                    source.source.vars name value other).getD
                      (EvmYul.UInt256.ofNat 0)
              rw [Locals.Source.Store.insert_of_ne hName]
              exact hOld
  · have hPointer := hRel.framePointer
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hPointer
  · intro other slot hOtherAfter hOtherLocation
    have hNe : other ≠ name := by
      intro hEq
      subst other
      rw [hLocation] at hOtherLocation
      simp at hOtherLocation
    have hOtherBefore : other ∈ beforeLive := by
      rcases hAfter other hOtherAfter with hEq | hBefore
      · exact False.elim (hNe hEq)
      · exact hBefore
    exact hRel.scratchBound other slot hOtherBefore hOtherLocation

/--
Activate an already initialized stack name. Function-entry source stores
contain parameters and returns before their concrete stack realization is
established, so the semantic insertion performed by `declare_stack_live` is
the identity.
-/
theorem declare_stack_live_existing
    {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {beforeLive afterLive : List Locals.Name}
    {frameBase frameDepth frameWords planDepth : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {value : Word} {rest : List Word}
    (hRel :
      ScratchStateRel contract plan beforeLive 1 frameBase
        frameDepth frameWords source target)
    (hStack : target.source.evm.stack = value :: rest)
    (hAfter :
      ∀ other, other ∈ afterLive →
        other = name ∨ other ∈ beforeLive)
    (hNameAfter : name ∈ afterLive)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hStackOrder :
      currentStackOrder plan afterLive =
        name :: currentStackOrder plan beforeLive)
    (hValue : source.source.vars name = some value) :
    ScratchStateRel contract plan afterLive 0 frameBase
      (frameDepth + 1) frameWords source target := by
  have hDeclared :=
    hRel.declare_stack_live hStack hAfter hNameAfter hLocation hStackOrder
  rw [Locals.Source.State.insert_eq_of_apply_eq hValue] at hDeclared
  simpa using hDeclared

/--
Activate an already initialized stack local immediately below an arbitrary
pending-value prefix.

Function parameters are processed from the bottom of the raw entry stack.
Unprocessed parameters therefore form a prefix above the parameter currently
being activated.
-/
theorem declare_stack_live_existing_at
    {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {beforeLive afterLive : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords planDepth : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {value : Word}
    (hRel :
      ScratchStateRel contract plan beforeLive (stackOffset + 1) frameBase
        frameDepth frameWords source target)
    (hAfter :
      ∀ other, other ∈ afterLive →
        other = name ∨ other ∈ beforeLive)
    (hFresh : name ∉ beforeLive)
    (hNameAfter : name ∈ afterLive)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hStackOrder :
      currentStackOrder plan afterLive =
        name :: currentStackOrder plan beforeLive)
    (hTargetValue : target.source.evm.stack[stackOffset]? = some value)
    (hValue : source.source.vars name = some value) :
    ScratchStateRel contract plan afterLive stackOffset frameBase
      (frameDepth + 1) frameWords source target := by
  refine
    { base :=
        { cursor := hRel.base.cursor
          core :=
            { machine := hRel.base.core.machine
              world := hRel.base.core.world
              store := ?_ } }
      framePointer := ?_
      frameActive := hRel.frameActive
      frameAllocated := hRel.frameAllocated
      frameNoWrap := hRel.frameNoWrap
      frameHostAddressable := hRel.frameHostAddressable
      activeNoWrap := hRel.activeNoWrap
      frameReserved := hRel.frameReserved
      scratchBound := ?_ }
  · intro other location hOtherAfter hOtherLocation
    rcases hAfter other hOtherAfter with hName | hBefore
    · subst other
      rw [hLocation] at hOtherLocation
      cases hOtherLocation
      refine ⟨0, ?_, ?_⟩
      · simpa [hStackOrder, Locals.Layout.lookupDepth?,
          Locals.Layout.lookupDepthFrom]
      · simpa [hValue] using hTargetValue
    · have hPrevious :=
        hRel.base.core.store other location hBefore hOtherLocation
      have hOtherNe : other ≠ name := by
        intro hEq
        subst other
        exact hFresh hBefore
      cases location with
      | stack otherPlanDepth =>
          rcases hPrevious with ⟨depth, hDepth, hStored⟩
          refine ⟨depth + 1, ?_, ?_⟩
          · rw [hStackOrder]
            simpa [Nat.add_assoc] using
              Locals.Layout.lookupDepth?_cons_of_ne hOtherNe.symm hDepth
          · change
              target.source.evm.stack[
                  stackOffset + (depth + 1)]? =
                source.source.vars other
            change
              target.source.evm.stack[
                  (stackOffset + 1) + depth]? =
                source.source.vars other at hStored
            rw [show
                stackOffset + (depth + 1) =
                  (stackOffset + 1) + depth by omega]
            exact hStored
      | scratch slot =>
          exact hPrevious
  · have hPointer := hRel.framePointer
    rw [show
        stackOffset + (frameDepth + 1) =
          (stackOffset + 1) + frameDepth by omega]
    exact hPointer
  · intro other slot hOtherAfter hOtherLocation
    rcases hAfter other hOtherAfter with hName | hBefore
    · subst other
      rw [hLocation] at hOtherLocation
      simp at hOtherLocation
    · exact hRel.scratchBound other slot hBefore hOtherLocation

theorem assign_scratch_live
    {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {beforeLive afterLive : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {slot : Nat} {value : Word}
    {rest : List Word}
    {reservation : MemoryContract.ScratchReservation}
    (hRel :
      ScratchStateRel contract plan beforeLive (stackOffset + 2) frameBase
        frameDepth frameWords source target)
    (hWF : plan.WellFormed)
    (hAfter :
      ∀ other, other ∈ afterLive →
        other = name ∨ other ∈ beforeLive)
    (hStackOrder :
      currentStackOrder plan afterLive =
        currentStackOrder plan beforeLive)
    (hNameAfter : name ∈ afterLive)
    (hLocation : plan.location? name = some (.scratch slot))
    (hAssignedBound : slot < frameWords)
    (hReservation : contract.scratch? = some reservation)
    (hRegion :
      reservation.containsRegion (scratchAddress frameBase slot) 1)
    (hStack :
      target.source.evm.stack =
        EvmYul.UInt256.ofNat (scratchAddress frameBase slot) ::
          value :: rest) :
    ScratchStateRel contract plan afterLive stackOffset frameBase
      frameDepth frameWords
      (source.withSource (source.source.insert name value))
      (StateRel.mstoreTarget
        (EvmYul.UInt256.ofNat (scratchAddress frameBase slot))
        value rest target) := by
  have hWriteEndFrame :
      scratchAddress frameBase slot + MemoryContract.wordBytes ≤
        frameBase + MemoryContract.wordBytes * frameWords := by
    have hSucc : slot + 1 ≤ frameWords :=
      Nat.succ_le_iff.mpr hAssignedBound
    calc
      scratchAddress frameBase slot + MemoryContract.wordBytes =
          frameBase + MemoryContract.wordBytes * (slot + 1) := by
            simp [scratchAddress, Nat.mul_add, Nat.add_assoc]
      _ ≤ frameBase + MemoryContract.wordBytes * frameWords :=
        Nat.add_le_add_left
          (Nat.mul_le_mul_left MemoryContract.wordBytes hSucc) frameBase
  have hWriteEndActive :=
    hWriteEndFrame.trans hRel.frameActive
  have hWriteEndMemory :=
    hWriteEndFrame.trans hRel.frameAllocated
  have hWriteEndLt :=
    lt_of_le_of_lt hWriteEndFrame hRel.frameNoWrap
  have hWriteEndHost :=
    lt_of_le_of_lt hWriteEndFrame hRel.frameHostAddressable
  have hWriteAddressLt :
      scratchAddress frameBase slot < EvmYul.UInt256.size := by
    omega
  have hWriteAddress :
      (EvmYul.UInt256.ofNat
        (scratchAddress frameBase slot)).toNat =
          scratchAddress frameBase slot :=
    EvmYul.UInt256.toNat_ofNat_of_lt hWriteAddressLt
  have hActiveEq :=
    Compiler.MemoryRelation.mstore_activeWords_eq_of_end_le
      target.source.evm.toMachineState
      (scratchAddress frameBase slot) value
      hWriteAddress
      (by simpa [MemoryContract.wordBytes] using hWriteEndActive)
  have hMemoryEq :=
    Compiler.MemoryRelation.writeWord_memory_size_eq_of_end_le
      target.source.evm.toMachineState
      (scratchAddress frameBase slot) value
      hWriteAddress
      (by simpa [MemoryContract.wordBytes] using hWriteEndHost)
      (by simpa [MemoryContract.wordBytes] using hWriteEndMemory)
  refine
    { base := ?_
      framePointer := ?_
      frameActive := ?_
      frameAllocated := ?_
      frameNoWrap := hRel.frameNoWrap
      frameHostAddressable := hRel.frameHostAddressable
      activeNoWrap := ?_
      frameReserved := hRel.frameReserved
      scratchBound := ?_ }
  · refine ⟨?_, ?_⟩
    · simpa [Simulation.ResourceReplay.State.withSource,
        StateRel.mstoreTarget] using hRel.base.cursor
    · refine ⟨?_, ?_, ?_⟩
      · simpa [Simulation.ResourceReplay.State.withSource,
          Locals.Source.State.insert,
          StateRel.mstoreTarget,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] using
          (Compiler.MemoryRelation.MachineRel.mstore_target
            (scratchAddress frameBase slot) value
            hRel.base.core.machine hReservation hRegion
            hWriteEndLt hWriteEndHost)
      · simpa [Simulation.ResourceReplay.State.withSource,
          Locals.Source.State.insert,
          StateRel.mstoreTarget,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] using hRel.base.core.world
      · intro other location hOtherAfter hOtherLocation
        by_cases hName : other = name
        · subst other
          cases location with
          | stack depth =>
              rw [hLocation] at hOtherLocation
              simp at hOtherLocation
          | scratch otherSlot =>
              rw [hLocation] at hOtherLocation
              cases hOtherLocation
              change
                (target.source.evm.toMachineState.mstore
                    (EvmYul.UInt256.ofNat
                      (scratchAddress frameBase slot)) value).lookupMemory
                      (EvmYul.UInt256.ofNat
                        (scratchAddress frameBase slot)) =
                  ((source.source.insert name value).vars name).getD
                    (EvmYul.UInt256.ofNat 0)
              rw [Compiler.MemoryRelation.lookupMemory_mstore_same
                target.source.evm.toMachineState
                (scratchAddress frameBase slot) value
                hWriteAddress
                (by simpa [MemoryContract.wordBytes] using hWriteEndHost)
                (by simpa [MemoryContract.wordBytes] using hWriteEndMemory)
                (by simpa [MemoryContract.wordBytes] using hWriteEndActive)
                (by simpa [MemoryContract.wordBytes] using
                  hRel.activeNoWrap)]
              simp [Locals.Source.State.insert]
        · have hOtherBefore : other ∈ beforeLive := by
            rcases hAfter other hOtherAfter with hEq | hBefore
            · exact False.elim (hName hEq)
            · exact hBefore
          have hOld :=
            hRel.base.core.store other location
              hOtherBefore hOtherLocation
          cases location with
          | stack planDepth =>
              rcases hOld with ⟨depth, hDepth, hOld⟩
              refine ⟨depth, ?_, ?_⟩
              · simpa [hStackOrder] using hDepth
              change
                rest[stackOffset + depth]? =
                  Locals.Source.Store.insert
                    source.source.vars name value other
              change
                target.source.evm.stack[
                    (stackOffset + 2) + depth]? =
                  source.source.vars other at hOld
              rw [hStack] at hOld
              have hRest :
                  rest[stackOffset + depth]? =
                    source.source.vars other := by
                simpa [show
                    (stackOffset + 2) + depth =
                      (stackOffset + depth) + 2 by omega] using hOld
              rw [Locals.Source.Store.insert_of_ne hName]
              exact hRest
          | scratch otherSlot =>
              have hOtherSlotNe :
                    otherSlot ≠ slot :=
                  plan.scratch_slot_ne_of_wellFormed
                    hWF hName hOtherLocation hLocation
              have hOtherEndMemory :=
                hRel.scratchAddress_end_le_memory
                  hOtherBefore hOtherLocation
              have hOtherEndLt :=
                hRel.scratchAddress_end_lt_size
                  hOtherBefore hOtherLocation
              have hOtherAddress :
                  (EvmYul.UInt256.ofNat
                    (scratchAddress frameBase otherSlot)).toNat =
                      scratchAddress frameBase otherSlot :=
                EvmYul.UInt256.toNat_ofNat_of_lt (by omega)
              have hDisjoint :
                  scratchAddress frameBase otherSlot +
                        MemoryContract.wordBytes ≤
                      scratchAddress frameBase slot ∨
                    scratchAddress frameBase slot +
                        MemoryContract.wordBytes ≤
                      scratchAddress frameBase otherSlot := by
                simp only [scratchAddress, MemoryContract.wordBytes]
                omega
              change
                (target.source.evm.toMachineState.mstore
                    (EvmYul.UInt256.ofNat
                      (scratchAddress frameBase slot)) value).lookupMemory
                      (EvmYul.UInt256.ofNat
                        (scratchAddress frameBase otherSlot)) =
                  (Locals.Source.Store.insert
                    source.source.vars name value other).getD
                      (EvmYul.UInt256.ofNat 0)
              rw [Compiler.MemoryRelation.lookupMemory_mstore_disjoint
                target.source.evm.toMachineState
                (scratchAddress frameBase slot)
                (scratchAddress frameBase otherSlot) value
                hWriteAddress hOtherAddress
                (by simpa [MemoryContract.wordBytes] using hWriteEndHost)
                (by simpa [MemoryContract.wordBytes] using hWriteEndMemory)
                (by simpa [MemoryContract.wordBytes] using hOtherEndMemory)
                (by simpa [MemoryContract.wordBytes] using hWriteEndActive)
                (by simpa [MemoryContract.wordBytes] using hDisjoint)]
              rw [Locals.Source.Store.insert_of_ne hName]
              exact hOld
  · change
      rest[stackOffset + frameDepth]? =
        some (EvmYul.UInt256.ofNat frameBase)
    have hPointer := hRel.framePointer
    rw [hStack] at hPointer
    simpa [show
        (stackOffset + 2) + frameDepth =
          (stackOffset + frameDepth) + 2 by omega] using hPointer
  · simpa [StateRel.mstoreTarget,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, hActiveEq] using hRel.frameActive
  · simpa [StateRel.mstoreTarget,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC,
      EvmYul.MachineState.mstore, hMemoryEq] using hRel.frameAllocated
  · simpa [StateRel.mstoreTarget,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, hActiveEq] using hRel.activeNoWrap
  · intro other otherSlot hOtherAfter hOtherLocation
    rcases hAfter other hOtherAfter with hEq | hBefore
    · subst other
      rw [hLocation] at hOtherLocation
      cases hOtherLocation
      exact hAssignedBound
    · exact hRel.scratchBound other otherSlot hBefore hOtherLocation

/--
Activate an already initialized spilled name after writing its existing value
to the compiler-owned frame.
-/
theorem assign_scratch_live_existing
    {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {beforeLive afterLive : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {slot : Nat} {value : Word}
    {rest : List Word}
    {reservation : MemoryContract.ScratchReservation}
    (hRel :
      ScratchStateRel contract plan beforeLive (stackOffset + 2) frameBase
        frameDepth frameWords source target)
    (hWF : plan.WellFormed)
    (hAfter :
      ∀ other, other ∈ afterLive →
        other = name ∨ other ∈ beforeLive)
    (hStackOrder :
      currentStackOrder plan afterLive =
        currentStackOrder plan beforeLive)
    (hNameAfter : name ∈ afterLive)
    (hLocation : plan.location? name = some (.scratch slot))
    (hAssignedBound : slot < frameWords)
    (hReservation : contract.scratch? = some reservation)
    (hRegion :
      reservation.containsRegion (scratchAddress frameBase slot) 1)
    (hStack :
      target.source.evm.stack =
        EvmYul.UInt256.ofNat (scratchAddress frameBase slot) ::
          value :: rest)
    (hValue : source.source.vars name = some value) :
    ScratchStateRel contract plan afterLive stackOffset frameBase
      frameDepth frameWords source
      (StateRel.mstoreTarget
        (EvmYul.UInt256.ofNat (scratchAddress frameBase slot))
        value rest target) := by
  have hAssigned :=
    hRel.assign_scratch_live hWF hAfter hStackOrder hNameAfter hLocation
      hAssignedBound hReservation hRegion hStack
  rw [Locals.Source.State.insert_eq_of_apply_eq hValue] at hAssigned
  simpa using hAssigned

theorem assign_scratch
    {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {slot : Nat} {value : Word}
    {rest : List Word}
    {reservation : MemoryContract.ScratchReservation}
    (hRel :
      ScratchStateRel contract plan live (stackOffset + 2) frameBase
        frameDepth frameWords source target)
    (hWF : plan.WellFormed)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot))
    (hReservation : contract.scratch? = some reservation)
    (hRegion :
      reservation.containsRegion (scratchAddress frameBase slot) 1)
    (hStack :
      target.source.evm.stack =
        EvmYul.UInt256.ofNat (scratchAddress frameBase slot) ::
          value :: rest) :
    ScratchStateRel contract plan live stackOffset frameBase
      frameDepth frameWords
      (source.withSource (source.source.insert name value))
      (StateRel.mstoreTarget
        (EvmYul.UInt256.ofNat (scratchAddress frameBase slot))
        value rest target) :=
  assign_scratch_live hRel hWF
    (fun other hOther => by
      by_cases hEq : other = name
      · exact Or.inl hEq
      · exact Or.inr hOther)
    rfl hLive hLocation
    (hRel.scratchBound name slot hLive hLocation)
    hReservation hRegion hStack

/--
Assigning a stack-resident local inside a scratch activation leaves the hidden
frame pointer and every frame invariant unchanged.
-/
theorem assign_stack_live
    {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {frameBase frameDepth frameWords planDepth depth : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {value old : Word} {rest : List Word}
    (hRel :
      ScratchStateRel contract plan live 1 frameBase
        frameDepth frameWords source target)
    (hStack : target.source.evm.stack = value :: rest)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hDepth :
      Locals.Layout.lookupDepth? name (currentStackOrder plan live) =
        some (depth + 1))
    (hDepthFrame : depth < frameDepth)
    (hOld : source.source.vars name = some old) :
    ScratchStateRel contract plan live 0 frameBase
      frameDepth frameWords
      (source.withSource (source.source.insert name value))
      (StateRel.replaceStackBy 2 (rest.set depth value) target) := by
  have hPointer := hRel.framePointer
  rw [hStack] at hPointer
  have hRestPointer :
      rest[frameDepth]? = some (EvmYul.UInt256.ofNat frameBase) := by
    simpa [show 1 + frameDepth = frameDepth + 1 by omega] using hPointer
  have hFrameBound : frameDepth < rest.length :=
    List.getElem?_eq_some_iff.mp hRestPointer |>.1
  have hFinalPointer :
      (rest.set depth value)[frameDepth]? =
        some (EvmYul.UInt256.ofNat frameBase) := by
    rw [List.getElem?_set_of_lt value rest hFrameBound]
    simp [Nat.ne_of_lt hDepthFrame, hRestPointer]
  refine
    { base :=
        hRel.base.assign_stack_live hStack hLive hLocation
          hDepth hOld
      framePointer := ?_
      frameActive := ?_
      frameAllocated := ?_
      frameNoWrap := hRel.frameNoWrap
      frameHostAddressable := hRel.frameHostAddressable
      activeNoWrap := ?_
      frameReserved := hRel.frameReserved
      scratchBound := hRel.scratchBound }
  · simpa [StateRel.replaceStackBy,
      Simulation.ResourceReplay.State.withSource,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hFinalPointer
  · simpa [StateRel.replaceStackBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.frameActive
  · simpa [StateRel.replaceStackBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.frameAllocated
  · simpa [StateRel.replaceStackBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.activeNoWrap

/--
Assigning a stack local under an arbitrary temporary prefix preserves the
hidden frame pointer and every scratch-frame invariant.
-/
theorem assign_stack_live_at
    {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords planDepth depth : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {value old : Word} {rest : List Word}
    (hRel :
      ScratchStateRel contract plan live (stackOffset + 1) frameBase
        frameDepth frameWords source target)
    (hStack : target.source.evm.stack = value :: rest)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hDepth :
      Locals.Layout.lookupDepth? name (currentStackOrder plan live) =
        some (depth + 1))
    (hDepthFrame : depth < frameDepth)
    (hOld : source.source.vars name = some old) :
    ScratchStateRel contract plan live stackOffset frameBase
      frameDepth frameWords
      (source.withSource (source.source.insert name value))
      (StateRel.replaceStackBy 2
        (rest.set (stackOffset + depth) value) target) := by
  have hPointer := hRel.framePointer
  rw [hStack] at hPointer
  have hRestPointer :
      rest[stackOffset + frameDepth]? =
        some (EvmYul.UInt256.ofNat frameBase) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hPointer
  have hFrameBound : stackOffset + frameDepth < rest.length :=
    List.getElem?_eq_some_iff.mp hRestPointer |>.1
  have hIndexNe :
      stackOffset + depth ≠ stackOffset + frameDepth := by
    omega
  have hIndexNe' :
      stackOffset + frameDepth ≠ stackOffset + depth := by
    omega
  have hDepthNe : depth ≠ frameDepth :=
    Nat.ne_of_lt hDepthFrame
  have hFinalPointer :
      (rest.set (stackOffset + depth) value)[
          stackOffset + frameDepth]? =
        some (EvmYul.UInt256.ofNat frameBase) := by
    rw [List.getElem?_set_of_lt value rest hFrameBound]
    simp [hIndexNe, hIndexNe', hDepthNe, hRestPointer]
  refine
    { base :=
        hRel.base.assign_stack_live_at hStack hLive hLocation
          hDepth hOld
      framePointer := ?_
      frameActive := ?_
      frameAllocated := ?_
      frameNoWrap := hRel.frameNoWrap
      frameHostAddressable := hRel.frameHostAddressable
      activeNoWrap := ?_
      frameReserved := hRel.frameReserved
      scratchBound := hRel.scratchBound }
  · simpa [StateRel.replaceStackBy,
      Simulation.ResourceReplay.State.withSource,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hFinalPointer
  · simpa [StateRel.replaceStackBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.frameActive
  · simpa [StateRel.replaceStackBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.frameAllocated
  · simpa [StateRel.replaceStackBy,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.activeNoWrap

theorem consume_forward {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {kind : Assembly.ResourceObserver} {value : Word}
    {source source' : SourceState transcript}
    {target : TargetState transcript}
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source target)
    (hConsume :
      Simulation.ResourceReplay.consume? kind source =
        some (value, source')) :
    ∃ target' : TargetState transcript,
      Simulation.ResourceReplay.consume? kind target =
          some (value, target') ∧
        ScratchStateRel contract plan live stackOffset frameBase
          frameDepth frameWords source' target' := by
  obtain ⟨target', hTarget, hBase⟩ :=
    hRel.base.consume_forward hConsume
  have hTargetSource : target'.source = target.source :=
    Simulation.ResourceReplay.consume?_source hTarget
  refine
    ⟨target', hTarget, hBase, ?_, ?_, ?_, hRel.frameNoWrap,
      hRel.frameHostAddressable, ?_, hRel.frameReserved,
      hRel.scratchBound⟩
  · simpa [hTargetSource] using hRel.framePointer
  · simpa [hTargetSource] using hRel.frameActive
  · simpa [hTargetSource] using hRel.frameAllocated
  · simpa [hTargetSource] using hRel.activeNoWrap

theorem consume_backward {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {kind : Assembly.ResourceObserver} {value : Word}
    {source : SourceState transcript}
    {target target' : TargetState transcript}
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source target)
    (hConsume :
      Simulation.ResourceReplay.consume? kind target =
        some (value, target')) :
    ∃ source' : SourceState transcript,
      Simulation.ResourceReplay.consume? kind source =
          some (value, source') ∧
        ScratchStateRel contract plan live stackOffset frameBase
          frameDepth frameWords source' target' := by
  obtain ⟨source', hSource, hBase⟩ :=
    hRel.base.consume_backward hConsume
  have hTargetSource : target'.source = target.source :=
    Simulation.ResourceReplay.consume?_source hConsume
  refine
    ⟨source', hSource, hBase, ?_, ?_, ?_, hRel.frameNoWrap,
      hRel.frameHostAddressable, ?_, hRel.frameReserved,
      hRel.scratchBound⟩
  · simpa [hTargetSource] using hRel.framePointer
  · simpa [hTargetSource] using hRel.frameActive
  · simpa [hTargetSource] using hRel.frameAllocated
  · simpa [hTargetSource] using hRel.activeNoWrap

end ScratchStateRel

/--
Transient realization while a procedure's raw entry parameters are being
converted to the allocation plan.

`pending` is in source parameter order. Its values therefore occupy the target
stack in reverse order above the already realized stack/scratch locals. The
ordinary `ScratchStateRel` begins below that pending prefix.
-/
structure CalleeEntryRel {transcript : Trace}
    (contract : MemoryContract.Contract) (plan : Plan)
    (realized : List Locals.Name)
    (pending : List (Locals.Name × Nat))
    (frameBase frameDepth frameWords : Nat)
    (source : SourceState transcript) (target : TargetState transcript) :
    Prop where
  state :
    ScratchStateRel contract plan realized pending.length frameBase
      frameDepth frameWords source target
  realization :
    ∃ values suffix,
      Functions.Source.Store.lookupMany
          (pending.map Prod.fst) source.source.vars =
        some values ∧
      target.source.evm.stack = values.reverse ++ suffix

namespace CalleeEntryRel

theorem finish {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {realized : List Locals.Name}
    {frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    (hRel :
      CalleeEntryRel contract plan realized [] frameBase
        frameDepth frameWords source target) :
    ScratchStateRel contract plan realized 0 frameBase
      frameDepth frameWords source target := by
  simpa using hRel.state

theorem cons_parts {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {realized : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {slot : Nat}
    (hRel :
      CalleeEntryRel contract plan realized
        ((name, slot) :: pending) frameBase frameDepth frameWords
        source target) :
    ∃ value values suffix,
      source.source.vars name = some value ∧
        Functions.Source.Store.lookupMany
            (pending.map Prod.fst) source.source.vars =
          some values ∧
        target.source.evm.stack =
          values.reverse ++ value :: suffix := by
  obtain ⟨allValues, suffix, hLookup, hStack⟩ := hRel.realization
  obtain ⟨value, values, hValue, hTail, hValues⟩ :=
    Functions.Source.Store.lookupMany_cons_parts hLookup
  rw [hValues] at hStack
  exact
    ⟨value, values, suffix, hValue, hTail, by
      simpa [List.reverse_cons, List.append_assoc] using hStack⟩

/--
Move one stack-designated pending parameter into the ordinary live-local
relation without changing target execution state.
-/
theorem activate_stack {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {realized : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameBase frameDepth frameWords planDepth : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {slot : Nat}
    (hRel :
      CalleeEntryRel contract plan realized
        ((name, slot) :: pending) frameBase frameDepth frameWords
        source target)
    (hFresh : name ∉ realized)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hStackOrder :
      currentStackOrder plan (name :: realized) =
        name :: currentStackOrder plan realized) :
    CalleeEntryRel contract plan (name :: realized) pending frameBase
      (frameDepth + 1) frameWords source target := by
  obtain ⟨value, values, suffix, hValue, hLookup, hStack⟩ :=
    hRel.cons_parts
  have hValueAt :
      target.source.evm.stack[pending.length]? = some value := by
    rw [hStack]
    have hLength :
        values.length = pending.length :=
      by
        simpa using Functions.Source.Store.lookupMany_length hLookup
    simp [hLength]
  refine
    { state := ?_
      realization :=
        ⟨values, value :: suffix, hLookup,
          by simpa [List.append_assoc] using hStack⟩ }
  apply hRel.state.declare_stack_live_existing_at
  · intro other hOther
    simp at hOther
    exact hOther
  · exact hFresh
  · simp
  · exact hLocation
  · exact hStackOrder
  · exact hValueAt
  · exact hValue

/--
Finish one scratch-parameter step after the compiler has written the value to
its frame slot and removed the original raw argument from the pending prefix.
-/
theorem activate_scratch_after {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {realized : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript}
    {target written final : TargetState transcript}
    {name : Locals.Name} {slot : Nat}
    {value : Word} {values suffix : List Word}
    (hRel :
      CalleeEntryRel contract plan realized
        ((name, slot) :: pending) frameBase frameDepth frameWords
        source target)
    (hLookup :
      Functions.Source.Store.lookupMany
          (pending.map Prod.fst) source.source.vars =
        some values)
    (hTargetStack :
      target.source.evm.stack =
        values.reverse ++ value :: suffix)
    (hWritten :
      ScratchStateRel contract plan (name :: realized)
        (pending.length + 1) frameBase frameDepth frameWords
        source written)
    (hWrittenStack : written.source.evm.stack = target.source.evm.stack)
    (hCursor : final.cursor = written.cursor)
    (hShared :
      final.source.evm.toSharedState =
        written.source.evm.toSharedState)
    (hFinalStack :
      final.source.evm.stack = values.reverse ++ suffix) :
    CalleeEntryRel contract plan (name :: realized) pending frameBase
      frameDepth frameWords source final := by
  have hLength :
      values.length = pending.length := by
    simpa using Functions.Source.Store.lookupMany_length hLookup
  have hOldStack :
      written.source.evm.stack =
        (values.reverse ++ [value]) ++ suffix := by
    rw [hWrittenStack, hTargetStack]
    simp [List.append_assoc]
  refine
    { state := ?_
      realization := ⟨values, suffix, hLookup, hFinalStack⟩ }
  have hWritten' :
      ScratchStateRel contract plan (name :: realized)
        (0 + (values.reverse ++ [value]).length) frameBase
        frameDepth frameWords source written := by
    simpa [hLength]
      using hWritten
  have hRebased :=
    ScratchStateRel.rebase_prefix_same_source hWritten'
      (stackOffset := 0)
      (oldPrefix := values.reverse ++ [value])
      (newPrefix := values.reverse)
      (baseStack := suffix)
      hCursor hShared hOldStack hFinalStack
  simpa [hLength] using hRebased

end CalleeEntryRel

/--
Runtime representation owned by one source activation.

Stack-only activations have no hidden frame pointer. Scratch activations carry
the pointer depth and fixed frame width required to realize spilled locals.
-/
inductive ActivationMode where
  | stack
  | scratch (frameDepth frameWords : Nat)
  deriving DecidableEq, Repr

namespace ActivationMode

def afterStackDeclaration : ActivationMode → ActivationMode
  | .stack => .stack
  | .scratch frameDepth frameWords =>
      .scratch (frameDepth + 1) frameWords

def StackDepthValid : ActivationMode → Nat → Prop
  | .stack, _depth => True
  | .scratch frameDepth _frameWords, depth => depth < frameDepth

def atStackDepth (mode : ActivationMode) (depth : Nat) : ActivationMode :=
  match mode with
  | .stack => .stack
  | .scratch _frameDepth frameWords =>
      .scratch depth frameWords

end ActivationMode

/--
Two activation modes use the same runtime representation and, for scratch
activations, the same fixed frame width. Lexical execution may change only the
hidden frame-pointer depth.
-/
inductive SameFrame : ActivationMode → ActivationMode → Prop where
  | stack : SameFrame .stack .stack
  | scratch (leftDepth rightDepth frameWords : Nat) :
      SameFrame
        (.scratch leftDepth frameWords)
        (.scratch rightDepth frameWords)

namespace SameFrame

theorem refl (mode : ActivationMode) : SameFrame mode mode := by
  cases mode with
  | stack =>
      exact .stack
  | scratch frameDepth frameWords =>
      exact .scratch frameDepth frameDepth frameWords

theorem symm
    {left right : ActivationMode}
    (hSame : SameFrame left right) :
    SameFrame right left := by
  cases hSame with
  | stack =>
      exact .stack
  | scratch leftDepth rightDepth frameWords =>
      exact .scratch rightDepth leftDepth frameWords

theorem trans
    {left middle right : ActivationMode}
    (hLeft : SameFrame left middle)
    (hRight : SameFrame middle right) :
    SameFrame left right := by
  cases hLeft with
  | stack =>
      cases hRight
      exact .stack
  | scratch leftDepth middleDepth frameWords =>
      cases hRight with
      | scratch _ rightDepth _ =>
          exact .scratch leftDepth rightDepth frameWords

theorem right_eq_stack_of_left_eq_stack
    {left right : ActivationMode}
    (hSame : SameFrame left right)
    (hLeft : left = .stack) :
    right = .stack := by
  cases hSame with
  | stack =>
      rfl
  | scratch =>
      cases hLeft

theorem afterStackDeclaration (mode : ActivationMode) :
    SameFrame mode mode.afterStackDeclaration := by
  cases mode with
  | stack =>
      exact .stack
  | scratch frameDepth frameWords =>
      exact .scratch frameDepth (frameDepth + 1) frameWords

theorem atStackDepth (mode : ActivationMode) (depth : Nat) :
    SameFrame mode (mode.atStackDepth depth) := by
  cases mode with
  | stack =>
      exact .stack
  | scratch frameDepth frameWords =>
      exact .scratch frameDepth depth frameWords

end SameFrame

/--
Every currently live local is stack-resident.

This is deliberately live-set indexed. A whole-plan stack-only theorem will
construct it once from the planner, while scoped proofs may restrict it.
-/
def LiveStackOnly (plan : Plan) (live : List Locals.Name) : Prop :=
  ∀ name slot,
    name ∈ live →
    plan.location? name = some (.scratch slot) →
    False

namespace StoreRel

/--
Construct the named-store relation from a concrete stack containing the source
values in the allocation plan's current runtime order.

This is the function-entry bridge: parameters arrive as raw EVM stack values
before declaration/prelude execution has established the ordinary activation
invariant.
-/
theorem of_lookupMany_currentStackOrder
    {plan : Plan} {live : List Locals.Name}
    {frameBase : Nat} {source : Locals.Source.State}
    {target : Structured.RunState} {values suffix : List Word}
    (hWF : plan.WellFormed)
    (hStackOnly : LiveStackOnly plan live)
    (hLookup :
      Functions.Source.Store.lookupMany
          (currentStackOrder plan live) source.vars =
        some values)
    (hStack : target.evm.stack = values ++ suffix) :
    StoreRel plan live 0 frameBase source target := by
  intro name location hLive hLocation
  cases location with
  | scratch slot =>
      exact False.elim (hStackOnly name slot hLive hLocation)
  | stack planDepth =>
      have hValid :=
        Locals.Allocation.Plan.bindingValid_of_wellFormed_of_location?_eq_some
          hWF hLocation
      have hPlanMem : name ∈ plan.stackOrder := by
        exact List.mem_of_getElem? hValid
      have hCurrentMem : name ∈ currentStackOrder plan live := by
        simp [currentStackOrder, hPlanMem, hLive]
      obtain ⟨depth, hDepth⟩ :=
        Locals.Layout.exists_lookupDepth?_eq_some_of_mem hCurrentMem
      have hNameAt :
          (currentStackOrder plan live)[depth]? = some name :=
        Locals.Layout.getElem?_eq_some_of_lookupDepth?_eq_some hDepth
      obtain ⟨value, hValueAt, hSourceValue⟩ :=
        Functions.Source.Store.lookupMany_getElem hLookup hNameAt
      have hValueBound : depth < values.length :=
        List.getElem?_eq_some_iff.mp hValueAt |>.1
      refine ⟨depth, hDepth, ?_⟩
      rw [Nat.zero_add, hStack,
        List.getElem?_append_left hValueBound,
        hValueAt, hSourceValue]

end StoreRel

/--
One relation for both allocator backends.

The stack constructor carries only ordinary named-local realization. The
scratch constructor carries the stronger active-frame invariants. Recursive
statement proofs can therefore preserve one interface without requiring an
impossible frame premise for stack-only artifacts or splitting into parallel
proof corridors.
-/
inductive ActivationStateRel {transcript : Trace}
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name) (stackOffset frameBase : Nat) :
    ActivationMode → SourceState transcript → TargetState transcript → Prop where
  | stack
      {source : SourceState transcript} {target : TargetState transcript}
      (liveStackOnly : LiveStackOnly plan live)
      (activeNoWrap :
        target.source.evm.activeWords.toNat * MemoryContract.wordBytes <
          EvmYul.UInt256.size)
      (state :
        StateRel contract plan live stackOffset frameBase source target) :
      ActivationStateRel contract plan live stackOffset frameBase
        .stack source target
  | scratch
      {frameDepth frameWords : Nat}
      {source : SourceState transcript} {target : TargetState transcript}
      (state :
        ScratchStateRel contract plan live stackOffset frameBase
          frameDepth frameWords source target) :
      ActivationStateRel contract plan live stackOffset frameBase
        (.scratch frameDepth frameWords) source target

namespace ActivationStateRel

/--
Restricting the source store to the current live scope preserves either
activation representation.
-/
theorem restrict_source_live {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {source : SourceState transcript} {target : TargetState transcript}
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase
        mode source target) :
    ActivationStateRel contract plan live stackOffset frameBase mode
      ((Functions.ObserverSemantics.stateModel transcript).restrictTo
        live source)
      target := by
  cases hRel with
  | stack hOnly hActive hState =>
      exact .stack hOnly hActive hState.restrict_source_live
  | scratch hScratch =>
      exact .scratch
        { hScratch with
          base := hScratch.base.restrict_source_live }

theorem transport_plan {transcript : Trace}
    {contract : MemoryContract.Contract}
    {left right : Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {source : SourceState transcript}
    {target : TargetState transcript}
    (hRel :
      ActivationStateRel contract left live stackOffset frameBase
        mode source target)
    (hAgree : PlanAgreesOn left right live) :
    ActivationStateRel contract right live stackOffset frameBase
      mode source target := by
  cases hRel with
  | stack hOnly hActive hState =>
      have hRightOnly : LiveStackOnly right live := by
        intro name slot hLive hRightLocation
        obtain
            ⟨leftLocation, agreedRightLocation,
              hLeftLocation, hAgreedRightLocation, hLocationAgree⟩ :=
          hAgree.location name hLive
        rw [hRightLocation] at hAgreedRightLocation
        cases hAgreedRightLocation
        cases hLocationAgree with
        | scratch agreedSlot =>
            exact hOnly name slot hLive hLeftLocation
      exact
        .stack hRightOnly hActive
          (hState.transport_plan hAgree)
  | scratch hScratch =>
      exact .scratch (hScratch.transport_plan hAgree)

theorem base {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {source : SourceState transcript} {target : TargetState transcript}
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase
        mode source target) :
    StateRel contract plan live stackOffset frameBase source target := by
  cases hRel with
  | stack _ _ state => exact state
  | scratch state => exact state.base

theorem activeNoWrap {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {source : SourceState transcript} {target : TargetState transcript}
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase
        mode source target) :
    target.source.evm.activeWords.toNat * MemoryContract.wordBytes <
      EvmYul.UInt256.size := by
  cases hRel with
  | stack _ activeNoWrap _ => exact activeNoWrap
  | scratch state => exact state.activeNoWrap

theorem mono {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {smaller larger : List Locals.Name}
    {stackOffset frameBase : Nat} {mode : ActivationMode}
    {source : SourceState transcript} {target : TargetState transcript}
    (hRel :
      ActivationStateRel contract plan larger stackOffset frameBase
        mode source target)
    (hSubset : ∀ name, name ∈ smaller → name ∈ larger)
    (hStackOrder :
      currentStackOrder plan smaller =
        currentStackOrder plan larger) :
    ActivationStateRel contract plan smaller stackOffset frameBase
      mode source target := by
  cases hRel with
  | stack hOnly activeNoWrap state =>
      exact .stack
        (fun name slot hLive hLocation =>
          hOnly name slot (hSubset name hLive) hLocation)
        activeNoWrap
        (state.mono hSubset hStackOrder)
  | scratch state =>
      exact .scratch (state.mono hSubset hStackOrder)

/--
Re-index an activation relation across extensionally equal live-name lists.

Source scopes are set-like, while the allocation plan chooses its own stable
stack order. The existing stack-order congruence and monotonicity theorem make
that representation difference invisible at adjacent proof boundaries.
-/
theorem reindex_live {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {before after : List Locals.Name}
    {stackOffset frameBase : Nat} {mode : ActivationMode}
    {source : SourceState transcript} {target : TargetState transcript}
    (hRel :
      ActivationStateRel contract plan before stackOffset frameBase
        mode source target)
    (hLive : ∀ name, name ∈ after ↔ name ∈ before) :
    ActivationStateRel contract plan after stackOffset frameBase
      mode source target :=
  hRel.mono
    (fun name hName => (hLive name).mp hName)
    (currentStackOrder_congr (plan := plan) hLive)

theorem push_target_by {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {source : SourceState transcript} {target : TargetState transcript}
    (pcDelta : Nat) (value : Word)
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase
        mode source target) :
    ActivationStateRel contract plan live (stackOffset + 1) frameBase
      mode source (StateRel.pushTargetBy pcDelta value target) := by
  cases hRel with
  | stack hOnly activeNoWrap state =>
      exact .stack hOnly
        (by
          simpa [StateRel.pushTargetBy,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC] using activeNoWrap)
        (state.push_target_by pcDelta value)
  | scratch state =>
      exact .scratch (state.push_target_by pcDelta value)

theorem push_target {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {source : SourceState transcript} {target : TargetState transcript}
    (value : Word)
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase
        mode source target) :
    ActivationStateRel contract plan live (stackOffset + 1) frameBase
      mode source (StateRel.pushTarget value target) := by
  simpa [StateRel.pushTarget] using hRel.push_target_by 1 value

theorem pop_target {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {source : SourceState transcript} {target : TargetState transcript}
    {value : Word} {rest : List Word}
    (hRel :
      ActivationStateRel contract plan live (stackOffset + 1) frameBase
        mode source target)
    (hStack : target.source.evm.stack = value :: rest) :
    ActivationStateRel contract plan live stackOffset frameBase mode
      source (StateRel.popTarget rest target) := by
  cases hRel with
  | stack hOnly activeNoWrap state =>
      exact
        .stack hOnly
          (by simpa [StateRel.popTarget] using activeNoWrap)
          (state.pop_target hStack)
  | scratch state =>
      exact .scratch (state.pop_target hStack)

/--
Rebase an activation across a target-only replacement of a temporary stack
prefix while preserving the source state and shared target state.
-/
theorem rebase_prefix_same_source {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {source : SourceState transcript}
    {target targetFinal : TargetState transcript}
    {oldPrefix newPrefix baseStack : List Word}
    (hRel :
      ActivationStateRel contract plan live
        (stackOffset + oldPrefix.length) frameBase mode source target)
    (hCursor : targetFinal.cursor = target.cursor)
    (hShared :
      targetFinal.source.evm.toSharedState =
        target.source.evm.toSharedState)
    (hOldStack :
      target.source.evm.stack = oldPrefix ++ baseStack)
    (hNewStack :
      targetFinal.source.evm.stack = newPrefix ++ baseStack) :
    ActivationStateRel contract plan live
      (stackOffset + newPrefix.length) frameBase mode source targetFinal := by
  cases hRel with
  | stack hOnly activeNoWrap state =>
      have hMachine :
          targetFinal.source.evm.toMachineState =
            target.source.evm.toMachineState :=
        congrArg EvmYul.SharedState.toMachineState hShared
      refine .stack hOnly ?_ ?_
      · simpa [hMachine] using activeNoWrap
      · refine
          { cursor := by simpa [hCursor] using state.cursor
            core :=
              { machine := by simpa [hMachine] using state.core.machine
                world := by simpa [hShared] using state.core.world
                store :=
                  state.core.store.rebase_prefix_stack_only hOnly
                    hOldStack hNewStack rfl } }
  | scratch state =>
      exact .scratch
        (state.rebase_prefix_same_source
          hCursor hShared hOldStack hNewStack)

theorem consume_forward {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {kind : Assembly.ResourceObserver} {value : Word}
    {source source' : SourceState transcript}
    {target : TargetState transcript}
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase
        mode source target)
    (hConsume :
      Simulation.ResourceReplay.consume? kind source =
        some (value, source')) :
    ∃ target' : TargetState transcript,
      Simulation.ResourceReplay.consume? kind target =
          some (value, target') ∧
        ActivationStateRel contract plan live stackOffset frameBase
          mode source' target' := by
  cases hRel with
  | stack hOnly activeNoWrap state =>
      obtain ⟨target', hTarget, hState⟩ :=
        state.consume_forward hConsume
      have hTargetSource : target'.source = target.source :=
        Simulation.ResourceReplay.consume?_source hTarget
      exact
        ⟨target', hTarget,
          .stack hOnly (by simpa [hTargetSource] using activeNoWrap) hState⟩
  | scratch state =>
      obtain ⟨target', hTarget, hState⟩ :=
        state.consume_forward hConsume
      exact ⟨target', hTarget, .scratch hState⟩

theorem consume_backward {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {kind : Assembly.ResourceObserver} {value : Word}
    {source : SourceState transcript}
    {target target' : TargetState transcript}
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase
        mode source target)
    (hConsume :
      Simulation.ResourceReplay.consume? kind target =
        some (value, target')) :
    ∃ source' : SourceState transcript,
      Simulation.ResourceReplay.consume? kind source =
          some (value, source') ∧
        ActivationStateRel contract plan live stackOffset frameBase
          mode source' target' := by
  cases hRel with
  | stack hOnly activeNoWrap state =>
      obtain ⟨source', hSource, hState⟩ :=
        state.consume_backward hConsume
      have hTargetSource : target'.source = target.source :=
        Simulation.ResourceReplay.consume?_source hConsume
      exact
        ⟨source', hSource,
          .stack hOnly (by simpa [hTargetSource] using activeNoWrap) hState⟩
  | scratch state =>
      obtain ⟨source', hSource, hState⟩ :=
        state.consume_backward hConsume
      exact ⟨source', hSource, .scratch hState⟩

theorem declare_stack_live {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {beforeLive afterLive : List Locals.Name}
    {frameBase planDepth : Nat} {mode : ActivationMode}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {value : Word} {rest : List Word}
    (hRel :
      ActivationStateRel contract plan beforeLive 1 frameBase
        mode source target)
    (hStack : target.source.evm.stack = value :: rest)
    (hAfter :
      ∀ other, other ∈ afterLive →
        other = name ∨ other ∈ beforeLive)
    (hNameAfter : name ∈ afterLive)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hStackOrder :
      currentStackOrder plan afterLive =
        name :: currentStackOrder plan beforeLive) :
    ActivationStateRel contract plan afterLive 0 frameBase
      mode.afterStackDeclaration
      (source.withSource (source.source.insert name value)) target := by
  cases hRel with
  | stack hOnly activeNoWrap state =>
      have hAfterOnly : LiveStackOnly plan afterLive := by
        intro other slot hOtherAfter hOtherLocation
        by_cases hName : other = name
        · subst other
          rw [hLocation] at hOtherLocation
          simp at hOtherLocation
        · have hOtherBefore : other ∈ beforeLive := by
            rcases hAfter other hOtherAfter with hEq | hBefore
            · exact False.elim (hName hEq)
            · exact hBefore
          exact hOnly other slot hOtherBefore hOtherLocation
      exact .stack hAfterOnly activeNoWrap
        (state.declare_stack_live hStack hAfter hNameAfter
          hLocation hStackOrder)
  | scratch state =>
      exact .scratch
        (state.declare_stack_live hStack hAfter hNameAfter
          hLocation hStackOrder)

theorem declare_stack_live_existing {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {beforeLive afterLive : List Locals.Name}
    {frameBase planDepth : Nat} {mode : ActivationMode}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {value : Word} {rest : List Word}
    (hRel :
      ActivationStateRel contract plan beforeLive 1 frameBase
        mode source target)
    (hStack : target.source.evm.stack = value :: rest)
    (hAfter :
      ∀ other, other ∈ afterLive →
        other = name ∨ other ∈ beforeLive)
    (hNameAfter : name ∈ afterLive)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hStackOrder :
      currentStackOrder plan afterLive =
        name :: currentStackOrder plan beforeLive)
    (hValue : source.source.vars name = some value) :
    ActivationStateRel contract plan afterLive 0 frameBase
      mode.afterStackDeclaration source target := by
  have hDeclared :=
    hRel.declare_stack_live hStack hAfter hNameAfter hLocation hStackOrder
  rw [Locals.Source.State.insert_eq_of_apply_eq hValue] at hDeclared
  simpa using hDeclared

end ActivationStateRel

namespace StateRel

/--
Activate an already initialized stack local immediately below an arbitrary
pending-value prefix.

This representation-neutral theorem is shared by stack-only and scratch-frame
activations.
-/
theorem declare_stack_live_existing_at
    {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {beforeLive afterLive : List Locals.Name}
    {stackOffset frameBase planDepth : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {value : Word}
    (hRel :
      StateRel contract plan beforeLive (stackOffset + 1) frameBase
        source target)
    (hAfter :
      ∀ other, other ∈ afterLive →
        other = name ∨ other ∈ beforeLive)
    (hFresh : name ∉ beforeLive)
    (hNameAfter : name ∈ afterLive)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hStackOrder :
      currentStackOrder plan afterLive =
        name :: currentStackOrder plan beforeLive)
    (hTargetValue : target.source.evm.stack[stackOffset]? = some value)
    (hValue : source.source.vars name = some value) :
    StateRel contract plan afterLive stackOffset frameBase
      source target := by
  refine
    { cursor := hRel.cursor
      core :=
        { machine := hRel.core.machine
          world := hRel.core.world
          store := ?_ } }
  intro other location hOtherAfter hOtherLocation
  rcases hAfter other hOtherAfter with hName | hBefore
  · subst other
    rw [hLocation] at hOtherLocation
    cases hOtherLocation
    refine ⟨0, ?_, ?_⟩
    · simpa [hStackOrder, Locals.Layout.lookupDepth?,
        Locals.Layout.lookupDepthFrom]
    · simpa [hValue] using hTargetValue
  · have hPrevious :=
      hRel.core.store other location hBefore hOtherLocation
    have hOtherNe : other ≠ name := by
      intro hEq
      subst other
      exact hFresh hBefore
    cases location with
    | stack otherPlanDepth =>
        rcases hPrevious with ⟨depth, hDepth, hStored⟩
        refine ⟨depth + 1, ?_, ?_⟩
        · rw [hStackOrder]
          simpa [Nat.add_assoc] using
            Locals.Layout.lookupDepth?_cons_of_ne hOtherNe.symm hDepth
        · change
            target.source.evm.stack[
                stackOffset + (depth + 1)]? =
              source.source.vars other
          change
            target.source.evm.stack[
                (stackOffset + 1) + depth]? =
              source.source.vars other at hStored
          rw [show
              stackOffset + (depth + 1) =
                (stackOffset + 1) + depth by omega]
          exact hStored
    | scratch slot =>
        exact hPrevious

end StateRel

namespace ActivationStateRel

/--
Activate an initialized stack local below a pending-value prefix in either
runtime representation.
-/
theorem declare_stack_live_existing_at
    {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {beforeLive afterLive : List Locals.Name}
    {stackOffset frameBase planDepth : Nat} {mode : ActivationMode}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {value : Word}
    (hRel :
      ActivationStateRel contract plan beforeLive (stackOffset + 1) frameBase
        mode source target)
    (hAfter :
      ∀ other, other ∈ afterLive →
        other = name ∨ other ∈ beforeLive)
    (hFresh : name ∉ beforeLive)
    (hNameAfter : name ∈ afterLive)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hStackOrder :
      currentStackOrder plan afterLive =
        name :: currentStackOrder plan beforeLive)
    (hTargetValue : target.source.evm.stack[stackOffset]? = some value)
    (hValue : source.source.vars name = some value) :
    ActivationStateRel contract plan afterLive stackOffset frameBase
      mode.afterStackDeclaration source target := by
  cases hRel with
  | stack hOnly hActive hState =>
      have hAfterOnly : LiveStackOnly plan afterLive := by
        intro other slot hOtherAfter hOtherLocation
        rcases hAfter other hOtherAfter with hName | hBefore
        · subst other
          rw [hLocation] at hOtherLocation
          simp at hOtherLocation
        · exact hOnly other slot hBefore hOtherLocation
      exact .stack hAfterOnly hActive
        (StateRel.declare_stack_live_existing_at hState hAfter hFresh
          hNameAfter hLocation hStackOrder hTargetValue hValue)
  | scratch hScratch =>
      exact .scratch
        (ScratchStateRel.declare_stack_live_existing_at hScratch hAfter hFresh
          hNameAfter hLocation hStackOrder hTargetValue hValue)

theorem assign_stack_live {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {frameBase planDepth depth : Nat}
    {mode : ActivationMode}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {value old : Word} {rest : List Word}
    (hRel :
      ActivationStateRel contract plan live 1 frameBase
        mode source target)
    (hStack : target.source.evm.stack = value :: rest)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hDepth :
      Locals.Layout.lookupDepth? name (currentStackOrder plan live) =
        some (depth + 1))
    (hDepthValid : mode.StackDepthValid depth)
    (hOld : source.source.vars name = some old) :
    ActivationStateRel contract plan live 0 frameBase mode
      (source.withSource (source.source.insert name value))
      (StateRel.replaceStackBy 2 (rest.set depth value) target) := by
  cases hRel with
  | stack liveStackOnly activeNoWrap state =>
      exact .stack liveStackOnly
        (by
          simpa [StateRel.replaceStackBy,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC] using activeNoWrap)
        (state.assign_stack_live hStack hLive hLocation hDepth hOld)
  | scratch state =>
      exact .scratch
        (state.assign_stack_live hStack hLive hLocation hDepth
          hDepthValid hOld)

/--
Representation-neutral stack assignment below an arbitrary temporary prefix.
-/
theorem assign_stack_live_at {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase planDepth depth : Nat}
    {mode : ActivationMode}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {value old : Word} {rest : List Word}
    (hRel :
      ActivationStateRel contract plan live (stackOffset + 1) frameBase
        mode source target)
    (hStack : target.source.evm.stack = value :: rest)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hDepth :
      Locals.Layout.lookupDepth? name (currentStackOrder plan live) =
        some (depth + 1))
    (hDepthValid : mode.StackDepthValid depth)
    (hOld : source.source.vars name = some old) :
    ActivationStateRel contract plan live stackOffset frameBase mode
      (source.withSource (source.source.insert name value))
      (StateRel.replaceStackBy 2
        (rest.set (stackOffset + depth) value) target) := by
  cases hRel with
  | stack liveStackOnly activeNoWrap state =>
      exact .stack liveStackOnly
        (by
          simpa [StateRel.replaceStackBy,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC] using activeNoWrap)
        (state.assign_stack_live_at hStack hLive hLocation hDepth hOld)
  | scratch state =>
      exact .scratch
        (state.assign_stack_live_at hStack hLive hLocation hDepth
          hDepthValid hOld)

theorem assign_scratch {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase : Nat} {mode : ActivationMode}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {slot : Nat} {value : Word}
    {rest : List Word}
    {reservation : MemoryContract.ScratchReservation}
    (hRel :
      ActivationStateRel contract plan live (stackOffset + 2) frameBase
        mode source target)
    (hWF : plan.WellFormed)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot))
    (hReservation : contract.scratch? = some reservation)
    (hRegion :
      reservation.containsRegion (scratchAddress frameBase slot) 1)
    (hStack :
      target.source.evm.stack =
        EvmYul.UInt256.ofNat (scratchAddress frameBase slot) ::
          value :: rest) :
    ActivationStateRel contract plan live stackOffset frameBase mode
      (source.withSource (source.source.insert name value))
      (StateRel.mstoreTarget
        (EvmYul.UInt256.ofNat (scratchAddress frameBase slot))
        value rest target) := by
  cases hRel with
  | stack liveStackOnly _activeNoWrap _state =>
      exact False.elim (liveStackOnly name slot hLive hLocation)
  | scratch state =>
      exact .scratch
        (state.assign_scratch hWF hLive hLocation
          hReservation hRegion hStack)

end ActivationStateRel

/--
Transient realization of raw procedure parameters in either runtime
representation.

The pending values occupy the target stack in reverse source order above the
already realized locals. Stack declarations update `mode` through
`afterStackDeclaration`; scratch declarations preserve it.
-/
structure ActivationCalleeEntryRel {transcript : Trace}
    (contract : MemoryContract.Contract) (plan : Plan)
    (realized : List Locals.Name)
    (pending : List (Locals.Name × Nat))
    (frameBase : Nat) (mode : ActivationMode)
    (source : SourceState transcript) (target : TargetState transcript) :
    Prop where
  state :
    ActivationStateRel contract plan realized pending.length frameBase
      mode source target
  realization :
    ∃ values suffix,
      Functions.Source.Store.lookupMany
          (pending.map Prod.fst) source.source.vars =
        some values ∧
      target.source.evm.stack = values.reverse ++ suffix

namespace ActivationCalleeEntryRel

/--
Construct an all-stack callee entry before any parameter has been activated.

The callee source store already contains every parameter and initialized
return, while the target data stack contains only the raw parameter values
above an arbitrary suffix. With no realized locals, the ordinary allocation
store relation is vacuous.
-/
theorem stack_empty {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {pending : List (Locals.Name × Nat)}
    {frameBase : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {values suffix : List Word}
    (hCursor : source.cursor = target.cursor)
    (hMachine :
      Compiler.MemoryRelation.MachineRel contract
        source.source.shared.toMachineState
        target.source.evm.toMachineState)
    (hWorld :
      source.source.shared.toState =
        target.source.evm.toSharedState.toState)
    (hActiveNoWrap :
      target.source.evm.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (hLookup :
      Functions.Source.Store.lookupMany
          (pending.map Prod.fst) source.source.vars =
        some values)
    (hStack :
      target.source.evm.stack = values.reverse ++ suffix) :
    ActivationCalleeEntryRel contract plan [] pending frameBase .stack
      source target := by
  refine
    { state := .stack ?_ hActiveNoWrap ?_
      realization := ⟨values, suffix, hLookup, hStack⟩ }
  · intro name slot hLive _hLocation
    simp at hLive
  · exact
      { cursor := hCursor
        core :=
          { machine := hMachine
            world := hWorld
            store := by
              intro name location hLive _hLocation
              simp at hLive } }

/--
Construct a scratch-frame callee entry before any parameter has been
activated.

The supplied frame facts are exactly those established by the canonical frame
acquisition sequence. The raw parameter values remain above the hidden frame
pointer until the real parameter prelude activates or spills them.
-/
theorem scratch_empty {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {pending : List (Locals.Name × Nat)}
    {frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    {values suffix : List Word}
    (hCursor : source.cursor = target.cursor)
    (hMachine :
      Compiler.MemoryRelation.MachineRel contract
        source.source.shared.toMachineState
        target.source.evm.toMachineState)
    (hWorld :
      source.source.shared.toState =
        target.source.evm.toSharedState.toState)
    (hFramePointer :
      target.source.evm.stack[pending.length + frameDepth]? =
        some (EvmYul.UInt256.ofNat frameBase))
    (hFrameActive :
      frameBase + MemoryContract.wordBytes * frameWords ≤
        target.source.evm.activeWords.toNat * MemoryContract.wordBytes)
    (hFrameAllocated :
      frameBase + MemoryContract.wordBytes * frameWords ≤
        target.source.evm.toMachineState.memory.size)
    (hFrameNoWrap :
      frameBase + MemoryContract.wordBytes * frameWords <
        EvmYul.UInt256.size)
    (hFrameHostAddressable :
      frameBase + MemoryContract.wordBytes * frameWords < USize.size)
    (hActiveNoWrap :
      target.source.evm.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (hFrameReserved :
      ∃ reservation,
        contract.scratch? = some reservation ∧
          reservation.containsRegion frameBase frameWords)
    (hLookup :
      Functions.Source.Store.lookupMany
          (pending.map Prod.fst) source.source.vars =
        some values)
    (hStack :
      target.source.evm.stack = values.reverse ++ suffix) :
    ActivationCalleeEntryRel contract plan [] pending frameBase
      (.scratch frameDepth frameWords) source target := by
  refine
    { state := .scratch ?_
      realization := ⟨values, suffix, hLookup, hStack⟩ }
  exact
    { base :=
        { cursor := hCursor
          core :=
            { machine := hMachine
              world := hWorld
              store := by
                intro name location hLive _hLocation
                simp at hLive } }
      framePointer := hFramePointer
      frameActive := hFrameActive
      frameAllocated := hFrameAllocated
      frameNoWrap := hFrameNoWrap
      frameHostAddressable := hFrameHostAddressable
      activeNoWrap := hActiveNoWrap
      frameReserved := hFrameReserved
      scratchBound := by
        intro name slot hLive _hLocation
        simp at hLive }

theorem finish {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {realized : List Locals.Name} {frameBase : Nat}
    {mode : ActivationMode}
    {source : SourceState transcript} {target : TargetState transcript}
    (hRel :
      ActivationCalleeEntryRel contract plan realized [] frameBase
        mode source target) :
    ActivationStateRel contract plan realized 0 frameBase
      mode source target := by
  simpa using hRel.state

theorem cons_parts {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {realized : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameBase : Nat} {mode : ActivationMode}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {slot : Nat}
    (hRel :
      ActivationCalleeEntryRel contract plan realized
        ((name, slot) :: pending) frameBase mode source target) :
    ∃ value values suffix,
      source.source.vars name = some value ∧
        Functions.Source.Store.lookupMany
            (pending.map Prod.fst) source.source.vars =
          some values ∧
        target.source.evm.stack =
          values.reverse ++ value :: suffix := by
  obtain ⟨allValues, suffix, hLookup, hStack⟩ := hRel.realization
  obtain ⟨value, values, hValue, hTail, hValues⟩ :=
    Functions.Source.Store.lookupMany_cons_parts hLookup
  rw [hValues] at hStack
  exact
    ⟨value, values, suffix, hValue, hTail, by
      simpa [List.reverse_cons, List.append_assoc] using hStack⟩

theorem activate_stack {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {realized : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameBase planDepth : Nat} {mode : ActivationMode}
    {source : SourceState transcript} {target : TargetState transcript}
    {name : Locals.Name} {slot : Nat}
    (hRel :
      ActivationCalleeEntryRel contract plan realized
        ((name, slot) :: pending) frameBase mode source target)
    (hFresh : name ∉ realized)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hStackOrder :
      currentStackOrder plan (name :: realized) =
        name :: currentStackOrder plan realized) :
    ActivationCalleeEntryRel contract plan (name :: realized) pending
      frameBase mode.afterStackDeclaration source target := by
  obtain ⟨value, values, suffix, hValue, hLookup, hStack⟩ :=
    hRel.cons_parts
  have hValueAt :
      target.source.evm.stack[pending.length]? = some value := by
    rw [hStack]
    have hLength :
        values.length = pending.length := by
      simpa using Functions.Source.Store.lookupMany_length hLookup
    simp [hLength]
  refine
    { state := ?_
      realization :=
        ⟨values, value :: suffix, hLookup,
          by simpa [List.append_assoc] using hStack⟩ }
  exact
    hRel.state.declare_stack_live_existing_at
      (fun other hOther => by
        simp at hOther
        exact hOther)
      hFresh (by simp) hLocation hStackOrder hValueAt hValue

theorem of_scratch {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {realized : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    (hRel :
      CalleeEntryRel contract plan realized pending frameBase
        frameDepth frameWords source target) :
    ActivationCalleeEntryRel contract plan realized pending frameBase
      (.scratch frameDepth frameWords) source target :=
  { state := .scratch hRel.state
    realization := hRel.realization }

theorem to_scratch {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {realized : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameBase frameDepth frameWords : Nat}
    {source : SourceState transcript} {target : TargetState transcript}
    (hRel :
      ActivationCalleeEntryRel contract plan realized pending frameBase
        (.scratch frameDepth frameWords) source target) :
    CalleeEntryRel contract plan realized pending frameBase
      frameDepth frameWords source target := by
  cases hRel.state with
  | scratch state =>
      exact
        { state := state
          realization := hRel.realization }

end ActivationCalleeEntryRel

/--
Expression result relation shared by stack-only and scratch activations.
-/
structure ActivationExprResultRel {transcript : Trace}
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name) (stackOffset frameBase resultCount : Nat)
    (mode : ActivationMode)
    (source : SourceState transcript)
    (targetInitial targetFinal : TargetState transcript)
    (values : List Word) : Prop where
  state :
    ActivationStateRel contract plan live
      (stackOffset + resultCount) frameBase mode source targetFinal
  valuesLength :
    values.length = resultCount
  stack :
    targetFinal.source.evm.stack =
      values.reverse ++ targetInitial.source.evm.stack

namespace ActivationExprResultRel

theorem nil {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {source : SourceState transcript} {target : TargetState transcript}
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase
        mode source target) :
    ActivationExprResultRel contract plan live stackOffset frameBase 0
      mode source target target [] := by
  exact ⟨by simpa using hRel, rfl, by simp⟩

theorem append {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {sourceHead sourceFinal : SourceState transcript}
    {targetInitial targetHead targetFinal : TargetState transcript}
    {headCount tailCount : Nat}
    {headValues tailValues : List Word}
    (hHead :
      ActivationExprResultRel contract plan live stackOffset frameBase
        headCount mode sourceHead targetInitial targetHead headValues)
    (hTail :
      ActivationExprResultRel contract plan live
        (stackOffset + headCount) frameBase tailCount mode
        sourceFinal targetHead targetFinal tailValues) :
    ActivationExprResultRel contract plan live stackOffset frameBase
      (headCount + tailCount) mode sourceFinal targetInitial targetFinal
      (headValues ++ tailValues) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [Nat.add_assoc] using hTail.state
  · simp [List.length_append, hHead.valuesLength, hTail.valuesLength]
  · rw [hTail.stack, hHead.stack]
    simp [List.reverse_append, List.append_assoc]

/--
Remove the concrete result prefix while retaining all source and target effects
of expression evaluation.
-/
theorem restore_base {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase resultCount : Nat}
    {mode : ActivationMode}
    {source : SourceState transcript}
    {targetInitial targetFinal : TargetState transcript}
    {values : List Word}
    (hRel :
      ActivationExprResultRel contract plan live stackOffset frameBase
        resultCount mode source targetInitial targetFinal values) :
    ActivationStateRel contract plan live stackOffset frameBase mode source
      (StateRel.popTarget targetInitial.source.evm.stack targetFinal) := by
  have hState :
      ActivationStateRel contract plan live
        (stackOffset + values.reverse.length) frameBase mode
        source targetFinal := by
    simpa [hRel.valuesLength] using hRel.state
  have hRebased :=
    hState.rebase_prefix_same_source
      (targetFinal :=
        StateRel.popTarget targetInitial.source.evm.stack targetFinal)
      (oldPrefix := values.reverse) (newPrefix := [])
      (baseStack := targetInitial.source.evm.stack)
      rfl
      rfl
      hRel.stack
      rfl
  simpa using hRebased

end ActivationExprResultRel

inductive ModeRel :
    Locals.Source.Mode → Structured.Mode → Prop where
  | regular : ModeRel .regular .regular
  | brk : ModeRel .brk .brk
  | cont : ModeRel .cont .cont
  | leave : ModeRel .leave .leave
  | halt (kind : Assembly.HaltKind) :
      ModeRel (.halt kind) (.halt kind)

/--
Terminal outcomes retain only observable shared state. Local-variable
realization is intentionally absent: the Locals compiler may discard every
local stack slot immediately before a halt, and no source continuation can
observe those bindings afterward.
-/
structure HaltStateRel {transcript : Trace}
    (contract : MemoryContract.Contract) (plan : Plan)
    (source : SourceState transcript) (target : TargetState transcript) :
    Prop where
  cursor : source.cursor = target.cursor
  shared : SharedRel contract source.source.shared target.source.evm.toSharedState

/--
Observable state at an activation exit.

All local and scratch-frame realization has been removed. The target stack is
exactly the returned values, in EVM top-first order, and those values are the
ordinary source lookup of the function's named returns.
-/
structure LeaveStateRel {transcript : Trace}
    (contract : MemoryContract.Contract) (returns : List Locals.Name)
    (source : SourceState transcript) (target : TargetState transcript) :
    Prop where
  cursor : source.cursor = target.cursor
  shared : SharedRel contract source.source.shared target.source.evm.toSharedState
  values :
    ∃ returned,
      Functions.Source.Store.lookupMany returns source.source.vars =
        some returned ∧
      target.source.evm.stack = returned.reverse

/--
Outcome relation retaining the active allocator representation for local
continuations and an exact value relation for activation exit.

For `leave`, `live` is interpreted as the function's ordered return names.
Both `leave` and terminal halts intentionally erase local and frame realization
because no source continuation can observe compiler cleanup after activation
exit.
-/
inductive ActivationOutcomeRel {transcript : Trace}
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name) (stackOffset frameBase : Nat)
    (mode : ActivationMode) :
    Functions.ObserverSemantics.Outcome (SourceState transcript) →
      Structured.ObserverSemantics.Outcome
        (transcript := transcript) → Prop where
  | regular
      {source : SourceState transcript} {target : TargetState transcript}
      (state :
        ActivationStateRel contract plan live stackOffset frameBase
          mode source target) :
      ActivationOutcomeRel contract plan live stackOffset frameBase mode
        (Functions.Source.Effectful.Outcome.regular source)
        (Structured.EffectSemantics.Outcome.regular target)
  | brk
      {source : SourceState transcript} {target : TargetState transcript}
      (state :
        ActivationStateRel contract plan live stackOffset frameBase
          mode source target) :
      ActivationOutcomeRel contract plan live stackOffset frameBase mode
        (Functions.Source.Effectful.Outcome.brk source)
        (Structured.EffectSemantics.Outcome.brk target)
  | cont
      {source : SourceState transcript} {target : TargetState transcript}
      (state :
        ActivationStateRel contract plan live stackOffset frameBase
          mode source target) :
      ActivationOutcomeRel contract plan live stackOffset frameBase mode
        (Functions.Source.Effectful.Outcome.cont source)
        (Structured.EffectSemantics.Outcome.cont target)
  | leave
      {source : SourceState transcript} {target : TargetState transcript}
      (state : LeaveStateRel contract live source target) :
      ActivationOutcomeRel contract plan live stackOffset frameBase mode
        (Functions.Source.Effectful.Outcome.leave source)
        (Structured.EffectSemantics.Outcome.leave target)
  | halt (kind : Assembly.HaltKind)
      {source : SourceState transcript} {target : TargetState transcript}
      (state : HaltStateRel contract plan source target) :
      ActivationOutcomeRel contract plan live stackOffset frameBase mode
        (Functions.Source.Effectful.Outcome.halt kind source)
        (Structured.EffectSemantics.Outcome.halt kind target)

namespace ActivationOutcomeRel

/--
Related continuing and terminal outcomes have exactly the same control mode.

This is the allocation-owned fact used by recursive statement-list
composition to show that both semantics skip the same unreachable tail.
-/
theorem modeRel {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {source :
      Functions.ObserverSemantics.Outcome (SourceState transcript)}
    {target :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (hRel :
      ActivationOutcomeRel contract plan live stackOffset frameBase mode
        source target) :
    ModeRel source.mode target.mode := by
  cases hRel with
  | regular _ => exact ModeRel.regular
  | brk _ => exact ModeRel.brk
  | cont _ => exact ModeRel.cont
  | leave _ => exact ModeRel.leave
  | halt kind _ => exact ModeRel.halt kind

theorem target_nonregular {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {source :
      Functions.ObserverSemantics.Outcome (SourceState transcript)}
    {target :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (hRel :
      ActivationOutcomeRel contract plan live stackOffset frameBase mode
        source target)
    (hSource : source.mode ≠ .regular) :
    target.mode ≠ .regular := by
  cases hRel with
  | regular _ =>
      exact False.elim (hSource rfl)
  | brk _ =>
      simp [Structured.EffectSemantics.Outcome.brk]
  | cont _ =>
      simp [Structured.EffectSemantics.Outcome.cont]
  | leave _ =>
      simp [Structured.EffectSemantics.Outcome.leave]
  | halt _ _ =>
      simp [Structured.EffectSemantics.Outcome.halt]

/--
The shared outcome relation preserves activation exit status.
-/
theorem target_isExit {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {source :
      Functions.ObserverSemantics.Outcome (SourceState transcript)}
    {target :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (hRel :
      ActivationOutcomeRel contract plan live stackOffset frameBase mode
        source target)
    (hSource :
      Functions.Source.Effectful.Outcome.IsExit source) :
    Structured.EffectSemantics.Outcome.IsExit target := by
  cases hRel with
  | regular _ =>
      simp [Functions.Source.Effectful.Outcome.IsExit,
        Functions.Source.Effectful.Outcome.regular,
        Locals.Source.Effectful.Outcome.regular] at hSource
  | brk _ =>
      simp [Functions.Source.Effectful.Outcome.IsExit,
        Functions.Source.Effectful.Outcome.brk,
        Locals.Source.Effectful.Outcome.brk] at hSource
  | cont _ =>
      simp [Functions.Source.Effectful.Outcome.IsExit,
        Functions.Source.Effectful.Outcome.cont,
        Locals.Source.Effectful.Outcome.cont] at hSource
  | leave _ =>
      simp [Structured.EffectSemantics.Outcome.IsExit,
        Structured.EffectSemantics.Outcome.leave]
  | halt kind _ =>
      simp [Structured.EffectSemantics.Outcome.IsExit,
        Structured.EffectSemantics.Outcome.halt]

/--
Activation representation is irrelevant after an activation exit.

`leave` has already materialized exactly the returned values and a terminal
halt exposes only shared state, so either relation may be re-indexed by any
activation mode.
-/
theorem reframe_of_isExit {transcript : Trace}
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {beforeMode afterMode : ActivationMode}
    {source :
      Functions.ObserverSemantics.Outcome (SourceState transcript)}
    {target :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (hRel :
      ActivationOutcomeRel contract plan live stackOffset frameBase
        beforeMode source target)
    (hExit :
      Functions.Source.Effectful.Outcome.IsExit source) :
    ActivationOutcomeRel contract plan live stackOffset frameBase
      afterMode source target := by
  cases hRel with
  | regular _ =>
      simp [Functions.Source.Effectful.Outcome.IsExit,
        Functions.Source.Effectful.Outcome.regular,
        Locals.Source.Effectful.Outcome.regular] at hExit
  | brk _ =>
      simp [Functions.Source.Effectful.Outcome.IsExit,
        Functions.Source.Effectful.Outcome.brk,
        Locals.Source.Effectful.Outcome.brk] at hExit
  | cont _ =>
      simp [Functions.Source.Effectful.Outcome.IsExit,
        Functions.Source.Effectful.Outcome.cont,
        Locals.Source.Effectful.Outcome.cont] at hExit
  | leave hState =>
      exact .leave hState
  | halt kind hState =>
      exact .halt kind hState

/--
After an activation exit, the allocation plan and non-return live environment
are unobservable. `leave` still requires the same ordered return-name list;
terminal halts erase both indices completely.
-/
theorem transport_of_isExit {transcript : Trace}
    {contract : MemoryContract.Contract}
    {beforePlan afterPlan : Plan}
    {beforeLive afterLive : List Locals.Name}
    {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {source :
      Functions.ObserverSemantics.Outcome (SourceState transcript)}
    {target :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (hRel :
      ActivationOutcomeRel contract beforePlan beforeLive
        stackOffset frameBase mode source target)
    (hExit :
      Functions.Source.Effectful.Outcome.IsExit source)
    (hLeaveLive :
      source.mode = .leave → beforeLive = afterLive) :
    ActivationOutcomeRel contract afterPlan afterLive
      stackOffset frameBase mode source target := by
  cases hRel with
  | regular _ =>
      simp [Functions.Source.Effectful.Outcome.IsExit,
        Functions.Source.Effectful.Outcome.regular,
        Locals.Source.Effectful.Outcome.regular] at hExit
  | brk _ =>
      simp [Functions.Source.Effectful.Outcome.IsExit,
        Functions.Source.Effectful.Outcome.brk,
        Locals.Source.Effectful.Outcome.brk] at hExit
  | cont _ =>
      simp [Functions.Source.Effectful.Outcome.IsExit,
        Functions.Source.Effectful.Outcome.cont,
        Locals.Source.Effectful.Outcome.cont] at hExit
  | leave hState =>
      have hLive := hLeaveLive rfl
      cases hLive
      exact .leave hState
  | halt kind hState =>
      exact .halt kind
        { cursor := hState.cursor
          shared := hState.shared }

end ActivationOutcomeRel

/--
Outcome-indexed allocation relation.

Continuing control modes retain the complete named-local realization. Halting
outcomes retain only the shared EVM state and observer cursor because compiler
cleanup is free to erase dead local representation before the terminal step.
-/
inductive OutcomeRel {transcript : Trace}
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name) (stackOffset frameBase : Nat) :
    Functions.ObserverSemantics.Outcome (SourceState transcript) →
      Structured.ObserverSemantics.Outcome
        (transcript := transcript) → Prop where
  | regular
      {source : SourceState transcript} {target : TargetState transcript}
      (state :
        StateRel contract plan live stackOffset frameBase source target) :
      OutcomeRel contract plan live stackOffset frameBase
        (Functions.Source.Effectful.Outcome.regular source)
        (Structured.EffectSemantics.Outcome.regular target)
  | brk
      {source : SourceState transcript} {target : TargetState transcript}
      (state :
        StateRel contract plan live stackOffset frameBase source target) :
      OutcomeRel contract plan live stackOffset frameBase
        (Functions.Source.Effectful.Outcome.brk source)
        (Structured.EffectSemantics.Outcome.brk target)
  | cont
      {source : SourceState transcript} {target : TargetState transcript}
      (state :
        StateRel contract plan live stackOffset frameBase source target) :
      OutcomeRel contract plan live stackOffset frameBase
        (Functions.Source.Effectful.Outcome.cont source)
        (Structured.EffectSemantics.Outcome.cont target)
  | leave
      {source : SourceState transcript} {target : TargetState transcript}
      (state :
        StateRel contract plan live stackOffset frameBase source target) :
      OutcomeRel contract plan live stackOffset frameBase
        (Functions.Source.Effectful.Outcome.leave source)
        (Structured.EffectSemantics.Outcome.leave target)
  | halt (kind : Assembly.HaltKind)
      {source : SourceState transcript} {target : TargetState transcript}
      (state : HaltStateRel contract plan source target) :
      OutcomeRel contract plan live stackOffset frameBase
        (Functions.Source.Effectful.Outcome.halt kind source)
        (Structured.EffectSemantics.Outcome.halt kind target)

namespace Frame

abbrev Config := AllocationSupport.ScratchFrameConfig

def bytes (config : Config) : Nat :=
  MemoryContract.wordBytes * config.frameWords

/--
Allocator value after `depth` active scratch frames.

The allocator cell initially contains `firstFrame`. Acquiring a frame returns
the current value and advances the cell by one fixed frame width.
-/
def baseAt (config : Config) (depth : Nat) : Nat :=
  config.firstFrame + depth * bytes config

def Budget (config : Config) (depth : Nat) : Prop :=
  baseAt config depth + bytes config ≤ config.limit

/--
Compiler-selected recursive resource mode.

Stack-only programs have no allocator metadata or suspended scratch frames.
Scratch-backed programs reuse the existing concrete allocator relations. This
index lets the recursive proof share one control dispatcher without inventing
allocator state for all-stack compiler outputs.
-/
inductive ResourceMode where
  | stackOnly
  | scratch (config : Config)
  deriving Repr

namespace ResourceMode

def Budget : ResourceMode → Nat → Prop
  | .stackOnly, _depth => True
  | .scratch config, depth => Frame.Budget config depth

def FuelSafe (mode : ResourceMode) (fuel : Nat) : Prop :=
  mode.Budget fuel

end ResourceMode

def AllocatorAt {transcript : Trace} (config : Config) (depth : Nat)
    (target : TargetState transcript) : Prop :=
  target.source.evm.toMachineState.lookupMemory
      (EvmYul.UInt256.ofNat config.allocatorCell) =
    EvmYul.UInt256.ofNat (baseAt config depth)

/--
Target execution may grow active and materialized memory but never shrinks
either component.

This resource relation is independent of allocator metadata and is shared by
expression preservation, nested-frame entry, and later call composition.
-/
structure TargetGrowth {transcript : Trace}
    (before after : TargetState transcript) : Prop where
  active :
    before.source.evm.activeWords.toNat ≤
      after.source.evm.activeWords.toNat
  memory :
    before.source.evm.toMachineState.memory.size ≤
      after.source.evm.toMachineState.memory.size

namespace TargetGrowth

theorem refl {transcript : Trace}
    (target : TargetState transcript) :
    TargetGrowth target target :=
  ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem trans {transcript : Trace}
    {first second third : TargetState transcript}
    (hLeft : TargetGrowth first second)
    (hRight : TargetGrowth second third) :
    TargetGrowth first third :=
  ⟨hLeft.active.trans hRight.active,
    hLeft.memory.trans hRight.memory⟩

end TargetGrowth

/--
A target transition leaves every already-active, materialized compiler-owned
word below `depth` unchanged.

This is the compositional memory invariant for suspended callers. A nested
callee may write its own frame at `baseAt config depth` or above, while source
memory operations remain outside the compiler reservation. Requiring the word
to exist before the transition avoids treating newly exposed dormant bytes as
part of the caller's saved state.
-/
structure ProtectedPrefix {transcript : Trace}
    (config : Config) (depth : Nat)
    (before after : TargetState transcript) : Prop where
  growth : TargetGrowth before after
  lookup :
    ∀ {address : Nat},
      config.firstFrame ≤ address →
      address + MemoryContract.wordBytes ≤ baseAt config depth →
      address + MemoryContract.wordBytes ≤
        before.source.evm.toMachineState.memory.size →
      address + MemoryContract.wordBytes ≤
        before.source.evm.activeWords.toNat * MemoryContract.wordBytes →
      after.source.evm.toMachineState.lookupMemory
          (EvmYul.UInt256.ofNat address) =
        before.source.evm.toMachineState.lookupMemory
          (EvmYul.UInt256.ofNat address)

namespace ProtectedPrefix

theorem refl {transcript : Trace}
    (config : Config) (depth : Nat)
    (target : TargetState transcript) :
    ProtectedPrefix config depth target target :=
  ⟨TargetGrowth.refl target, by intros; rfl⟩

theorem trans {transcript : Trace}
    {config : Config} {depth : Nat}
    {first second third : TargetState transcript}
    (hFirst : ProtectedPrefix config depth first second)
    (hSecond : ProtectedPrefix config depth second third) :
    ProtectedPrefix config depth first third := by
  refine ⟨hFirst.growth.trans hSecond.growth, ?_⟩
  intro address hStart hEnd hMemory hActive
  have hMiddleMemory :
      address + MemoryContract.wordBytes ≤
        second.source.evm.toMachineState.memory.size :=
    hMemory.trans hFirst.growth.memory
  have hMiddleActive :
      address + MemoryContract.wordBytes ≤
        second.source.evm.activeWords.toNat *
          MemoryContract.wordBytes :=
    hActive.trans
      (Nat.mul_le_mul_right
        MemoryContract.wordBytes hFirst.growth.active)
  exact
    (hSecond.lookup hStart hEnd hMiddleMemory hMiddleActive).trans
      (hFirst.lookup hStart hEnd hMemory hActive)

theorem of_machine_eq {transcript : Trace}
    {config : Config} {depth : Nat}
    {before after : TargetState transcript}
    (hMachine :
      after.source.evm.toMachineState =
        before.source.evm.toMachineState) :
    ProtectedPrefix config depth before after := by
  refine ⟨?_, ?_⟩
  · exact
      ⟨by simpa [hMachine],
        by simpa [hMachine]⟩
  · intro address _hStart _hEnd _hMemory _hActive
    change
      after.source.evm.toMachineState.lookupMemory
          (EvmYul.UInt256.ofNat address) =
        before.source.evm.toMachineState.lookupMemory
          (EvmYul.UInt256.ofNat address)
    rw [hMachine]

/--
Growing active memory without changing materialized bytes preserves every
already-active word in the protected compiler prefix.
-/
theorem of_memory_eq_active_growth {transcript : Trace}
    {config : Config} {depth : Nat}
    {before after : TargetState transcript}
    (hMemory :
      after.source.evm.toMachineState.memory =
        before.source.evm.toMachineState.memory)
    (hActive :
      before.source.evm.activeWords.toNat ≤
        after.source.evm.activeWords.toNat)
    (hBeforeNoWrap :
      before.source.evm.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (hAfterNoWrap :
      after.source.evm.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size) :
    ProtectedPrefix config depth before after := by
  refine
    { growth :=
        { active := hActive
          memory := by simpa [hMemory] }
      lookup := ?_ }
  intro address _hStart _hEnd hReadMemory hReadActive
  have hAddressLt :
      address < EvmYul.UInt256.size := by
    exact lt_of_le_of_lt
      (Nat.le_add_right address MemoryContract.wordBytes)
      (hReadActive.trans_lt hBeforeNoWrap)
  exact
    Compiler.MemoryRelation.MachineRel.lookupMemory_eq_of_memory_eq_active_growth
      address
      (EvmYul.UInt256.toNat_ofNat_of_lt hAddressLt)
      hMemory hActive hBeforeNoWrap hAfterNoWrap
      hReadMemory hReadActive

end ProtectedPrefix

structure AllocatorReady {transcript : Trace}
    (config : Config) (depth : Nat)
    (target : TargetState transcript) : Prop where
  allocatorAt : AllocatorAt config depth target
  cellActive :
    config.allocatorCell + MemoryContract.wordBytes ≤
      target.source.evm.activeWords.toNat * MemoryContract.wordBytes
  cellAllocated :
    config.allocatorCell + MemoryContract.wordBytes ≤
      target.source.evm.toMachineState.memory.size
  activeNoWrap :
    target.source.evm.activeWords.toNat * MemoryContract.wordBytes <
      EvmYul.UInt256.size

namespace AllocatorReady

/--
Transport allocator readiness across target execution that leaves the
allocator word unchanged while growing active and materialized memory.

This is the common target-side interface used by ordinary source primitives
and compiler-owned spill accesses. Only frame acquire/release deliberately
change the allocator word.
-/
theorem of_lookup_growth
    {transcript : Trace}
    {config : Config} {depth : Nat}
    {before after : TargetState transcript}
    (hReady : AllocatorReady config depth before)
    (hLookup :
      after.source.evm.toMachineState.lookupMemory
          (EvmYul.UInt256.ofNat config.allocatorCell) =
        before.source.evm.toMachineState.lookupMemory
          (EvmYul.UInt256.ofNat config.allocatorCell))
    (hActive :
      before.source.evm.activeWords.toNat ≤
        after.source.evm.activeWords.toNat)
    (hMemory :
      before.source.evm.toMachineState.memory.size ≤
        after.source.evm.toMachineState.memory.size)
    (hNoWrap :
      after.source.evm.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size) :
    AllocatorReady config depth after := by
  refine
    { allocatorAt := ?_
      cellActive := ?_
      cellAllocated := ?_
      activeNoWrap := hNoWrap }
  · exact hLookup.trans hReady.allocatorAt
  · exact hReady.cellActive.trans
      (Nat.mul_le_mul_right MemoryContract.wordBytes hActive)
  · exact hReady.cellAllocated.trans hMemory

/--
Active-memory growth with identical materialized memory preserves allocator
readiness.
-/
theorem of_memory_eq_active_growth
    {transcript : Trace}
    {config : Config} {depth : Nat}
    {before after : TargetState transcript}
    (hReady : AllocatorReady config depth before)
    (hMemory :
      after.source.evm.toMachineState.memory =
        before.source.evm.toMachineState.memory)
    (hActive :
      before.source.evm.activeWords.toNat ≤
        after.source.evm.activeWords.toNat)
    (hNoWrap :
      after.source.evm.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size) :
    AllocatorReady config depth after := by
  have hCellLt :
      config.allocatorCell < EvmYul.UInt256.size := by
    exact lt_of_le_of_lt
      (Nat.le_add_right config.allocatorCell MemoryContract.wordBytes)
      (hReady.cellActive.trans_lt hReady.activeNoWrap)
  have hCellWord :
      (EvmYul.UInt256.ofNat config.allocatorCell).toNat =
        config.allocatorCell :=
    EvmYul.UInt256.toNat_ofNat_of_lt hCellLt
  have hLookup :=
    Compiler.MemoryRelation.MachineRel.lookupMemory_eq_of_memory_eq_active_growth
        config.allocatorCell hCellWord hMemory hActive
        hReady.activeNoWrap hNoWrap
        hReady.cellAllocated hReady.cellActive
  apply hReady.of_lookup_growth hLookup hActive
  · simpa [hMemory]
  · exact hNoWrap

/--
An unchanged target machine preserves allocator readiness exactly.
-/
theorem of_machine_eq
    {transcript : Trace}
    {config : Config} {depth : Nat}
    {before after : TargetState transcript}
    (hReady : AllocatorReady config depth before)
    (hMachine :
      after.source.evm.toMachineState =
        before.source.evm.toMachineState) :
    AllocatorReady config depth after := by
  apply hReady.of_memory_eq_active_growth
  · simpa [hMachine]
  · simpa [hMachine]
  · simpa [hMachine] using hReady.activeNoWrap

/--
A target `MSTORE` disjoint from the allocator cell preserves allocator
readiness. This is the compiler-owned spill-store counterpart of the
source-primitive allocator theorem.
-/
theorem of_mstore_disjoint
    {transcript : Trace}
    {config : Config} {depth address : Nat} {value : Word}
    {before after : TargetState transcript}
    (hReady : AllocatorReady config depth before)
    (hMachine :
      after.source.evm.toMachineState =
        before.source.evm.toMachineState.mstore
          (EvmYul.UInt256.ofNat address) value)
    (hAddress :
      (EvmYul.UInt256.ofNat address).toNat = address)
    (hHost : address + MemoryContract.wordBytes < USize.size)
    (hDisjoint :
      config.allocatorCell + MemoryContract.wordBytes ≤ address ∨
        address + MemoryContract.wordBytes ≤ config.allocatorCell) :
    AllocatorReady config depth after := by
  have hCellLt :
      config.allocatorCell < EvmYul.UInt256.size := by
    exact lt_of_le_of_lt
      (Nat.le_add_right config.allocatorCell MemoryContract.wordBytes)
      (hReady.cellActive.trans_lt hReady.activeNoWrap)
  have hCell :
      (EvmYul.UInt256.ofNat config.allocatorCell).toNat =
        config.allocatorCell :=
    EvmYul.UInt256.toNat_ofNat_of_lt hCellLt
  have hLookup :
      after.source.evm.toMachineState.lookupMemory
            (EvmYul.UInt256.ofNat config.allocatorCell) =
        before.source.evm.toMachineState.lookupMemory
            (EvmYul.UInt256.ofNat config.allocatorCell) := by
    rw [hMachine]
    exact
      Compiler.MemoryRelation.lookupMemory_mstore_disjoint_growing
        before.source.evm.toMachineState address config.allocatorCell value
        hAddress hCell
        (by simpa [MemoryContract.wordBytes] using hHost)
        (by simpa [MemoryContract.wordBytes] using hReady.cellAllocated)
        (by simpa [MemoryContract.wordBytes] using hReady.cellActive)
        (by simpa [MemoryContract.wordBytes] using hReady.activeNoWrap)
        (by simpa [MemoryContract.wordBytes] using hDisjoint)
  have hAddressEnd :
      address + MemoryContract.wordBytes < EvmYul.UInt256.size :=
    lt_trans hHost Compiler.MemoryRelation.usize_size_lt_uint256_size
  have hActive :
      before.source.evm.activeWords.toNat ≤
        after.source.evm.activeWords.toNat := by
    rw [hMachine]
    exact
      Compiler.MemoryRelation.activeWords_toNat_le_mstore
        before.source.evm.toMachineState address value hAddressEnd
  have hMemory :
      before.source.evm.toMachineState.memory.size ≤
        after.source.evm.toMachineState.memory.size := by
    rw [hMachine]
    simpa [EvmYul.MachineState.mstore] using
      (Compiler.MemoryRelation.writeWord_memory_size_ge
        before.source.evm.toMachineState address value hAddress
        (by simpa [MemoryContract.wordBytes] using hHost))
  have hNoWrap :
      after.source.evm.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
    rw [hMachine]
    simpa [MemoryContract.wordBytes] using
      (Compiler.MemoryRelation.mstore_activeBytes_lt_size_of_activeBytes_lt_size
        before.source.evm.toMachineState address value
        (by simpa [MemoryContract.wordBytes] using hReady.activeNoWrap)
        (by simpa [MemoryContract.wordBytes] using hHost))
  exact hReady.of_lookup_growth hLookup hActive hMemory hNoWrap

end AllocatorReady

namespace ResourceMode

def Ready {transcript : Trace}
    (mode : ResourceMode) (depth : Nat)
    (target : TargetState transcript) : Prop :=
  match mode with
  | .stackOnly => True
  | .scratch config => AllocatorReady config depth target

end ResourceMode

/--
Resource effect of ordinary target execution at a fixed allocator depth.

Growth and allocator readiness are unconditional. Protected-prefix
preservation is available when the current depth fits inside the checked
scratch reservation. Keeping all three facts in one transition interface lets
recursive expression and statement proofs compose effects without replaying
the underlying semantics.
-/
structure AllocatorEffect {transcript : Trace}
    (config : Config) (depth : Nat)
    (before after : TargetState transcript) : Prop where
  ready : AllocatorReady config depth after
  growth : TargetGrowth before after
  prefixStable :
    ∀ {protectedDepth : Nat},
      protectedDepth ≤ depth →
      Budget config protectedDepth →
      ProtectedPrefix config protectedDepth before after

namespace AllocatorEffect

theorem refl {transcript : Trace}
    {config : Config} {depth : Nat}
    {target : TargetState transcript}
    (hReady : AllocatorReady config depth target) :
    AllocatorEffect config depth target target :=
  { ready := hReady
    growth := TargetGrowth.refl target
    prefixStable :=
      fun {_protectedDepth} _hDepth _hBudget =>
        ProtectedPrefix.refl config _protectedDepth target }

theorem trans {transcript : Trace}
    {config : Config} {depth : Nat}
    {first second third : TargetState transcript}
    (hFirst : AllocatorEffect config depth first second)
    (hSecond : AllocatorEffect config depth second third) :
    AllocatorEffect config depth first third :=
  { ready := hSecond.ready
    growth := hFirst.growth.trans hSecond.growth
    prefixStable := fun hDepth hBudget =>
      (hFirst.prefixStable hDepth hBudget).trans
        (hSecond.prefixStable hDepth hBudget) }

theorem of_machine_eq {transcript : Trace}
    {config : Config} {depth : Nat}
    {before after : TargetState transcript}
    (hReady : AllocatorReady config depth before)
    (hMachine :
      after.source.evm.toMachineState =
        before.source.evm.toMachineState) :
    AllocatorEffect config depth before after :=
  { ready := hReady.of_machine_eq hMachine
    growth :=
      { active := by simpa [hMachine]
        memory := by simpa [hMachine] }
    prefixStable := fun _hDepth _hBudget =>
      ProtectedPrefix.of_machine_eq hMachine }

theorem of_memory_eq_active_growth {transcript : Trace}
    {config : Config} {depth : Nat}
    {before after : TargetState transcript}
    (hReady : AllocatorReady config depth before)
    (hMemory :
      after.source.evm.toMachineState.memory =
        before.source.evm.toMachineState.memory)
    (hActive :
      before.source.evm.activeWords.toNat ≤
        after.source.evm.activeWords.toNat)
    (hAfterNoWrap :
      after.source.evm.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size) :
    AllocatorEffect config depth before after :=
  { ready :=
      hReady.of_memory_eq_active_growth hMemory hActive hAfterNoWrap
    growth :=
      { active := hActive
        memory := by simpa [hMemory] }
    prefixStable := fun _hDepth _hBudget =>
      ProtectedPrefix.of_memory_eq_active_growth
        hMemory hActive hReady.activeNoWrap hAfterNoWrap }

end AllocatorEffect

/--
Resource effect of statement execution at a fixed allocator depth.

Statements may update compiler spills in the current activation, so they
preserve only frames suspended strictly below `depth`. Expression execution
uses the stronger `AllocatorEffect`, which also protects the current frame.
-/
structure SuspendedEffect {transcript : Trace}
    (config : Config) (depth : Nat)
    (before after : TargetState transcript) : Prop where
  ready : AllocatorReady config depth after
  growth : TargetGrowth before after
  prefixStable :
    ∀ {protectedDepth : Nat},
      protectedDepth < depth →
      Budget config protectedDepth →
      ProtectedPrefix config protectedDepth before after

namespace SuspendedEffect

theorem of_allocatorEffect {transcript : Trace}
    {config : Config} {depth : Nat}
    {before after : TargetState transcript}
    (hEffect : AllocatorEffect config depth before after) :
    SuspendedEffect config depth before after :=
  { ready := hEffect.ready
    growth := hEffect.growth
    prefixStable := fun hDepth hBudget =>
      hEffect.prefixStable (Nat.le_of_lt hDepth) hBudget }

theorem refl {transcript : Trace}
    {config : Config} {depth : Nat}
    {target : TargetState transcript}
    (hReady : AllocatorReady config depth target) :
    SuspendedEffect config depth target target :=
  of_allocatorEffect (AllocatorEffect.refl hReady)

theorem trans {transcript : Trace}
    {config : Config} {depth : Nat}
    {first second third : TargetState transcript}
    (hFirst : SuspendedEffect config depth first second)
    (hSecond : SuspendedEffect config depth second third) :
    SuspendedEffect config depth first third :=
  { ready := hSecond.ready
    growth := hFirst.growth.trans hSecond.growth
    prefixStable := fun hDepth hBudget =>
      (hFirst.prefixStable hDepth hBudget).trans
        (hSecond.prefixStable hDepth hBudget) }

/--
One target `MSTORE` above every suspended prefix preserves the complete
statement resource effect.
-/
theorem of_mstore_above
    {transcript : Trace}
    {config : Config} {depth address : Nat} {value : Word}
    {before after : TargetState transcript}
    (hReady : AllocatorReady config depth before)
    (hMachine :
      after.source.evm.toMachineState =
        before.source.evm.toMachineState.mstore
          (EvmYul.UInt256.ofNat address) value)
    (hAddress :
      (EvmYul.UInt256.ofNat address).toNat = address)
    (hHost : address + MemoryContract.wordBytes < USize.size)
    (hAllocatorDisjoint :
      config.allocatorCell + MemoryContract.wordBytes ≤ address ∨
        address + MemoryContract.wordBytes ≤ config.allocatorCell)
    (hAbove :
      ∀ {protectedDepth : Nat},
        protectedDepth < depth →
        baseAt config protectedDepth ≤ address) :
    SuspendedEffect config depth before after := by
  have hFinalReady :=
    hReady.of_mstore_disjoint hMachine hAddress hHost hAllocatorDisjoint
  have hAddressEnd :
      address + MemoryContract.wordBytes < EvmYul.UInt256.size :=
    lt_trans hHost Compiler.MemoryRelation.usize_size_lt_uint256_size
  have hGrowth : TargetGrowth before after := by
    refine ⟨?_, ?_⟩
    · rw [hMachine]
      exact
        Compiler.MemoryRelation.activeWords_toNat_le_mstore
          before.source.evm.toMachineState address value hAddressEnd
    · rw [hMachine]
      simpa [EvmYul.MachineState.mstore] using
        (Compiler.MemoryRelation.writeWord_memory_size_ge
          before.source.evm.toMachineState address value hAddress
          (by simpa [MemoryContract.wordBytes] using hHost))
  refine
    { ready := hFinalReady
      growth := hGrowth
      prefixStable := ?_ }
  intro protectedDepth hDepth _hBudget
  refine
    { growth := hGrowth
      lookup := ?_ }
  intro query _hStart hEnd hReadMemory hReadActive
  have hQueryLt : query < EvmYul.UInt256.size := by
    exact lt_of_le_of_lt
      (Nat.le_add_right query MemoryContract.wordBytes)
      (hReadActive.trans_lt hReady.activeNoWrap)
  have hQuery :
      (EvmYul.UInt256.ofNat query).toNat = query :=
    EvmYul.UInt256.toNat_ofNat_of_lt hQueryLt
  rw [hMachine]
  exact
    Compiler.MemoryRelation.lookupMemory_mstore_disjoint_growing
      before.source.evm.toMachineState address query value
      hAddress hQuery
      (by simpa [MemoryContract.wordBytes] using hHost)
      (by simpa [MemoryContract.wordBytes] using hReadMemory)
      (by simpa [MemoryContract.wordBytes] using hReadActive)
      (by simpa [MemoryContract.wordBytes] using hReady.activeNoWrap)
      (Or.inl (hEnd.trans (hAbove hDepth)))

end SuspendedEffect

/--
Resource transition with independent final allocator depth and protected-prefix
bound.

Call phases may change allocator depth while preserving the same suspended
caller prefix. Keeping these indices separate makes acquire, callee execution,
writeback, and release compose without encoding a second call semantics.
-/
structure BoundedEffect {transcript : Trace}
    (config : Config) (finalDepth protectedBound : Nat)
    (before after : TargetState transcript) : Prop where
  ready : AllocatorReady config finalDepth after
  growth : TargetGrowth before after
  prefixStable :
    ∀ {protectedDepth : Nat},
      protectedDepth < protectedBound →
      Budget config protectedDepth →
      ProtectedPrefix config protectedDepth before after

namespace BoundedEffect

theorem of_allocatorEffect {transcript : Trace}
    {config : Config} {depth : Nat}
    {before after : TargetState transcript}
    (hEffect : AllocatorEffect config depth before after) :
    BoundedEffect config depth (depth + 1) before after :=
  { ready := hEffect.ready
    growth := hEffect.growth
    prefixStable := fun hDepth hBudget =>
      hEffect.prefixStable (by omega) hBudget }

theorem of_suspendedEffect {transcript : Trace}
    {config : Config} {depth : Nat}
    {before after : TargetState transcript}
    (hEffect : SuspendedEffect config depth before after) :
    BoundedEffect config depth depth before after :=
  { ready := hEffect.ready
    growth := hEffect.growth
    prefixStable := hEffect.prefixStable }

theorem refl {transcript : Trace}
    {config : Config} {finalDepth protectedBound : Nat}
    {target : TargetState transcript}
    (hReady : AllocatorReady config finalDepth target) :
    BoundedEffect config finalDepth protectedBound target target :=
  { ready := hReady
    growth := TargetGrowth.refl target
    prefixStable := fun _hDepth _hBudget =>
      ProtectedPrefix.refl config _ target }

theorem of_machine_eq {transcript : Trace}
    {config : Config} {finalDepth protectedBound : Nat}
    {before after : TargetState transcript}
    (hReady : AllocatorReady config finalDepth before)
    (hMachine :
      after.source.evm.toMachineState =
        before.source.evm.toMachineState) :
    BoundedEffect config finalDepth protectedBound before after :=
  { ready := hReady.of_machine_eq hMachine
    growth :=
      { active := by simpa [hMachine]
        memory := by simpa [hMachine] }
    prefixStable := fun _hDepth _hBudget =>
      ProtectedPrefix.of_machine_eq hMachine }

theorem trans {transcript : Trace}
    {config : Config}
    {firstDepth finalDepth protectedBound : Nat}
    {first second third : TargetState transcript}
    (hFirst :
      BoundedEffect config firstDepth protectedBound first second)
    (hSecond :
      BoundedEffect config finalDepth protectedBound second third) :
    BoundedEffect config finalDepth protectedBound first third :=
  { ready := hSecond.ready
    growth := hFirst.growth.trans hSecond.growth
    prefixStable := fun hDepth hBudget =>
      (hFirst.prefixStable hDepth hBudget).trans
        (hSecond.prefixStable hDepth hBudget) }

theorem weaken {transcript : Trace}
    {config : Config} {finalDepth smallerBound largerBound : Nat}
    {before after : TargetState transcript}
    (hBound : smallerBound ≤ largerBound)
    (hEffect :
      BoundedEffect config finalDepth largerBound before after) :
    BoundedEffect config finalDepth smallerBound before after :=
  { ready := hEffect.ready
    growth := hEffect.growth
    prefixStable := fun hDepth hBudget =>
      hEffect.prefixStable (hDepth.trans_le hBound) hBudget }

/--
One target `MSTORE` above an independently chosen protected prefix preserves a
bounded allocator effect, even when the allocator remains ready at a deeper
callee depth.
-/
theorem of_mstore_above
    {transcript : Trace}
    {config : Config} {finalDepth protectedBound address : Nat}
    {value : Word}
    {before after : TargetState transcript}
    (hReady : AllocatorReady config finalDepth before)
    (hMachine :
      after.source.evm.toMachineState =
        before.source.evm.toMachineState.mstore
          (EvmYul.UInt256.ofNat address) value)
    (hAddress :
      (EvmYul.UInt256.ofNat address).toNat = address)
    (hHost : address + MemoryContract.wordBytes < USize.size)
    (hAllocatorDisjoint :
      config.allocatorCell + MemoryContract.wordBytes ≤ address ∨
        address + MemoryContract.wordBytes ≤ config.allocatorCell)
    (hAbove :
      ∀ {protectedDepth : Nat},
        protectedDepth < protectedBound →
        baseAt config protectedDepth ≤ address) :
    BoundedEffect config finalDepth protectedBound before after := by
  have hFinalReady :=
    hReady.of_mstore_disjoint hMachine hAddress hHost hAllocatorDisjoint
  have hAddressEnd :
      address + MemoryContract.wordBytes < EvmYul.UInt256.size :=
    lt_trans hHost Compiler.MemoryRelation.usize_size_lt_uint256_size
  have hGrowth : TargetGrowth before after := by
    refine ⟨?_, ?_⟩
    · rw [hMachine]
      exact
        Compiler.MemoryRelation.activeWords_toNat_le_mstore
          before.source.evm.toMachineState address value hAddressEnd
    · rw [hMachine]
      simpa [EvmYul.MachineState.mstore] using
        (Compiler.MemoryRelation.writeWord_memory_size_ge
          before.source.evm.toMachineState address value hAddress
          (by simpa [MemoryContract.wordBytes] using hHost))
  refine
    { ready := hFinalReady
      growth := hGrowth
      prefixStable := ?_ }
  intro protectedDepth hDepth _hBudget
  refine
    { growth := hGrowth
      lookup := ?_ }
  intro query _hStart hEnd hReadMemory hReadActive
  have hQueryLt : query < EvmYul.UInt256.size := by
    exact lt_of_le_of_lt
      (Nat.le_add_right query MemoryContract.wordBytes)
      (hReadActive.trans_lt hReady.activeNoWrap)
  have hQuery :
      (EvmYul.UInt256.ofNat query).toNat = query :=
    EvmYul.UInt256.toNat_ofNat_of_lt hQueryLt
  rw [hMachine]
  exact
    Compiler.MemoryRelation.lookupMemory_mstore_disjoint_growing
      before.source.evm.toMachineState address query value
      hAddress hQuery
      (by simpa [MemoryContract.wordBytes] using hHost)
      (by simpa [MemoryContract.wordBytes] using hReadMemory)
      (by simpa [MemoryContract.wordBytes] using hReadActive)
      (by simpa [MemoryContract.wordBytes] using hReady.activeNoWrap)
      (Or.inl (hEnd.trans (hAbove hDepth)))

end BoundedEffect

/--
Statement resource effect selected by the activation representation.

A stack activation owns no allocator frame, so every allocated frame remains
suspended and the stronger `AllocatorEffect` applies. A scratch activation may
update its newest frame, so only the weaker `SuspendedEffect` is required.
-/
def ActivationEffect {transcript : Trace}
    (config : Config) (depth : Nat) (mode : ActivationMode)
    (before after : TargetState transcript) : Prop :=
  match mode with
  | .stack => AllocatorEffect config depth before after
  | .scratch _ _ => SuspendedEffect config depth before after

namespace ActivationEffect

theorem of_allocatorEffect {transcript : Trace}
    {config : Config} {depth : Nat} {mode : ActivationMode}
    {before after : TargetState transcript}
    (hEffect : AllocatorEffect config depth before after) :
    ActivationEffect config depth mode before after := by
  cases mode with
  | stack => exact hEffect
  | scratch => exact SuspendedEffect.of_allocatorEffect hEffect

theorem ready {transcript : Trace}
    {config : Config} {depth : Nat} {mode : ActivationMode}
    {before after : TargetState transcript}
    (hEffect : ActivationEffect config depth mode before after) :
    AllocatorReady config depth after := by
  cases mode with
  | stack => exact AllocatorEffect.ready hEffect
  | scratch => exact SuspendedEffect.ready hEffect

theorem growth {transcript : Trace}
    {config : Config} {depth : Nat} {mode : ActivationMode}
    {before after : TargetState transcript}
    (hEffect : ActivationEffect config depth mode before after) :
    TargetGrowth before after := by
  cases mode with
  | stack => exact AllocatorEffect.growth hEffect
  | scratch => exact SuspendedEffect.growth hEffect

theorem to_suspendedEffect {transcript : Trace}
    {config : Config} {depth : Nat} {mode : ActivationMode}
    {before after : TargetState transcript}
    (hEffect : ActivationEffect config depth mode before after) :
    SuspendedEffect config depth before after := by
  cases mode with
  | stack => exact SuspendedEffect.of_allocatorEffect hEffect
  | scratch => exact hEffect

theorem to_boundedEffect {transcript : Trace}
    {config : Config} {depth : Nat} {mode : ActivationMode}
    {before after : TargetState transcript}
    (hEffect : ActivationEffect config depth mode before after) :
    BoundedEffect config depth
        (match mode with
        | .stack => depth + 1
        | .scratch _ _ => depth)
        before after := by
  cases mode with
  | stack => exact BoundedEffect.of_allocatorEffect hEffect
  | scratch => exact BoundedEffect.of_suspendedEffect hEffect

theorem of_boundedEffect {transcript : Trace}
    {config : Config} {depth : Nat} {mode : ActivationMode}
    {before after : TargetState transcript}
    (hEffect :
      BoundedEffect config depth
        (match mode with
        | .stack => depth + 1
        | .scratch _ _ => depth)
        before after) :
    ActivationEffect config depth mode before after := by
  cases mode with
  | stack =>
      change BoundedEffect config depth (depth + 1) before after at hEffect
      exact
        { ready := hEffect.ready
          growth := hEffect.growth
          prefixStable := fun hDepth hBudget =>
            hEffect.prefixStable (Nat.lt_succ_iff.mpr hDepth) hBudget }
  | scratch =>
      change BoundedEffect config depth depth before after at hEffect
      exact
        { ready := hEffect.ready
          growth := hEffect.growth
          prefixStable := hEffect.prefixStable }

theorem refl {transcript : Trace}
    {config : Config} {depth : Nat} {mode : ActivationMode}
    {target : TargetState transcript}
    (hReady : AllocatorReady config depth target) :
    ActivationEffect config depth mode target target := by
  cases mode with
  | stack => exact AllocatorEffect.refl hReady
  | scratch => exact SuspendedEffect.refl hReady

theorem trans {transcript : Trace}
    {config : Config} {depth : Nat} {mode : ActivationMode}
    {first second third : TargetState transcript}
    (hFirst : ActivationEffect config depth mode first second)
    (hSecond : ActivationEffect config depth mode second third) :
    ActivationEffect config depth mode first third := by
  cases mode with
  | stack => exact AllocatorEffect.trans hFirst hSecond
  | scratch => exact SuspendedEffect.trans hFirst hSecond

theorem trans_of_sameFrame {transcript : Trace}
    {config : Config} {depth : Nat}
    {firstMode secondMode : ActivationMode}
    {first second third : TargetState transcript}
    (hFirst : ActivationEffect config depth firstMode first second)
    (hSame : SameFrame firstMode secondMode)
    (hSecond : ActivationEffect config depth secondMode second third) :
    ActivationEffect config depth firstMode first third := by
  cases hSame with
  | stack => exact AllocatorEffect.trans hFirst hSecond
  | scratch => exact SuspendedEffect.trans hFirst hSecond

theorem mode_of_sameFrame {transcript : Trace}
    {config : Config} {depth : Nat}
    {beforeMode afterMode : ActivationMode}
    {before after : TargetState transcript}
    (hEffect : ActivationEffect config depth beforeMode before after)
    (hSame : SameFrame beforeMode afterMode) :
    ActivationEffect config depth afterMode before after := by
  cases hSame with
  | stack => exact hEffect
  | scratch => exact hEffect

end ActivationEffect

/--
Allocator prefix owned by one activation representation.

A stack activation protects through the next frame depth because it owns no
frame. A scratch activation protects only strictly older frames because its
current frame may be mutated.
-/
def activationProtectedBound (depth : Nat) (mode : ActivationMode) : Nat :=
  match mode with
  | .stack => depth + 1
  | .scratch _ _ => depth

/--
Outcome-indexed resource effect for abrupt statement and block results.

Break, continue, leave, and ordinary terminal leaves can retain the usual
activation effect. A nested call that halts may leave its callee allocator
depth installed because no continuation observes it; that path instead
retains the exact final depth and protects every caller-owned prefix.
-/
inductive OutcomeEffect {transcript : Trace}
    (config : Config) (depth : Nat) (mode : ActivationMode)
    (before after : TargetState transcript) :
    Locals.Source.Mode → Prop where
  | activation {outcomeMode : Locals.Source.Mode}
      (effect : ActivationEffect config depth mode before after) :
      OutcomeEffect config depth mode before after outcomeMode
  | halt (kind : Assembly.HaltKind) {finalDepth : Nat}
      (effect :
        BoundedEffect config finalDepth
          (activationProtectedBound depth mode) before after) :
      OutcomeEffect config depth mode before after (.halt kind)

namespace OutcomeEffect

theorem of_activation {transcript : Trace}
    {config : Config} {depth : Nat} {mode : ActivationMode}
    {before after : TargetState transcript}
    {outcomeMode : Locals.Source.Mode}
    (hEffect : ActivationEffect config depth mode before after) :
    OutcomeEffect config depth mode before after outcomeMode :=
  .activation hEffect

theorem halt_of_bounded {transcript : Trace}
    {config : Config} {depth finalDepth : Nat} {mode : ActivationMode}
    {before after : TargetState transcript}
    {kind : Assembly.HaltKind}
    (hEffect :
      BoundedEffect config finalDepth
        (activationProtectedBound depth mode) before after) :
    OutcomeEffect config depth mode before after (.halt kind) :=
  .halt kind hEffect

theorem activation_of_not_halt {transcript : Trace}
    {config : Config} {depth : Nat} {mode : ActivationMode}
    {before after : TargetState transcript}
    {outcomeMode : Locals.Source.Mode}
    (hEffect : OutcomeEffect config depth mode before after outcomeMode)
    (hNotHalt : ∀ kind, outcomeMode ≠ .halt kind) :
    ActivationEffect config depth mode before after := by
  cases hEffect with
  | activation effect =>
      exact effect
  | halt kind effect =>
      exact False.elim (hNotHalt kind rfl)

theorem exists_boundedEffect {transcript : Trace}
    {config : Config} {depth : Nat} {mode : ActivationMode}
    {before after : TargetState transcript}
    {outcomeMode : Locals.Source.Mode}
    (hEffect : OutcomeEffect config depth mode before after outcomeMode) :
    ∃ finalDepth,
      BoundedEffect config finalDepth
        (activationProtectedBound depth mode) before after := by
  cases hEffect with
  | activation effect =>
      cases mode with
      | stack =>
          exact ⟨depth, BoundedEffect.of_allocatorEffect effect⟩
      | scratch =>
          exact ⟨depth, BoundedEffect.of_suspendedEffect effect⟩
  | halt _ effect =>
      exact ⟨_, effect⟩

theorem mode_of_sameFrame {transcript : Trace}
    {config : Config} {depth : Nat}
    {beforeMode afterMode : ActivationMode}
    {before after : TargetState transcript}
    {outcomeMode : Locals.Source.Mode}
    (hEffect :
      OutcomeEffect config depth beforeMode before after outcomeMode)
    (hSame : SameFrame beforeMode afterMode) :
    OutcomeEffect config depth afterMode before after outcomeMode := by
  cases hEffect with
  | activation effect =>
      exact .activation (effect.mode_of_sameFrame hSame)
  | halt kind effect =>
      cases hSame <;> exact .halt kind effect

theorem prepend_activation {transcript : Trace}
    {config : Config} {depth : Nat}
    {beforeMode afterMode : ActivationMode}
    {first second third : TargetState transcript}
    {outcomeMode : Locals.Source.Mode}
    (hFirst : ActivationEffect config depth beforeMode first second)
    (hSame : SameFrame beforeMode afterMode)
    (hSecond :
      OutcomeEffect config depth afterMode second third outcomeMode) :
    OutcomeEffect config depth beforeMode first third outcomeMode := by
  cases hSame with
  | stack =>
      cases hSecond with
      | activation effect =>
          exact .activation (AllocatorEffect.trans hFirst effect)
      | halt kind effect =>
          exact .halt kind (hFirst.to_boundedEffect.trans effect)
  | scratch =>
      cases hSecond with
      | activation effect =>
          exact .activation (SuspendedEffect.trans hFirst effect)
      | halt kind effect =>
          exact .halt kind (hFirst.to_boundedEffect.trans effect)

end OutcomeEffect

namespace ResourceMode

def ActivationEffect {transcript : Trace}
    (resource : ResourceMode) (depth : Nat) (mode : ActivationMode)
    (before after : TargetState transcript) : Prop :=
  match resource with
  | .stackOnly => True
  | .scratch config =>
      Frame.ActivationEffect config depth mode before after

def OutcomeEffect {transcript : Trace}
    (resource : ResourceMode) (depth : Nat) (mode : ActivationMode)
    (before after : TargetState transcript)
    (outcomeMode : Locals.Source.Mode) : Prop :=
  match resource with
  | .stackOnly => True
  | .scratch config =>
      Frame.OutcomeEffect config depth mode before after outcomeMode

namespace ActivationEffect

theorem refl {transcript : Trace}
    {resource : ResourceMode} {depth : Nat} {mode : ActivationMode}
    {target : TargetState transcript}
    (hReady : resource.Ready depth target) :
    resource.ActivationEffect depth mode target target := by
  cases resource with
  | stackOnly =>
      trivial
  | scratch config =>
      exact Frame.ActivationEffect.refl hReady

theorem trans {transcript : Trace}
    {resource : ResourceMode} {depth : Nat} {mode : ActivationMode}
    {first second third : TargetState transcript}
    (hFirst : resource.ActivationEffect depth mode first second)
    (hSecond : resource.ActivationEffect depth mode second third) :
    resource.ActivationEffect depth mode first third := by
  cases resource with
  | stackOnly =>
      trivial
  | scratch config =>
      exact Frame.ActivationEffect.trans hFirst hSecond

theorem trans_of_sameFrame {transcript : Trace}
    {resource : ResourceMode} {depth : Nat}
    {firstMode secondMode : ActivationMode}
    {first second third : TargetState transcript}
    (hFirst : resource.ActivationEffect depth firstMode first second)
    (hSame : SameFrame firstMode secondMode)
    (hSecond : resource.ActivationEffect depth secondMode second third) :
    resource.ActivationEffect depth firstMode first third := by
  cases resource with
  | stackOnly =>
      trivial
  | scratch config =>
      exact Frame.ActivationEffect.trans_of_sameFrame hFirst hSame hSecond

theorem mode_of_sameFrame {transcript : Trace}
    {resource : ResourceMode} {depth : Nat}
    {beforeMode afterMode : ActivationMode}
    {before after : TargetState transcript}
    (hEffect :
      resource.ActivationEffect depth beforeMode before after)
    (hSame : SameFrame beforeMode afterMode) :
    resource.ActivationEffect depth afterMode before after := by
  cases resource with
  | stackOnly =>
      trivial
  | scratch config =>
      exact Frame.ActivationEffect.mode_of_sameFrame hEffect hSame

end ActivationEffect

namespace OutcomeEffect

theorem of_activation {transcript : Trace}
    {resource : ResourceMode} {depth : Nat} {mode : ActivationMode}
    {before after : TargetState transcript}
    {outcomeMode : Locals.Source.Mode}
    (hEffect : resource.ActivationEffect depth mode before after) :
    resource.OutcomeEffect depth mode before after outcomeMode := by
  cases resource with
  | stackOnly =>
      trivial
  | scratch config =>
      exact Frame.OutcomeEffect.of_activation hEffect

theorem mode_of_sameFrame {transcript : Trace}
    {resource : ResourceMode} {depth : Nat}
    {beforeMode afterMode : ActivationMode}
    {before after : TargetState transcript}
    {outcomeMode : Locals.Source.Mode}
    (hEffect :
      resource.OutcomeEffect depth beforeMode before after outcomeMode)
    (hSame : SameFrame beforeMode afterMode) :
    resource.OutcomeEffect depth afterMode before after outcomeMode := by
  cases resource with
  | stackOnly =>
      trivial
  | scratch config =>
      exact Frame.OutcomeEffect.mode_of_sameFrame hEffect hSame

theorem prepend_activation {transcript : Trace}
    {resource : ResourceMode} {depth : Nat}
    {beforeMode afterMode : ActivationMode}
    {first second third : TargetState transcript}
    {outcomeMode : Locals.Source.Mode}
    (hFirst : resource.ActivationEffect depth beforeMode first second)
    (hSame : SameFrame beforeMode afterMode)
    (hSecond :
      resource.OutcomeEffect depth afterMode second third outcomeMode) :
    resource.OutcomeEffect depth beforeMode first third outcomeMode := by
  cases resource with
  | stackOnly =>
      trivial
  | scratch config =>
      exact Frame.OutcomeEffect.prepend_activation hFirst hSame hSecond

end OutcomeEffect

end ResourceMode

theorem mstore_end_le_activeBytes
    {machine : EvmYul.MachineState} {address : Nat} {value : Word}
    (hEnd : address + MemoryContract.wordBytes < EvmYul.UInt256.size) :
    address + MemoryContract.wordBytes ≤
      (machine.mstore (EvmYul.UInt256.ofNat address) value).activeWords.toNat *
        MemoryContract.wordBytes := by
  simpa [MemoryContract.wordBytes] using
    (Compiler.MemoryRelation.mstore_end_le_activeBytes
      machine address value
      (by simpa [MemoryContract.wordBytes] using hEnd))

@[simp] theorem baseAt_zero (config : Config) :
    baseAt config 0 = config.firstFrame := by
  simp [baseAt]

theorem baseAt_succ (config : Config) (depth : Nat) :
    baseAt config (depth + 1) = baseAt config depth + bytes config := by
  simp [baseAt, Nat.add_mul, Nat.add_assoc]

theorem baseAt_mono (config : Config) :
    Monotone (baseAt config) := by
  intro left right hLe
  unfold baseAt
  exact
    Nat.add_le_add_left
      (Nat.mul_le_mul_right (bytes config) hLe)
      config.firstFrame

theorem budget_base_le_limit {config : Config} {depth : Nat}
    (hBudget : Budget config depth) :
    baseAt config depth ≤ config.limit :=
  Nat.le_trans (Nat.le_add_right _ _) hBudget

theorem scratchAddress_end_le_frameEnd
    {config : Config} {frameBase slot : Nat}
    (hSlot : slot < config.frameWords) :
    scratchAddress frameBase slot + MemoryContract.wordBytes ≤
      frameBase + bytes config := by
  have hSucc : slot + 1 ≤ config.frameWords :=
    Nat.succ_le_iff.mpr hSlot
  calc
    scratchAddress frameBase slot + MemoryContract.wordBytes =
        frameBase + MemoryContract.wordBytes * (slot + 1) := by
          simp [scratchAddress, Nat.mul_add, Nat.add_assoc]
    _ ≤ frameBase + MemoryContract.wordBytes * config.frameWords :=
      Nat.add_le_add_left
        (Nat.mul_le_mul_left MemoryContract.wordBytes hSucc) frameBase
    _ = frameBase + bytes config := rfl

theorem scratchAddress_end_le_limit
    {config : Config} {depth slot : Nat}
    (hBudget : Budget config depth)
    (hSlot : slot < config.frameWords) :
    scratchAddress (baseAt config depth) slot +
        MemoryContract.wordBytes ≤
      config.limit :=
  Nat.le_trans (scratchAddress_end_le_frameEnd hSlot) hBudget

theorem budget_of_succ {config : Config} {depth : Nat}
    (hBudget : Budget config (depth + 1)) :
    Budget config depth := by
  unfold Budget at hBudget ⊢
  rw [baseAt_succ] at hBudget
  exact
    Nat.le_trans
      (Nat.le_add_right
        (baseAt config depth + bytes config) (bytes config))
      (by
        simpa [Nat.add_assoc] using hBudget)

theorem budget_mono {config : Config} {smaller larger : Nat}
    (hDepth : smaller ≤ larger)
    (hBudget : Budget config larger) :
    Budget config smaller := by
  unfold Budget at hBudget ⊢
  exact
    Nat.le_trans
      (Nat.add_le_add_right (baseAt_mono config hDepth) (bytes config))
      hBudget

/--
The current Functions activation's relationship to the global scratch-frame
allocator.

Stack-only activations do not own a frame and therefore leave the allocator
depth unconstrained. A scratch activation owns exactly the most recently
acquired frame: its base is `baseAt` the preceding depth and its width is the
single compiler-wide frame width.
-/
inductive ActivationOwned (config : Config) :
    Nat → Nat → ActivationMode → Prop where
  | stack {allocatorDepth frameBase : Nat} :
      ActivationOwned config allocatorDepth frameBase .stack
  | scratch
      {previousDepth frameBase frameDepth frameWords : Nat}
      (depth : frameBase = baseAt config previousDepth)
      (words : frameWords = config.frameWords) :
      ActivationOwned config (previousDepth + 1) frameBase
        (.scratch frameDepth frameWords)

namespace ActivationOwned

theorem sameFrame
    {config : Config}
    {allocatorDepth frameBase : Nat}
    {before after : ActivationMode}
    (hOwned :
      ActivationOwned config allocatorDepth frameBase before)
    (hSame : SameFrame before after) :
    ActivationOwned config allocatorDepth frameBase after := by
  cases hOwned with
  | stack =>
      cases hSame
      exact .stack
  | @scratch previousDepth _ beforeDepth frameWords hBase hWords =>
      cases hSame with
      | scratch _ afterDepth _ =>
          exact .scratch hBase hWords

/--
Every owned scratch frame begins strictly after the allocator metadata word.
-/
theorem allocatorCell_end_le_frameBase
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase frameDepth frameWords : Nat}
    {config : Config}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
    (hOwned :
      ActivationOwned config allocatorDepth frameBase
        (.scratch frameDepth frameWords)) :
    config.allocatorCell + MemoryContract.wordBytes ≤ frameBase := by
  cases hOwned with
  | @scratch previousDepth _ _ _ hBase _hWords =>
      obtain
        ⟨_reservation, _hReservation, hAllocator, hFirst, _hLimit,
          _hWords, _hWF, _hHost, _hPositive, _hFits⟩ :=
        AllocationSupport.scratchFrameConfig?_sound hConfig
      rw [hBase, baseAt, hAllocator, hFirst]
      unfold MemoryContract.ScratchReservation.allocatorCell
        MemoryContract.ScratchReservation.frameBase
      exact Nat.le_add_right _ _

/--
Every compiler spill address in the owned frame lies after the allocator word,
so ordinary frame stores cannot overwrite allocator metadata.
-/
theorem allocatorCell_disjoint_scratchAddress
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase frameDepth frameWords slot : Nat}
    {config : Config}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
    (hOwned :
      ActivationOwned config allocatorDepth frameBase
        (.scratch frameDepth frameWords)) :
    config.allocatorCell + MemoryContract.wordBytes ≤
      scratchAddress frameBase slot := by
  exact (hOwned.allocatorCell_end_le_frameBase hConfig).trans
    (Nat.le_add_right frameBase
      (MemoryContract.wordBytes * slot))

/--
Every live word in an owned scratch activation ends at or before the current
allocator base. Acquiring the next frame therefore writes strictly above the
caller's frame.
-/
theorem scratchAddress_end_le_allocatorBase
    {config : Config}
    {allocatorDepth frameBase frameDepth frameWords slot : Nat}
    (hOwned :
      ActivationOwned config allocatorDepth frameBase
        (.scratch frameDepth frameWords))
    (hSlot : slot < frameWords) :
    scratchAddress frameBase slot + MemoryContract.wordBytes ≤
      baseAt config allocatorDepth := by
  cases hOwned with
  | @scratch previousDepth _ _ _ hBase hWords =>
      rw [hBase, baseAt_succ]
      exact scratchAddress_end_le_frameEnd (by simpa [hWords] using hSlot)

/--
A spill in the current scratch activation begins after every strictly
suspended allocator prefix.
-/
theorem baseAt_le_scratchAddress_of_lt
    {config : Config}
    {allocatorDepth protectedDepth frameBase frameDepth frameWords slot : Nat}
    (hOwned :
      ActivationOwned config allocatorDepth frameBase
        (.scratch frameDepth frameWords))
    (hDepth : protectedDepth < allocatorDepth) :
    baseAt config protectedDepth ≤ scratchAddress frameBase slot := by
  cases hOwned with
  | @scratch previousDepth _ _ _ hBase _hWords =>
      rw [hBase]
      exact
        (baseAt_mono config (by omega)).trans
          (Nat.le_add_right (baseAt config previousDepth)
            (MemoryContract.wordBytes * slot))

/--
Every compiler spill address in an owned scratch activation ends inside the
concrete frame represented by `ScratchStateRel`.
-/
theorem scratchAddress_end_le_ownedFrame
    {config : Config}
    {allocatorDepth frameBase frameDepth frameWords slot : Nat}
    (hOwned :
      ActivationOwned config allocatorDepth frameBase
        (.scratch frameDepth frameWords))
    (hSlot : slot < frameWords) :
    scratchAddress frameBase slot + MemoryContract.wordBytes ≤
      frameBase + MemoryContract.wordBytes * frameWords := by
  cases hOwned with
  | @scratch previousDepth _ _ _ _hBase hWords =>
      simpa [bytes, hWords] using
        (scratchAddress_end_le_frameEnd
          (config := config)
          (by simpa [hWords] using hSlot))

/--
Every spill address owned by an active scratch frame begins at or after the
first compiler frame.
-/
theorem firstFrame_le_scratchAddress
    {config : Config}
    {allocatorDepth frameBase frameDepth frameWords slot : Nat}
    (hOwned :
      ActivationOwned config allocatorDepth frameBase
        (.scratch frameDepth frameWords)) :
    config.firstFrame ≤ scratchAddress frameBase slot := by
  cases hOwned with
  | @scratch previousDepth _ _ _ hBase _hWords =>
      rw [hBase]
      exact
        (Nat.le_add_right config.firstFrame
          (previousDepth * bytes config)).trans
          (Nat.le_add_right (baseAt config previousDepth)
            (MemoryContract.wordBytes * slot))

/--
An owned scratch frame ends exactly where the allocator says the next frame
will begin.
-/
theorem frameEnd_eq_allocatorBase
    {config : Config}
    {allocatorDepth frameBase frameDepth frameWords : Nat}
    (hOwned :
      ActivationOwned config allocatorDepth frameBase
        (.scratch frameDepth frameWords)) :
    frameBase + MemoryContract.wordBytes * frameWords =
      baseAt config allocatorDepth := by
  cases hOwned with
  | @scratch previousDepth _ _ _ hBase hWords =>
      rw [hBase, hWords, baseAt_succ]
      rfl

/--
A concrete spill store in the currently owned scratch activation preserves all
suspended frames and allocator readiness.
-/
theorem suspendedEffect_of_mstore
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase frameDepth frameWords slot : Nat}
    {config : Config}
    {transcript : Trace} {value : Word}
    {before after : TargetState transcript}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          contract globalFrameWords =
        some config)
    (hOwned :
      ActivationOwned config allocatorDepth frameBase
        (.scratch frameDepth frameWords))
    (hReady : AllocatorReady config allocatorDepth before)
    (hMachine :
      after.source.evm.toMachineState =
        before.source.evm.toMachineState.mstore
          (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) value)
    (hAddress :
      (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)).toNat =
        scratchAddress frameBase slot)
    (hHost :
      scratchAddress frameBase slot + MemoryContract.wordBytes <
        USize.size) :
    SuspendedEffect config allocatorDepth before after :=
  SuspendedEffect.of_mstore_above
    hReady hMachine hAddress hHost
    (Or.inl (hOwned.allocatorCell_disjoint_scratchAddress hConfig))
    (fun hDepth => hOwned.baseAt_le_scratchAddress_of_lt hDepth)

end ActivationOwned

namespace ResourceMode

def Owned (resource : ResourceMode)
    (allocatorDepth frameBase : Nat)
    (mode : ActivationMode) : Prop :=
  match resource with
  | .stackOnly => mode = .stack
  | .scratch config =>
      ActivationOwned config allocatorDepth frameBase mode

end ResourceMode

/--
Reconstruct a suspended caller activation after a callee has returned values
above the exact caller stack.

Stack locals are restored from the return destination. Scratch locals are
restored from `ProtectedPrefix`, while target growth transports frame bounds.
The caller source store is unchanged; only its shared state may have advanced
through the callee.
-/
theorem resume_after_call
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {config : Config} {allocatorDepth : Nat}
    {plan : Plan} {live : List Locals.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {sourceBefore sourceAfter : SourceState transcript}
    {targetBefore targetAfter : TargetState transcript}
    {returned : List Word}
    (hRel :
      ActivationStateRel contract plan live 0 frameBase mode
        sourceBefore targetBefore)
    (hOwned :
      ActivationOwned config allocatorDepth frameBase mode)
    (hVars :
      sourceAfter.source.vars = sourceBefore.source.vars)
    (hCursor : sourceAfter.cursor = targetAfter.cursor)
    (hMachine :
      Compiler.MemoryRelation.MachineRel contract
        sourceAfter.source.shared.toMachineState
        targetAfter.source.evm.toMachineState)
    (hWorld :
      sourceAfter.source.shared.toState =
        targetAfter.source.evm.toSharedState.toState)
    (hStack :
      targetAfter.source.evm.stack =
        returned ++ targetBefore.source.evm.stack)
    (hActiveNoWrap :
      targetAfter.source.evm.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (hProtected :
      ProtectedPrefix config allocatorDepth
        targetBefore targetAfter) :
    ActivationStateRel contract plan live returned.length frameBase mode
      sourceAfter targetAfter := by
  cases hRel with
  | stack hOnly _hBeforeNoWrap hState =>
      refine .stack hOnly hActiveNoWrap ?_
      refine
        { cursor := hCursor
          core :=
            { machine := hMachine
              world := hWorld
              store := ?_ } }
      intro name location hLive hLocation
      have hOld :=
        hState.core.store name location hLive hLocation
      cases location with
      | stack planDepth =>
          rcases hOld with ⟨depth, hDepth, hValue⟩
          refine ⟨depth, hDepth, ?_⟩
          rw [hStack]
          rw [List.getElem?_append_right
            (Nat.le_add_right returned.length depth)]
          simpa [hVars] using hValue
      | scratch slot =>
          exact False.elim (hOnly name slot hLive hLocation)
  | scratch hScratch =>
      refine .scratch ?_
      refine
        { base :=
            { cursor := hCursor
              core :=
                { machine := hMachine
                  world := hWorld
                  store := ?_ } }
          framePointer := ?_
          frameActive :=
            hScratch.frameActive.trans
              (Nat.mul_le_mul_right
                MemoryContract.wordBytes hProtected.growth.active)
          frameAllocated :=
            hScratch.frameAllocated.trans hProtected.growth.memory
          frameNoWrap := hScratch.frameNoWrap
          frameHostAddressable := hScratch.frameHostAddressable
          activeNoWrap := hActiveNoWrap
          frameReserved := hScratch.frameReserved
          scratchBound := hScratch.scratchBound }
      · intro name location hLive hLocation
        have hOld :=
          hScratch.base.core.store name location hLive hLocation
        cases location with
        | stack planDepth =>
            rcases hOld with ⟨depth, hDepth, hValue⟩
            refine ⟨depth, hDepth, ?_⟩
            rw [hStack]
            rw [List.getElem?_append_right
              (Nat.le_add_right returned.length depth)]
            simpa [hVars] using hValue
        | scratch slot =>
            exact
              (hProtected.lookup
                (hOwned.firstFrame_le_scratchAddress)
                (hOwned.scratchAddress_end_le_allocatorBase
                  (hScratch.scratchBound name slot hLive hLocation))
                ((hOwned.scratchAddress_end_le_ownedFrame
                    (hScratch.scratchBound name slot hLive hLocation)).trans
                  hScratch.frameAllocated)
                ((hOwned.scratchAddress_end_le_ownedFrame
                    (hScratch.scratchBound name slot hLive hLocation)).trans
                  hScratch.frameActive)).trans
                (by simpa [hVars] using hOld)
      · rw [hStack]
        rw [List.getElem?_append_right
          (Nat.le_add_right returned.length _)]
        simpa [Nat.add_assoc] using hScratch.framePointer

/--
Source-facing resource premise for a run with the given call fuel.

Functions evaluation decreases fuel before recursive calls, so every active
scratch-frame depth is bounded by the initial fuel. `depth_safe` turns that
semantic bound into the concrete reservation bound required by frame
acquisition.
-/
def FuelSafe (config : Config) (fuel : Nat) : Prop :=
  Budget config fuel

theorem FuelSafe.depth_safe {config : Config} {fuel depth : Nat}
    (hSafe : FuelSafe config fuel) (hDepth : depth ≤ fuel) :
    Budget config depth :=
  budget_mono hDepth hSafe

theorem ResourceMode.FuelSafe.depth_safe
    {resource : ResourceMode} {fuel depth : Nat}
    (hSafe : resource.FuelSafe fuel) (hDepth : depth ≤ fuel) :
    resource.Budget depth := by
  cases resource with
  | stackOnly =>
      trivial
  | scratch config =>
      exact Frame.FuelSafe.depth_safe hSafe hDepth

theorem budget_zero_of_scratchFrameConfig?
    {contract : MemoryContract.Contract} {frameWords : Nat}
    {config : Config}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config) :
    Budget config 0 := by
  obtain
    ⟨reservation, _hReservation, hAllocator, hFirst, hLimit,
      hWords, _hWF, _hHost, hPositive, hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  simp only [Budget, baseAt_zero, bytes]
  rw [hFirst, hLimit, hWords]
  change frameWords ≤ reservation.words - 1 at hFits
  change 0 < reservation.words at hPositive
  change
    reservation.base + 32 + 32 * frameWords ≤
      reservation.base + 32 * reservation.words
  omega

theorem allocatorAt_zero_after_init
    {transcript : Trace}
    {contract : MemoryContract.Contract} {frameWords : Nat}
    {config : Config}
    {target : TargetState transcript} {rest : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hActiveNoWrap :
      target.source.evm.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size) :
    AllocatorAt config 0
      (StateRel.mstoreTarget
        (EvmYul.UInt256.ofNat config.allocatorCell)
        (EvmYul.UInt256.ofNat config.firstFrame)
        rest target) := by
  obtain
    ⟨reservation, _hReservation, hAllocator, hFirst, _hLimit,
      _hWords, hWF, hHost, hPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  have hCellEnd :
      config.allocatorCell + MemoryContract.wordBytes ≤
        reservation.endExclusive := by
    rw [hAllocator]
    unfold MemoryContract.ScratchReservation.allocatorCell
      MemoryContract.ScratchReservation.endExclusive
      MemoryContract.ScratchReservation.bytes
    simp only [MemoryContract.wordBytes]
    omega
  have hCellHost :
      config.allocatorCell + MemoryContract.wordBytes < USize.size :=
    lt_of_le_of_lt hCellEnd hHost
  have hCellEnd256 :
      config.allocatorCell + MemoryContract.wordBytes <
        EvmYul.UInt256.size :=
    lt_of_le_of_lt hCellEnd hWF.2
  have hCellAddress :
      (EvmYul.UInt256.ofNat config.allocatorCell).toNat =
        config.allocatorCell :=
    EvmYul.UInt256.toNat_ofNat_of_lt (by omega)
  have hPostActive :
      (target.source.evm.toMachineState.mstore
          (EvmYul.UInt256.ofNat config.allocatorCell)
          (EvmYul.UInt256.ofNat config.firstFrame)).activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
    simpa [MemoryContract.wordBytes] using
      (Compiler.MemoryRelation.mstore_activeBytes_lt_size_of_activeBytes_lt_size
          target.source.evm.toMachineState config.allocatorCell
          (EvmYul.UInt256.ofNat config.firstFrame)
          (by simpa [MemoryContract.wordBytes] using hActiveNoWrap)
          (by simpa [MemoryContract.wordBytes] using hCellHost))
  have hLookup :=
    Compiler.MemoryRelation.lookupMemory_mstore_same_growing
      target.source.evm.toMachineState config.allocatorCell
      (EvmYul.UInt256.ofNat config.firstFrame)
      hCellAddress
      (by simpa [MemoryContract.wordBytes] using hCellHost)
      (by simpa [MemoryContract.wordBytes] using hCellEnd256)
      (by simpa [MemoryContract.wordBytes] using hPostActive)
  simpa [AllocatorAt, StateRel.mstoreTarget, baseAt_zero,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC] using hLookup

theorem activeNoWrap_after_init
    {transcript : Trace}
    {contract : MemoryContract.Contract} {frameWords : Nat}
    {config : Config}
    {target : TargetState transcript} {rest : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hActiveNoWrap :
      target.source.evm.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size) :
    (StateRel.mstoreTarget
        (EvmYul.UInt256.ofNat config.allocatorCell)
        (EvmYul.UInt256.ofNat config.firstFrame)
        rest target).source.evm.activeWords.toNat *
          MemoryContract.wordBytes <
      EvmYul.UInt256.size := by
  obtain
    ⟨reservation, _hReservation, hAllocator, _hFirst, _hLimit,
      _hWords, _hWF, hHost, hPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  have hCellHost :
      config.allocatorCell + MemoryContract.wordBytes < USize.size := by
    rw [hAllocator]
    unfold MemoryContract.ScratchReservation.allocatorCell
    unfold MemoryContract.ScratchReservation.HostAddressable at hHost
    unfold MemoryContract.ScratchReservation.endExclusive
      MemoryContract.ScratchReservation.bytes at hHost
    simp only [MemoryContract.wordBytes] at hHost ⊢
    omega
  simpa [StateRel.mstoreTarget,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC, MemoryContract.wordBytes] using
      (Compiler.MemoryRelation.mstore_activeBytes_lt_size_of_activeBytes_lt_size
          target.source.evm.toMachineState config.allocatorCell
          (EvmYul.UInt256.ofNat config.firstFrame)
          (by simpa [MemoryContract.wordBytes] using hActiveNoWrap)
          (by simpa [MemoryContract.wordBytes] using hCellHost))

theorem allocatorReady_zero_after_init
    {transcript : Trace}
    {contract : MemoryContract.Contract} {frameWords : Nat}
    {config : Config}
    {target : TargetState transcript} {rest : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hActiveNoWrap :
      target.source.evm.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size) :
    AllocatorReady config 0
      (StateRel.mstoreTarget
        (EvmYul.UInt256.ofNat config.allocatorCell)
        (EvmYul.UInt256.ofNat config.firstFrame)
        rest target) := by
  obtain
    ⟨reservation, _hReservation, hAllocator, _hFirst, _hLimit,
      _hWords, hWF, hHost, hPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  have hCellEnd :
      config.allocatorCell + MemoryContract.wordBytes ≤
        reservation.endExclusive := by
    rw [hAllocator]
    unfold MemoryContract.ScratchReservation.allocatorCell
      MemoryContract.ScratchReservation.endExclusive
      MemoryContract.ScratchReservation.bytes
    simp only [MemoryContract.wordBytes]
    omega
  have hCellHost :
      config.allocatorCell + MemoryContract.wordBytes < USize.size :=
    lt_of_le_of_lt hCellEnd hHost
  have hCellEnd256 :
      config.allocatorCell + MemoryContract.wordBytes <
        EvmYul.UInt256.size :=
    lt_of_le_of_lt hCellEnd hWF.2
  have hCellAddress :
      (EvmYul.UInt256.ofNat config.allocatorCell).toNat =
        config.allocatorCell :=
    EvmYul.UInt256.toNat_ofNat_of_lt (by omega)
  let final :=
    StateRel.mstoreTarget
      (EvmYul.UInt256.ofNat config.allocatorCell)
      (EvmYul.UInt256.ofNat config.firstFrame)
      rest target
  refine
    { allocatorAt := ?_
      cellActive := ?_
      cellAllocated := ?_
      activeNoWrap := ?_ }
  · exact allocatorAt_zero_after_init hConfig hActiveNoWrap
  · simpa [final, StateRel.mstoreTarget,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, MemoryContract.wordBytes] using
        (Compiler.MemoryRelation.mstore_end_le_activeBytes
          target.source.evm.toMachineState config.allocatorCell
          (EvmYul.UInt256.ofNat config.firstFrame)
          (by simpa [MemoryContract.wordBytes] using hCellEnd256))
  · simpa [final, StateRel.mstoreTarget,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC,
      EvmYul.MachineState.mstore] using
        (Compiler.MemoryRelation.writeWord_memory_size_ge_end
          target.source.evm.toMachineState config.allocatorCell
          (EvmYul.UInt256.ofNat config.firstFrame)
          hCellAddress
          (by simpa [MemoryContract.wordBytes] using hCellHost))
  · exact activeNoWrap_after_init hConfig hActiveNoWrap

theorem noWrap_of_budget_of_scratchFrameConfig?
    {contract : MemoryContract.Contract} {frameWords depth : Nat}
    {config : Config}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hBudget : Budget config depth) :
    baseAt config depth + bytes config < EvmYul.UInt256.size := by
  obtain
    ⟨reservation, _hReservation, _hAllocator, _hFirst, hLimit,
      _hWords, hWF, _hHost, _hPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  exact lt_of_le_of_lt (by simpa [Budget, hLimit] using hBudget) hWF.2

theorem hostAddressable_of_budget_of_scratchFrameConfig?
    {contract : MemoryContract.Contract} {frameWords depth : Nat}
    {config : Config}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hBudget : Budget config depth) :
    baseAt config depth + bytes config < USize.size := by
  obtain
    ⟨reservation, _hReservation, _hAllocator, _hFirst, hLimit,
      _hWords, _hWF, hHost, _hPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  exact lt_of_le_of_lt
    (by simpa [Budget, hLimit] using hBudget) hHost

theorem reserved_of_budget_of_scratchFrameConfig?
    {contract : MemoryContract.Contract} {frameWords depth : Nat}
    {config : Config}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract frameWords =
        some config)
    (hBudget : Budget config depth) :
    ∃ reservation,
      contract.scratch? = some reservation ∧
        reservation.containsRegion
          (baseAt config depth) config.frameWords := by
  obtain
      ⟨reservation, hReservation, _hAllocator, hFirst, hLimit,
        _hWords, _hWF, _hHost, _hPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  refine ⟨reservation, hReservation, ?_⟩
  constructor
  · unfold baseAt
    rw [hFirst]
    unfold MemoryContract.ScratchReservation.frameBase
    omega
  · rw [← hLimit]
    simpa [Budget, bytes] using hBudget

end Frame

end AllocationObserverRelation
end Functions
end EvmCompiler
