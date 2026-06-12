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

/--
Every source local that is semantically live has already been initialized.

Allocation plans include declarations that may not have executed yet, so this
cannot be inferred from plan well-formedness alone. Recursive source execution
maintains it as a source-facing invariant.
-/
def LiveDefined (live : List Locals.Name) (source : Locals.Source.State) :
    Prop :=
  ∀ name, name ∈ live → ∃ value, source.vars name = some value

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

end StoreRel

namespace StateRel

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

end ActivationMode

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

def AllocatorAt {transcript : Trace} (config : Config) (depth : Nat)
    (target : TargetState transcript) : Prop :=
  target.source.evm.toMachineState.lookupMemory
      (EvmYul.UInt256.ofNat config.allocatorCell) =
    EvmYul.UInt256.ofNat (baseAt config depth)

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

end Frame

end AllocationObserverRelation
end Functions
end EvmCompiler
