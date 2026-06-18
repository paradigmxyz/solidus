import EvmCompiler.Compiler.MemoryRelation
import EvmCompiler.Functions.AllocationSupport
import EvmCompiler.Functions.InteractionSemantics
import EvmCompiler.Expressions.InteractionSemantics
import EvmCompiler.Simulation.MemorySafety
import EvmYul.MachineStateOps

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionRelation

/-!
Canonical state and outcome relations for the adjacent Functions-to-allocated-
Expressions boundary.

This module owns allocation representation only. It contains no compiler,
execution interpreter, observer transcript, or replay cursor. Open-world
effects are related separately by `Simulation.Interaction.Rel` using these
relations at computation results.
-/

abbrev Word := Assembly.Word
abbrev Plan := Locals.Allocation.Plan
abbrev Location := Locals.Allocation.LocalLocation
abbrev SourceState := Functions.InteractionSemantics.State
abbrev TargetState := Expressions.InteractionSemantics.RunState
abbrev SourceOutcome := Functions.InteractionSemantics.Outcome
abbrev TargetOutcome := Expressions.InteractionSemantics.Outcome

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
  · have hBefore : name ∈ beforeLive := hSubset name hAfter
    simp [hAfter, hBefore]
  · simp [hAfter]

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

def LiveDefined (live : List Locals.Name) (source : Locals.Source.State) :
    Prop :=
  ∀ name, name ∈ live → ∃ value, source.vars name = some value

namespace LiveDefined

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

/-- Realization of the live source store in allocated stack/scratch slots. -/
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

/-- Every currently live local is represented on the target stack. -/
def LiveStackOnly (plan : Plan) (live : List Locals.Name) : Prop :=
  ∀ name slot,
    name ∈ live →
    plan.location? name = some (.scratch slot) →
    False

namespace StoreRel

/-- Rebase live locals across a target stack-prefix replacement. -/
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

theorem rebase_prefix_stack_only
    {plan : Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {source sourceFinal : Locals.Source.State}
    {target targetFinal : Structured.RunState}
    {oldPrefix newPrefix baseStack : List Word}
    (hOnly : LiveStackOnly plan live)
    (hRel :
      StoreRel plan live (stackOffset + oldPrefix.length) frameBase
        source target)
    (hOldStack : target.evm.stack = oldPrefix ++ baseStack)
    (hNewStack : targetFinal.evm.stack = newPrefix ++ baseStack)
    (hVars : sourceFinal.vars = source.vars) :
    StoreRel plan live (stackOffset + newPrefix.length) frameBase
      sourceFinal targetFinal := by
  apply rebase_prefix_of_lookup hRel hOldStack hNewStack _ hVars
  intro name slot hLive hLocation
  exact False.elim (hOnly name slot hLive hLocation)

end StoreRel

/-- Observable shared state, allowing only compiler-reserved memory differences. -/
structure SharedRel
    (contract : MemoryContract.Contract)
    (source target : EvmYul.SharedState .EVM) : Prop where
  machine :
    Compiler.MemoryRelation.MachineRel contract
      source.toMachineState target.toMachineState
  world :
    source.toState = target.toState

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

theorem openWorld_eq
    {contract : MemoryContract.Contract}
    {source target : EvmYul.SharedState .EVM}
    (hRel : SharedRel contract source target) :
    Simulation.OpenWorld.ofEVMShared source =
      Simulation.OpenWorld.ofEVMShared target := by
  unfold Simulation.OpenWorld.ofEVMShared
  rw [hRel.world]

theorem calldata_eq
    {contract : MemoryContract.Contract}
    {source target : EvmYul.SharedState .EVM}
    (hRel : SharedRel contract source target)
    (callLocal : Simulation.CallLocal)
    (hWindow :
      Simulation.MemorySafety.WindowSafe contract
        callLocal.inputOffset.toNat callLocal.inputSize.toNat) :
    (Simulation.ExternalFrame.ofShared source).calldata callLocal =
      (Simulation.ExternalFrame.ofShared target).calldata callLocal := by
  exact
    Simulation.MemorySafety.readWithPadding_eq_of_windowSafe
      hRel.machine callLocal.inputOffset.toNat callLocal.inputSize.toNat hWindow

theorem initCode_eq
    {contract : MemoryContract.Contract}
    {source target : EvmYul.SharedState .EVM}
    (hRel : SharedRel contract source target)
    (createLocal : Simulation.CreateLocal)
    (hWindow :
      Simulation.MemorySafety.WindowSafe contract
        createLocal.initOffset.toNat createLocal.initSize.toNat) :
    (Simulation.ExternalFrame.ofShared source).initCode createLocal =
      (Simulation.ExternalFrame.ofShared target).initCode createLocal := by
  exact
    Simulation.MemorySafety.readWithPadding_eq_of_windowSafe
      hRel.machine createLocal.initOffset.toNat createLocal.initSize.toNat hWindow

theorem callRequest_eq
    {contract : MemoryContract.Contract}
    {source target : EvmYul.SharedState .EVM}
    (hRel : SharedRel contract source target)
    (kind : Simulation.CallKind) (operands : Simulation.CallOperands)
    (hWindow :
      Simulation.MemorySafety.WindowSafe contract
        operands.inputOffset.toNat operands.inputSize.toNat) :
    (Simulation.ExternalFrame.ofShared source).callRequest kind operands =
      (Simulation.ExternalFrame.ofShared target).callRequest kind operands := by
  have hEnv := hRel.executionEnv_eq
  have hData := hRel.calldata_eq operands.callLocal hWindow
  unfold Simulation.ExternalFrame.calldata
    Simulation.ExternalFrame.ofShared at hData
  cases kind <;>
    simp [Simulation.ExternalFrame.callRequest,
      Simulation.ExternalFrame.calldata,
      Simulation.ExternalFrame.ofShared, hEnv, hData]

theorem createRequest_eq
    {contract : MemoryContract.Contract}
    {source target : EvmYul.SharedState .EVM}
    (hRel : SharedRel contract source target)
    (kind : Simulation.CreateKind) (operands : Simulation.CreateOperands)
    (hWindow :
      Simulation.MemorySafety.WindowSafe contract
        operands.initOffset.toNat operands.initSize.toNat) :
    (Simulation.ExternalFrame.ofShared source).createRequest kind operands =
      (Simulation.ExternalFrame.ofShared target).createRequest kind operands := by
  have hEnv := hRel.executionEnv_eq
  have hCode := hRel.initCode_eq operands.createLocal hWindow
  unfold Simulation.ExternalFrame.initCode
    Simulation.ExternalFrame.ofShared at hCode
  cases kind <;>
    simp [Simulation.ExternalFrame.createRequest,
      Simulation.ExternalFrame.initCode,
      Simulation.ExternalFrame.ofShared, hEnv, hCode]

theorem finishCall
    {contract : MemoryContract.Contract}
    {source target : Assembly.EVMState}
    (hRel : SharedRel contract source.toSharedState target.toSharedState)
    (hTargetNoWrap :
      target.toMachineState.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (callLocal : Simulation.CallLocal)
    (response : Simulation.CallResponse)
    (sourceRest targetRest : EvmYul.Stack Word)
    (hInput :
      Simulation.MemorySafety.WindowSafe contract
        callLocal.inputOffset.toNat callLocal.inputSize.toNat)
    (hOutput :
      Simulation.MemorySafety.WindowSafe contract
        callLocal.outputOffset.toNat callLocal.outputSize.toNat) :
    SharedRel contract
      (Assembly.InteractionSemantics.EVMState.finishCall
        source sourceRest callLocal response).toSharedState
      (Assembly.InteractionSemantics.EVMState.finishCall
        target targetRest callLocal response).toSharedState := by
  refine ⟨?_, ?_⟩
  · have hMachine :=
      Simulation.MemorySafety.finishExternalCall_both
        hRel.machine hTargetNoWrap response.returnData
        callLocal.inputOffset callLocal.inputSize
        callLocal.outputOffset callLocal.outputSize hInput hOutput
    simpa [Assembly.InteractionSemantics.EVMState.finishCall,
      Assembly.InteractionSemantics.EVMState.installWorld,
      Simulation.CallLocal.finishMachine,
      EvmYul.EVM.State.incrPC] using hMachine
  · simp [Assembly.InteractionSemantics.EVMState.finishCall,
      Assembly.InteractionSemantics.EVMState.installWorld,
      EvmYul.EVM.State.incrPC,
      Simulation.OpenWorld.installEVMShared, hRel.world]

theorem finishCreate
    {contract : MemoryContract.Contract}
    {source target : Assembly.EVMState}
    (hRel : SharedRel contract source.toSharedState target.toSharedState)
    (hTargetNoWrap :
      target.toMachineState.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (createLocal : Simulation.CreateLocal)
    (response : Simulation.CreateResponse)
    (sourceRest targetRest : EvmYul.Stack Word)
    (hInput :
      Simulation.MemorySafety.WindowSafe contract
        createLocal.initOffset.toNat createLocal.initSize.toNat) :
    SharedRel contract
      (Assembly.InteractionSemantics.EVMState.finishCreate
        source sourceRest createLocal response).toSharedState
      (Assembly.InteractionSemantics.EVMState.finishCreate
        target targetRest createLocal response).toSharedState := by
  refine ⟨?_, ?_⟩
  · have hMachine :=
      Simulation.MemorySafety.finishExternalCall_both
        hRel.machine hTargetNoWrap response.returnData
        createLocal.initOffset createLocal.initSize
        (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)
        hInput (Simulation.MemorySafety.windowSafe_zero contract 0)
    simpa [Assembly.InteractionSemantics.EVMState.finishCreate,
      Assembly.InteractionSemantics.EVMState.installWorld,
      Simulation.CreateLocal.finishMachine,
      EvmYul.EVM.State.incrPC] using hMachine
  · simp [Assembly.InteractionSemantics.EVMState.finishCreate,
      Assembly.InteractionSemantics.EVMState.installWorld,
      EvmYul.EVM.State.incrPC,
      Simulation.OpenWorld.installEVMShared, hRel.world]

end SharedRel

/-- Core allocation relation, independent of observers and interaction history. -/
structure CoreRel
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name) (stackOffset frameBase : Nat)
    (source : SourceState) (target : TargetState) : Prop where
  machine :
    Compiler.MemoryRelation.MachineRel contract
      source.shared.toMachineState target.evm.toMachineState
  world :
    source.shared.toState = target.evm.toSharedState.toState
  store :
    StoreRel plan live stackOffset frameBase source target

abbrev StateRel := CoreRel

namespace StateRel

/-- Restricting the source store to represented live names preserves it. -/
theorem restrict_source_live
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {source : SourceState} {target : TargetState}
    (hRel :
      StateRel contract plan live stackOffset frameBase source target) :
    StateRel contract plan live stackOffset frameBase
      (source.restrictTo live) target := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [Locals.Source.State.restrictTo] using hRel.machine
  · simpa [Locals.Source.State.restrictTo] using hRel.world
  · intro name location hLive hLocation
    have hValue := hRel.store name location hLive hLocation
    cases location with
    | stack depth =>
        rcases hValue with ⟨actualDepth, hDepth, hStack⟩
        exact
          ⟨actualDepth, hDepth, by
            simpa [Locals.Source.State.restrictTo,
              Locals.Source.Store.restrictTo, hLive] using hStack⟩
    | scratch slot =>
        simpa [Locals.Source.State.restrictTo,
          Locals.Source.Store.restrictTo, hLive] using hValue

def pushTargetBy (pcDelta : Nat) (value : Word)
    (target : TargetState) : TargetState :=
  target.withEVM
    (target.evm.replaceStackAndIncrPC
      (value :: target.evm.stack) (pcΔ := pcDelta))

def pushTarget (value : Word) (target : TargetState) : TargetState :=
  pushTargetBy 1 value target

def contractTargetBy (pcDelta : Nat) (value : Word) (rest : List Word)
    (target : TargetState) : TargetState :=
  target.withEVM
    (target.evm.replaceStackAndIncrPC
      (value :: rest) (pcΔ := pcDelta))

def mstoreTarget (address value : Word) (rest : List Word)
    (target : TargetState) : TargetState :=
  target.withEVM
    (({ target.evm with
        toMachineState :=
          target.evm.toMachineState.mstore address value }).replaceStackAndIncrPC
      rest)

theorem shared
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {source : SourceState} {target : TargetState}
    (hRel : StateRel contract plan live stackOffset frameBase source target) :
    SharedRel contract source.shared target.evm.toSharedState :=
  ⟨hRel.machine, hRel.world⟩

theorem push_target_by
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {source : SourceState} {target : TargetState}
    (pcDelta : Nat) (value : Word)
    (hRel : StateRel contract plan live stackOffset frameBase source target) :
    StateRel contract plan live (stackOffset + 1) frameBase source
      (pushTargetBy pcDelta value target) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [pushTargetBy, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.machine
  · simpa [pushTargetBy, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.world
  · intro name location hLive hLocation
    have hValue := hRel.store name location hLive hLocation
    cases location with
    | stack planDepth =>
        rcases hValue with ⟨depth, hDepth, hValue⟩
        refine ⟨depth, hDepth, ?_⟩
        change
          (value :: target.evm.stack)[stackOffset + 1 + depth]? =
            source.vars name
        rw [show stackOffset + 1 + depth =
            (stackOffset + depth) + 1 by omega]
        simpa using hValue
    | scratch slot =>
        simpa [pushTargetBy,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] using hValue

theorem push_target
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {source : SourceState} {target : TargetState}
    (value : Word)
    (hRel : StateRel contract plan live stackOffset frameBase source target) :
    StateRel contract plan live (stackOffset + 1) frameBase source
      (pushTarget value target) :=
  push_target_by 1 value hRel

theorem contract_target_by
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {source : SourceState} {target : TargetState}
    {right left value : Word} {rest : List Word}
    (hRel :
      StateRel contract plan live (stackOffset + 2) frameBase source target)
    (hStack : target.evm.stack = right :: left :: rest)
    (pcDelta : Nat) :
    StateRel contract plan live (stackOffset + 1) frameBase source
      (contractTargetBy pcDelta value rest target) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [contractTargetBy, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.machine
  · simpa [contractTargetBy, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.world
  · intro name location hLive hLocation
    have hStored := hRel.store name location hLive hLocation
    cases location with
    | stack planDepth =>
        rcases hStored with ⟨depth, hDepth, hValue⟩
        refine ⟨depth, hDepth, ?_⟩
        change
          (value :: rest)[stackOffset + 1 + depth]? = source.vars name
        change
          target.evm.stack[stackOffset + 2 + depth]? = source.vars name
          at hValue
        rw [hStack] at hValue
        have hRest : rest[stackOffset + depth]? = source.vars name := by
          simpa [show stackOffset + 2 + depth =
              (stackOffset + depth) + 2 by omega] using hValue
        simpa [show stackOffset + 1 + depth =
            (stackOffset + depth) + 1 by omega] using hRest
    | scratch slot =>
        simpa [contractTargetBy, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] using hStored

theorem replace_top_by
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {source : SourceState} {target : TargetState}
    {old value : Word} {rest : List Word}
    (hRel :
      StateRel contract plan live (stackOffset + 1) frameBase source target)
    (hStack : target.evm.stack = old :: rest)
    (pcDelta : Nat) :
    StateRel contract plan live (stackOffset + 1) frameBase source
      (contractTargetBy pcDelta value rest target) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [contractTargetBy, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.machine
  · simpa [contractTargetBy, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using hRel.world
  · intro name location hLive hLocation
    have hStored := hRel.store name location hLive hLocation
    cases location with
    | stack planDepth =>
        rcases hStored with ⟨depth, hDepth, hValue⟩
        refine ⟨depth, hDepth, ?_⟩
        change
          (value :: rest)[stackOffset + 1 + depth]? = source.vars name
        change
          target.evm.stack[stackOffset + 1 + depth]? = source.vars name
          at hValue
        rw [hStack] at hValue
        simpa [show stackOffset + 1 + depth =
            (stackOffset + depth) + 1 by omega] using hValue
    | scratch slot =>
        simpa [contractTargetBy, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] using hStored

/-- Turn the top expression result into a newly live stack local. -/
theorem declare_stack_live
    {contract : MemoryContract.Contract} {plan : Plan}
    {beforeLive afterLive : List Locals.Name}
    {frameBase planDepth : Nat}
    {source : SourceState} {target : TargetState}
    {name : Locals.Name} {value : Word} {rest : List Word}
    (hRel :
      StateRel contract plan beforeLive 1 frameBase source target)
    (hStack : target.evm.stack = value :: rest)
    (hAfter :
      ∀ other, other ∈ afterLive →
        other = name ∨ other ∈ beforeLive)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hStackOrder :
      currentStackOrder plan afterLive =
        name :: currentStackOrder plan beforeLive) :
    StateRel contract plan afterLive 0 frameBase
      (source.insert name value) target := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [Locals.Source.State.insert] using hRel.machine
  · simpa [Locals.Source.State.insert] using hRel.world
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
            simp [Locals.Source.State.insert]
      | scratch slot =>
          rw [hLocation] at hOtherLocation
          simp at hOtherLocation
    · have hOtherBefore : other ∈ beforeLive := by
        rcases hAfter other hOtherAfter with hEq | hBefore
        · exact False.elim (hName hEq)
        · exact hBefore
      have hOld :=
        hRel.store other location hOtherBefore hOtherLocation
      cases location with
      | stack otherPlanDepth =>
          rcases hOld with ⟨depth, hDepth, hValue⟩
          refine ⟨depth + 1, ?_, ?_⟩
          · rw [hStackOrder]
            simpa [Nat.add_assoc] using
              (Locals.Layout.lookupDepth?_cons_of_ne
                (Ne.symm hName) hDepth)
          · simpa [Locals.Source.State.insert,
              Locals.Source.Store.insert_of_ne hName,
              Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hValue
      | scratch slot =>
          change
            target.evm.toMachineState.lookupMemory
                (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) =
              (Locals.Source.Store.insert
                source.vars name value other).getD
                  (EvmYul.UInt256.ofNat 0)
          rw [Locals.Source.Store.insert_of_ne hName]
          exact hOld

/-- Replace one live stack local with the expression result above the layout. -/
theorem assign_stack_live
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {frameBase planDepth depth : Nat}
    {source : SourceState} {target targetFinal : TargetState}
    {name : Locals.Name} {value old : Word} {rest : List Word}
    (hRel : StateRel contract plan live 1 frameBase source target)
    (hStack : target.evm.stack = value :: rest)
    (hFinalStack : targetFinal.evm.stack = rest.set depth value)
    (hShared : targetFinal.evm.toSharedState = target.evm.toSharedState)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hDepth :
      Locals.Layout.lookupDepth? name (currentStackOrder plan live) =
        some (depth + 1))
    (hOld : source.vars name = some old) :
    StateRel contract plan live 0 frameBase
      (source.insert name value) targetFinal := by
  have hAssigned := hRel.store name (.stack planDepth) hLive hLocation
  rcases hAssigned with ⟨assignedDepth, hAssignedDepth, hAssignedValue⟩
  have hAssignedDepthEq : assignedDepth = depth := by
    exact Nat.succ.inj
      (Option.some.inj
        (hAssignedDepth.symm.trans hDepth))
  subst assignedDepth
  rw [hStack, hOld] at hAssignedValue
  have hRestAssigned : rest[depth]? = some old := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      hAssignedValue
  have hDepthBound : depth < rest.length :=
    List.getElem?_eq_some_iff.mp hRestAssigned |>.1
  refine ⟨?_, ?_, ?_⟩
  · simpa [Locals.Source.State.insert, hShared] using hRel.machine
  · simpa [Locals.Source.State.insert, hShared] using hRel.world
  · intro other location hOtherLive hOtherLocation
    have hPrevious := hRel.store other location hOtherLive hOtherLocation
    cases location with
    | stack otherPlanDepth =>
        rcases hPrevious with ⟨otherDepth, hOtherDepth, hOtherValue⟩
        refine ⟨otherDepth, hOtherDepth, ?_⟩
        simp only [Nat.zero_add, Locals.Source.State.insert]
        rw [hFinalStack]
        by_cases hName : other = name
        · subst other
          rw [hDepth] at hOtherDepth
          cases hOtherDepth
          rw [List.getElem?_set_eq_of_lt value hDepthBound]
          exact
            (Locals.Source.Store.insert_self source.vars name value).symm
        · have hDepthNe : depth ≠ otherDepth := by
            intro hEq
            have hOtherName : other = name :=
              Locals.Layout.name_eq_of_lookupDepth?_eq_some
                (by simpa [hEq] using hOtherDepth) hDepth
            exact hName hOtherName
          change target.evm.stack[1 + otherDepth]? = source.vars other
            at hOtherValue
          rw [hStack] at hOtherValue
          have hRestOther : rest[otherDepth]? = source.vars other := by
            simpa [show 1 + otherDepth = otherDepth + 1 by omega] using
              hOtherValue
          rw [List.getElem?_set_of_lt' value rest hDepthBound]
          simp [hDepthNe, hRestOther,
            Locals.Source.Store.insert_of_ne hName]
    | scratch slot =>
        change
          targetFinal.evm.toMachineState.lookupMemory
              (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) =
            (Locals.Source.Store.insert source.vars name value other).getD
              (EvmYul.UInt256.ofNat 0)
        have hName : other ≠ name := by
          intro hEq
          subst other
          rw [hLocation] at hOtherLocation
          simp at hOtherLocation
        rw [Locals.Source.Store.insert_of_ne hName]
        have hMachine := congrArg EvmYul.SharedState.toMachineState hShared
        change
          target.evm.toMachineState.lookupMemory
              (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) =
            (source.vars other).getD (EvmYul.UInt256.ofNat 0) at hPrevious
        rw [hMachine]
        exact hPrevious

end StateRel

/-- Additional representation facts for a live compiler-owned scratch frame. -/
structure ScratchStateRel
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name)
    (stackOffset frameBase frameDepth frameWords : Nat)
    (source : SourceState) (target : TargetState) : Prop where
  base :
    StateRel contract plan live stackOffset frameBase source target
  framePointer :
    target.evm.stack[stackOffset + frameDepth]? =
      some (EvmYul.UInt256.ofNat frameBase)
  frameActive :
    frameBase + MemoryContract.wordBytes * frameWords ≤
      target.evm.activeWords.toNat * MemoryContract.wordBytes
  frameAllocated :
    frameBase + MemoryContract.wordBytes * frameWords ≤
      target.evm.toMachineState.memory.size
  frameNoWrap :
    frameBase + MemoryContract.wordBytes * frameWords <
      EvmYul.UInt256.size
  frameHostAddressable :
    frameBase + MemoryContract.wordBytes * frameWords < USize.size
  activeNoWrap :
    target.evm.activeWords.toNat * MemoryContract.wordBytes <
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

namespace ScratchStateRel

theorem scratchAddress_reserved_of_bound
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState} {target : TargetState}
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
  have hSucc : slot + 1 ≤ frameWords := Nat.succ_le_iff.mpr hSlot
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

theorem scratchAddress_reserved
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState} {target : TargetState}
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

theorem scratchAddress_end_le_active
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState} {target : TargetState}
    {name : Locals.Name} {slot : Nat}
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot)) :
    scratchAddress frameBase slot + MemoryContract.wordBytes ≤
      target.evm.activeWords.toNat * MemoryContract.wordBytes := by
  have hSlot := hRel.scratchBound name slot hLive hLocation
  have hSucc : slot + 1 ≤ frameWords := Nat.succ_le_iff.mpr hSlot
  calc
    scratchAddress frameBase slot + MemoryContract.wordBytes =
        frameBase + MemoryContract.wordBytes * (slot + 1) := by
          simp [scratchAddress, Nat.mul_add, Nat.add_assoc]
    _ ≤ frameBase + MemoryContract.wordBytes * frameWords :=
      Nat.add_le_add_left
        (Nat.mul_le_mul_left MemoryContract.wordBytes hSucc) frameBase
    _ ≤ target.evm.activeWords.toNat * MemoryContract.wordBytes :=
      hRel.frameActive

theorem scratchAddress_end_lt_size
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState} {target : TargetState}
    {name : Locals.Name} {slot : Nat}
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot)) :
    scratchAddress frameBase slot + MemoryContract.wordBytes <
      EvmYul.UInt256.size := by
  have hSlot := hRel.scratchBound name slot hLive hLocation
  have hSucc : slot + 1 ≤ frameWords := Nat.succ_le_iff.mpr hSlot
  exact lt_of_le_of_lt
    (show
      scratchAddress frameBase slot + MemoryContract.wordBytes ≤
        frameBase + MemoryContract.wordBytes * frameWords by
      calc
        scratchAddress frameBase slot + MemoryContract.wordBytes =
            frameBase + MemoryContract.wordBytes * (slot + 1) := by
              simp [scratchAddress, Nat.mul_add, Nat.add_assoc]
        _ ≤ frameBase + MemoryContract.wordBytes * frameWords :=
          Nat.add_le_add_left
            (Nat.mul_le_mul_left MemoryContract.wordBytes hSucc) frameBase)
    hRel.frameNoWrap

theorem scratchAddress_end_le_memory
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState} {target : TargetState}
    {name : Locals.Name} {slot : Nat}
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot)) :
    scratchAddress frameBase slot + MemoryContract.wordBytes ≤
      target.evm.toMachineState.memory.size := by
  have hSlot := hRel.scratchBound name slot hLive hLocation
  have hSucc : slot + 1 ≤ frameWords := Nat.succ_le_iff.mpr hSlot
  calc
    scratchAddress frameBase slot + MemoryContract.wordBytes =
        frameBase + MemoryContract.wordBytes * (slot + 1) := by
          simp [scratchAddress, Nat.mul_add, Nat.add_assoc]
    _ ≤ frameBase + MemoryContract.wordBytes * frameWords :=
      Nat.add_le_add_left
        (Nat.mul_le_mul_left MemoryContract.wordBytes hSucc) frameBase
    _ ≤ target.evm.toMachineState.memory.size := hRel.frameAllocated

theorem mload_machine_eq
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState} {target : TargetState}
    {name : Locals.Name} {slot : Nat}
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source target)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot)) :
    target.evm.toMachineState.mload
        (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) =
      (target.evm.toMachineState.lookupMemory
          (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)),
        target.evm.toMachineState) := by
  have hEndActive := hRel.scratchAddress_end_le_active hLive hLocation
  have hEndLt := hRel.scratchAddress_end_lt_size hLive hLocation
  have hAddressLt : scratchAddress frameBase slot < EvmYul.UInt256.size :=
    lt_of_lt_of_le
      (Nat.lt_add_of_pos_right
        (by decide : 0 < MemoryContract.wordBytes))
      (Nat.le_of_lt hEndLt)
  have hAddressToNat :
      (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)).toNat =
        scratchAddress frameBase slot :=
    EvmYul.UInt256.toNat_ofNat_of_lt hAddressLt
  exact
    Compiler.MemoryRelation.mload_eq_lookup_of_end_le
      target.evm.toMachineState (scratchAddress frameBase slot)
      hAddressToNat (by simpa [MemoryContract.wordBytes] using hEndActive)

/-- Rebase a live scratch activation across a growing target computation. -/
theorem rebase_prefix_mono
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source sourceFinal : SourceState}
    {target targetFinal : TargetState}
    {oldPrefix newPrefix baseStack : List Word}
    (hRel :
      ScratchStateRel contract plan live
        (stackOffset + oldPrefix.length) frameBase
        frameDepth frameWords source target)
    (hBase :
      StateRel contract plan live
        (stackOffset + newPrefix.length) frameBase
        sourceFinal targetFinal)
    (hOldStack : target.evm.stack = oldPrefix ++ baseStack)
    (hNewStack : targetFinal.evm.stack = newPrefix ++ baseStack)
    (hMemory :
      target.evm.toMachineState.memory.size ≤
        targetFinal.evm.toMachineState.memory.size)
    (hActive :
      target.evm.activeWords.toNat ≤ targetFinal.evm.activeWords.toNat)
    (hActiveNoWrap :
      targetFinal.evm.activeWords.toNat * MemoryContract.wordBytes <
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
        (Nat.le_add_right oldPrefix.length (stackOffset + frameDepth))]
        at hPointer
      simpa using hPointer
    rw [hNewStack]
    rw [show
        stackOffset + newPrefix.length + frameDepth =
          newPrefix.length + (stackOffset + frameDepth) by omega]
    rw [List.getElem?_append_right
      (Nat.le_add_right newPrefix.length (stackOffset + frameDepth))]
    simpa using hBasePointer
  · exact hRel.frameActive.trans
      (Nat.mul_le_mul_right MemoryContract.wordBytes hActive)
  · exact hRel.frameAllocated.trans hMemory

theorem push_target_by
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState} {target : TargetState}
    (pcDelta : Nat) (value : Word)
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source target) :
    ScratchStateRel contract plan live (stackOffset + 1) frameBase
      frameDepth frameWords source (StateRel.pushTargetBy pcDelta value target) := by
  refine ⟨hRel.base.push_target_by pcDelta value, ?_, ?_, ?_,
    hRel.frameNoWrap, hRel.frameHostAddressable, ?_, hRel.frameReserved,
    hRel.scratchBound⟩
  · change
      (value :: target.evm.stack)[stackOffset + 1 + frameDepth]? =
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

theorem contract_target_by
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState} {target : TargetState}
    {right left value : Word} {rest : List Word}
    (hRel :
      ScratchStateRel contract plan live (stackOffset + 2) frameBase
        frameDepth frameWords source target)
    (hStack : target.evm.stack = right :: left :: rest)
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

theorem replace_top_by
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState} {target : TargetState}
    {old value : Word} {rest : List Word}
    (hRel :
      ScratchStateRel contract plan live (stackOffset + 1) frameBase
        frameDepth frameWords source target)
    (hStack : target.evm.stack = old :: rest)
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
Preserve an allocated scratch frame across a response installation whose
shared state, result stack, and concrete machine update are known.
-/
theorem finishExternal
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState} {target : TargetState}
    {oldPrefix baseStack : List Word}
    (hRel :
      ScratchStateRel contract plan live
        (stackOffset + oldPrefix.length) frameBase
        frameDepth frameWords source target)
    (sourceFinalShared : EvmYul.SharedState .EVM)
    (targetFinalEVM : Assembly.EVMState)
    (result : Word) (returnData : ByteArray)
    (inputOffset inputSize outputOffset outputSize : Word)
    (hOldStack : target.evm.stack = oldPrefix ++ baseStack)
    (hSharedFinal :
      SharedRel contract sourceFinalShared targetFinalEVM.toSharedState)
    (hFinalStack : targetFinalEVM.stack = result :: baseStack)
    (hFinalMachine :
      targetFinalEVM.toMachineState =
        target.evm.toMachineState.finishExternalCall returnData
          inputOffset inputSize outputOffset outputSize)
    (hInput :
      Simulation.MemorySafety.WindowSafe contract
        inputOffset.toNat inputSize.toNat)
    (hOutput :
      Simulation.MemorySafety.WindowSafe contract
        outputOffset.toNat outputSize.toNat) :
    ScratchStateRel contract plan live (stackOffset + 1) frameBase
      frameDepth frameWords
      (source.withShared sourceFinalShared)
      (target.withEVM targetFinalEVM) := by
  let sourceFinal := source.withShared sourceFinalShared
  let targetFinal := target.withEVM targetFinalEVM
  have hNewStack : targetFinal.evm.stack = [result] ++ baseStack := by
    simpa [targetFinal, Structured.RunState.withEVM] using hFinalStack
  have hGrowth :=
    Simulation.MemorySafety.finishExternalCall_growth
      target.evm.toMachineState hRel.activeNoWrap returnData
      inputOffset inputSize outputOffset outputSize hInput hOutput
  have hScratchStable :
      ∀ name slot,
        name ∈ live →
        plan.location? name = some (.scratch slot) →
        targetFinal.evm.toMachineState.lookupMemory
            (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) =
          target.evm.toMachineState.lookupMemory
            (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) := by
    intro name slot hLive hLocation
    obtain ⟨reservation, hReservation, _hFrame⟩ := hRel.frameReserved
    have hLookup :=
      Simulation.MemorySafety.lookupMemory_finishExternalCall_of_reserved
        target.evm.toMachineState hRel.activeNoWrap returnData
        inputOffset inputSize outputOffset outputSize hInput hOutput
        (scratchAddress frameBase slot) hReservation
        (hRel.scratchAddress_reserved hLive hLocation hReservation)
        (hRel.scratchAddress_end_le_memory hLive hLocation)
        (hRel.scratchAddress_end_le_active hLive hLocation)
    simpa [targetFinal, Structured.RunState.withEVM, hFinalMachine] using
      hLookup
  have hBase :
      StateRel contract plan live (stackOffset + [result].length) frameBase
        sourceFinal targetFinal := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [sourceFinal, targetFinal, Structured.RunState.withEVM] using
        hSharedFinal.machine
    · simpa [sourceFinal, targetFinal, Structured.RunState.withEVM] using
        hSharedFinal.world
    · exact
        StoreRel.rebase_prefix_of_lookup hRel.base.store hOldStack
          hNewStack hScratchStable (by simp [sourceFinal,
            Locals.Source.State.withShared])
  have hResult :=
    hRel.rebase_prefix_mono hBase hOldStack hNewStack
      (by simpa [targetFinal, Structured.RunState.withEVM, hFinalMachine] using
        hGrowth.memory)
      (by simpa [targetFinal, Structured.RunState.withEVM, hFinalMachine] using
        hGrowth.active)
      (by simpa [targetFinal, Structured.RunState.withEVM, hFinalMachine] using
        hGrowth.activeNoWrap)
  simpa [sourceFinal, targetFinal] using hResult

/-- Preserve a live scratch frame across one open-world CALL response. -/
theorem finishCall
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState} {target : TargetState}
    {oldPrefix baseStack : List Word}
    (hRel :
      ScratchStateRel contract plan live
        (stackOffset + oldPrefix.length) frameBase
        frameDepth frameWords source target)
    (sourceEVM : Assembly.EVMState)
    (hSourceShared : sourceEVM.toSharedState = source.shared)
    (callLocal : Simulation.CallLocal)
    (response : Simulation.CallResponse)
    (hOldStack : target.evm.stack = oldPrefix ++ baseStack)
    (hInput :
      Simulation.MemorySafety.WindowSafe contract
        callLocal.inputOffset.toNat callLocal.inputSize.toNat)
    (hOutput :
      Simulation.MemorySafety.WindowSafe contract
        callLocal.outputOffset.toNat callLocal.outputSize.toNat) :
    ScratchStateRel contract plan live (stackOffset + 1) frameBase
      frameDepth frameWords
      (source.withShared
        (Assembly.InteractionSemantics.EVMState.finishCall
          sourceEVM [] callLocal response).toSharedState)
      (target.withEVM
        (Assembly.InteractionSemantics.EVMState.finishCall
          target.evm baseStack callLocal response)) := by
  have hInputRel :
      SharedRel contract sourceEVM.toSharedState target.evm.toSharedState := by
    rw [hSourceShared]
    exact hRel.base.shared
  have hSharedFinal :=
    SharedRel.finishCall hInputRel hRel.activeNoWrap callLocal response
      [] baseStack hInput hOutput
  apply finishExternal hRel _ _ response.statusWord response.returnData
    callLocal.inputOffset callLocal.inputSize
    callLocal.outputOffset callLocal.outputSize hOldStack hSharedFinal
  · simp [Assembly.InteractionSemantics.EVMState.finishCall,
      Assembly.InteractionSemantics.EVMState.installWorld,
      EvmYul.EVM.State.incrPC]
  · simp [Assembly.InteractionSemantics.EVMState.finishCall,
      Assembly.InteractionSemantics.EVMState.installWorld,
      Simulation.CallLocal.finishMachine,
      EvmYul.EVM.State.incrPC]
  · exact hInput
  · exact hOutput

/-- Preserve a live scratch frame across one open-world CREATE response. -/
theorem finishCreate
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState} {target : TargetState}
    {oldPrefix baseStack : List Word}
    (hRel :
      ScratchStateRel contract plan live
        (stackOffset + oldPrefix.length) frameBase
        frameDepth frameWords source target)
    (sourceEVM : Assembly.EVMState)
    (hSourceShared : sourceEVM.toSharedState = source.shared)
    (createLocal : Simulation.CreateLocal)
    (response : Simulation.CreateResponse)
    (hOldStack : target.evm.stack = oldPrefix ++ baseStack)
    (hInput :
      Simulation.MemorySafety.WindowSafe contract
        createLocal.initOffset.toNat createLocal.initSize.toNat) :
    ScratchStateRel contract plan live (stackOffset + 1) frameBase
      frameDepth frameWords
      (source.withShared
        (Assembly.InteractionSemantics.EVMState.finishCreate
          sourceEVM [] createLocal response).toSharedState)
      (target.withEVM
        (Assembly.InteractionSemantics.EVMState.finishCreate
          target.evm baseStack createLocal response)) := by
  have hInputRel :
      SharedRel contract sourceEVM.toSharedState target.evm.toSharedState := by
    rw [hSourceShared]
    exact hRel.base.shared
  have hSharedFinal :=
    SharedRel.finishCreate hInputRel hRel.activeNoWrap createLocal response
      [] baseStack hInput
  apply finishExternal hRel _ _ response.address response.returnData
    createLocal.initOffset createLocal.initSize
    (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)
    hOldStack hSharedFinal
  · simp [Assembly.InteractionSemantics.EVMState.finishCreate,
      Assembly.InteractionSemantics.EVMState.installWorld,
      EvmYul.EVM.State.incrPC]
  · simp [Assembly.InteractionSemantics.EVMState.finishCreate,
      Assembly.InteractionSemantics.EVMState.installWorld,
      Simulation.CreateLocal.finishMachine,
      EvmYul.EVM.State.incrPC]
  · exact hInput
  · exact Simulation.MemorySafety.windowSafe_zero contract 0

/-- Assign a stack local while retaining every scratch-frame invariant. -/
theorem assign_stack_live
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {frameBase frameDepth frameWords planDepth depth : Nat}
    {source : SourceState} {target targetFinal : TargetState}
    {name : Locals.Name} {value old : Word} {rest : List Word}
    (hRel :
      ScratchStateRel contract plan live 1 frameBase
        frameDepth frameWords source target)
    (hStack : target.evm.stack = value :: rest)
    (hFinalStack : targetFinal.evm.stack = rest.set depth value)
    (hShared : targetFinal.evm.toSharedState = target.evm.toSharedState)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hDepth :
      Locals.Layout.lookupDepth? name (currentStackOrder plan live) =
        some (depth + 1))
    (hDepthFrame : depth < frameDepth)
    (hOld : source.vars name = some old) :
    ScratchStateRel contract plan live 0 frameBase frameDepth frameWords
      (source.insert name value) targetFinal := by
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
        hRel.base.assign_stack_live hStack hFinalStack hShared hLive
          hLocation hDepth hOld
      framePointer := ?_
      frameActive := ?_
      frameAllocated := ?_
      frameNoWrap := hRel.frameNoWrap
      frameHostAddressable := hRel.frameHostAddressable
      activeNoWrap := ?_
      frameReserved := hRel.frameReserved
      scratchBound := hRel.scratchBound }
  · rw [hFinalStack]
    simpa using hFinalPointer
  · simpa [hShared] using hRel.frameActive
  · simpa [hShared] using hRel.frameAllocated
  · simpa [hShared] using hRel.activeNoWrap

/--
Store a newly live scratch local in compiler-reserved frame memory. The source
store changes, while source-visible memory remains related outside the
reservation.
-/
theorem assign_scratch_live
    {contract : MemoryContract.Contract} {plan : Plan}
    {beforeLive afterLive : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords : Nat}
    {source : SourceState} {target : TargetState}
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
    (hLocation : plan.location? name = some (.scratch slot))
    (hAssignedBound : slot < frameWords)
    (hReservation : contract.scratch? = some reservation)
    (hRegion :
      reservation.containsRegion (scratchAddress frameBase slot) 1)
    (hStack :
      target.evm.stack =
        EvmYul.UInt256.ofNat (scratchAddress frameBase slot) ::
          value :: rest) :
    ScratchStateRel contract plan afterLive stackOffset frameBase
      frameDepth frameWords (source.insert name value)
      (StateRel.mstoreTarget
        (EvmYul.UInt256.ofNat (scratchAddress frameBase slot))
        value rest target) := by
  have hWriteEndFrame :
      scratchAddress frameBase slot + MemoryContract.wordBytes ≤
        frameBase + MemoryContract.wordBytes * frameWords := by
    have hSucc : slot + 1 ≤ frameWords := Nat.succ_le_iff.mpr hAssignedBound
    calc
      scratchAddress frameBase slot + MemoryContract.wordBytes =
          frameBase + MemoryContract.wordBytes * (slot + 1) := by
            simp [scratchAddress, Nat.mul_add, Nat.add_assoc]
      _ ≤ frameBase + MemoryContract.wordBytes * frameWords :=
        Nat.add_le_add_left
          (Nat.mul_le_mul_left MemoryContract.wordBytes hSucc) frameBase
  have hWriteEndActive := hWriteEndFrame.trans hRel.frameActive
  have hWriteEndMemory := hWriteEndFrame.trans hRel.frameAllocated
  have hWriteEndLt := lt_of_le_of_lt hWriteEndFrame hRel.frameNoWrap
  have hWriteEndHost :=
    lt_of_le_of_lt hWriteEndFrame hRel.frameHostAddressable
  have hWriteAddressLt :
      scratchAddress frameBase slot < EvmYul.UInt256.size := by
    omega
  have hWriteAddress :
      (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)).toNat =
        scratchAddress frameBase slot :=
    EvmYul.UInt256.toNat_ofNat_of_lt hWriteAddressLt
  have hActiveEq :=
    Compiler.MemoryRelation.mstore_activeWords_eq_of_end_le
      target.evm.toMachineState
      (scratchAddress frameBase slot) value hWriteAddress
      (by simpa [MemoryContract.wordBytes] using hWriteEndActive)
  have hMemoryEq :=
    Compiler.MemoryRelation.writeWord_memory_size_eq_of_end_le
      target.evm.toMachineState
      (scratchAddress frameBase slot) value hWriteAddress
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
  · refine ⟨?_, ?_, ?_⟩
    · simpa [Locals.Source.State.insert, StateRel.mstoreTarget,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] using
        (Compiler.MemoryRelation.MachineRel.mstore_target
          (scratchAddress frameBase slot) value hRel.base.machine
          hReservation hRegion hWriteEndLt hWriteEndHost)
    · simpa [Locals.Source.State.insert, StateRel.mstoreTarget,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] using hRel.base.world
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
              (target.evm.toMachineState.mstore
                  (EvmYul.UInt256.ofNat
                    (scratchAddress frameBase slot)) value).lookupMemory
                    (EvmYul.UInt256.ofNat
                      (scratchAddress frameBase slot)) =
                ((source.insert name value).vars name).getD
                  (EvmYul.UInt256.ofNat 0)
            rw [Compiler.MemoryRelation.lookupMemory_mstore_same
              target.evm.toMachineState
              (scratchAddress frameBase slot) value hWriteAddress
              (by simpa [MemoryContract.wordBytes] using hWriteEndHost)
              (by simpa [MemoryContract.wordBytes] using hWriteEndMemory)
              (by simpa [MemoryContract.wordBytes] using hWriteEndActive)
              (by simpa [MemoryContract.wordBytes] using hRel.activeNoWrap)]
            simp [Locals.Source.State.insert]
      · have hOtherBefore : other ∈ beforeLive := by
          rcases hAfter other hOtherAfter with hEq | hBefore
          · exact False.elim (hName hEq)
          · exact hBefore
        have hOld :=
          hRel.base.store other location hOtherBefore hOtherLocation
        cases location with
        | stack planDepth =>
            rcases hOld with ⟨depth, hDepth, hOld⟩
            refine ⟨depth, ?_, ?_⟩
            · simpa [hStackOrder] using hDepth
            · change
                rest[stackOffset + depth]? =
                  Locals.Source.Store.insert
                    source.vars name value other
              change
                target.evm.stack[(stackOffset + 2) + depth]? =
                  source.vars other at hOld
              rw [hStack] at hOld
              have hRest :
                  rest[stackOffset + depth]? = source.vars other := by
                simpa [show
                    (stackOffset + 2) + depth =
                      (stackOffset + depth) + 2 by omega] using hOld
              rw [Locals.Source.Store.insert_of_ne hName]
              exact hRest
        | scratch otherSlot =>
            have hOtherSlotNe : otherSlot ≠ slot :=
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
              (target.evm.toMachineState.mstore
                  (EvmYul.UInt256.ofNat
                    (scratchAddress frameBase slot)) value).lookupMemory
                    (EvmYul.UInt256.ofNat
                      (scratchAddress frameBase otherSlot)) =
                (Locals.Source.Store.insert
                  source.vars name value other).getD
                    (EvmYul.UInt256.ofNat 0)
            rw [Compiler.MemoryRelation.lookupMemory_mstore_disjoint
              target.evm.toMachineState
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

/-- A stack declaration shifts only the hidden scratch-frame depth. -/
theorem declare_stack_live
    {contract : MemoryContract.Contract} {plan : Plan}
    {beforeLive afterLive : List Locals.Name}
    {frameBase frameDepth frameWords planDepth : Nat}
    {source : SourceState} {target : TargetState}
    {name : Locals.Name} {value : Word} {rest : List Word}
    (hRel :
      ScratchStateRel contract plan beforeLive 1 frameBase
        frameDepth frameWords source target)
    (hStack : target.evm.stack = value :: rest)
    (hAfter :
      ∀ other, other ∈ afterLive →
        other = name ∨ other ∈ beforeLive)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hStackOrder :
      currentStackOrder plan afterLive =
        name :: currentStackOrder plan beforeLive) :
    ScratchStateRel contract plan afterLive 0 frameBase
      (frameDepth + 1) frameWords
      (source.insert name value) target := by
  refine
    { base :=
        hRel.base.declare_stack_live hStack hAfter hLocation hStackOrder
      framePointer := ?_
      frameActive := hRel.frameActive
      frameAllocated := hRel.frameAllocated
      frameNoWrap := hRel.frameNoWrap
      frameHostAddressable := hRel.frameHostAddressable
      activeNoWrap := hRel.activeNoWrap
      frameReserved := hRel.frameReserved
      scratchBound := ?_ }
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hRel.framePointer
  · intro other slot hOtherAfter hOtherLocation
    by_cases hName : other = name
    · subst other
      rw [hLocation] at hOtherLocation
      simp at hOtherLocation
    · have hOtherBefore : other ∈ beforeLive := by
        rcases hAfter other hOtherAfter with hEq | hBefore
        · exact False.elim (hName hEq)
        · exact hBefore
      exact hRel.scratchBound other slot hOtherBefore hOtherLocation

end ScratchStateRel

/-- Runtime representation selected by the ordinary allocation artifact. -/
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

/-- One representation-neutral allocation relation for recursive proofs. -/
inductive ActivationStateRel
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name) (stackOffset frameBase : Nat) :
    ActivationMode → SourceState → TargetState → Prop where
  | stack {source target}
      (liveStackOnly : LiveStackOnly plan live)
      (activeNoWrap :
        target.evm.activeWords.toNat * MemoryContract.wordBytes <
          EvmYul.UInt256.size)
      (state :
        StateRel contract plan live stackOffset frameBase source target) :
      ActivationStateRel contract plan live stackOffset frameBase
        .stack source target
  | scratch {frameDepth frameWords source target}
      (state :
        ScratchStateRel contract plan live stackOffset frameBase
          frameDepth frameWords source target) :
      ActivationStateRel contract plan live stackOffset frameBase
        (.scratch frameDepth frameWords) source target

namespace ActivationStateRel

/-- Scope restriction preserves either allocation representation. -/
theorem restrict_source_live
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {source : SourceState} {target : TargetState}
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase mode
        source target) :
    ActivationStateRel contract plan live stackOffset frameBase mode
      (source.restrictTo live) target := by
  cases hRel with
  | stack hOnly hActive hState =>
      exact .stack hOnly hActive hState.restrict_source_live
  | scratch hScratch =>
      exact .scratch
        { hScratch with
          base := hScratch.base.restrict_source_live }

/-- Declare one stack-resident local in either allocation representation. -/
theorem declare_stack_live
    {contract : MemoryContract.Contract} {plan : Plan}
    {beforeLive afterLive : List Locals.Name}
    {frameBase planDepth : Nat} {mode : ActivationMode}
    {source : SourceState} {target : TargetState}
    {name : Locals.Name} {value : Word} {rest : List Word}
    (hRel :
      ActivationStateRel contract plan beforeLive 1 frameBase mode
        source target)
    (hStack : target.evm.stack = value :: rest)
    (hAfter :
      ∀ other, other ∈ afterLive →
        other = name ∨ other ∈ beforeLive)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hStackOrder :
      currentStackOrder plan afterLive =
        name :: currentStackOrder plan beforeLive) :
    ActivationStateRel contract plan afterLive 0 frameBase
      mode.afterStackDeclaration (source.insert name value) target := by
  cases hRel with
  | stack hOnly hActive hState =>
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
      exact .stack hAfterOnly hActive
        (hState.declare_stack_live hStack hAfter hLocation hStackOrder)
  | scratch hScratch =>
      exact .scratch
        (hScratch.declare_stack_live hStack hAfter hLocation hStackOrder)

theorem shared
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode} {source : SourceState} {target : TargetState}
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase mode
        source target) :
    SharedRel contract source.shared target.evm.toSharedState := by
  cases hRel with
  | stack _ _ state => exact state.shared
  | scratch state => exact state.base.shared

theorem activeNoWrap
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode} {source : SourceState} {target : TargetState}
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase mode
        source target) :
    target.evm.activeWords.toNat * MemoryContract.wordBytes <
      EvmYul.UInt256.size := by
  cases hRel with
  | stack _ activeNoWrap _ => exact activeNoWrap
  | scratch state => exact state.activeNoWrap

theorem state
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode} {source : SourceState} {target : TargetState}
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase mode
        source target) :
    StateRel contract plan live stackOffset frameBase source target := by
  cases hRel with
  | stack _ _ state => exact state
  | scratch state => exact state.base

theorem push_target_by
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode} {source : SourceState} {target : TargetState}
    (pcDelta : Nat) (value : Word)
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase mode
        source target) :
    ActivationStateRel contract plan live (stackOffset + 1) frameBase mode
      source (StateRel.pushTargetBy pcDelta value target) := by
  cases hRel with
  | stack liveStackOnly activeNoWrap state =>
      exact .stack liveStackOnly
        (by simpa [StateRel.pushTargetBy,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] using activeNoWrap)
        (state.push_target_by pcDelta value)
  | scratch state =>
      exact .scratch (state.push_target_by pcDelta value)

/--
Rebase either allocation representation across a target stack-prefix change.
The caller supplies the exact scratch-cell equality because memory-writing
primitive families establish it from their source-facing reservation safety.
-/
theorem rebase_prefix
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode} {source sourceFinal : SourceState}
    {target targetFinal : TargetState}
    {oldPrefix newPrefix baseStack : List Word}
    (hRel :
      ActivationStateRel contract plan live
        (stackOffset + oldPrefix.length) frameBase mode source target)
    (hShared :
      SharedRel contract sourceFinal.shared targetFinal.evm.toSharedState)
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
    (hVars : sourceFinal.vars = source.vars)
    (hMemory :
      target.evm.toMachineState.memory.size ≤
        targetFinal.evm.toMachineState.memory.size)
    (hActive :
      target.evm.activeWords.toNat ≤ targetFinal.evm.activeWords.toNat)
    (hActiveNoWrap :
      targetFinal.evm.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size) :
    ActivationStateRel contract plan live
      (stackOffset + newPrefix.length) frameBase mode sourceFinal targetFinal := by
  have hBase :
      StateRel contract plan live
        (stackOffset + newPrefix.length) frameBase sourceFinal targetFinal :=
    ⟨hShared.machine, hShared.world,
      StoreRel.rebase_prefix_of_lookup hRel.state.store hOldStack hNewStack
        hScratch hVars⟩
  cases hRel with
  | stack liveStackOnly _activeNoWrap _state =>
      exact .stack liveStackOnly hActiveNoWrap hBase
  | scratch state =>
      exact .scratch
        (state.rebase_prefix_mono hBase hOldStack hNewStack
          hMemory hActive hActiveNoWrap)

/-- Preserve either allocation representation across one response update. -/
theorem finishExternal
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase : Nat} {mode : ActivationMode}
    {source : SourceState} {target : TargetState}
    {oldPrefix baseStack : List Word}
    (hRel :
      ActivationStateRel contract plan live
        (stackOffset + oldPrefix.length) frameBase mode source target)
    (sourceFinalShared : EvmYul.SharedState .EVM)
    (targetFinalEVM : Assembly.EVMState)
    (result : Word) (returnData : ByteArray)
    (inputOffset inputSize outputOffset outputSize : Word)
    (hOldStack : target.evm.stack = oldPrefix ++ baseStack)
    (hSharedFinal :
      SharedRel contract sourceFinalShared targetFinalEVM.toSharedState)
    (hFinalStack : targetFinalEVM.stack = result :: baseStack)
    (hFinalMachine :
      targetFinalEVM.toMachineState =
        target.evm.toMachineState.finishExternalCall returnData
          inputOffset inputSize outputOffset outputSize)
    (hInput :
      Simulation.MemorySafety.WindowSafe contract
        inputOffset.toNat inputSize.toNat)
    (hOutput :
      Simulation.MemorySafety.WindowSafe contract
        outputOffset.toNat outputSize.toNat) :
    ActivationStateRel contract plan live (stackOffset + 1) frameBase mode
      (source.withShared sourceFinalShared)
      (target.withEVM targetFinalEVM) := by
  cases hRel with
  | scratch state =>
      exact .scratch
        (state.finishExternal sourceFinalShared targetFinalEVM result
          returnData inputOffset inputSize outputOffset outputSize
          hOldStack hSharedFinal hFinalStack hFinalMachine hInput hOutput)
  | stack liveStackOnly activeNoWrap state =>
      have hGrowth :=
        Simulation.MemorySafety.finishExternalCall_growth
          target.evm.toMachineState activeNoWrap returnData
          inputOffset inputSize outputOffset outputSize hInput hOutput
      have hNewStack :
          (target.withEVM targetFinalEVM).evm.stack = [result] ++ baseStack := by
        simpa [Structured.RunState.withEVM] using hFinalStack
      refine .stack liveStackOnly ?_ ?_
      · simpa [Structured.RunState.withEVM, hFinalMachine] using
          hGrowth.activeNoWrap
      · refine ⟨?_, ?_, ?_⟩
        · simpa [Structured.RunState.withEVM] using hSharedFinal.machine
        · simpa [Structured.RunState.withEVM] using hSharedFinal.world
        · exact
            state.store.rebase_prefix_stack_only liveStackOnly hOldStack
              hNewStack (by simp [Locals.Source.State.withShared])

theorem finishCall
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase : Nat} {mode : ActivationMode}
    {source : SourceState} {target : TargetState}
    {oldPrefix baseStack : List Word}
    (hRel :
      ActivationStateRel contract plan live
        (stackOffset + oldPrefix.length) frameBase mode source target)
    (sourceEVM : Assembly.EVMState)
    (hSourceShared : sourceEVM.toSharedState = source.shared)
    (callLocal : Simulation.CallLocal)
    (response : Simulation.CallResponse)
    (hOldStack : target.evm.stack = oldPrefix ++ baseStack)
    (hInput :
      Simulation.MemorySafety.WindowSafe contract
        callLocal.inputOffset.toNat callLocal.inputSize.toNat)
    (hOutput :
      Simulation.MemorySafety.WindowSafe contract
        callLocal.outputOffset.toNat callLocal.outputSize.toNat) :
    ActivationStateRel contract plan live (stackOffset + 1) frameBase mode
      (source.withShared
        (Assembly.InteractionSemantics.EVMState.finishCall
          sourceEVM [] callLocal response).toSharedState)
      (target.withEVM
        (Assembly.InteractionSemantics.EVMState.finishCall
          target.evm baseStack callLocal response)) := by
  have hInputRel :
      SharedRel contract sourceEVM.toSharedState target.evm.toSharedState := by
    rw [hSourceShared]
    cases hRel with
    | stack _ _ state => exact state.shared
    | scratch state => exact state.base.shared
  have hSharedFinal :=
    SharedRel.finishCall hInputRel
      (by
        cases hRel with
        | stack _ activeNoWrap _ => exact activeNoWrap
        | scratch state => exact state.activeNoWrap)
      callLocal response [] baseStack hInput hOutput
  apply finishExternal hRel _ _ response.statusWord response.returnData
    callLocal.inputOffset callLocal.inputSize
    callLocal.outputOffset callLocal.outputSize hOldStack hSharedFinal
  · simp [Assembly.InteractionSemantics.EVMState.finishCall,
      Assembly.InteractionSemantics.EVMState.installWorld,
      EvmYul.EVM.State.incrPC]
  · simp [Assembly.InteractionSemantics.EVMState.finishCall,
      Assembly.InteractionSemantics.EVMState.installWorld,
      Simulation.CallLocal.finishMachine,
      EvmYul.EVM.State.incrPC]
  · exact hInput
  · exact hOutput

theorem finishCreate
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase : Nat} {mode : ActivationMode}
    {source : SourceState} {target : TargetState}
    {oldPrefix baseStack : List Word}
    (hRel :
      ActivationStateRel contract plan live
        (stackOffset + oldPrefix.length) frameBase mode source target)
    (sourceEVM : Assembly.EVMState)
    (hSourceShared : sourceEVM.toSharedState = source.shared)
    (createLocal : Simulation.CreateLocal)
    (response : Simulation.CreateResponse)
    (hOldStack : target.evm.stack = oldPrefix ++ baseStack)
    (hInput :
      Simulation.MemorySafety.WindowSafe contract
        createLocal.initOffset.toNat createLocal.initSize.toNat) :
    ActivationStateRel contract plan live (stackOffset + 1) frameBase mode
      (source.withShared
        (Assembly.InteractionSemantics.EVMState.finishCreate
          sourceEVM [] createLocal response).toSharedState)
      (target.withEVM
        (Assembly.InteractionSemantics.EVMState.finishCreate
          target.evm baseStack createLocal response)) := by
  have hInputRel :
      SharedRel contract sourceEVM.toSharedState target.evm.toSharedState := by
    rw [hSourceShared]
    cases hRel with
    | stack _ _ state => exact state.shared
    | scratch state => exact state.base.shared
  have hSharedFinal :=
    SharedRel.finishCreate hInputRel
      (by
        cases hRel with
        | stack _ activeNoWrap _ => exact activeNoWrap
        | scratch state => exact state.activeNoWrap)
      createLocal response [] baseStack hInput
  apply finishExternal hRel _ _ response.address response.returnData
    createLocal.initOffset createLocal.initSize
    (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 0)
    hOldStack hSharedFinal
  · simp [Assembly.InteractionSemantics.EVMState.finishCreate,
      Assembly.InteractionSemantics.EVMState.installWorld,
      EvmYul.EVM.State.incrPC]
  · simp [Assembly.InteractionSemantics.EVMState.finishCreate,
      Assembly.InteractionSemantics.EVMState.installWorld,
      Simulation.CreateLocal.finishMachine,
      EvmYul.EVM.State.incrPC]
  · exact hInput
  · exact Simulation.MemorySafety.windowSafe_zero contract 0

end ActivationStateRel

/-- Exact target stack prefix produced by an allocated expression. -/
structure ExprResultRel
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name) (stackOffset frameBase resultCount : Nat)
    (source : SourceState) (targetInitial targetFinal : TargetState)
    (values : List Word) : Prop where
  state :
    StateRel contract plan live (stackOffset + resultCount) frameBase
      source targetFinal
  valuesLength : values.length = resultCount
  stack :
    targetFinal.evm.stack = values.reverse ++ targetInitial.evm.stack

namespace ExprResultRel

theorem literal
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {source : SourceState} {target : TargetState}
    (value : Word)
    (hRel : StateRel contract plan live stackOffset frameBase source target) :
    ExprResultRel contract plan live stackOffset frameBase 1
      source target (StateRel.pushTargetBy 33 value target) [value] := by
  refine ⟨StateRel.push_target_by 33 value hRel, rfl, ?_⟩
  simp [StateRel.pushTargetBy,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

end ExprResultRel

/-- Expression-result relation retaining a live scratch frame. -/
structure ScratchExprResultRel
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name)
    (stackOffset frameBase frameDepth frameWords resultCount : Nat)
    (source : SourceState) (targetInitial targetFinal : TargetState)
    (values : List Word) : Prop where
  state :
    ScratchStateRel contract plan live
      (stackOffset + resultCount) frameBase frameDepth frameWords
      source targetFinal
  valuesLength : values.length = resultCount
  stack :
    targetFinal.evm.stack = values.reverse ++ targetInitial.evm.stack

/-- Expression result retaining whichever allocation representation is live. -/
structure ActivationExprResultRel
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name)
    (stackOffset frameBase resultCount : Nat) (mode : ActivationMode)
    (source : SourceState) (targetInitial targetFinal : TargetState)
    (values : List Word) : Prop where
  state :
    ActivationStateRel contract plan live
      (stackOffset + resultCount) frameBase mode source targetFinal
  valuesLength : values.length = resultCount
  stack :
    targetFinal.evm.stack = values.reverse ++ targetInitial.evm.stack

namespace ActivationExprResultRel

theorem nil
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {source : SourceState} {target : TargetState}
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase mode
        source target) :
    ActivationExprResultRel contract plan live stackOffset frameBase 0 mode
      source target target [] := by
  exact ⟨by simpa using hRel, rfl, by simp⟩

theorem literal
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode} {source : SourceState} {target : TargetState}
    (value : Word)
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase mode
        source target) :
    ActivationExprResultRel contract plan live stackOffset frameBase 1 mode
      source target (StateRel.pushTargetBy 33 value target) [value] := by
  refine ⟨hRel.push_target_by 33 value, rfl, ?_⟩
  simp [StateRel.pushTargetBy,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem append
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {sourceHead sourceFinal : SourceState}
    {targetInitial targetHead targetFinal : TargetState}
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

inductive ModeRel : Locals.Source.Mode → Structured.Mode → Prop where
  | regular : ModeRel .regular .regular
  | brk : ModeRel .brk .brk
  | cont : ModeRel .cont .cont
  | leave : ModeRel .leave .leave
  | halt (kind : Assembly.HaltKind) :
      ModeRel (.halt kind) (.halt kind)

/-- Terminal states retain only the observable shared state. -/
structure HaltStateRel
    (contract : MemoryContract.Contract) (plan : Plan)
    (source : SourceState) (target : TargetState) : Prop where
  shared : SharedRel contract source.shared target.evm.toSharedState

/-- Exact activation-exit relation after compiler-owned frame cleanup. -/
structure LeaveStateRel
    (contract : MemoryContract.Contract) (returns : List Locals.Name)
    (source : SourceState) (target : TargetState) : Prop where
  shared : SharedRel contract source.shared target.evm.toSharedState
  activeNoWrap :
    target.evm.activeWords.toNat * MemoryContract.wordBytes <
      EvmYul.UInt256.size
  values :
    ∃ returned,
      Functions.Source.Store.lookupMany returns source.vars = some returned ∧
        target.evm.stack = returned.reverse

/--
Outcome relation retaining the selected allocation representation for every
continuing mode. Activation exits intentionally erase local realization after
the compiler-owned cleanup has made it unobservable.
-/
inductive ActivationOutcomeRel
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name) (stackOffset frameBase : Nat)
    (mode : ActivationMode) : SourceOutcome → TargetOutcome → Prop where
  | regular {source : SourceState} {target : TargetState}
      (state :
        ActivationStateRel contract plan live stackOffset frameBase mode
          source target) :
      ActivationOutcomeRel contract plan live stackOffset frameBase mode
        (Functions.Source.Effectful.Outcome.regular source)
        (Structured.EffectSemantics.Outcome.regular target)
  | brk {source : SourceState} {target : TargetState}
      (state :
        ActivationStateRel contract plan live stackOffset frameBase mode
          source target) :
      ActivationOutcomeRel contract plan live stackOffset frameBase mode
        (Functions.Source.Effectful.Outcome.brk source)
        (Structured.EffectSemantics.Outcome.brk target)
  | cont {source : SourceState} {target : TargetState}
      (state :
        ActivationStateRel contract plan live stackOffset frameBase mode
          source target) :
      ActivationOutcomeRel contract plan live stackOffset frameBase mode
        (Functions.Source.Effectful.Outcome.cont source)
        (Structured.EffectSemantics.Outcome.cont target)
  | leave {source : SourceState} {target : TargetState}
      (state : LeaveStateRel contract live source target) :
      ActivationOutcomeRel contract plan live stackOffset frameBase mode
        (Functions.Source.Effectful.Outcome.leave source)
        (Structured.EffectSemantics.Outcome.leave target)
  | halt (kind : Assembly.HaltKind)
      {source : SourceState} {target : TargetState}
      (state : HaltStateRel contract plan source target) :
      ActivationOutcomeRel contract plan live stackOffset frameBase mode
        (Functions.Source.Effectful.Outcome.halt kind source)
        (Structured.EffectSemantics.Outcome.halt kind target)

namespace ActivationOutcomeRel

theorem modeRel
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {source : SourceOutcome} {target : TargetOutcome}
    (hRel :
      ActivationOutcomeRel contract plan live stackOffset frameBase mode
        source target) :
    ModeRel source.mode target.mode := by
  cases hRel with
  | regular _ => exact .regular
  | brk _ => exact .brk
  | cont _ => exact .cont
  | leave _ => exact .leave
  | halt kind _ => exact .halt kind

end ActivationOutcomeRel

/-- Mode-indexed result relation for ordinary activation control. -/
inductive OutcomeRel
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name) (stackOffset frameBase : Nat) :
    SourceOutcome → TargetOutcome → Prop where
  | regular {source : SourceState} {target : TargetState}
      (state : StateRel contract plan live stackOffset frameBase source target) :
      OutcomeRel contract plan live stackOffset frameBase
        (Functions.Source.Effectful.Outcome.regular source)
        (Structured.EffectSemantics.Outcome.regular target)
  | brk {source : SourceState} {target : TargetState}
      (state : StateRel contract plan live stackOffset frameBase source target) :
      OutcomeRel contract plan live stackOffset frameBase
        (Functions.Source.Effectful.Outcome.brk source)
        (Structured.EffectSemantics.Outcome.brk target)
  | cont {source : SourceState} {target : TargetState}
      (state : StateRel contract plan live stackOffset frameBase source target) :
      OutcomeRel contract plan live stackOffset frameBase
        (Functions.Source.Effectful.Outcome.cont source)
        (Structured.EffectSemantics.Outcome.cont target)
  | leave {source : SourceState} {target : TargetState}
      (state : StateRel contract plan live stackOffset frameBase source target) :
      OutcomeRel contract plan live stackOffset frameBase
        (Functions.Source.Effectful.Outcome.leave source)
        (Structured.EffectSemantics.Outcome.leave target)
  | halt (kind : Assembly.HaltKind)
      {source : SourceState} {target : TargetState}
      (state : HaltStateRel contract plan source target) :
      OutcomeRel contract plan live stackOffset frameBase
        (Functions.Source.Effectful.Outcome.halt kind source)
        (Structured.EffectSemantics.Outcome.halt kind target)

namespace OutcomeRel

theorem modeRel
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {source : SourceOutcome} {target : TargetOutcome}
    (hRel :
      OutcomeRel contract plan live stackOffset frameBase source target) :
    ModeRel source.mode target.mode := by
  cases hRel with
  | regular _ => exact .regular
  | brk _ => exact .brk
  | cont _ => exact .cont
  | leave _ => exact .leave
  | halt kind _ => exact .halt kind

end OutcomeRel

abbrev OpenOutcomeRel
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name) (stackOffset frameBase : Nat)
    (source : Simulation.Interaction EVMException SourceOutcome)
    (target : Simulation.Interaction EVMException TargetOutcome) : Prop :=
  Simulation.Interaction.Rel
    (Simulation.Interaction.ExceptRel Eq
      (OutcomeRel contract plan live stackOffset frameBase))
    source target

end AllocationInteractionRelation
end Functions
end EvmCompiler
