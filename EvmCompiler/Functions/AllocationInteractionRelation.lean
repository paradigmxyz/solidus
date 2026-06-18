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

def LiveDefined (live : List Locals.Name) (source : Locals.Source.State) :
    Prop :=
  ∀ name, name ∈ live → ∃ value, source.vars name = some value

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

def pushTargetBy (pcDelta : Nat) (value : Word)
    (target : TargetState) : TargetState :=
  target.withEVM
    (target.evm.replaceStackAndIncrPC
      (value :: target.evm.stack) (pcΔ := pcDelta))

def pushTarget (value : Word) (target : TargetState) : TargetState :=
  pushTargetBy 1 value target

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

end ScratchStateRel

/-- Runtime representation selected by the ordinary allocation artifact. -/
inductive ActivationMode where
  | stack
  | scratch (frameDepth frameWords : Nat)
  deriving DecidableEq, Repr

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
