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
