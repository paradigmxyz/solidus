import EvmCompiler.Assembly.Compact
import EvmCompiler.Assembly.InteractionConcreteResources
import Mathlib.Algebra.Group.Fin.Basic

namespace EvmCompiler
namespace Assembly
namespace GasfulBridge

open Simulation

/-!
Gasful EVM boundary for raw emitted bytecode.

This module names the honest relation between EVMYulLean's charged `EVM.X`
runner and the compiler's open raw-bytecode interaction semantics.  External
CALL/CREATE behavior remains the existing open strategy boundary; this file
records the parent-frame gas accounting that a concrete strategy must match.
-/

def chargeGas (state : EVMState) (cost : Nat) : EVMState :=
  { state with
    gasAvailable := state.gasAvailable - EvmYul.UInt256.ofNat cost }

theorem eraseGas_chargeGas (state : EVMState) (cost : Nat) :
    eraseGas (chargeGas state cost) = eraseGas state := by
  cases state
  rfl

theorem eraseControl_chargeGas (state : EVMState) (cost : Nat) :
    eraseControl (chargeGas state cost) = eraseControl state := by
  simp [eraseControl, eraseGas_chargeGas]

theorem sameData_chargeGas_left (state : EVMState) (cost : Nat) :
    SameData (chargeGas state cost) state := by
  exact eraseControl_chargeGas state cost

theorem sameData_chargeGas_right (state : EVMState) (cost : Nat) :
    SameData state (chargeGas state cost) := by
  exact (eraseControl_chargeGas state cost).symm

/-- Erase the mutable open world as well as gas/control, retaining only the
frame-local data that emitted bytecode can compare across an external
request/response boundary. -/
def eraseOpenWorldData (state : EVMState) : EVMState :=
  { eraseControl state with
    accountMap := ∅
    substate := default
    createdAccounts := ∅ }

/-- Honest gas-erased relation at an external boundary. Mutable accounts,
substate, and created-account tracking are compared through the code-erased
`OpenWorld` projection; protected frame-local data is compared directly after
erasing gas and interpreter control. -/
structure OpenSameData (left right : EVMState) : Prop where
  world :
    OpenWorld.ofEVMShared left.toSharedState =
      OpenWorld.ofEVMShared right.toSharedState
  frame : eraseOpenWorldData left = eraseOpenWorldData right

theorem OpenSameData.of_sameData
    {left right : EVMState} (hSame : SameData left right) :
    OpenSameData left right := by
  change eraseControl left = eraseControl right at hSame
  constructor
  · simpa [eraseControl, eraseGas] using
      congrArg
        (fun state : EVMState =>
          OpenWorld.ofEVMShared state.toSharedState)
        hSame
  · unfold eraseOpenWorldData
    rw [hSame]

theorem OpenSameData.trans
    {first second third : EVMState}
    (hFirst : OpenSameData first second)
    (hSecond : OpenSameData second third) :
    OpenSameData first third :=
  ⟨hFirst.world.trans hSecond.world, hFirst.frame.trans hSecond.frame⟩

/-- Recursive gasful/open state invariant. The mutable world is compared
through its normalized open projection, frame-local data ignores gas/control,
and the current PC remains exact so both runners decode the same instruction. -/
structure OpenStateRel (gasful openState : EVMState) : Prop where
  openData : OpenSameData gasful openState
  pc_eq : gasful.pc = openState.pc

namespace OpenStateRel

theorem refl (state : EVMState) : OpenStateRel state state :=
  ⟨OpenSameData.of_sameData (SameData.refl state), rfl⟩

theorem trans {first second third : EVMState}
    (hFirst : OpenStateRel first second)
    (hSecond : OpenStateRel second third) :
    OpenStateRel first third :=
  ⟨hFirst.openData.trans hSecond.openData,
    hFirst.pc_eq.trans hSecond.pc_eq⟩

theorem of_sameData {gasful openState : EVMState}
    (hData : SameData gasful openState)
    (hPc : gasful.pc = openState.pc) :
    OpenStateRel gasful openState :=
  ⟨OpenSameData.of_sameData hData, hPc⟩

theorem stack_eq {gasful openState : EVMState}
    (hRel : OpenStateRel gasful openState) :
    gasful.stack = openState.stack := by
  have hFrame := hRel.openData.frame
  cases gasful
  cases openState
  simp [eraseOpenWorldData, eraseControl, eraseGas] at hFrame
  exact hFrame.2

theorem executionEnv_eq {gasful openState : EVMState}
    (hRel : OpenStateRel gasful openState) :
    gasful.executionEnv = openState.executionEnv := by
  have hFrame := hRel.openData.frame
  cases gasful
  cases openState
  simp [eraseOpenWorldData, eraseControl, eraseGas] at hFrame
  exact hFrame.1.1.2.2.2.1

theorem code_eq {gasful openState : EVMState}
    (hRel : OpenStateRel gasful openState) :
    gasful.executionEnv.code = openState.executionEnv.code := by
  rw [hRel.executionEnv_eq]

end OpenStateRel

theorem OpenStateRel.replaceStackAndIncrPC
    {left right : EVMState} {leftStack rightStack : EvmYul.Stack Word}
    {pcDelta : Nat} (hRel : OpenStateRel left right)
    (hStack : leftStack = rightStack) :
    OpenStateRel
      (left.replaceStackAndIncrPC leftStack (pcΔ := pcDelta))
      (right.replaceStackAndIncrPC rightStack (pcΔ := pcDelta)) := by
  constructor
  · constructor
    · simpa [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] using hRel.openData.world
    · have hFrame := hRel.openData.frame
      cases left
      cases right
      simp [eraseOpenWorldData, eraseControl, eraseGas,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] at hFrame ⊢
      exact ⟨hFrame.1, hStack⟩
  · simpa [EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, hRel.pc_eq]

theorem OpenStateRel.withPcStack
    {left right : EVMState} {leftPc rightPc : Word}
    {leftStack rightStack : EvmYul.Stack Word}
    (hRel : OpenStateRel left right)
    (hPc : leftPc = rightPc) (hStack : leftStack = rightStack) :
    OpenStateRel { left with pc := leftPc, stack := leftStack }
      { right with pc := rightPc, stack := rightStack } := by
  constructor
  · constructor
    · simpa using hRel.openData.world
    · have hFrame := hRel.openData.frame
      cases left
      cases right
      simp [eraseOpenWorldData, eraseControl, eraseGas] at hFrame ⊢
      exact ⟨hFrame.1, hStack⟩
  · exact hPc

/-- A concrete exchange answers a resource query with the value read from the
given gasful/open frame state. External exchanges are intentionally left to the
existing open-world strategy relation. -/
def ExchangeResolvedAt (state : EVMState)
    (exchange : Interaction.Exchange) : Prop :=
  match exchange with
  | ⟨.resource kind, answer⟩ =>
      answer = InteractionConcreteResources.resourceValue kind state
  | ⟨.external _ _, _⟩ => True

theorem resourceExchange_resolvedAt
    (kind : ResourceQuery) (state : EVMState) :
    ExchangeResolvedAt state
      (InteractionConcreteResources.resourceExchange kind
        (InteractionConcreteResources.resourceValue kind state)) := by
  cases kind <;> rfl

theorem gas_resourceExchange_resolvedAt (state : EVMState) :
    ExchangeResolvedAt state
      (InteractionConcreteResources.resourceExchange .gas
        (EvmYul.MachineState.gas state.toMachineState)) := by
  rfl

theorem msize_resourceExchange_resolvedAt (state : EVMState) :
    ExchangeResolvedAt state
      (InteractionConcreteResources.resourceExchange .msize
        (EvmYul.MachineState.msize state.toMachineState)) := by
  rfl

/-- `GAS` in the open target is resolved by the actual charged frame state at
the point where the gasful EVM step has already paid the instruction charge. -/
theorem gas_observation_executes_after_charge
    (state : EVMState) (cost : Nat) :
    Interaction.Executes
      (InteractionSemantics.Target.openStepInstrResult
        (.prim .gas) (chargeGas state cost))
      [InteractionConcreteResources.resourceExchange .gas
        (InteractionConcreteResources.resourceValue .gas
          (chargeGas state cost))]
      (.ok
        (InteractionConcreteResources.resourceResult .gas
          (chargeGas state cost))) := by
  exact
    InteractionConcreteResources.openStepInstrResult_executes_of_resource
      (instr := .prim .gas) (state := chargeGas state cost)
      (kind := .gas) rfl

/-- `MSIZE` is resolved by the actual charged frame state, in the same ordered
resource protocol as `GAS`. -/
theorem msize_observation_executes_after_charge
    (state : EVMState) (cost : Nat) :
    Interaction.Executes
      (InteractionSemantics.Target.openStepInstrResult
        (.prim .msize) (chargeGas state cost))
      [InteractionConcreteResources.resourceExchange .msize
        (InteractionConcreteResources.resourceValue .msize
          (chargeGas state cost))]
      (.ok
        (InteractionConcreteResources.resourceResult .msize
          (chargeGas state cost))) := by
  exact
    InteractionConcreteResources.openStepInstrResult_executes_of_resource
      (instr := .prim .msize) (state := chargeGas state cost)
      (kind := .msize) rfl

theorem compact_gas_observation_executes_after_charge
    (state : EVMState) (cost : Nat) :
    Interaction.Executes
      ((Compact.Instr.prim .gas).openStepResult (chargeGas state cost))
      [InteractionConcreteResources.resourceExchange .gas
        (InteractionConcreteResources.resourceValue .gas
          (chargeGas state cost))]
      (.ok
        (InteractionConcreteResources.resourceResult .gas
          (chargeGas state cost))) := by
  simpa [Compact.Instr.openStepResult, Compact.Instr.openStep,
    InteractionSemantics.Target.openStepInstrResult,
    Target.stepInstrResultWith] using
    gas_observation_executes_after_charge state cost

theorem compact_msize_observation_executes_after_charge
    (state : EVMState) (cost : Nat) :
    Interaction.Executes
      ((Compact.Instr.prim .msize).openStepResult (chargeGas state cost))
      [InteractionConcreteResources.resourceExchange .msize
        (InteractionConcreteResources.resourceValue .msize
          (chargeGas state cost))]
      (.ok
        (InteractionConcreteResources.resourceResult .msize
          (chargeGas state cost))) := by
  simpa [Compact.Instr.openStepResult, Compact.Instr.openStep,
    InteractionSemantics.Target.openStepInstrResult,
    Target.stepInstrResultWith] using
    msize_observation_executes_after_charge state cost

/-- Raw decoded bytecode executes a charged `GAS` observer with the actual
post-charge gas value. -/
theorem raw_gas_observation_executes_after_charge
    {bytes : ByteArray} {pc : Nat} {state : EVMState} {cost : Nat}
    (hDecode : Compact.decodeAt bytes pc (.prim .gas))
    (hPc : (chargeGas state cost).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (chargeGas state cost))
      [InteractionConcreteResources.resourceExchange .gas
        (InteractionConcreteResources.resourceValue .gas
          (chargeGas state cost))]
      (.ok
        (InteractionConcreteResources.resourceResult .gas
          (chargeGas state cost))) := by
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim .gas) trivial hDecode hPc]
  exact compact_gas_observation_executes_after_charge state cost

/-- Raw decoded bytecode executes a charged `MSIZE` observer with the actual
post-charge active-memory size. -/
theorem raw_msize_observation_executes_after_charge
    {bytes : ByteArray} {pc : Nat} {state : EVMState} {cost : Nat}
    (hDecode : Compact.decodeAt bytes pc (.prim .msize))
    (hPc : (chargeGas state cost).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (chargeGas state cost))
      [InteractionConcreteResources.resourceExchange .msize
        (InteractionConcreteResources.resourceValue .msize
          (chargeGas state cost))]
      (.ok
        (InteractionConcreteResources.resourceResult .msize
          (chargeGas state cost))) := by
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim .msize) trivial hDecode hPc]
  exact compact_msize_observation_executes_after_charge state cost

/-- Successful charged ordinary execution is compared after erasing gas and
compiler-owned control counters. The concrete `gasfulStep` field is the
EVMYulLean step result after memory and dynamic gas checks have succeeded. -/
structure ChargedStepRel
    (before : EVMState) (cost : Nat)
    (gasfulStep openStep : EVMState) : Prop where
  gasfulErasesToOpen :
    SameData gasfulStep openStep
  openErasesToCharged :
    SameData openStep (chargeGas before cost)

/-- The opcode selected by `EVM.X` at the current gasful program counter.  A
decode miss follows EVMYulLean's `X` definition and behaves like `STOP`. -/
def decodedOperationAt (state : EVMState) : EvmYul.Operation .EVM :=
  ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
    (EvmYul.Operation.STOP, none)).1

def memoryExpansionCostAt (state : EVMState) : Nat :=
  EvmYul.EVM.memoryExpansionCost state (decodedOperationAt state)

def afterMemoryChargeAt (state : EVMState) : EVMState :=
  chargeGas state (memoryExpansionCostAt state)

def dynamicGasCostAt (state : EVMState) : Nat :=
  EvmYul.EVM.C' (afterMemoryChargeAt state) (decodedOperationAt state)

def afterDynamicChargeAt (state : EVMState) : EVMState :=
  chargeGas (afterMemoryChargeAt state) (dynamicGasCostAt state)

/-- The state passed to `EvmYul.step` by `EVM.X` after the memory charge, the
interpreter-owned `execLength` increment, and the dynamic gas charge. -/
def afterEVMInstructionChargeAt (state : EVMState) : EVMState :=
  chargeGas
    { afterMemoryChargeAt state with execLength := state.execLength + 1 }
    (dynamicGasCostAt state)

theorem afterEVMInstructionChargeAt_openStateRel_left
    {gasful openState : EVMState}
    (hRel : OpenStateRel gasful openState) :
    OpenStateRel (afterEVMInstructionChargeAt gasful) openState := by
  constructor
  · constructor
    · simpa [afterEVMInstructionChargeAt, afterMemoryChargeAt,
        chargeGas] using hRel.openData.world
    · simpa [afterEVMInstructionChargeAt, afterMemoryChargeAt,
        chargeGas, eraseOpenWorldData, eraseControl, eraseGas] using
        hRel.openData.frame
  · simpa [afterEVMInstructionChargeAt, afterMemoryChargeAt,
      chargeGas] using hRel.pc_eq

theorem sameData_afterEVMInstructionCharge_afterDynamic
    (state : EVMState) :
    SameData (afterEVMInstructionChargeAt state)
      (afterDynamicChargeAt state) := by
  cases state
  rfl

def resourcePrimOp : ResourceQuery → PrimOp
  | .gas => .gas
  | .msize => .msize

def gasfulResourceNext (kind : ResourceQuery) (state : EVMState) : EVMState :=
  let charged := afterEVMInstructionChargeAt state
  charged.replaceStackAndIncrPC
    (charged.stack.push
      (InteractionConcreteResources.resourceValue kind
        (afterDynamicChargeAt state)))

def openResourceNext (kind : ResourceQuery) (state : EVMState) : EVMState :=
  (afterDynamicChargeAt state).replaceStackAndIncrPC
    ((afterDynamicChargeAt state).stack.push
      (InteractionConcreteResources.resourceValue kind
        (afterDynamicChargeAt state)))

def openResourceNextAt (_kind : ResourceQuery) (value : Word)
    (state : EVMState) : EVMState :=
  state.replaceStackAndIncrPC (state.stack.push value)

theorem resourceNext_openStateRel
    (kind : ResourceQuery) {gasful openState : EVMState}
    (hRel : OpenStateRel gasful openState) :
    OpenStateRel (gasfulResourceNext kind gasful)
      (openResourceNextAt kind
        (InteractionConcreteResources.resourceValue kind
          (afterDynamicChargeAt gasful)) openState) := by
  apply OpenStateRel.replaceStackAndIncrPC
    (afterEVMInstructionChargeAt_openStateRel_left hRel)
  have hStack :
      (afterEVMInstructionChargeAt gasful).stack = openState.stack := by
    simpa [afterEVMInstructionChargeAt, afterMemoryChargeAt, chargeGas] using
      hRel.stack_eq
  rw [hStack]

theorem raw_resource_observation_executes_at
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (kind : ResourceQuery) (value : Word)
    (hDecode : Compact.decodeAt bytes pc (.prim (resourcePrimOp kind)))
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult bytes 1 state)
      [InteractionConcreteResources.resourceExchange kind value]
      (.ok (.running (openResourceNextAt kind value state))) := by
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim (resourcePrimOp kind)) trivial hDecode hPc]
  cases kind <;>
    simp [resourcePrimOp, Compact.Instr.openStepResult,
      Compact.Instr.openStep,
      Assembly.InteractionSemantics.Target.openStepInstr,
      Assembly.Target.stepInstrWith,
      Assembly.InteractionSemantics.PrimOp.openStep,
      Assembly.InteractionSemantics.PrimOp.resourceStep,
      Assembly.PrimOp.toEVM,
      Simulation.ExternalKind.ofEVMOperation?,
      Assembly.PrimOp.haltKind?, Compact.Instr.haltKind?,
      openResourceNextAt, Simulation.Interaction.bind] <;>
    exact Interaction.Executes.request _ (Interaction.Executes.done _)

@[simp] theorem resourceResult_eq_running
    (kind : ResourceQuery) (state : EVMState) :
    InteractionConcreteResources.resourceResult kind
        (afterDynamicChargeAt state) =
      .running (openResourceNext kind state) := by
  rfl

@[simp] theorem afterMemoryChargeAt_execLength (state : EVMState) :
    (afterMemoryChargeAt state).execLength = state.execLength := rfl

theorem evmyul_step_gas
    (state : EVMState) (arg : Option (Word × Nat)) :
    EvmYul.step (τ := .EVM) EvmYul.Operation.GAS arg state =
      .ok
        (state.replaceStackAndIncrPC
          (state.stack.push (EvmYul.MachineState.gas state.toMachineState))) := by
  rfl

theorem evmyul_step_msize
    (state : EVMState) (arg : Option (Word × Nat)) :
    EvmYul.step (τ := .EVM) EvmYul.Operation.MSIZE arg state =
      .ok
        (state.replaceStackAndIncrPC
          (state.stack.push
            (EvmYul.MachineState.msize state.toMachineState))) := by
  rfl

theorem evm_step_resource_eq
    (kind : ResourceQuery) (fuel : Nat) (state : EVMState)
    (arg : Option (Word × Nat)) :
    EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
        (some ((resourcePrimOp kind).toEVM, arg))
        (afterMemoryChargeAt state) =
      .ok (gasfulResourceNext kind state) := by
  cases kind <;>
    simp [EvmYul.EVM.step, resourcePrimOp, gasfulResourceNext,
      afterEVMInstructionChargeAt, afterDynamicChargeAt, chargeGas,
      PrimOp.toEVM, evmyul_step_gas, evmyul_step_msize,
      InteractionConcreteResources.resourceValue,
      EvmYul.MachineState.gas, EvmYul.MachineState.msize]

theorem gasfulResourceNext_sameData
    (kind : ResourceQuery) (state : EVMState) :
    SameData (gasfulResourceNext kind state)
      (openResourceNext kind state) := by
  cases kind <;> cases state <;> rfl

theorem gasfulResourceNext_pc
    (kind : ResourceQuery) (state : EVMState) :
    (gasfulResourceNext kind state).pc = (openResourceNext kind state).pc := by
  cases kind <;> cases state <;> rfl

structure XGasChecksPass (state : EVMState) : Prop where
  memoryGas :
    ¬ state.gasAvailable.toNat < memoryExpansionCostAt state
  dynamicGas :
    ¬ (afterMemoryChargeAt state).gasAvailable.toNat <
      dynamicGasCostAt state

theorem XGasChecksPass.memoryGas_raw {state : EVMState}
    (hGas : XGasChecksPass state) :
    ¬ state.gasAvailable.toNat <
      EvmYul.EVM.memoryExpansionCost state
        ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
          (EvmYul.Operation.STOP, none)).1 := by
  simpa [decodedOperationAt, memoryExpansionCostAt] using hGas.memoryGas

theorem XGasChecksPass.dynamicGas_raw {state : EVMState}
    (hGas : XGasChecksPass state) :
    ¬ (state.gasAvailable -
        EvmYul.UInt256.ofNat
          (EvmYul.EVM.memoryExpansionCost state
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1)).toNat <
      EvmYul.EVM.C'
        { state with
          gasAvailable :=
            state.gasAvailable -
              EvmYul.UInt256.ofNat
                (EvmYul.EVM.memoryExpansionCost state
                  ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
                    (EvmYul.Operation.STOP, none)).1) }
        ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
          (EvmYul.Operation.STOP, none)).1 := by
  simpa [decodedOperationAt, memoryExpansionCostAt, afterMemoryChargeAt,
    dynamicGasCostAt, chargeGas] using hGas.dynamicGas

structure XOpcodeStackChecksPass (state : EVMState) : Prop where
  gas : XGasChecksPass state
  opcodeValid :
    EvmYul.EVM.δ (decodedOperationAt state) ≠ none
  stackEnough :
    ¬ state.stack.length <
      (EvmYul.EVM.δ (decodedOperationAt state)).getD 0

theorem XOpcodeStackChecksPass.opcodeValid_raw {state : EVMState}
    (hPrefix : XOpcodeStackChecksPass state) :
    EvmYul.EVM.δ
      ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
        (EvmYul.Operation.STOP, none)).1 ≠ none := by
  simpa [decodedOperationAt] using hPrefix.opcodeValid

theorem XOpcodeStackChecksPass.stackEnough_raw {state : EVMState}
    (hPrefix : XOpcodeStackChecksPass state) :
    ¬ state.stack.length <
      (EvmYul.EVM.δ
        ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
          (EvmYul.Operation.STOP, none)).1).getD 0 := by
  simpa [decodedOperationAt] using hPrefix.stackEnough

/-- `EVM.X` raises out-of-gas before the instruction dynamic charge when the
actual memory-expansion charge cannot be paid. -/
theorem x_outOfGas_before_memory_charge
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    (hGas : state.gasAvailable.toNat < memoryExpansionCostAt state) :
    EvmYul.EVM.X (fuel + 1) validJumps state =
      .error EvmYul.EVM.ExecutionException.OutOfGass := by
  have hGas' :
      state.gasAvailable.toNat <
        EvmYul.EVM.memoryExpansionCost state
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)).1 := by
    simpa [decodedOperationAt, memoryExpansionCostAt] using hGas
  simp [EvmYul.EVM.X, hGas']

/-- `EVM.X` raises out-of-gas before executing the instruction when the
post-memory-charge frame cannot pay the dynamic instruction charge. -/
theorem x_outOfGas_before_dynamic_charge
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    (hMemoryGas :
      ¬ state.gasAvailable.toNat < memoryExpansionCostAt state)
    (hDynamicGas :
      (afterMemoryChargeAt state).gasAvailable.toNat <
        dynamicGasCostAt state) :
    EvmYul.EVM.X (fuel + 1) validJumps state =
      .error EvmYul.EVM.ExecutionException.OutOfGass := by
  have hMemoryGas' :
      ¬ state.gasAvailable.toNat <
        EvmYul.EVM.memoryExpansionCost state
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)).1 := by
    simpa [decodedOperationAt, memoryExpansionCostAt] using hMemoryGas
  have hDynamicGas' :
      (state.gasAvailable -
          EvmYul.UInt256.ofNat
            (EvmYul.EVM.memoryExpansionCost state
              ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
                (EvmYul.Operation.STOP, none)).1)).toNat <
        EvmYul.EVM.C'
          { state with
            gasAvailable :=
              state.gasAvailable -
                EvmYul.UInt256.ofNat
                  (EvmYul.EVM.memoryExpansionCost state
                    ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
                      (EvmYul.Operation.STOP, none)).1) }
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)).1 := by
    simpa [decodedOperationAt, memoryExpansionCostAt, afterMemoryChargeAt,
      dynamicGasCostAt, chargeGas] using hDynamicGas
  simp [EvmYul.EVM.X, hMemoryGas', hDynamicGas']

theorem x_invalid_instruction_after_gas_checks
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    (hGas : XGasChecksPass state)
    (hInvalid : EvmYul.EVM.δ (decodedOperationAt state) = none) :
    EvmYul.EVM.X (fuel + 1) validJumps state =
      .error EvmYul.EVM.ExecutionException.InvalidInstruction := by
  have hInvalid' :
      EvmYul.EVM.δ
        ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
          (EvmYul.Operation.STOP, none)).1 = none := by
    simpa [decodedOperationAt] using hInvalid
  simp [EvmYul.EVM.X, hGas.memoryGas_raw, hGas.dynamicGas_raw, hInvalid']

theorem x_stack_underflow_after_gas_opcode_check
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    (hGas : XGasChecksPass state)
    (hOpcodeValid : EvmYul.EVM.δ (decodedOperationAt state) ≠ none)
    (hStack :
      state.stack.length <
        (EvmYul.EVM.δ (decodedOperationAt state)).getD 0) :
    EvmYul.EVM.X (fuel + 1) validJumps state =
      .error EvmYul.EVM.ExecutionException.StackUnderflow := by
  have hOpcodeValid' :
      EvmYul.EVM.δ
        ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
          (EvmYul.Operation.STOP, none)).1 ≠ none := by
    simpa [decodedOperationAt] using hOpcodeValid
  have hStack' :
      state.stack.length <
        (EvmYul.EVM.δ
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)).1).getD 0 := by
    simpa [decodedOperationAt] using hStack
  simp [EvmYul.EVM.X, hGas.memoryGas_raw, hGas.dynamicGas_raw,
    hOpcodeValid', hStack']

theorem x_bad_jump_destination_after_stack_check
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    (hPrefix : XOpcodeStackChecksPass state)
    (hBadJump :
      decodedOperationAt state = EvmYul.Operation.JUMP ∧
        EvmYul.EVM.X.notIn state.stack[0]? validJumps = true) :
    EvmYul.EVM.X (fuel + 1) validJumps state =
      .error EvmYul.EVM.ExecutionException.BadJumpDestination := by
  have hBadJump' :
      ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
        (EvmYul.Operation.STOP, none)).1 = EvmYul.Operation.JUMP ∧
        EvmYul.EVM.X.notIn state.stack[0]? validJumps = true := by
    simpa [decodedOperationAt] using hBadJump
  have hMemoryGas' :
      ¬ state.gasAvailable.toNat <
        EvmYul.EVM.memoryExpansionCost state EvmYul.Operation.JUMP := by
    simpa [hBadJump'.1] using hPrefix.gas.memoryGas_raw
  have hDynamicGas' :
      ¬ (state.gasAvailable -
          EvmYul.UInt256.ofNat
            (EvmYul.EVM.memoryExpansionCost state EvmYul.Operation.JUMP)).toNat <
        EvmYul.EVM.C'
          { state with
            gasAvailable :=
              state.gasAvailable -
                EvmYul.UInt256.ofNat
                  (EvmYul.EVM.memoryExpansionCost state
                    EvmYul.Operation.JUMP) }
          EvmYul.Operation.JUMP := by
    simpa [hBadJump'.1] using hPrefix.gas.dynamicGas_raw
  have hOpcodeValid' :
      EvmYul.EVM.δ EvmYul.Operation.JUMP ≠ none := by
    simpa [hBadJump'.1] using hPrefix.opcodeValid_raw
  have hStackEnough' :
      ¬ state.stack.length <
        (EvmYul.EVM.δ EvmYul.Operation.JUMP).getD 0 := by
    simpa [hBadJump'.1] using hPrefix.stackEnough_raw
  simp [EvmYul.EVM.X, hBadJump'.1, hBadJump'.2, hMemoryGas',
    hDynamicGas', hOpcodeValid', hStackEnough']

theorem x_bad_jumpi_destination_after_stack_check
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    (hPrefix : XOpcodeStackChecksPass state)
    (hBadJumpi :
      decodedOperationAt state = EvmYul.Operation.JUMPI ∧
        state.stack[1]? ≠ some (EvmYul.UInt256.ofNat 0) ∧
        EvmYul.EVM.X.notIn state.stack[0]? validJumps = true) :
    EvmYul.EVM.X (fuel + 1) validJumps state =
      .error EvmYul.EVM.ExecutionException.BadJumpDestination := by
  have hBadJumpi' :
      ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
        (EvmYul.Operation.STOP, none)).1 = EvmYul.Operation.JUMPI ∧
        state.stack[1]? ≠ some (EvmYul.UInt256.ofNat 0) ∧
        EvmYul.EVM.X.notIn state.stack[0]? validJumps = true := by
    simpa [decodedOperationAt] using hBadJumpi
  have hMemoryGas' :
      ¬ state.gasAvailable.toNat <
        EvmYul.EVM.memoryExpansionCost state EvmYul.Operation.JUMPI := by
    simpa [hBadJumpi'.1] using hPrefix.gas.memoryGas_raw
  have hDynamicGas' :
      ¬ (state.gasAvailable -
          EvmYul.UInt256.ofNat
            (EvmYul.EVM.memoryExpansionCost state EvmYul.Operation.JUMPI)).toNat <
        EvmYul.EVM.C'
          { state with
            gasAvailable :=
              state.gasAvailable -
                EvmYul.UInt256.ofNat
                  (EvmYul.EVM.memoryExpansionCost state
                    EvmYul.Operation.JUMPI) }
          EvmYul.Operation.JUMPI := by
    simpa [hBadJumpi'.1] using hPrefix.gas.dynamicGas_raw
  have hOpcodeValid' :
      EvmYul.EVM.δ EvmYul.Operation.JUMPI ≠ none := by
    simpa [hBadJumpi'.1] using hPrefix.opcodeValid_raw
  have hStackEnough' :
      ¬ state.stack.length <
        (EvmYul.EVM.δ EvmYul.Operation.JUMPI).getD 0 := by
    simpa [hBadJumpi'.1] using hPrefix.stackEnough_raw
  have hCondNonzero' :
      ¬ state.stack[1]? = some ({ val := 0 } : Word) := by
    simpa using hBadJumpi'.2.1
  simp [EvmYul.EVM.X, hBadJumpi'.1, hBadJumpi'.2.1,
    hBadJumpi'.2.2, hCondNonzero', hMemoryGas', hDynamicGas',
    hOpcodeValid', hStackEnough']

def badJumpAt (validJumps : Array Word) (state : EVMState) : Prop :=
  decodedOperationAt state = EvmYul.Operation.JUMP ∧
    EvmYul.EVM.X.notIn state.stack[0]? validJumps = true

def badJumpiAt (validJumps : Array Word) (state : EVMState) : Prop :=
  decodedOperationAt state = EvmYul.Operation.JUMPI ∧
    state.stack[1]? ≠ some (EvmYul.UInt256.ofNat 0) ∧
    EvmYul.EVM.X.notIn state.stack[0]? validJumps = true

def invalidReturnDataCopyAt (state : EVMState) : Prop :=
  decodedOperationAt state = EvmYul.Operation.RETURNDATACOPY ∧
    state.returnData.size <
      (state.stack[1]?.getD (EvmYul.UInt256.ofNat 0)).toNat +
        (state.stack[2]?.getD (EvmYul.UInt256.ofNat 0)).toNat

def stackOverflowAt (state : EVMState) : Prop :=
  1024 <
    state.stack.length -
      (EvmYul.EVM.δ (decodedOperationAt state)).getD 0 +
      (EvmYul.EVM.α (decodedOperationAt state)).getD 0

def staticModeViolationAt (state : EVMState) : Prop :=
  state.executionEnv.perm = false ∧
    (decodedOperationAt state = EvmYul.Operation.CREATE ∨
      decodedOperationAt state = EvmYul.Operation.CREATE2 ∨
      decodedOperationAt state = EvmYul.Operation.SSTORE ∨
      decodedOperationAt state = EvmYul.Operation.SELFDESTRUCT ∨
      decodedOperationAt state = EvmYul.Operation.LOG0 ∨
      decodedOperationAt state = EvmYul.Operation.LOG1 ∨
      decodedOperationAt state = EvmYul.Operation.LOG2 ∨
      decodedOperationAt state = EvmYul.Operation.LOG3 ∨
      decodedOperationAt state = EvmYul.Operation.LOG4 ∨
      decodedOperationAt state = EvmYul.Operation.TSTORE ∨
      decodedOperationAt state = EvmYul.Operation.CALL ∧
        state.stack[2]? ≠ some (EvmYul.UInt256.ofNat 0))

def sstoreStipendOutOfGasAt (state : EVMState) : Prop :=
  decodedOperationAt state = EvmYul.Operation.SSTORE ∧
    (afterMemoryChargeAt state).gasAvailable.toNat ≤
      GasConstants.Gcallstipend

structure XJumpChecksPass
    (validJumps : Array Word) (state : EVMState) : Prop where
  stack : XOpcodeStackChecksPass state
  notBadJump : ¬ badJumpAt validJumps state
  notBadJumpi : ¬ badJumpiAt validJumps state

structure XMemoryAccessChecksPass
    (validJumps : Array Word) (state : EVMState) : Prop where
  jumps : XJumpChecksPass validJumps state
  returnDataCopyOk : ¬ invalidReturnDataCopyAt state

structure XStackLimitChecksPass
    (validJumps : Array Word) (state : EVMState) : Prop where
  memoryAccess : XMemoryAccessChecksPass validJumps state
  stackLimitOk : ¬ stackOverflowAt state

structure XStaticChecksPass
    (validJumps : Array Word) (state : EVMState) : Prop where
  stackLimit : XStackLimitChecksPass validJumps state
  staticOk : ¬ staticModeViolationAt state

structure XSstoreStipendChecksPass
    (validJumps : Array Word) (state : EVMState) : Prop where
  static : XStaticChecksPass validJumps state
  sstoreStipendOk : ¬ sstoreStipendOutOfGasAt state

theorem x_invalid_returndatacopy_after_jump_checks
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    (hPrefix : XJumpChecksPass validJumps state)
    (hInvalid : invalidReturnDataCopyAt state) :
    EvmYul.EVM.X (fuel + 1) validJumps state =
      .error EvmYul.EVM.ExecutionException.InvalidMemoryAccess := by
  rcases hInvalid with ⟨hOp, hBounds⟩
  have hOp' :
      ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
        (EvmYul.Operation.STOP, none)).1 =
        EvmYul.Operation.RETURNDATACOPY := by
    simpa [decodedOperationAt] using hOp
  have hBounds' :
      state.returnData.size <
        (state.stack[1]?.getD ({ val := 0 } : Word)).toNat +
          (state.stack[2]?.getD ({ val := 0 } : Word)).toNat := by
    simpa using hBounds
  have hMemoryGas' :
      ¬ state.gasAvailable.toNat <
        EvmYul.EVM.memoryExpansionCost state
          EvmYul.Operation.RETURNDATACOPY := by
    simpa [hOp'] using hPrefix.stack.gas.memoryGas_raw
  have hDynamicGas' :
      ¬ (state.gasAvailable -
          EvmYul.UInt256.ofNat
            (EvmYul.EVM.memoryExpansionCost state
              EvmYul.Operation.RETURNDATACOPY)).toNat <
        EvmYul.EVM.C'
          { state with
            gasAvailable :=
              state.gasAvailable -
                EvmYul.UInt256.ofNat
                  (EvmYul.EVM.memoryExpansionCost state
                    EvmYul.Operation.RETURNDATACOPY) }
          EvmYul.Operation.RETURNDATACOPY := by
    simpa [hOp'] using hPrefix.stack.gas.dynamicGas_raw
  have hOpcodeValid' :
      EvmYul.EVM.δ EvmYul.Operation.RETURNDATACOPY ≠ none := by
    simpa [hOp'] using hPrefix.stack.opcodeValid_raw
  have hStackEnough' :
      ¬ state.stack.length <
        (EvmYul.EVM.δ EvmYul.Operation.RETURNDATACOPY).getD 0 := by
    simpa [hOp'] using hPrefix.stack.stackEnough_raw
  simp [EvmYul.EVM.X, hOp', hBounds', hMemoryGas', hDynamicGas',
    hOpcodeValid', hStackEnough']

theorem x_stack_overflow_after_memory_access_checks
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    (hPrefix : XMemoryAccessChecksPass validJumps state)
    (hOverflow : stackOverflowAt state) :
    EvmYul.EVM.X (fuel + 1) validJumps state =
      .error EvmYul.EVM.ExecutionException.StackOverflow := by
  have hNoBadJump' :
      ¬ (((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
          (EvmYul.Operation.STOP, none)).1 = EvmYul.Operation.JUMP ∧
        EvmYul.EVM.X.notIn state.stack[0]? validJumps = true) := by
    simpa [badJumpAt, decodedOperationAt] using
      hPrefix.jumps.notBadJump
  have hNoBadJumpi' :
      ¬ (((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
          (EvmYul.Operation.STOP, none)).1 = EvmYul.Operation.JUMPI ∧
        state.stack[1]? ≠ some (EvmYul.UInt256.ofNat 0) ∧
        EvmYul.EVM.X.notIn state.stack[0]? validJumps = true) := by
    simpa [badJumpiAt, decodedOperationAt] using
      hPrefix.jumps.notBadJumpi
  have hNoBadJumpiExact' :
      ¬ (((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
          (EvmYul.Operation.STOP, none)).1 = EvmYul.Operation.JUMPI ∧
        ¬ state.stack[1]? = some ({ val := 0 } : Word) ∧
        EvmYul.EVM.X.notIn state.stack[0]? validJumps = true) := by
    intro h
    exact hNoBadJumpi'
      ⟨h.1, by simpa using h.2.1, h.2.2⟩
  have hReturnDataOk' :
      ¬ (((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
          (EvmYul.Operation.STOP, none)).1 =
            EvmYul.Operation.RETURNDATACOPY ∧
        state.returnData.size <
          (state.stack[1]?.getD ({ val := 0 } : Word)).toNat +
            (state.stack[2]?.getD ({ val := 0 } : Word)).toNat) := by
    simpa [invalidReturnDataCopyAt, decodedOperationAt] using
      hPrefix.returnDataCopyOk
  have hOverflow' :
      1024 <
        state.stack.length -
          (EvmYul.EVM.δ
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1).getD 0 +
          (EvmYul.EVM.α
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1).getD 0 := by
    simpa [stackOverflowAt, decodedOperationAt] using hOverflow
  simp [EvmYul.EVM.X, hPrefix.jumps.stack.gas.memoryGas_raw,
    hPrefix.jumps.stack.gas.dynamicGas_raw,
    hPrefix.jumps.stack.opcodeValid_raw,
    hPrefix.jumps.stack.stackEnough_raw, hNoBadJump', hNoBadJumpiExact',
    hReturnDataOk', hOverflow']

theorem x_static_mode_violation_after_stack_limit_checks
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    (hPrefix : XStackLimitChecksPass validJumps state)
    (hStatic : staticModeViolationAt state) :
    EvmYul.EVM.X (fuel + 1) validJumps state =
      .error EvmYul.EVM.ExecutionException.StaticModeViolation := by
  have hNoBadJump' :
      ¬ (((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
          (EvmYul.Operation.STOP, none)).1 = EvmYul.Operation.JUMP ∧
        EvmYul.EVM.X.notIn state.stack[0]? validJumps = true) := by
    simpa [badJumpAt, decodedOperationAt] using
      hPrefix.memoryAccess.jumps.notBadJump
  have hNoBadJumpi' :
      ¬ (((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
          (EvmYul.Operation.STOP, none)).1 = EvmYul.Operation.JUMPI ∧
        state.stack[1]? ≠ some (EvmYul.UInt256.ofNat 0) ∧
        EvmYul.EVM.X.notIn state.stack[0]? validJumps = true) := by
    simpa [badJumpiAt, decodedOperationAt] using
      hPrefix.memoryAccess.jumps.notBadJumpi
  have hNoBadJumpiExact' :
      ¬ (((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
          (EvmYul.Operation.STOP, none)).1 = EvmYul.Operation.JUMPI ∧
        ¬ state.stack[1]? = some ({ val := 0 } : Word) ∧
        EvmYul.EVM.X.notIn state.stack[0]? validJumps = true) := by
    intro h
    exact hNoBadJumpi'
      ⟨h.1, by simpa using h.2.1, h.2.2⟩
  have hReturnDataOk' :
      ¬ (((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
          (EvmYul.Operation.STOP, none)).1 =
            EvmYul.Operation.RETURNDATACOPY ∧
        state.returnData.size <
          (state.stack[1]?.getD ({ val := 0 } : Word)).toNat +
            (state.stack[2]?.getD ({ val := 0 } : Word)).toNat) := by
    simpa [invalidReturnDataCopyAt, decodedOperationAt] using
      hPrefix.memoryAccess.returnDataCopyOk
  have hStackLimitOk' :
      ¬ 1024 <
        state.stack.length -
          (EvmYul.EVM.δ
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1).getD 0 +
          (EvmYul.EVM.α
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1).getD 0 := by
    simpa [stackOverflowAt, decodedOperationAt] using
      hPrefix.stackLimitOk
  have hStatic' :
      state.executionEnv.perm = false ∧
        (((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1 =
            EvmYul.Operation.CREATE ∨
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1 =
            EvmYul.Operation.CREATE2 ∨
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1 =
            EvmYul.Operation.SSTORE ∨
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1 =
            EvmYul.Operation.SELFDESTRUCT ∨
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1 =
            EvmYul.Operation.LOG0 ∨
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1 =
            EvmYul.Operation.LOG1 ∨
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1 =
            EvmYul.Operation.LOG2 ∨
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1 =
            EvmYul.Operation.LOG3 ∨
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1 =
            EvmYul.Operation.LOG4 ∨
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1 =
            EvmYul.Operation.TSTORE ∨
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1 =
            EvmYul.Operation.CALL ∧
          state.stack[2]? ≠ some (EvmYul.UInt256.ofNat 0)) := by
    simpa [staticModeViolationAt, decodedOperationAt] using hStatic
  have hStaticCond' :
      (((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)).1 =
          EvmYul.Operation.CREATE ∨
        ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)).1 =
          EvmYul.Operation.CREATE2 ∨
        ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)).1 =
          EvmYul.Operation.SSTORE ∨
        ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)).1 =
          EvmYul.Operation.SELFDESTRUCT ∨
        ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)).1 =
          EvmYul.Operation.LOG0 ∨
        ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)).1 =
          EvmYul.Operation.LOG1 ∨
        ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)).1 =
          EvmYul.Operation.LOG2 ∨
        ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)).1 =
          EvmYul.Operation.LOG3 ∨
        ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)).1 =
          EvmYul.Operation.LOG4 ∨
        ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)).1 =
          EvmYul.Operation.TSTORE) ∨
        ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)).1 =
          EvmYul.Operation.CALL ∧
        ¬ state.stack[2]? = some ({ val := 0 } : Word) := by
    simpa [or_assoc] using hStatic'.2
  simp [EvmYul.EVM.X, hPrefix.memoryAccess.jumps.stack.gas.memoryGas_raw,
    hPrefix.memoryAccess.jumps.stack.gas.dynamicGas_raw,
    hPrefix.memoryAccess.jumps.stack.opcodeValid_raw,
    hPrefix.memoryAccess.jumps.stack.stackEnough_raw, hNoBadJump',
    hNoBadJumpiExact', hReturnDataOk', hStackLimitOk', hStatic'.1,
    hStaticCond']

theorem x_sstore_stipend_outOfGas_after_static_check
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    (hPrefix : XStaticChecksPass validJumps state)
    (hSstore : sstoreStipendOutOfGasAt state) :
    EvmYul.EVM.X (fuel + 1) validJumps state =
      .error EvmYul.EVM.ExecutionException.OutOfGass := by
  rcases hSstore with ⟨hOp, hStipend⟩
  have hOp' :
      ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
        (EvmYul.Operation.STOP, none)).1 = EvmYul.Operation.SSTORE := by
    simpa [decodedOperationAt] using hOp
  have hNoStatic : ¬ state.executionEnv.perm = false := by
    intro hPerm
    exact hPrefix.staticOk
      ⟨hPerm, by simp [staticModeViolationAt, hOp]⟩
  have hStackLimitOk' :
      ¬ 1024 <
        state.stack.length -
          (EvmYul.EVM.δ EvmYul.Operation.SSTORE).getD 0 +
          (EvmYul.EVM.α EvmYul.Operation.SSTORE).getD 0 := by
    simpa [stackOverflowAt, decodedOperationAt, hOp'] using
      hPrefix.stackLimit.stackLimitOk
  have hStipend' :
      (state.gasAvailable -
          EvmYul.UInt256.ofNat
            (EvmYul.EVM.memoryExpansionCost state
              EvmYul.Operation.SSTORE)).toNat ≤
        GasConstants.Gcallstipend := by
    simpa [afterMemoryChargeAt, memoryExpansionCostAt,
      decodedOperationAt, chargeGas, hOp'] using hStipend
  have hMemoryGas' :
      ¬ state.gasAvailable.toNat <
        EvmYul.EVM.memoryExpansionCost state EvmYul.Operation.SSTORE := by
    simpa [hOp'] using
      hPrefix.stackLimit.memoryAccess.jumps.stack.gas.memoryGas_raw
  have hDynamicGas' :
      ¬ (state.gasAvailable -
          EvmYul.UInt256.ofNat
            (EvmYul.EVM.memoryExpansionCost state
              EvmYul.Operation.SSTORE)).toNat <
        EvmYul.EVM.C'
          { state with
            gasAvailable :=
              state.gasAvailable -
                EvmYul.UInt256.ofNat
                  (EvmYul.EVM.memoryExpansionCost state
                    EvmYul.Operation.SSTORE) }
          EvmYul.Operation.SSTORE := by
    simpa [hOp'] using
      hPrefix.stackLimit.memoryAccess.jumps.stack.gas.dynamicGas_raw
  have hOpcodeValid' :
      EvmYul.EVM.δ EvmYul.Operation.SSTORE ≠ none := by
    simpa [hOp'] using
      hPrefix.stackLimit.memoryAccess.jumps.stack.opcodeValid_raw
  have hStackEnough' :
      ¬ state.stack.length <
        (EvmYul.EVM.δ EvmYul.Operation.SSTORE).getD 0 := by
    simpa [hOp'] using
      hPrefix.stackLimit.memoryAccess.jumps.stack.stackEnough_raw
  simp [EvmYul.EVM.X, hOp', hNoStatic, hStackLimitOk', hStipend',
    hMemoryGas', hDynamicGas', hOpcodeValid', hStackEnough']

theorem x_create_initcode_outOfGas_after_sstore_check
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hCreate :
      decodedOperationAt state = EvmYul.Operation.CREATE ∨
        decodedOperationAt state = EvmYul.Operation.CREATE2)
    (hTooLarge :
      (EvmYul.UInt256.ofNat 49152) <
        state.stack[2]?.getD (EvmYul.UInt256.ofNat 0)) :
    EvmYul.EVM.X (fuel + 1) validJumps state =
      .error EvmYul.EVM.ExecutionException.OutOfGass := by
  rcases hCreate with hCreate | hCreate
  · have hCreate' :
        ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
          (EvmYul.Operation.STOP, none)).1 = EvmYul.Operation.CREATE := by
      simpa [decodedOperationAt] using hCreate
    have hNoStatic : ¬ state.executionEnv.perm = false := by
      intro hPerm
      exact hPrefix.static.staticOk
        ⟨hPerm, by simp [staticModeViolationAt, hCreate]⟩
    have hStackLimitOk' :
        ¬ 1024 <
          state.stack.length -
            (EvmYul.EVM.δ EvmYul.Operation.CREATE).getD 0 +
            (EvmYul.EVM.α EvmYul.Operation.CREATE).getD 0 := by
      simpa [stackOverflowAt, decodedOperationAt, hCreate'] using
        hPrefix.static.stackLimit.stackLimitOk
    have hTooLarge' :
        ({ val := 49152 } : Word) <
          state.stack[2]?.getD ({ val := 0 } : Word) := by
      simpa using hTooLarge
    have hMemoryGas' :
        ¬ state.gasAvailable.toNat <
          EvmYul.EVM.memoryExpansionCost state
            EvmYul.Operation.CREATE := by
      simpa [hCreate'] using
        hPrefix.static.stackLimit.memoryAccess.jumps.stack.gas.memoryGas_raw
    have hDynamicGas' :
        ¬ (state.gasAvailable -
            EvmYul.UInt256.ofNat
              (EvmYul.EVM.memoryExpansionCost state
                EvmYul.Operation.CREATE)).toNat <
          EvmYul.EVM.C'
            { state with
              gasAvailable :=
                state.gasAvailable -
                  EvmYul.UInt256.ofNat
                    (EvmYul.EVM.memoryExpansionCost state
                      EvmYul.Operation.CREATE) }
            EvmYul.Operation.CREATE := by
      simpa [hCreate'] using
        hPrefix.static.stackLimit.memoryAccess.jumps.stack.gas.dynamicGas_raw
    have hOpcodeValid' :
        EvmYul.EVM.δ EvmYul.Operation.CREATE ≠ none := by
      simpa [hCreate'] using
        hPrefix.static.stackLimit.memoryAccess.jumps.stack.opcodeValid_raw
    have hStackEnough' :
        ¬ state.stack.length <
          (EvmYul.EVM.δ EvmYul.Operation.CREATE).getD 0 := by
      simpa [hCreate'] using
        hPrefix.static.stackLimit.memoryAccess.jumps.stack.stackEnough_raw
    simp [EvmYul.EVM.X, EvmYul.Operation.isCreate, hCreate',
      hNoStatic, hStackLimitOk',
      hTooLarge', hMemoryGas', hDynamicGas', hOpcodeValid', hStackEnough']
  · have hCreate' :
        ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
          (EvmYul.Operation.STOP, none)).1 = EvmYul.Operation.CREATE2 := by
      simpa [decodedOperationAt] using hCreate
    have hNoStatic : ¬ state.executionEnv.perm = false := by
      intro hPerm
      exact hPrefix.static.staticOk
        ⟨hPerm, by simp [staticModeViolationAt, hCreate]⟩
    have hStackLimitOk' :
        ¬ 1024 <
          state.stack.length -
            (EvmYul.EVM.δ EvmYul.Operation.CREATE2).getD 0 +
            (EvmYul.EVM.α EvmYul.Operation.CREATE2).getD 0 := by
      simpa [stackOverflowAt, decodedOperationAt, hCreate'] using
        hPrefix.static.stackLimit.stackLimitOk
    have hTooLarge' :
        ({ val := 49152 } : Word) <
          state.stack[2]?.getD ({ val := 0 } : Word) := by
      simpa using hTooLarge
    have hMemoryGas' :
        ¬ state.gasAvailable.toNat <
          EvmYul.EVM.memoryExpansionCost state
            EvmYul.Operation.CREATE2 := by
      simpa [hCreate'] using
        hPrefix.static.stackLimit.memoryAccess.jumps.stack.gas.memoryGas_raw
    have hDynamicGas' :
        ¬ (state.gasAvailable -
            EvmYul.UInt256.ofNat
              (EvmYul.EVM.memoryExpansionCost state
                EvmYul.Operation.CREATE2)).toNat <
          EvmYul.EVM.C'
            { state with
              gasAvailable :=
                state.gasAvailable -
                  EvmYul.UInt256.ofNat
                    (EvmYul.EVM.memoryExpansionCost state
                      EvmYul.Operation.CREATE2) }
            EvmYul.Operation.CREATE2 := by
      simpa [hCreate'] using
        hPrefix.static.stackLimit.memoryAccess.jumps.stack.gas.dynamicGas_raw
    have hOpcodeValid' :
        EvmYul.EVM.δ EvmYul.Operation.CREATE2 ≠ none := by
      simpa [hCreate'] using
        hPrefix.static.stackLimit.memoryAccess.jumps.stack.opcodeValid_raw
    have hStackEnough' :
        ¬ state.stack.length <
          (EvmYul.EVM.δ EvmYul.Operation.CREATE2).getD 0 := by
      simpa [hCreate'] using
        hPrefix.static.stackLimit.memoryAccess.jumps.stack.stackEnough_raw
    simp [EvmYul.EVM.X, EvmYul.Operation.isCreate, hCreate',
      hNoStatic, hStackLimitOk',
      hTooLarge', hMemoryGas', hDynamicGas', hOpcodeValid', hStackEnough']

def haltOutputAt (state : EVMState)
    (op : EvmYul.Operation .EVM) : Option ByteArray :=
  if op ∈ [EvmYul.Operation.RETURN, EvmYul.Operation.REVERT] then
    some state.toMachineState.H_return
  else if op ∈ [EvmYul.Operation.STOP, EvmYul.Operation.SELFDESTRUCT] then
    some ByteArray.empty
  else
    none

def xPostStepResult (fuel : Nat) (validJumps : Array Word)
    (op : EvmYul.Operation .EVM) (state : EVMState) :
    Except EVMException (EvmYul.EVM.ExecutionResult EVMState) :=
  match haltOutputAt state op with
  | none => EvmYul.EVM.X fuel validJumps state
  | some output =>
      if op == EvmYul.Operation.REVERT then
        .ok (.revert state.gasAvailable output)
      else
        .ok (.success state output)

def xPostStepExceptResult (fuel : Nat) (validJumps : Array Word)
    (op : EvmYul.Operation .EVM) :
    Except EVMException EVMState →
      Except EVMException (EvmYul.EVM.ExecutionResult EVMState)
  | .error err => .error err
  | .ok state => xPostStepResult fuel validJumps op state

/-- Once every checked exceptional branch has been ruled out, `EVM.X` delegates
to the actual gasful `EVM.step` result and then applies the frame-level
continuation/halt rule. For CALL/CREATE this preserves the existing strategy
boundary: the child-frame behavior is exactly whatever the concrete `EVM.step`
returned to the parent. -/
theorem x_after_prechecks_of_step_result
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    {stepResult : Except EVMException EVMState}
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt state) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          state.stack[2]?.getD (EvmYul.UInt256.ofNat 0)))
    (hStep :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = stepResult) :
    EvmYul.EVM.X (fuel + 1) validJumps state =
      xPostStepExceptResult fuel validJumps
        (decodedOperationAt state) stepResult := by
  have hNoBadJump' :
      ¬ (((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
          (EvmYul.Operation.STOP, none)).1 = EvmYul.Operation.JUMP ∧
        EvmYul.EVM.X.notIn state.stack[0]? validJumps = true) := by
    simpa [badJumpAt, decodedOperationAt] using
      hPrefix.static.stackLimit.memoryAccess.jumps.notBadJump
  have hNoBadJumpi' :
      ¬ (((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
          (EvmYul.Operation.STOP, none)).1 = EvmYul.Operation.JUMPI ∧
        state.stack[1]? ≠ some (EvmYul.UInt256.ofNat 0) ∧
        EvmYul.EVM.X.notIn state.stack[0]? validJumps = true) := by
    simpa [badJumpiAt, decodedOperationAt] using
      hPrefix.static.stackLimit.memoryAccess.jumps.notBadJumpi
  have hNoBadJumpiExact' :
      ¬ (((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
          (EvmYul.Operation.STOP, none)).1 = EvmYul.Operation.JUMPI ∧
        ¬ state.stack[1]? = some ({ val := 0 } : Word) ∧
        EvmYul.EVM.X.notIn state.stack[0]? validJumps = true) := by
    intro h
    exact hNoBadJumpi'
      ⟨h.1, by simpa using h.2.1, h.2.2⟩
  have hReturnDataOk' :
      ¬ (((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
          (EvmYul.Operation.STOP, none)).1 =
            EvmYul.Operation.RETURNDATACOPY ∧
        state.returnData.size <
          (state.stack[1]?.getD ({ val := 0 } : Word)).toNat +
            (state.stack[2]?.getD ({ val := 0 } : Word)).toNat) := by
    simpa [invalidReturnDataCopyAt, decodedOperationAt] using
      hPrefix.static.stackLimit.memoryAccess.returnDataCopyOk
  have hStackLimitOk' :
      ¬ 1024 <
        state.stack.length -
          (EvmYul.EVM.δ
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1).getD 0 +
          (EvmYul.EVM.α
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1).getD 0 := by
    simpa [stackOverflowAt, decodedOperationAt] using
      hPrefix.static.stackLimit.stackLimitOk
  have hStaticOk' :
      ¬ (state.executionEnv.perm = false ∧
        (((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1 =
            EvmYul.Operation.CREATE ∨
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1 =
            EvmYul.Operation.CREATE2 ∨
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1 =
            EvmYul.Operation.SSTORE ∨
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1 =
            EvmYul.Operation.SELFDESTRUCT ∨
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1 =
            EvmYul.Operation.LOG0 ∨
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1 =
            EvmYul.Operation.LOG1 ∨
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1 =
            EvmYul.Operation.LOG2 ∨
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1 =
            EvmYul.Operation.LOG3 ∨
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1 =
            EvmYul.Operation.LOG4 ∨
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1 =
            EvmYul.Operation.TSTORE ∨
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1 =
            EvmYul.Operation.CALL ∧
          state.stack[2]? ≠ some (EvmYul.UInt256.ofNat 0))) := by
    simpa [staticModeViolationAt, decodedOperationAt] using
      hPrefix.static.staticOk
  have hStaticOkExact' :
      ¬ (state.executionEnv.perm = false ∧
        ((((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
                (EvmYul.Operation.STOP, none)).1 =
              EvmYul.Operation.CREATE ∨
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
                (EvmYul.Operation.STOP, none)).1 =
              EvmYul.Operation.CREATE2 ∨
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
                (EvmYul.Operation.STOP, none)).1 =
              EvmYul.Operation.SSTORE ∨
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
                (EvmYul.Operation.STOP, none)).1 =
              EvmYul.Operation.SELFDESTRUCT ∨
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
                (EvmYul.Operation.STOP, none)).1 =
              EvmYul.Operation.LOG0 ∨
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
                (EvmYul.Operation.STOP, none)).1 =
              EvmYul.Operation.LOG1 ∨
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
                (EvmYul.Operation.STOP, none)).1 =
              EvmYul.Operation.LOG2 ∨
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
                (EvmYul.Operation.STOP, none)).1 =
              EvmYul.Operation.LOG3 ∨
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
                (EvmYul.Operation.STOP, none)).1 =
              EvmYul.Operation.LOG4 ∨
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
                (EvmYul.Operation.STOP, none)).1 =
              EvmYul.Operation.TSTORE) ∨
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1 =
            EvmYul.Operation.CALL ∧
          ¬ (state.stack[2]? = some ({ val := 0 } : Word)))) := by
    intro h
    exact hStaticOk'
      ⟨h.1, by simpa [or_assoc] using h.2⟩
  have hSstoreOk' :
      ¬ (((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
          (EvmYul.Operation.STOP, none)).1 = EvmYul.Operation.SSTORE ∧
        (state.gasAvailable -
            EvmYul.UInt256.ofNat
              (EvmYul.EVM.memoryExpansionCost state
                ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
                  (EvmYul.Operation.STOP, none)).1)).toNat ≤
          GasConstants.Gcallstipend) := by
    simpa [sstoreStipendOutOfGasAt, afterMemoryChargeAt,
      memoryExpansionCostAt, decodedOperationAt, chargeGas] using
      hPrefix.sstoreStipendOk
  have hCreateOk' :
      ¬ (EvmYul.Operation.isCreate
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1 = true ∧
          ({ val := 49152 } : Word) <
            state.stack[2]?.getD ({ val := 0 } : Word)) := by
    simpa [decodedOperationAt] using hCreateOk
  have hStep' :
      EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            { state with
              gasAvailable :=
                state.gasAvailable -
                  EvmYul.UInt256.ofNat
                    (EvmYul.EVM.memoryExpansionCost state
                      ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
                        (EvmYul.Operation.STOP, none)).1) }
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).1)
          (some
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)))
          { state with
            gasAvailable :=
              state.gasAvailable -
                EvmYul.UInt256.ofNat
                  (EvmYul.EVM.memoryExpansionCost state
                    ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
                      (EvmYul.Operation.STOP, none)).1) } =
        stepResult := by
    simpa [dynamicGasCostAt, afterMemoryChargeAt, memoryExpansionCostAt,
      decodedOperationAt, chargeGas] using hStep
  simp [EvmYul.EVM.X, hPrefix.static.stackLimit.memoryAccess.jumps.stack.gas.memoryGas_raw,
    hPrefix.static.stackLimit.memoryAccess.jumps.stack.gas.dynamicGas_raw,
    hPrefix.static.stackLimit.memoryAccess.jumps.stack.opcodeValid_raw,
    hPrefix.static.stackLimit.memoryAccess.jumps.stack.stackEnough_raw,
    hNoBadJump', hNoBadJumpiExact', hReturnDataOk', hStackLimitOk',
    hStaticOkExact', hSstoreOk', hCreateOk', hStep', xPostStepResult,
    xPostStepExceptResult, haltOutputAt, dynamicGasCostAt,
    afterMemoryChargeAt, memoryExpansionCostAt, decodedOperationAt, chargeGas]
  cases stepResult <;> rfl

theorem x_after_prechecks_of_step
    {fuel : Nat} {validJumps : Array Word} {state gasfulNext : EVMState}
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt state) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          state.stack[2]?.getD (EvmYul.UInt256.ofNat 0)))
    (hStep :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok gasfulNext) :
    EvmYul.EVM.X (fuel + 1) validJumps state =
      xPostStepResult fuel validJumps (decodedOperationAt state) gasfulNext := by
  simpa [xPostStepExceptResult] using
    (x_after_prechecks_of_step_result
      (fuel := fuel) (validJumps := validJumps) (state := state)
      (stepResult := .ok gasfulNext) hPrefix hCreateOk hStep)

theorem x_after_prechecks_of_step_error
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    {err : EVMException}
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt state) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          state.stack[2]?.getD (EvmYul.UInt256.ofNat 0)))
    (hStep :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .error err) :
    EvmYul.EVM.X (fuel + 1) validJumps state = .error err := by
  simpa [xPostStepExceptResult] using
    (x_after_prechecks_of_step_result
      (fuel := fuel) (validJumps := validJumps) (state := state)
      (stepResult := .error err) hPrefix hCreateOk hStep)

/-- `JUMPDEST` is the smallest successful charged step: after all gas and
exception prechecks pass, `EVM.X` recurses on the interpreter's charged
fallthrough state. -/
theorem x_jumpdest_continues_after_charges
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hJumpdest : decodedOperationAt state = EvmYul.Operation.JUMPDEST)
    {gasfulNext : EVMState}
    (hStep :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          (EvmYul.Operation.JUMPDEST,
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).2))
        (afterMemoryChargeAt state) = .ok gasfulNext) :
    EvmYul.EVM.X (fuel + 1) validJumps state =
      EvmYul.EVM.X fuel validJumps gasfulNext := by
  have hOp' :
      ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
        (EvmYul.Operation.STOP, none)).1 =
        EvmYul.Operation.JUMPDEST := by
    simpa [decodedOperationAt] using hJumpdest
  have hMemoryGas' :
      ¬ state.gasAvailable.toNat <
        EvmYul.EVM.memoryExpansionCost state
          EvmYul.Operation.JUMPDEST := by
    simpa [hOp'] using
      hPrefix.static.stackLimit.memoryAccess.jumps.stack.gas.memoryGas_raw
  have hDynamicGas' :
      ¬ (state.gasAvailable -
          EvmYul.UInt256.ofNat
            (EvmYul.EVM.memoryExpansionCost state
              EvmYul.Operation.JUMPDEST)).toNat <
        EvmYul.EVM.C'
          { state with
            gasAvailable :=
              state.gasAvailable -
                EvmYul.UInt256.ofNat
                  (EvmYul.EVM.memoryExpansionCost state
                    EvmYul.Operation.JUMPDEST) }
          EvmYul.Operation.JUMPDEST := by
    simpa [hOp'] using
      hPrefix.static.stackLimit.memoryAccess.jumps.stack.gas.dynamicGas_raw
  have hOpcodeValid' :
      EvmYul.EVM.δ EvmYul.Operation.JUMPDEST ≠ none := by
    simpa [hOp'] using
      hPrefix.static.stackLimit.memoryAccess.jumps.stack.opcodeValid_raw
  have hStackEnough' :
      ¬ state.stack.length <
        (EvmYul.EVM.δ EvmYul.Operation.JUMPDEST).getD 0 := by
    simpa [hOp'] using
      hPrefix.static.stackLimit.memoryAccess.jumps.stack.stackEnough_raw
  have hStackLimitOk' :
      ¬ 1024 <
        state.stack.length -
          (EvmYul.EVM.δ EvmYul.Operation.JUMPDEST).getD 0 +
          (EvmYul.EVM.α EvmYul.Operation.JUMPDEST).getD 0 := by
    simpa [stackOverflowAt, decodedOperationAt, hOp'] using
      hPrefix.static.stackLimit.stackLimitOk
  have hStep' :
      EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            { state with
              gasAvailable :=
                state.gasAvailable -
                  EvmYul.UInt256.ofNat
                    (EvmYul.EVM.memoryExpansionCost state
                      EvmYul.Operation.JUMPDEST) }
            EvmYul.Operation.JUMPDEST)
          (some
            (EvmYul.Operation.JUMPDEST,
              ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
                (EvmYul.Operation.STOP, none)).2))
          { state with
            gasAvailable :=
              state.gasAvailable -
                EvmYul.UInt256.ofNat
                  (EvmYul.EVM.memoryExpansionCost state
                    EvmYul.Operation.JUMPDEST) } =
        .ok gasfulNext := by
    simpa [dynamicGasCostAt, afterMemoryChargeAt, memoryExpansionCostAt,
      decodedOperationAt, hOp', chargeGas] using hStep
  simp [EvmYul.EVM.X, hOp', hMemoryGas', hDynamicGas',
    hOpcodeValid', hStackEnough', hStackLimitOk',
    hStep', EvmYul.Operation.isCreate,
    afterMemoryChargeAt, dynamicGasCostAt,
    memoryExpansionCostAt, decodedOperationAt, chargeGas]

def gasfulPcNext (state : EVMState) : EVMState :=
  let charged := afterEVMInstructionChargeAt state
  charged.replaceStackAndIncrPC (charged.stack.push charged.pc)

def openPcNext (state : EVMState) : EVMState :=
  let charged := afterDynamicChargeAt state
  charged.replaceStackAndIncrPC (charged.stack.push charged.pc)

theorem evmyul_step_pc
    (state : EVMState) (arg : Option (Word × Nat)) :
    EvmYul.step (τ := .EVM) .PC arg state =
      .ok (state.replaceStackAndIncrPC (state.stack.push state.pc)) := by
  rfl

theorem evm_step_pc_eq_next
    (fuel : Nat) (state : EVMState) (arg : Option (Word × Nat)) :
    EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
        (some (EvmYul.Operation.PC, arg)) (afterMemoryChargeAt state) =
      .ok (gasfulPcNext state) := by
  simp [EvmYul.EVM.step, gasfulPcNext,
    afterEVMInstructionChargeAt, afterMemoryChargeAt,
    afterDynamicChargeAt, chargeGas, evmyul_step_pc]

theorem raw_pc_success_executes_after_charges
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hDecode : Compact.decodeAt bytes pc (.prim .pc))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      [] (.ok (.running (openPcNext state))) := by
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim .pc) trivial hDecode hPc]
  have hOpen :
      Compact.Instr.openStepResult (.prim .pc) (afterDynamicChargeAt state) =
        .done (.ok (.running (openPcNext state))) := by
    simp [Compact.Instr.openStepResult, Compact.Instr.openStep,
      Assembly.InteractionSemantics.Target.openStepInstr,
      Assembly.Target.stepInstrWith,
      Assembly.InteractionSemantics.PrimOp.openStep,
      Assembly.PrimOp.step, Assembly.PrimOp.toEVM,
      Assembly.PrimOp.continuingStep?, Assembly.PrimOp.haltKind?,
      Compact.Instr.haltKind?,
      Simulation.ExternalKind.ofEVMOperation?,
      Simulation.Interaction.bind, evmyul_step_pc,
      openPcNext, afterDynamicChargeAt, afterMemoryChargeAt, chargeGas]
    rfl
  rw [hOpen]
  exact Interaction.Executes.done _

theorem pcNext_openStateRel (state : EVMState) :
    OpenStateRel (gasfulPcNext state) (openPcNext state) := by
  apply OpenStateRel.of_sameData
  · cases state
    rfl
  · rfl

def openPcNextAt (state : EVMState) : EVMState :=
  state.replaceStackAndIncrPC (state.stack.push state.pc)

theorem pcNext_openStateRel_rel
    {gasful openState : EVMState}
    (hRel : OpenStateRel gasful openState) :
    OpenStateRel (gasfulPcNext gasful) (openPcNextAt openState) := by
  apply OpenStateRel.replaceStackAndIncrPC
    (afterEVMInstructionChargeAt_openStateRel_left hRel)
  have hCharged := afterEVMInstructionChargeAt_openStateRel_left hRel
  rw [hCharged.stack_eq, hCharged.pc_eq]

theorem raw_pc_success_executes_at
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hDecode : Compact.decodeAt bytes pc (.prim .pc))
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult bytes 1 state)
      [] (.ok (.running (openPcNextAt state))) := by
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim .pc) trivial hDecode hPc]
  have hOpen :
      Compact.Instr.openStepResult (.prim .pc) state =
        .done (.ok (.running (openPcNextAt state))) := by
    simp [Compact.Instr.openStepResult, Compact.Instr.openStep,
      Assembly.InteractionSemantics.Target.openStepInstr,
      Assembly.Target.stepInstrWith,
      Assembly.InteractionSemantics.PrimOp.openStep,
      Assembly.PrimOp.step, Assembly.PrimOp.toEVM,
      Assembly.PrimOp.continuingStep?, Assembly.PrimOp.haltKind?,
      Compact.Instr.haltKind?,
      Simulation.ExternalKind.ofEVMOperation?,
      Simulation.Interaction.bind, evmyul_step_pc, openPcNextAt]
    rfl
  rw [hOpen]
  exact Interaction.Executes.done _

def gasfulPushNext (width : Nat) (value : Word)
    (state : EVMState) : EVMState :=
  let charged := afterEVMInstructionChargeAt state
  charged.replaceStackAndIncrPC (charged.stack.push value)
    (pcΔ := width + 1)

def openPushNext (width : Nat) (value : Word)
    (state : EVMState) : EVMState :=
  let charged := afterDynamicChargeAt state
  charged.replaceStackAndIncrPC (charged.stack.push value)
    (pcΔ := width + 1)

theorem evmyul_step_push_eq
    {width : Nat} {op : EvmYul.Operation .EVM}
    (state : EVMState) (value : Word)
    (hFits : Compact.FitsWidth width value.toNat)
    (hOp : Compact.pushOp? width = some op) :
    EvmYul.step (τ := .EVM) op (some (value, width)) state =
      .ok
        (state.replaceStackAndIncrPC (state.stack.push value)
          (pcΔ := width + 1)) := by
  have hPos := hFits.1
  have hLe := hFits.2.1
  interval_cases width <;>
    simp [Compact.pushOp?] at hOp <;> cases hOp <;> rfl

theorem pushOp_isCreate_false
    {width : Nat} {op : EvmYul.Operation .EVM} {value : Word}
    (hFits : Compact.FitsWidth width value.toNat)
    (hOp : Compact.pushOp? width = some op) :
    EvmYul.Operation.isCreate op = false := by
  have hPos := hFits.1
  have hLe := hFits.2.1
  interval_cases width <;>
    simp [Compact.pushOp?] at hOp <;> cases hOp <;> rfl

theorem pushOp_haltOutputAt_none
    {width : Nat} {op : EvmYul.Operation .EVM} {value : Word}
    (state : EVMState)
    (hFits : Compact.FitsWidth width value.toNat)
    (hOp : Compact.pushOp? width = some op) :
    haltOutputAt state op = none := by
  have hPos := hFits.1
  have hLe := hFits.2.1
  interval_cases width <;>
    simp [Compact.pushOp?, haltOutputAt] at hOp ⊢ <;> cases hOp <;> rfl

theorem evm_step_pushOp_eq_evmyul
    {width : Nat} {op : EvmYul.Operation .EVM}
    (fuel : Nat) (state : EVMState) (value : Word)
    (hFits : Compact.FitsWidth width value.toNat)
    (hOp : Compact.pushOp? width = some op) :
    EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
        (some (op, some (value, width))) (afterMemoryChargeAt state) =
      EvmYul.step (τ := .EVM) op (some (value, width))
        (afterEVMInstructionChargeAt state) := by
  have hPos := hFits.1
  have hLe := hFits.2.1
  interval_cases width <;>
    simp [Compact.pushOp?] at hOp <;> cases hOp <;>
    rfl

theorem evm_step_push_eq_next
    {width : Nat} {op : EvmYul.Operation .EVM}
    (fuel : Nat) (state : EVMState) (value : Word)
    (hFits : Compact.FitsWidth width value.toNat)
    (hOp : Compact.pushOp? width = some op) :
    EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
        (some (op, some (value, width))) (afterMemoryChargeAt state) =
      .ok (gasfulPushNext width value state) := by
  rw [evm_step_pushOp_eq_evmyul fuel state value hFits hOp]
  simpa [gasfulPushNext] using
    evmyul_step_push_eq
      (afterEVMInstructionChargeAt state) value hFits hOp

theorem raw_push_success_executes_after_charges
    {bytes : ByteArray} {pc width : Nat} {state : EVMState} {value : Word}
    (hFits : Compact.FitsWidth width value.toNat)
    (hDecode : Compact.decodeAt bytes pc (.push width value))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      [] (.ok (.running (openPushNext width value state))) := by
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .push width value) hFits hDecode hPc]
  exact Interaction.Executes.done _

theorem pushNext_openStateRel (width : Nat) (value : Word)
    (state : EVMState) :
    OpenStateRel (gasfulPushNext width value state)
      (openPushNext width value state) := by
  apply OpenStateRel.of_sameData
  · cases state
    rfl
  · rfl

def openPushNextAt (width : Nat) (value : Word)
    (state : EVMState) : EVMState :=
  state.replaceStackAndIncrPC (state.stack.push value)
    (pcΔ := width + 1)

theorem pushNext_openStateRel_rel
    (width : Nat) (value : Word) {gasful openState : EVMState}
    (hRel : OpenStateRel gasful openState) :
    OpenStateRel (gasfulPushNext width value gasful)
      (openPushNextAt width value openState) := by
  apply OpenStateRel.replaceStackAndIncrPC
    (afterEVMInstructionChargeAt_openStateRel_left hRel)
  have hCharged := afterEVMInstructionChargeAt_openStateRel_left hRel
  rw [hCharged.stack_eq]

theorem raw_push_success_executes_at
    {bytes : ByteArray} {pc width : Nat} {state : EVMState} {value : Word}
    (hFits : Compact.FitsWidth width value.toNat)
    (hDecode : Compact.decodeAt bytes pc (.push width value))
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult bytes 1 state)
      [] (.ok (.running (openPushNextAt width value state))) := by
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .push width value) hFits hDecode hPc]
  exact Interaction.Executes.done _

def gasfulJumpNext (state : EVMState)
    (rest : EvmYul.Stack Word) (dest : Word) : EVMState :=
  { afterEVMInstructionChargeAt state with pc := dest, stack := rest }

def openJumpNext (state : EVMState)
    (rest : EvmYul.Stack Word) (dest : Word) : EVMState :=
  { afterDynamicChargeAt state with pc := dest, stack := rest }

theorem evmyul_step_jump_eq
    (state : EVMState) (arg : Option (Word × Nat))
    (rest : EvmYul.Stack Word) (dest : Word)
    (hStack : state.stack = dest :: rest) :
    EvmYul.step (τ := .EVM) .JUMP arg state =
      .ok { state with pc := dest, stack := rest } := by
  unfold EvmYul.step
  simp only [Id.run]
  rw [hStack]
  rfl

theorem evm_step_jump_eq_next
    (fuel : Nat) (state : EVMState) (arg : Option (Word × Nat))
    (rest : EvmYul.Stack Word) (dest : Word)
    (hStack : state.stack = dest :: rest) :
    EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
        (some (EvmYul.Operation.JUMP, arg)) (afterMemoryChargeAt state) =
      .ok (gasfulJumpNext state rest dest) := by
  simp [EvmYul.EVM.step, gasfulJumpNext,
    afterEVMInstructionChargeAt, afterMemoryChargeAt,
    afterDynamicChargeAt, chargeGas, hStack, evmyul_step_jump_eq]
  exact evmyul_step_jump_eq _ _ _ _ rfl

theorem raw_jump_success_executes_after_charges
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    {rest : EvmYul.Stack Word} {dest : Word}
    (hStack : state.stack = dest :: rest)
    (hDecode : Compact.decodeAt bytes pc .jump)
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      [] (.ok (.running (openJumpNext state rest dest))) := by
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .jump) trivial hDecode hPc]
  have hOpen :
      Compact.Instr.openStepResult .jump (afterDynamicChargeAt state) =
        .done (.ok (.running (openJumpNext state rest dest))) := by
    simp [Compact.Instr.openStepResult, Compact.Instr.openStep,
      Assembly.InteractionSemantics.Target.openStepInstr,
      Assembly.Target.stepInstrWith, openJumpNext,
      afterDynamicChargeAt, afterMemoryChargeAt, chargeGas, hStack,
      EvmYul.Stack.pop]
    rfl
  rw [hOpen]
  exact Interaction.Executes.done _

theorem jumpNext_openStateRel
    (state : EVMState) (rest : EvmYul.Stack Word) (dest : Word) :
    OpenStateRel (gasfulJumpNext state rest dest)
      (openJumpNext state rest dest) := by
  apply OpenStateRel.of_sameData
  · cases state
    rfl
  · rfl

def openJumpNextAt (state : EVMState)
    (rest : EvmYul.Stack Word) (dest : Word) : EVMState :=
  { state with pc := dest, stack := rest }

theorem jumpNext_openStateRel_rel
    {gasful openState : EVMState} (rest : EvmYul.Stack Word) (dest : Word)
    (hRel : OpenStateRel gasful openState) :
    OpenStateRel (gasfulJumpNext gasful rest dest)
      (openJumpNextAt openState rest dest) := by
  apply OpenStateRel.withPcStack
    (afterEVMInstructionChargeAt_openStateRel_left hRel) rfl rfl

theorem raw_jump_success_executes_at
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    {rest : EvmYul.Stack Word} {dest : Word}
    (hStack : state.stack = dest :: rest)
    (hDecode : Compact.decodeAt bytes pc .jump)
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult bytes 1 state)
      [] (.ok (.running (openJumpNextAt state rest dest))) := by
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .jump) trivial hDecode hPc]
  have hOpen :
      Compact.Instr.openStepResult .jump state =
        .done (.ok (.running (openJumpNextAt state rest dest))) := by
    simp [Compact.Instr.openStepResult, Compact.Instr.openStep,
      Assembly.InteractionSemantics.Target.openStepInstr,
      Assembly.Target.stepInstrWith, openJumpNextAt, hStack,
      EvmYul.Stack.pop]
    rfl
  rw [hOpen]
  exact Interaction.Executes.done _

def gasfulJumpiNext (state : EVMState)
    (rest : EvmYul.Stack Word) (dest cond : Word) : EVMState :=
  { afterEVMInstructionChargeAt state with
    pc := if cond != EvmYul.UInt256.ofNat 0 then dest
      else state.pc + EvmYul.UInt256.ofNat 1
    stack := rest }

def openJumpiNext (state : EVMState)
    (rest : EvmYul.Stack Word) (dest cond : Word) : EVMState :=
  { afterDynamicChargeAt state with
    pc := if cond != EvmYul.UInt256.ofNat 0 then dest
      else state.pc + EvmYul.UInt256.ofNat 1
    stack := rest }

theorem evmyul_step_jumpi_eq
    (state : EVMState) (arg : Option (Word × Nat))
    (rest : EvmYul.Stack Word) (dest cond : Word)
    (hStack : state.stack = dest :: cond :: rest) :
    EvmYul.step (τ := .EVM) .JUMPI arg state =
      .ok
        { state with
          pc := if cond != EvmYul.UInt256.ofNat 0 then dest
            else state.pc + EvmYul.UInt256.ofNat 1
          stack := rest } := by
  unfold EvmYul.step
  simp only [Id.run]
  rw [hStack]
  rfl

theorem evm_step_jumpi_eq_next
    (fuel : Nat) (state : EVMState) (arg : Option (Word × Nat))
    (rest : EvmYul.Stack Word) (dest cond : Word)
    (hStack : state.stack = dest :: cond :: rest) :
    EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
        (some (EvmYul.Operation.JUMPI, arg)) (afterMemoryChargeAt state) =
      .ok (gasfulJumpiNext state rest dest cond) := by
  simp [EvmYul.EVM.step, gasfulJumpiNext,
    afterEVMInstructionChargeAt, afterMemoryChargeAt,
    afterDynamicChargeAt, chargeGas, hStack, evmyul_step_jumpi_eq]
  exact evmyul_step_jumpi_eq _ _ _ _ _ rfl

theorem raw_jumpi_success_executes_after_charges
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    {rest : EvmYul.Stack Word} {dest cond : Word}
    (hStack : state.stack = dest :: cond :: rest)
    (hDecode : Compact.decodeAt bytes pc .jumpi)
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      [] (.ok (.running (openJumpiNext state rest dest cond))) := by
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .jumpi) trivial hDecode hPc]
  have hOpen :
      Compact.Instr.openStepResult .jumpi (afterDynamicChargeAt state) =
        .done (.ok (.running (openJumpiNext state rest dest cond))) := by
    simp [Compact.Instr.openStepResult, Compact.Instr.openStep,
      Assembly.InteractionSemantics.Target.openStepInstr,
      Assembly.Target.stepInstrWith, openJumpiNext,
      afterDynamicChargeAt, afterMemoryChargeAt, chargeGas, hStack,
      EvmYul.Stack.pop2]
    rfl
  rw [hOpen]
  exact Interaction.Executes.done _

theorem jumpiNext_openStateRel
    (state : EVMState) (rest : EvmYul.Stack Word) (dest cond : Word) :
    OpenStateRel (gasfulJumpiNext state rest dest cond)
      (openJumpiNext state rest dest cond) := by
  apply OpenStateRel.of_sameData
  · cases state
    rfl
  · rfl

def openJumpiNextAt (state : EVMState)
    (rest : EvmYul.Stack Word) (dest cond : Word) : EVMState :=
  { state with
    pc := if cond != EvmYul.UInt256.ofNat 0 then dest
      else state.pc + EvmYul.UInt256.ofNat 1
    stack := rest }

theorem jumpiNext_openStateRel_rel
    {gasful openState : EVMState} (rest : EvmYul.Stack Word)
    (dest cond : Word) (hRel : OpenStateRel gasful openState) :
    OpenStateRel (gasfulJumpiNext gasful rest dest cond)
      (openJumpiNextAt openState rest dest cond) := by
  apply OpenStateRel.withPcStack
    (afterEVMInstructionChargeAt_openStateRel_left hRel)
  · simp [hRel.pc_eq]
  · rfl

theorem raw_jumpi_success_executes_at
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    {rest : EvmYul.Stack Word} {dest cond : Word}
    (hStack : state.stack = dest :: cond :: rest)
    (hDecode : Compact.decodeAt bytes pc .jumpi)
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult bytes 1 state)
      [] (.ok (.running (openJumpiNextAt state rest dest cond))) := by
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .jumpi) trivial hDecode hPc]
  have hOpen :
      Compact.Instr.openStepResult .jumpi state =
        .done (.ok (.running (openJumpiNextAt state rest dest cond))) := by
    simp [Compact.Instr.openStepResult, Compact.Instr.openStep,
      Assembly.InteractionSemantics.Target.openStepInstr,
      Assembly.Target.stepInstrWith, openJumpiNextAt, hStack,
      EvmYul.Stack.pop2]
    rfl
  rw [hOpen]
  exact Interaction.Executes.done _

def openJumpdestNextAt (state : EVMState) : EVMState := state.incrPC

theorem evm_step_jumpdest_eq_next
    (fuel : Nat) (state : EVMState) (arg : Option (Word × Nat)) :
    EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
        (some (EvmYul.Operation.JUMPDEST, arg)) (afterMemoryChargeAt state) =
      .ok (afterEVMInstructionChargeAt state).incrPC := by
  simp [EvmYul.EVM.step, afterEVMInstructionChargeAt,
    afterMemoryChargeAt, afterDynamicChargeAt, chargeGas]
  rfl

theorem jumpdestNext_openStateRel_rel
    {gasful openState : EVMState}
    (hRel : OpenStateRel gasful openState) :
    OpenStateRel (afterEVMInstructionChargeAt gasful).incrPC
      (openJumpdestNextAt openState) := by
  have hCharged := afterEVMInstructionChargeAt_openStateRel_left hRel
  have hNext := OpenStateRel.replaceStackAndIncrPC
    (pcDelta := 1) hCharged hCharged.stack_eq
  simpa [openJumpdestNextAt,
    EvmYul.EVM.State.replaceStackAndIncrPC] using hNext

theorem raw_jumpdest_executes_at
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hDecode : Compact.decodeAt bytes pc .jumpdest)
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult bytes 1 state)
      [] (.ok (.running (openJumpdestNextAt state))) := by
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .jumpdest) trivial hDecode hPc]
  exact Interaction.Executes.done _

/-- The open raw-bytecode `JUMPDEST` step is closed and emits no external or
resource observations when run from the actual post-charge erased state. -/
theorem raw_jumpdest_executes_after_charges
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hDecode : Compact.decodeAt bytes pc .jumpdest)
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      []
      (.ok (.running (afterDynamicChargeAt state).incrPC)) := by
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .jumpdest) trivial hDecode hPc]
  exact Interaction.Executes.done _

theorem jumpdest_chargedStepRel_after_charges
    (state : EVMState) :
    ChargedStepRel state
      (memoryExpansionCostAt state + dynamicGasCostAt state)
      (afterEVMInstructionChargeAt state).incrPC
      (afterDynamicChargeAt state).incrPC where
  gasfulErasesToOpen := by
    cases state
    rfl
  openErasesToCharged := by
    cases state
    rfl

theorem sameRuntimeData_afterEVMInstructionCharge_afterDynamic
    (state : EVMState) :
    SameRuntimeData (afterEVMInstructionChargeAt state)
      (afterDynamicChargeAt state) := by
  cases state
  rfl

inductive PureStackStep : PrimStep -> Prop where
  | bin (f : EvmYul.Primop.Binary) : PureStackStep (.bin f)
  | un (f : EvmYul.Primop.Unary) : PureStackStep (.un f)
  | tri (f : EvmYul.Primop.Ternary) : PureStackStep (.tri f)
  | pop : PureStackStep .pop
  | dup (n : Nat) : PureStackStep (.dup n)
  | swap (n : Nat) : PureStackStep (.swap n)

def OpenCompatibleStep (step : PrimStep) : Prop :=
  ∀ {left right leftNext : EVMState},
    OpenStateRel left right →
    step.run left = .ok leftNext →
    ∃ rightNext,
      step.run right = .ok rightNext ∧ OpenStateRel leftNext rightNext

theorem PureStackStep.run_openStateRel
    {step : PrimStep} (hPure : PureStackStep step)
    {left right leftNext : EVMState}
    (hRel : OpenStateRel left right)
    (hLeft : step.run left = .ok leftNext) :
    ∃ rightNext,
      step.run right = .ok rightNext ∧ OpenStateRel leftNext rightNext := by
  have hStack := hRel.stack_eq
  cases hPure with
  | bin f =>
      cases hPop : right.stack.pop2 with
      | none =>
          have hLeftPop : left.stack.pop2 = none := by simpa [hStack]
          simp [PrimStep.run, EvmYul.EVM.execBinOp, hLeftPop] at hLeft
      | some values =>
          rcases values with ⟨rest, a, b⟩
          have hLeftPop : left.stack.pop2 = some (rest, a, b) := by
            simpa [hStack] using hPop
          simp [PrimStep.run, EvmYul.EVM.execBinOp, hLeftPop] at hLeft
          simp only [Id.run, Except.ok.injEq] at hLeft
          subst leftNext
          refine ⟨right.replaceStackAndIncrPC (rest.push (f a b)), ?_, ?_⟩
          · simp [PrimStep.run, EvmYul.EVM.execBinOp, hPop]
            rfl
          · exact OpenStateRel.replaceStackAndIncrPC hRel rfl
  | un f =>
      cases hPop : right.stack.pop with
      | none =>
          have hLeftPop : left.stack.pop = none := by simpa [hStack]
          simp [PrimStep.run, EvmYul.EVM.execUnOp, hLeftPop] at hLeft
      | some values =>
          rcases values with ⟨rest, a⟩
          have hLeftPop : left.stack.pop = some (rest, a) := by
            simpa [hStack] using hPop
          simp [PrimStep.run, EvmYul.EVM.execUnOp, hLeftPop] at hLeft
          simp only [Id.run, Except.ok.injEq] at hLeft
          subst leftNext
          refine ⟨right.replaceStackAndIncrPC (rest.push (f a)), ?_, ?_⟩
          · simp [PrimStep.run, EvmYul.EVM.execUnOp, hPop]
            rfl
          · exact OpenStateRel.replaceStackAndIncrPC hRel rfl
  | tri f =>
      cases hPop : right.stack.pop3 with
      | none =>
          have hLeftPop : left.stack.pop3 = none := by simpa [hStack]
          simp [PrimStep.run, EvmYul.EVM.execTriOp, hLeftPop] at hLeft
      | some values =>
          rcases values with ⟨rest, a, b, c⟩
          have hLeftPop : left.stack.pop3 = some (rest, a, b, c) := by
            simpa [hStack] using hPop
          simp [PrimStep.run, EvmYul.EVM.execTriOp, hLeftPop] at hLeft
          simp only [Id.run, Except.ok.injEq] at hLeft
          subst leftNext
          refine ⟨right.replaceStackAndIncrPC (rest.push (f a b c)), ?_, ?_⟩
          · simp [PrimStep.run, EvmYul.EVM.execTriOp, hPop]
            rfl
          · exact OpenStateRel.replaceStackAndIncrPC hRel rfl
  | pop =>
      cases hPop : right.stack.pop with
      | none =>
          have hLeftPop : left.stack.pop = none := by simpa [hStack]
          simp [PrimStep.run, hLeftPop] at hLeft
      | some values =>
          rcases values with ⟨rest, a⟩
          have hLeftPop : left.stack.pop = some (rest, a) := by
            simpa [hStack] using hPop
          simp [PrimStep.run, hLeftPop] at hLeft
          subst leftNext
          refine ⟨right.replaceStackAndIncrPC rest, ?_, ?_⟩
          · simp [PrimStep.run, hPop]
          · exact OpenStateRel.replaceStackAndIncrPC hRel rfl
  | dup n =>
      by_cases hLength : n ≤ right.stack.length
      · have hLeftLength : n ≤ left.stack.length := by simpa [hStack]
        simp [PrimStep.run, EvmYul.dup, hLeftLength] at hLeft
        subst leftNext
        let newStack :=
          (right.stack.take n).getLast?.getD default :: right.stack
        refine ⟨right.replaceStackAndIncrPC newStack, ?_, ?_⟩
        · simp [PrimStep.run, EvmYul.dup, hLength, newStack]
        · apply OpenStateRel.replaceStackAndIncrPC hRel
          simp [newStack, hStack]
      · have hShort : right.stack.length < n := Nat.lt_of_not_ge hLength
        have hLeftLength : ¬ n ≤ left.stack.length := by simpa [hStack]
        have hLeftShort : left.stack.length < n := by simpa [hStack]
        simp [PrimStep.run, EvmYul.dup, hLength, hLeftLength,
          hShort, hLeftShort] at hLeft
  | swap n =>
      by_cases hLength : n + 1 ≤ right.stack.length
      · have hLeftLength : n + 1 ≤ left.stack.length := by simpa [hStack]
        simp [PrimStep.run, EvmYul.swap, hLeftLength] at hLeft
        subst leftNext
        let pref := right.stack.take (n + 1)
        let newStack := pref.getLast?.getD default ::
          (pref.tail!.dropLast ++
            pref.head! :: right.stack.drop (n + 1))
        refine ⟨right.replaceStackAndIncrPC newStack, ?_, ?_⟩
        · simp [PrimStep.run, EvmYul.swap, hLength, pref, newStack]
        · apply OpenStateRel.replaceStackAndIncrPC hRel
          simp [pref, newStack, hStack]
      · have hShort : right.stack.length < n + 1 :=
          Nat.lt_of_not_ge hLength
        have hLeftLength : ¬ n + 1 ≤ left.stack.length := by
          simpa [hStack]
        have hLeftShort : left.stack.length < n + 1 := by simpa [hStack]
        simp [PrimStep.run, EvmYul.swap, hLength, hLeftLength,
          hShort, hLeftShort] at hLeft

theorem PureStackStep.openCompatible
    {step : PrimStep} (hPure : PureStackStep step) :
    OpenCompatibleStep step := by
  intro left right leftNext hRel hLeft
  exact hPure.run_openStateRel hRel hLeft

theorem openCompatible_executionEnv
    (f : EvmYul.ExecutionEnv EvmYul.OperationType.EVM → Word) :
    OpenCompatibleStep (.executionEnv f) := by
  intro left right leftNext hRel hLeft
  have hStack := hRel.stack_eq
  have hEnv := hRel.executionEnv_eq
  simp [PrimStep.run, EvmYul.EVM.executionEnvOp] at hLeft
  simp only [Id.run, Except.ok.injEq] at hLeft
  subst leftNext
  refine ⟨right.replaceStackAndIncrPC
    (right.stack.push (f right.executionEnv)), ?_, ?_⟩
  · simp [PrimStep.run, EvmYul.EVM.executionEnvOp]
    rfl
  · apply OpenStateRel.replaceStackAndIncrPC hRel
    rw [hStack, hEnv]

theorem openCompatible_unaryExecutionEnv
    (f : EvmYul.ExecutionEnv EvmYul.OperationType.EVM → Word → Word) :
    OpenCompatibleStep (.unaryExecutionEnv f) := by
  intro left right leftNext hRel hLeft
  have hStack := hRel.stack_eq
  have hEnv := hRel.executionEnv_eq
  cases hPop : right.stack.pop with
  | none =>
      have hLeftPop : left.stack.pop = none := by simpa [hStack]
      simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp, hLeftPop] at hLeft
  | some values =>
      rcases values with ⟨rest, a⟩
      have hLeftPop : left.stack.pop = some (rest, a) := by
        simpa [hStack] using hPop
      simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp, hLeftPop] at hLeft
      simp only [Id.run, Except.ok.injEq] at hLeft
      subst leftNext
      refine ⟨right.replaceStackAndIncrPC
        (rest.push (f right.executionEnv a)), ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp, hPop]
        rfl
      · apply OpenStateRel.replaceStackAndIncrPC hRel
        rw [hEnv]

structure MachineDataRel
    (left right : EvmYul.MachineState) : Prop where
  activeWords : left.activeWords = right.activeWords
  memory : left.memory = right.memory
  returnData : left.returnData = right.returnData
  hReturn : left.H_return = right.H_return

theorem OpenStateRel.machineDataRel
    {left right : EVMState} (hRel : OpenStateRel left right) :
    MachineDataRel left.toMachineState right.toMachineState := by
  have hFrame := hRel.openData.frame
  cases left
  cases right
  simp [eraseOpenWorldData, eraseControl, eraseGas] at hFrame
  exact ⟨hFrame.1.2.1, hFrame.1.2.2.1,
    hFrame.1.2.2.2.1, hFrame.1.2.2.2.2⟩

theorem OpenStateRel.withMachineState
    {left right : EVMState}
    {leftMachine rightMachine : EvmYul.MachineState}
    (hRel : OpenStateRel left right)
    (hMachine : MachineDataRel leftMachine rightMachine) :
    OpenStateRel { left with toMachineState := leftMachine }
      { right with toMachineState := rightMachine } := by
  constructor
  · constructor
    · simpa using hRel.openData.world
    · have hFrame := hRel.openData.frame
      cases left
      cases right
      cases leftMachine
      cases rightMachine
      simp [eraseOpenWorldData, eraseControl, eraseGas] at hFrame ⊢
      exact ⟨⟨hFrame.1.1, hMachine.activeWords, hMachine.memory,
        hMachine.returnData, hMachine.hReturn⟩, hFrame.2⟩
  · exact hRel.pc_eq

def MachineReadCompatible (f : EvmYul.MachineState → Word) : Prop :=
  ∀ {left right}, MachineDataRel left right → f left = f right

def MachineBinaryCompatible
    (f : EvmYul.MachineState → Word → Word → EvmYul.MachineState) : Prop :=
  ∀ {left right} (a b : Word),
    MachineDataRel left right → MachineDataRel (f left a b) (f right a b)

def MachineBinaryResultCompatible
    (f : EvmYul.MachineState → Word → Word →
      Word × EvmYul.MachineState) : Prop :=
  ∀ {left right} (a b : Word),
    MachineDataRel left right →
      (f left a b).1 = (f right a b).1 ∧
        MachineDataRel (f left a b).2 (f right a b).2

def MachineUnaryResultCompatible
    (f : EvmYul.MachineState → Word → Word × EvmYul.MachineState) : Prop :=
  ∀ {left right} (a : Word),
    MachineDataRel left right →
      (f left a).1 = (f right a).1 ∧
        MachineDataRel (f left a).2 (f right a).2

def MachineTernaryCompatible
    (f : EvmYul.MachineState → Word → Word → Word →
      EvmYul.MachineState) : Prop :=
  ∀ {left right} (a b c : Word),
    MachineDataRel left right →
      MachineDataRel (f left a b c) (f right a b c)

theorem openCompatible_machineState
    {f : EvmYul.MachineState → Word}
    (hCompatible : MachineReadCompatible f) :
    OpenCompatibleStep (.machineState f) := by
  intro left right leftNext hRel hLeft
  have hStack := hRel.stack_eq
  have hResult := hCompatible hRel.machineDataRel
  simp [PrimStep.run, EvmYul.EVM.machineStateOp] at hLeft
  simp only [Id.run, Except.ok.injEq] at hLeft
  subst leftNext
  refine ⟨right.replaceStackAndIncrPC
    (right.stack.push (f right.toMachineState)), ?_, ?_⟩
  · simp [PrimStep.run, EvmYul.EVM.machineStateOp]
    rfl
  · apply OpenStateRel.replaceStackAndIncrPC hRel
    rw [hStack, hResult]

theorem openCompatible_binaryMachineState
    {f : EvmYul.MachineState → Word → Word → EvmYul.MachineState}
    (hCompatible : MachineBinaryCompatible f) :
    OpenCompatibleStep (.binaryMachineState f) := by
  intro left right leftNext hRel hLeft
  have hStack := hRel.stack_eq
  cases hPop : right.stack.pop2 with
  | none =>
      have hLeftPop : left.stack.pop2 = none := by simpa [hStack]
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp, hLeftPop] at hLeft
  | some values =>
      rcases values with ⟨rest, a, b⟩
      have hLeftPop : left.stack.pop2 = some (rest, a, b) := by
        simpa [hStack] using hPop
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp, hLeftPop] at hLeft
      simp only [Id.run, Except.ok.injEq] at hLeft
      subst leftNext
      let leftMachine := f left.toMachineState a b
      let rightMachine := f right.toMachineState a b
      have hMachine : MachineDataRel leftMachine rightMachine :=
        hCompatible a b hRel.machineDataRel
      let rightState : EVMState := { right with toMachineState := rightMachine }
      refine ⟨rightState.replaceStackAndIncrPC rest, ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp, hPop,
          rightState, rightMachine]
        rfl
      · apply OpenStateRel.replaceStackAndIncrPC
          (hRel.withMachineState hMachine)
        rfl

theorem openCompatible_binaryMachineStateWithResult
    {f : EvmYul.MachineState → Word → Word →
      Word × EvmYul.MachineState}
    (hCompatible : MachineBinaryResultCompatible f) :
    OpenCompatibleStep (.binaryMachineStateWithResult f) := by
  intro left right leftNext hRel hLeft
  have hStack := hRel.stack_eq
  cases hPop : right.stack.pop2 with
  | none =>
      have hLeftPop : left.stack.pop2 = none := by simpa [hStack]
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp', hLeftPop] at hLeft
  | some values =>
      rcases values with ⟨rest, a, b⟩
      have hLeftPop : left.stack.pop2 = some (rest, a, b) := by
        simpa [hStack] using hPop
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp', hLeftPop] at hLeft
      simp only [Id.run, Except.ok.injEq] at hLeft
      subst leftNext
      let leftResult := f left.toMachineState a b
      let rightResult := f right.toMachineState a b
      have hResult := hCompatible a b hRel.machineDataRel
      have hValue : leftResult.1 = rightResult.1 := hResult.1
      have hMachine : MachineDataRel leftResult.2 rightResult.2 := hResult.2
      let rightState : EVMState := { right with toMachineState := rightResult.2 }
      refine ⟨rightState.replaceStackAndIncrPC (rest.push rightResult.1), ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp', hPop,
          rightState, rightResult]
        rfl
      · apply OpenStateRel.replaceStackAndIncrPC
          (hRel.withMachineState hMachine)
        exact congrArg rest.push hValue

theorem openCompatible_ternaryMachineState
    {f : EvmYul.MachineState → Word → Word → Word → EvmYul.MachineState}
    (hCompatible : MachineTernaryCompatible f) :
    OpenCompatibleStep (.ternaryMachineState f) := by
  intro left right leftNext hRel hLeft
  have hStack := hRel.stack_eq
  cases hPop : right.stack.pop3 with
  | none =>
      have hLeftPop : left.stack.pop3 = none := by simpa [hStack]
      simp [PrimStep.run, EvmYul.EVM.ternaryMachineStateOp, hLeftPop] at hLeft
  | some values =>
      rcases values with ⟨rest, a, b, c⟩
      have hLeftPop : left.stack.pop3 = some (rest, a, b, c) := by
        simpa [hStack] using hPop
      simp [PrimStep.run, EvmYul.EVM.ternaryMachineStateOp, hLeftPop] at hLeft
      simp only [Id.run, Except.ok.injEq] at hLeft
      subst leftNext
      let leftMachine := f left.toMachineState a b c
      let rightMachine := f right.toMachineState a b c
      have hMachine : MachineDataRel leftMachine rightMachine :=
        hCompatible a b c hRel.machineDataRel
      let rightState : EVMState := { right with toMachineState := rightMachine }
      refine ⟨rightState.replaceStackAndIncrPC rest, ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.ternaryMachineStateOp, hPop,
          rightState, rightMachine]
        rfl
      · apply OpenStateRel.replaceStackAndIncrPC
          (hRel.withMachineState hMachine)
        rfl

theorem openCompatible_mload
    (hCompatible :
      MachineUnaryResultCompatible EvmYul.MachineState.mload) :
    OpenCompatibleStep .mload := by
  intro left right leftNext hRel hLeft
  have hStack := hRel.stack_eq
  cases hPop : right.stack.pop with
  | none =>
      have hLeftPop : left.stack.pop = none := by simpa [hStack]
      simp [PrimStep.run, hLeftPop] at hLeft
  | some values =>
      rcases values with ⟨rest, a⟩
      have hLeftPop : left.stack.pop = some (rest, a) := by
        simpa [hStack] using hPop
      simp [PrimStep.run, hLeftPop] at hLeft
      subst leftNext
      let leftResult := left.toMachineState.mload a
      let rightResult := right.toMachineState.mload a
      have hResult := hCompatible a hRel.machineDataRel
      have hValue : leftResult.1 = rightResult.1 := hResult.1
      have hMachine : MachineDataRel leftResult.2 rightResult.2 := hResult.2
      let rightState : EVMState := { right with toMachineState := rightResult.2 }
      refine ⟨rightState.replaceStackAndIncrPC (rest.push rightResult.1), ?_, ?_⟩
      · simp [PrimStep.run, hPop, rightState, rightResult]
      · apply OpenStateRel.replaceStackAndIncrPC
          (hRel.withMachineState hMachine)
        exact congrArg rest.push hValue

theorem openCompatible_returndatacopy
    (hCompatible :
      MachineTernaryCompatible EvmYul.MachineState.returndatacopy) :
    OpenCompatibleStep .returndatacopy := by
  intro left right leftNext hRel hLeft
  have hStack := hRel.stack_eq
  have hReturn := hRel.machineDataRel.returnData
  cases hPop : right.stack.pop3 with
  | none =>
      have hLeftPop : left.stack.pop3 = none := by simpa [hStack]
      simp [PrimStep.run, hLeftPop] at hLeft
  | some values =>
      rcases values with ⟨rest, a, b, c⟩
      have hLeftPop : left.stack.pop3 = some (rest, a, b, c) := by
        simpa [hStack] using hPop
      by_cases hInvalid : left.returnData.size < b.toNat + c.toNat
      · simp [PrimStep.run, hLeftPop, hInvalid] at hLeft
      · have hRightValid : ¬ right.returnData.size < b.toNat + c.toNat := by
          simpa [hReturn] using hInvalid
        simp [PrimStep.run, hLeftPop, hInvalid] at hLeft
        subst leftNext
        let leftMachine := left.toMachineState.returndatacopy a b c
        let rightMachine := right.toMachineState.returndatacopy a b c
        have hMachine : MachineDataRel leftMachine rightMachine :=
          hCompatible a b c hRel.machineDataRel
        let rightState : EVMState := { right with toMachineState := rightMachine }
        refine ⟨rightState.replaceStackAndIncrPC rest, ?_, ?_⟩
        · simp [PrimStep.run, hPop, hRightValid, rightState, rightMachine]
        · apply OpenStateRel.replaceStackAndIncrPC
            (hRel.withMachineState hMachine)
          rfl

theorem machineReadCompatible_returndatasize :
    MachineReadCompatible EvmYul.MachineState.returndatasize := by
  intro left right hRel
  simp [EvmYul.MachineState.returndatasize, hRel.returnData]

theorem machineUnaryResultCompatible_mload :
    MachineUnaryResultCompatible EvmYul.MachineState.mload := by
  intro left right a hRel
  cases left
  cases right
  rcases hRel with ⟨hActive, hMemory, hReturn, hHReturn⟩
  simp_all [EvmYul.MachineState.mload,
    EvmYul.MachineState.lookupMemory]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem machineBinaryCompatible_mstore :
    MachineBinaryCompatible EvmYul.MachineState.mstore := by
  intro left right a b hRel
  cases left
  cases right
  rcases hRel with ⟨hActive, hMemory, hReturn, hHReturn⟩
  simp_all [EvmYul.MachineState.mstore,
    EvmYul.MachineState.writeWord, EvmYul.writeBytes]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem machineBinaryCompatible_mstore8 :
    MachineBinaryCompatible EvmYul.MachineState.mstore8 := by
  intro left right a b hRel
  cases left
  cases right
  rcases hRel with ⟨hActive, hMemory, hReturn, hHReturn⟩
  simp_all [EvmYul.MachineState.mstore8, EvmYul.writeBytes]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem machineTernaryCompatible_mcopy :
    MachineTernaryCompatible EvmYul.MachineState.mcopy := by
  intro left right a b c hRel
  cases left
  cases right
  rcases hRel with ⟨hActive, hMemory, hReturn, hHReturn⟩
  simp_all [EvmYul.MachineState.mcopy, EvmYul.writeBytes]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem machineTernaryCompatible_returndatacopy :
    MachineTernaryCompatible EvmYul.MachineState.returndatacopy := by
  intro left right a b c hRel
  cases left
  cases right
  rcases hRel with ⟨hActive, hMemory, hReturn, hHReturn⟩
  simp_all [EvmYul.MachineState.returndatacopy, EvmYul.writeBytes]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem machineBinaryResultCompatible_keccak256 :
    MachineBinaryResultCompatible EvmYul.MachineState.keccak256 := by
  intro left right a b hRel
  cases left
  cases right
  rcases hRel with ⟨hActive, hMemory, hReturn, hHReturn⟩
  simp_all [EvmYul.MachineState.keccak256]
  exact ⟨rfl, rfl, rfl, rfl⟩

structure StateDataRel
    (left right : EvmYul.State EvmYul.OperationType.EVM) : Prop where
  world : OpenWorld.ofEVMState left = OpenWorld.ofEVMState right
  initialAccounts : left.σ₀ = right.σ₀
  totalGasUsedInBlock : left.totalGasUsedInBlock = right.totalGasUsedInBlock
  transactionReceipts : left.transactionReceipts = right.transactionReceipts
  executionEnv : left.executionEnv = right.executionEnv
  blocks : left.blocks = right.blocks
  genesisBlockHeader : left.genesisBlockHeader = right.genesisBlockHeader

theorem OpenStateRel.stateDataRel
    {left right : EVMState} (hRel : OpenStateRel left right) :
    StateDataRel left.toState right.toState := by
  have hFrame := hRel.openData.frame
  cases left
  cases right
  simp [eraseOpenWorldData, eraseControl, eraseGas] at hFrame
  exact
    { world := hRel.openData.world
      initialAccounts := hFrame.1.1.1
      totalGasUsedInBlock := hFrame.1.1.2.1
      transactionReceipts := hFrame.1.1.2.2.1
      executionEnv := hFrame.1.1.2.2.2.1
      blocks := hFrame.1.1.2.2.2.2.1
      genesisBlockHeader := hFrame.1.1.2.2.2.2.2 }

theorem OpenStateRel.withState
    {left right : EVMState}
    {leftState rightState : EvmYul.State EvmYul.OperationType.EVM}
    (hRel : OpenStateRel left right)
    (hState : StateDataRel leftState rightState) :
    OpenStateRel { left with toState := leftState }
      { right with toState := rightState } := by
  constructor
  · constructor
    · exact hState.world
    · have hFrame := hRel.openData.frame
      cases left
      cases right
      cases leftState
      cases rightState
      simp [eraseOpenWorldData, eraseControl, eraseGas] at hFrame ⊢
      exact
        ⟨⟨⟨hState.initialAccounts, hState.totalGasUsedInBlock,
              hState.transactionReceipts, hState.executionEnv,
              hState.blocks, hState.genesisBlockHeader⟩,
            hFrame.1.2⟩,
          hFrame.2⟩
  · exact hRel.pc_eq

def StateReadCompatible
    (f : EvmYul.State EvmYul.OperationType.EVM → Word) : Prop :=
  ∀ {left right}, StateDataRel left right → f left = f right

def StateUnaryCompatible
    (f : EvmYul.State EvmYul.OperationType.EVM → Word →
      EvmYul.State EvmYul.OperationType.EVM × Word) : Prop :=
  ∀ {left right} (a : Word),
    StateDataRel left right →
      StateDataRel (f left a).1 (f right a).1 ∧
        (f left a).2 = (f right a).2

def StateBinaryCompatible
    (f : EvmYul.State EvmYul.OperationType.EVM → Word → Word →
      EvmYul.State EvmYul.OperationType.EVM) : Prop :=
  ∀ {left right} (a b : Word),
    StateDataRel left right → StateDataRel (f left a b) (f right a b)

theorem openCompatible_state
    {f : EvmYul.State EvmYul.OperationType.EVM → Word}
    (hCompatible : StateReadCompatible f) :
    OpenCompatibleStep (.state f) := by
  intro left right leftNext hRel hLeft
  have hStack := hRel.stack_eq
  have hResult := hCompatible hRel.stateDataRel
  simp [PrimStep.run, EvmYul.EVM.stateOp] at hLeft
  simp only [Id.run, Except.ok.injEq] at hLeft
  subst leftNext
  refine ⟨right.replaceStackAndIncrPC
    (right.stack.push (f right.toState)), ?_, ?_⟩
  · simp [PrimStep.run, EvmYul.EVM.stateOp]
    rfl
  · apply OpenStateRel.replaceStackAndIncrPC hRel
    rw [hStack, hResult]

theorem openCompatible_unaryState
    {f : EvmYul.State EvmYul.OperationType.EVM → Word →
      EvmYul.State EvmYul.OperationType.EVM × Word}
    (hCompatible : StateUnaryCompatible f) :
    OpenCompatibleStep (.unaryState f) := by
  intro left right leftNext hRel hLeft
  have hStack := hRel.stack_eq
  cases hPop : right.stack.pop with
  | none =>
      have hLeftPop : left.stack.pop = none := by simpa [hStack]
      simp [PrimStep.run, EvmYul.EVM.unaryStateOp, hLeftPop] at hLeft
  | some values =>
      rcases values with ⟨rest, a⟩
      have hLeftPop : left.stack.pop = some (rest, a) := by
        simpa [hStack] using hPop
      simp [PrimStep.run, EvmYul.EVM.unaryStateOp, hLeftPop] at hLeft
      simp only [Id.run, Except.ok.injEq] at hLeft
      subst leftNext
      let leftResult := f left.toState a
      let rightResult := f right.toState a
      have hResult := hCompatible a hRel.stateDataRel
      have hState : StateDataRel leftResult.1 rightResult.1 := hResult.1
      have hValue : leftResult.2 = rightResult.2 := hResult.2
      let rightState : EVMState := { right with toState := rightResult.1 }
      refine ⟨rightState.replaceStackAndIncrPC (rest.push rightResult.2), ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.unaryStateOp, hPop,
          rightState, rightResult]
        rfl
      · apply OpenStateRel.replaceStackAndIncrPC (hRel.withState hState)
        exact congrArg rest.push hValue

theorem openCompatible_binaryState
    {f : EvmYul.State EvmYul.OperationType.EVM → Word → Word →
      EvmYul.State EvmYul.OperationType.EVM}
    (hCompatible : StateBinaryCompatible f) :
    OpenCompatibleStep (.binaryState f) := by
  intro left right leftNext hRel hLeft
  have hStack := hRel.stack_eq
  have hEnv := hRel.stateDataRel.executionEnv
  cases hPerm : right.executionEnv.perm with
  | false =>
      have hLeftPerm : left.executionEnv.perm = false := by simpa [hEnv]
      simp [PrimStep.run, hLeftPerm] at hLeft
  | true =>
      have hLeftPerm : left.executionEnv.perm = true := by simpa [hEnv]
      cases hPop : right.stack.pop2 with
      | none =>
          have hLeftPop : left.stack.pop2 = none := by simpa [hStack]
          simp [PrimStep.run, EvmYul.EVM.binaryStateOp,
            hLeftPerm, hLeftPop] at hLeft
      | some values =>
          rcases values with ⟨rest, a, b⟩
          have hLeftPop : left.stack.pop2 = some (rest, a, b) := by
            simpa [hStack] using hPop
          simp [PrimStep.run, EvmYul.EVM.binaryStateOp,
            hLeftPerm, hLeftPop] at hLeft
          simp only [Id.run, Except.ok.injEq] at hLeft
          subst leftNext
          let leftState := f left.toState a b
          let rightStateData := f right.toState a b
          have hState : StateDataRel leftState rightStateData :=
            hCompatible a b hRel.stateDataRel
          let rightState : EVMState := { right with toState := rightStateData }
          refine ⟨rightState.replaceStackAndIncrPC rest, ?_, ?_⟩
          · simp [PrimStep.run, EvmYul.EVM.binaryStateOp, hPerm, hPop,
              rightState, rightStateData]
            rfl
          · apply OpenStateRel.replaceStackAndIncrPC (hRel.withState hState)
            rfl

def StateUnaryReadCompatible
    (f : EvmYul.State EvmYul.OperationType.EVM → Word → Word) : Prop :=
  ∀ {left right} (a : Word),
    StateDataRel left right → f left a = f right a

theorem stateUnaryCompatible_of_read
    {f : EvmYul.State EvmYul.OperationType.EVM → Word → Word}
    (hCompatible : StateUnaryReadCompatible f) :
    StateUnaryCompatible (fun state value => (state, f state value)) := by
  intro left right a hRel
  exact ⟨hRel, hCompatible a hRel⟩

theorem stateReadCompatible_coinBase :
    StateReadCompatible
      (.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase) := by
  intro left right hRel
  simp [Function.comp_def, EvmYul.State.coinBase, hRel.executionEnv]

theorem stateReadCompatible_timeStamp :
    StateReadCompatible EvmYul.State.timeStamp := by
  intro left right hRel
  simp [EvmYul.State.timeStamp, hRel.executionEnv]

theorem stateReadCompatible_number :
    StateReadCompatible EvmYul.State.number := by
  intro left right hRel
  simp [EvmYul.State.number, hRel.executionEnv]

theorem stateReadCompatible_gasLimit :
    StateReadCompatible EvmYul.State.gasLimit := by
  intro left right hRel
  simp [EvmYul.State.gasLimit, hRel.executionEnv]

theorem stateReadCompatible_chainId :
    StateReadCompatible EvmYul.State.chainId := by
  intro left right hRel
  rfl

theorem stateUnaryReadCompatible_calldataload :
    StateUnaryReadCompatible EvmYul.State.calldataload := by
  intro left right a hRel
  simp [EvmYul.State.calldataload, hRel.executionEnv]

theorem stateUnaryReadCompatible_blockHash :
    StateUnaryReadCompatible EvmYul.State.blockHash := by
  intro left right a hRel
  simp [EvmYul.State.blockHash, EvmYul.State.blockHashes,
    hRel.executionEnv, hRel.blocks]

structure SharedDataRel
    (left right : EvmYul.SharedState EvmYul.OperationType.EVM) : Prop where
  state : StateDataRel left.toState right.toState
  machine : MachineDataRel left.toMachineState right.toMachineState

theorem OpenStateRel.sharedDataRel
    {left right : EVMState} (hRel : OpenStateRel left right) :
    SharedDataRel left.toSharedState right.toSharedState :=
  ⟨hRel.stateDataRel, hRel.machineDataRel⟩

theorem OpenStateRel.withSharedState
    {left right : EVMState}
    {leftShared rightShared : EvmYul.SharedState EvmYul.OperationType.EVM}
    (hRel : OpenStateRel left right)
    (hShared : SharedDataRel leftShared rightShared) :
    OpenStateRel { left with toSharedState := leftShared }
      { right with toSharedState := rightShared } := by
  have hState := hRel.withState hShared.state
  have hMachine := hState.withMachineState hShared.machine
  simpa using hMachine

def SharedTernaryCompatible
    (f : EvmYul.SharedState EvmYul.OperationType.EVM → Word → Word → Word →
      EvmYul.SharedState EvmYul.OperationType.EVM) : Prop :=
  ∀ {left right} (a b c : Word),
    SharedDataRel left right → SharedDataRel (f left a b c) (f right a b c)

theorem openCompatible_ternaryCopy
    {f : EvmYul.SharedState EvmYul.OperationType.EVM → Word → Word → Word →
      EvmYul.SharedState EvmYul.OperationType.EVM}
    (hCompatible : SharedTernaryCompatible f) :
    OpenCompatibleStep (.ternaryCopy f) := by
  intro left right leftNext hRel hLeft
  have hStack := hRel.stack_eq
  cases hPop : right.stack.pop3 with
  | none =>
      have hLeftPop : left.stack.pop3 = none := by simpa [hStack]
      simp [PrimStep.run, EvmYul.EVM.ternaryCopyOp, hLeftPop] at hLeft
  | some values =>
      rcases values with ⟨rest, a, b, c⟩
      have hLeftPop : left.stack.pop3 = some (rest, a, b, c) := by
        simpa [hStack] using hPop
      simp [PrimStep.run, EvmYul.EVM.ternaryCopyOp, hLeftPop] at hLeft
      simp only [Id.run, Except.ok.injEq] at hLeft
      subst leftNext
      let leftShared := f left.toSharedState a b c
      let rightShared := f right.toSharedState a b c
      have hShared : SharedDataRel leftShared rightShared :=
        hCompatible a b c hRel.sharedDataRel
      let rightState : EVMState := { right with toSharedState := rightShared }
      refine ⟨rightState.replaceStackAndIncrPC rest, ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.ternaryCopyOp, hPop,
          rightState, rightShared]
        rfl
      · apply OpenStateRel.replaceStackAndIncrPC
          (hRel.withSharedState hShared)
        rfl

theorem sharedTernaryCompatible_calldatacopy :
    SharedTernaryCompatible EvmYul.SharedState.calldatacopy := by
  intro left right a b c hRel
  constructor
  · simpa [EvmYul.SharedState.calldatacopy] using hRel.state
  · cases left
    cases right
    rcases hRel.machine with ⟨hActive, hMemory, hReturn, hHReturn⟩
    have hEnv := hRel.state.executionEnv
    simp [EvmYul.SharedState.calldatacopy] at hEnv ⊢
    simp_all
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem sharedTernaryCompatible_codeCopy :
    SharedTernaryCompatible EvmYul.SharedState.codeCopy := by
  intro left right a b c hRel
  constructor
  · simpa [EvmYul.SharedState.codeCopy] using hRel.state
  · cases left
    cases right
    rcases hRel.machine with ⟨hActive, hMemory, hReturn, hHReturn⟩
    have hEnv := hRel.state.executionEnv
    simp [EvmYul.SharedState.codeCopy] at hEnv ⊢
    simp_all
    exact ⟨rfl, rfl, rfl, rfl⟩

namespace StateDataRel

theorem accounts
    {left right : EvmYul.State EvmYul.OperationType.EVM}
    (hRel : StateDataRel left right) :
    (OpenWorld.ofEVMState left).accounts =
      (OpenWorld.ofEVMState right).accounts :=
  congrArg OpenWorld.accounts hRel.world

theorem substate
    {left right : EvmYul.State EvmYul.OperationType.EVM}
    (hRel : StateDataRel left right) :
    left.substate = right.substate :=
  congrArg OpenWorld.substate hRel.world

theorem createdAccounts
    {left right : EvmYul.State EvmYul.OperationType.EVM}
    (hRel : StateDataRel left right) :
    left.createdAccounts = right.createdAccounts :=
  congrArg OpenWorld.createdAccounts hRel.world

theorem accountViews
    {left right : EvmYul.State EvmYul.OperationType.EVM}
    (hRel : StateDataRel left right)
    (address : EvmYul.AccountAddress) :
    (left.accountMap.find? address).map OpenAccount.ofEVM =
      (right.accountMap.find? address).map OpenAccount.ofEVM := by
  have hLookup := congrArg (fun accounts => accounts.find? address) hRel.accounts
  simpa [OpenWorld.ofEVMState, OpenWorld.find?_mapVal_const] using hLookup

theorem accountValueEq
    {left right : EvmYul.State EvmYul.OperationType.EVM}
    (hRel : StateDataRel left right)
    (address : EvmYul.AccountAddress)
    {α : Type} (defaultValue : α) (value : OpenAccount → α) :
    (left.accountMap.find? address).option defaultValue
        (fun account => value (OpenAccount.ofEVM account)) =
      (right.accountMap.find? address).option defaultValue
        (fun account => value (OpenAccount.ofEVM account)) := by
  have hViews := hRel.accountViews address
  cases hLeft : left.accountMap.find? address with
  | none =>
      rw [hLeft] at hViews
      cases hRight : right.accountMap.find? address with
      | none => rfl
      | some rightAccount => simp [hRight] at hViews
  | some leftAccount =>
      rw [hLeft] at hViews
      cases hRight : right.accountMap.find? address with
      | none => simp [hRight] at hViews
      | some rightAccount =>
          rw [hRight] at hViews
          have hAccount : OpenAccount.ofEVM leftAccount =
              OpenAccount.ofEVM rightAccount := by
            simpa using Option.some.inj hViews
          simpa [hLeft, hRight] using congrArg value hAccount

theorem accountElimValueEq
    {left right : EvmYul.State EvmYul.OperationType.EVM}
    (hRel : StateDataRel left right)
    (address : EvmYul.AccountAddress)
    {α : Type} (defaultValue : α) (value : OpenAccount → α) :
    (left.accountMap.find? address).elim defaultValue
        (fun account => value (OpenAccount.ofEVM account)) =
      (right.accountMap.find? address).elim defaultValue
        (fun account => value (OpenAccount.ofEVM account)) := by
  have hViews := hRel.accountViews address
  cases hLeft : left.accountMap.find? address with
  | none =>
      rw [hLeft] at hViews
      cases hRight : right.accountMap.find? address with
      | none => rfl
      | some rightAccount => simp [hRight] at hViews
  | some leftAccount =>
      rw [hLeft] at hViews
      cases hRight : right.accountMap.find? address with
      | none => simp [hRight] at hViews
      | some rightAccount =>
          rw [hRight] at hViews
          have hAccount : OpenAccount.ofEVM leftAccount =
              OpenAccount.ofEVM rightAccount := by
            simpa using Option.some.inj hViews
          simpa [hLeft, hRight] using congrArg value hAccount

theorem dead_eq
    {left right : EvmYul.State EvmYul.OperationType.EVM}
    (hRel : StateDataRel left right) (address : EvmYul.AccountAddress) :
    CodeErasedState.dead left.accountMap address =
      CodeErasedState.dead right.accountMap address := by
  unfold CodeErasedState.dead
  simpa [OpenAccount.ofAccount_evm] using
    hRel.accountValueEq address true OpenAccount.empty

theorem addAccessedAccount
    {left right : EvmYul.State EvmYul.OperationType.EVM}
    (hRel : StateDataRel left right) (address : EvmYul.AccountAddress) :
    StateDataRel (left.addAccessedAccount address)
      (right.addAccessedAccount address) := by
  exact
    { world := by
        apply OpenWorld.ext_of_fields
        · simpa [OpenWorld.ofEVMState, EvmYul.State.addAccessedAccount]
            using hRel.accounts
        · simp [OpenWorld.ofEVMState, EvmYul.State.addAccessedAccount,
            hRel.substate]
        · simpa [OpenWorld.ofEVMState, EvmYul.State.addAccessedAccount]
            using hRel.createdAccounts
      initialAccounts := by
        simpa [EvmYul.State.addAccessedAccount] using hRel.initialAccounts
      totalGasUsedInBlock := by
        simpa [EvmYul.State.addAccessedAccount] using hRel.totalGasUsedInBlock
      transactionReceipts := by
        simpa [EvmYul.State.addAccessedAccount] using hRel.transactionReceipts
      executionEnv := by
        simpa [EvmYul.State.addAccessedAccount] using hRel.executionEnv
      blocks := by simpa [EvmYul.State.addAccessedAccount] using hRel.blocks
      genesisBlockHeader := by
        simpa [EvmYul.State.addAccessedAccount] using hRel.genesisBlockHeader }

theorem addAccessedStorageKey
    {left right : EvmYul.State EvmYul.OperationType.EVM}
    (hRel : StateDataRel left right)
    (storageKey : EvmYul.AccountAddress × Word) :
    StateDataRel (left.addAccessedStorageKey storageKey)
      (right.addAccessedStorageKey storageKey) := by
  exact
    { world := by
        apply OpenWorld.ext_of_fields
        · simpa [OpenWorld.ofEVMState, EvmYul.State.addAccessedStorageKey]
            using hRel.accounts
        · simp [OpenWorld.ofEVMState, EvmYul.State.addAccessedStorageKey,
            hRel.substate]
        · simpa [OpenWorld.ofEVMState, EvmYul.State.addAccessedStorageKey]
            using hRel.createdAccounts
      initialAccounts := by
        simpa [EvmYul.State.addAccessedStorageKey] using hRel.initialAccounts
      totalGasUsedInBlock := by
        simpa [EvmYul.State.addAccessedStorageKey]
          using hRel.totalGasUsedInBlock
      transactionReceipts := by
        simpa [EvmYul.State.addAccessedStorageKey]
          using hRel.transactionReceipts
      executionEnv := by
        simpa [EvmYul.State.addAccessedStorageKey] using hRel.executionEnv
      blocks := by simpa [EvmYul.State.addAccessedStorageKey] using hRel.blocks
      genesisBlockHeader := by
        simpa [EvmYul.State.addAccessedStorageKey]
          using hRel.genesisBlockHeader }

end StateDataRel

theorem stateReadCompatible_selfbalance :
    StateReadCompatible EvmYul.State.selfbalance := by
  intro left right hRel
  let owner := left.executionEnv.codeOwner
  have hOwner : right.executionEnv.codeOwner = owner := by
    simpa [owner] using congrArg EvmYul.ExecutionEnv.codeOwner
      hRel.executionEnv.symm
  rw [EvmYul.State.selfbalance, EvmYul.State.selfbalance, hOwner]
  simpa [OpenAccount.ofEVM] using
    hRel.accountElimValueEq owner (EvmYul.UInt256.ofNat 0)
      OpenAccount.balance

theorem stateUnaryCompatible_balance :
    StateUnaryCompatible EvmYul.State.balance := by
  intro left right value hRel
  let address := EvmYul.AccountAddress.ofUInt256 value
  constructor
  · exact hRel.addAccessedAccount address
  · simpa [EvmYul.State.balance, address, OpenAccount.ofEVM] using
      hRel.accountElimValueEq address (EvmYul.UInt256.ofNat 0)
        OpenAccount.balance

theorem stateUnaryCompatible_extCodeSize :
    StateUnaryCompatible EvmYul.State.extCodeSize := by
  intro left right value hRel
  let address := EvmYul.AccountAddress.ofUInt256 value
  constructor
  · exact hRel.addAccessedAccount address
  · simpa [EvmYul.State.extCodeSize, address, OpenAccount.ofEVM,
      EvmYul.State.accountCodeImage] using
      hRel.accountValueEq address (EvmYul.UInt256.ofNat 0)
        (fun account => EvmYul.UInt256.ofNat account.codeBytes.size)

theorem stateUnaryCompatible_extCodeHash :
    StateUnaryCompatible EvmYul.State.extCodeHash := by
  intro left right value hRel
  rw [← CodeErasedState.extCodeHash_evm,
    ← CodeErasedState.extCodeHash_evm]
  let address := EvmYul.AccountAddress.ofUInt256 value
  have hDead := hRel.dead_eq address
  have hHash :=
    hRel.accountValueEq address (EvmYul.UInt256.ofNat 0)
      (fun account =>
        EvmYul.UInt256.ofNat <| EvmYul.fromByteArrayBigEndian
          (ffi.KEC account.codeBytes))
  unfold CodeErasedState.extCodeHash
  dsimp only
  rw [hDead]
  by_cases h : CodeErasedState.dead right.accountMap address
  · simp [h, address]
    exact hRel.addAccessedAccount address
  · simp [h, address]
    constructor
    · exact hRel.addAccessedAccount address
    · simpa [address, OpenAccount.ofEVM,
        EvmYul.State.accountCodeImage] using hHash

theorem stateUnaryCompatible_sload :
    StateUnaryCompatible EvmYul.State.sload := by
  intro left right key hRel
  let owner := left.executionEnv.codeOwner
  have hOwner : right.executionEnv.codeOwner = owner := by
    simpa [owner] using congrArg EvmYul.ExecutionEnv.codeOwner
      hRel.executionEnv.symm
  unfold EvmYul.State.sload
  dsimp only
  rw [hOwner]
  constructor
  · exact hRel.addAccessedStorageKey (owner, key)
  · simpa [owner, OpenAccount.ofEVM, EvmYul.Account.lookupStorage] using
      hRel.accountValueEq owner (EvmYul.UInt256.ofNat 0)
        (fun account => account.storage.findD key (EvmYul.UInt256.ofNat 0))

theorem stateUnaryCompatible_tload :
    StateUnaryCompatible EvmYul.State.tload := by
  intro left right key hRel
  let owner := left.executionEnv.codeOwner
  have hOwner : right.executionEnv.codeOwner = owner := by
    simpa [owner] using congrArg EvmYul.ExecutionEnv.codeOwner
      hRel.executionEnv.symm
  unfold EvmYul.State.tload
  dsimp only
  rw [hOwner]
  constructor
  · exact hRel
  · simpa [owner, OpenAccount.ofEVM,
      EvmYul.Account.lookupTransientStorage] using
      hRel.accountValueEq owner (EvmYul.UInt256.ofNat 0)
        (fun account =>
          account.transientStorage.findD key (EvmYul.UInt256.ofNat 0))

namespace StateDataRel

theorem updateAccount
    {left right : EvmYul.State EvmYul.OperationType.EVM}
    (hRel : StateDataRel left right)
    (address : EvmYul.AccountAddress)
    (leftAccount rightAccount : EvmYul.Account EvmYul.OperationType.EVM)
    (hAccount : OpenAccount.ofEVM leftAccount = OpenAccount.ofEVM rightAccount) :
    StateDataRel (left.updateAccount address leftAccount)
      (right.updateAccount address rightAccount) := by
  exact
    { world := by
        apply OpenWorld.ext_of_fields
        · change
            ((left.accountMap.insert address leftAccount).mapVal
                fun _ account => OpenAccount.ofEVM account) =
              ((right.accountMap.insert address rightAccount).mapVal
                fun _ account => OpenAccount.ofEVM account)
          rw [OpenWorld.mapVal_insert, OpenWorld.mapVal_insert]
          have hAccounts := hRel.accounts
          change
            (left.accountMap.mapVal fun _ account => OpenAccount.ofEVM account) =
              (right.accountMap.mapVal fun _ account => OpenAccount.ofEVM account)
            at hAccounts
          rw [hAccounts, hAccount]
        · simpa [OpenWorld.ofEVMState, EvmYul.State.updateAccount]
            using hRel.substate
        · simpa [OpenWorld.ofEVMState, EvmYul.State.updateAccount]
            using hRel.createdAccounts
      initialAccounts := by
        simpa [EvmYul.State.updateAccount] using hRel.initialAccounts
      totalGasUsedInBlock := by
        simpa [EvmYul.State.updateAccount] using hRel.totalGasUsedInBlock
      transactionReceipts := by
        simpa [EvmYul.State.updateAccount] using hRel.transactionReceipts
      executionEnv := by
        simpa [EvmYul.State.updateAccount] using hRel.executionEnv
      blocks := by simpa [EvmYul.State.updateAccount] using hRel.blocks
      genesisBlockHeader := by
        simpa [EvmYul.State.updateAccount] using hRel.genesisBlockHeader }

theorem updateTransientStorageAccount
    {left right : EvmYul.Account EvmYul.OperationType.EVM}
    (hAccount : OpenAccount.ofEVM left = OpenAccount.ofEVM right)
    (key value : Word) :
    OpenAccount.ofEVM (left.updateTransientStorage key value) =
      OpenAccount.ofEVM (right.updateTransientStorage key value) := by
  rw [← OpenAccount.ofAccount_evm, ← OpenAccount.ofAccount_evm,
    OpenAccount.ofAccount_updateTransientStorage,
    OpenAccount.ofAccount_updateTransientStorage]
  rw [OpenAccount.ofAccount_evm, OpenAccount.ofAccount_evm, hAccount]
  have hStorage := congrArg OpenAccount.transientStorage hAccount
  change left.tstorage = right.tstorage at hStorage
  simp [hStorage]

theorem updateStorageAccount
    {left right : EvmYul.Account EvmYul.OperationType.EVM}
    (hAccount : OpenAccount.ofEVM left = OpenAccount.ofEVM right)
    (key value : Word) :
    OpenAccount.ofEVM (left.updateStorage key value) =
      OpenAccount.ofEVM (right.updateStorage key value) := by
  rw [← OpenAccount.ofAccount_evm, ← OpenAccount.ofAccount_evm,
    OpenAccount.ofAccount_updateStorage,
    OpenAccount.ofAccount_updateStorage]
  rw [OpenAccount.ofAccount_evm, OpenAccount.ofAccount_evm, hAccount]
  have hStorage := congrArg OpenAccount.storage hAccount
  change left.storage = right.storage at hStorage
  simp [hStorage]

theorem withRefundBalance
    {left right : EvmYul.State EvmYul.OperationType.EVM}
    (hRel : StateDataRel left right) (refundBalance : Word) :
    StateDataRel
      { left with substate.refundBalance := refundBalance }
      { right with substate.refundBalance := refundBalance } := by
  exact
    { world := by
        apply OpenWorld.ext_of_fields
        · simpa [OpenWorld.ofEVMState] using hRel.accounts
        · simp [OpenWorld.ofEVMState, hRel.substate]
        · simpa [OpenWorld.ofEVMState] using hRel.createdAccounts
      initialAccounts := by simpa using hRel.initialAccounts
      totalGasUsedInBlock := by simpa using hRel.totalGasUsedInBlock
      transactionReceipts := by simpa using hRel.transactionReceipts
      executionEnv := by simpa using hRel.executionEnv
      blocks := by simpa using hRel.blocks
      genesisBlockHeader := by simpa using hRel.genesisBlockHeader }

theorem tstore
    {left right : EvmYul.State EvmYul.OperationType.EVM}
    (hRel : StateDataRel left right) (key value : Word) :
    StateDataRel (left.tstore key value) (right.tstore key value) := by
  let owner := left.executionEnv.codeOwner
  have hRightOwner : right.executionEnv.codeOwner = owner := by
    simpa [owner] using congrArg EvmYul.ExecutionEnv.codeOwner
      hRel.executionEnv.symm
  unfold EvmYul.State.tstore
  dsimp only
  rw [hRightOwner]
  have hLookup := hRel.accountViews owner
  cases hLeft : left.lookupAccount owner with
  | none =>
      change left.accountMap.find? owner = none at hLeft
      rw [hLeft] at hLookup
      cases hRight : right.lookupAccount owner with
      | none => simpa [hLeft, hRight] using hRel
      | some rightAccount =>
          change right.accountMap.find? owner = some rightAccount at hRight
          rw [hRight] at hLookup
          simp at hLookup
  | some leftAccount =>
      change left.accountMap.find? owner = some leftAccount at hLeft
      rw [hLeft] at hLookup
      cases hRight : right.lookupAccount owner with
      | none =>
          change right.accountMap.find? owner = none at hRight
          rw [hRight] at hLookup
          simp at hLookup
      | some rightAccount =>
          change right.accountMap.find? owner = some rightAccount at hRight
          rw [hRight] at hLookup
          have hAccount : OpenAccount.ofEVM leftAccount =
              OpenAccount.ofEVM rightAccount := by
            simpa using Option.some.inj hLookup
          simpa [hLeft, hRight] using
            hRel.updateAccount owner
              (leftAccount.updateTransientStorage key value)
              (rightAccount.updateTransientStorage key value)
              (updateTransientStorageAccount hAccount key value)

theorem sstore
    {left right : EvmYul.State EvmYul.OperationType.EVM}
    (hRel : StateDataRel left right) (key value : Word) :
    StateDataRel (left.sstore key value) (right.sstore key value) := by
  let owner := left.executionEnv.codeOwner
  have hRightOwner : right.executionEnv.codeOwner = owner := by
    simpa [owner] using congrArg EvmYul.ExecutionEnv.codeOwner
      hRel.executionEnv.symm
  have hCurrent :
      CodeErasedState.currentStorageValue left owner key =
        CodeErasedState.currentStorageValue right owner key := by
    have hLookup := hRel.accountViews owner
    cases hLeft : left.accountMap.find? owner with
    | none =>
        rw [hLeft] at hLookup
        cases hRight : right.accountMap.find? owner with
        | none =>
            simp [CodeErasedState.currentStorageValue,
              Batteries.RBMap.find!, hLeft, hRight]
        | some rightAccount => simp [hRight] at hLookup
    | some leftAccount =>
        rw [hLeft] at hLookup
        cases hRight : right.accountMap.find? owner with
        | none => simp [hRight] at hLookup
        | some rightAccount =>
            rw [hRight] at hLookup
            have hAccount : OpenAccount.ofEVM leftAccount =
                OpenAccount.ofEVM rightAccount := by
              simpa using Option.some.inj hLookup
            have hStorage := congrArg OpenAccount.storage hAccount
            change leftAccount.storage = rightAccount.storage at hStorage
            simp [CodeErasedState.currentStorageValue,
              Batteries.RBMap.find!, hLeft, hRight, hStorage]
  have hInitial :
      CodeErasedState.initialStorageValue left owner key =
        CodeErasedState.initialStorageValue right owner key := by
    simp [CodeErasedState.initialStorageValue, hRel.initialAccounts]
  have hRefund :
      left.substate.refundBalance = right.substate.refundBalance := by
    simpa using congrArg EvmYul.Substate.refundBalance hRel.substate
  rw [CodeErasedState.sstore_eq, CodeErasedState.sstore_eq, hRightOwner]
  let newRefund : Word :=
    CodeErasedState.sstoreRefundBalance
      (CodeErasedState.initialStorageValue left owner key)
      (CodeErasedState.currentStorageValue left owner key)
      value left.substate.refundBalance
  have hNewRefund :
      newRefund =
        CodeErasedState.sstoreRefundBalance
          (CodeErasedState.initialStorageValue right owner key)
          (CodeErasedState.currentStorageValue right owner key)
          value right.substate.refundBalance := by
    simp [newRefund, hInitial, hCurrent, hRefund]
  change
    StateDataRel
      ((left.lookupAccount owner).option left
        (fun account =>
          { (left.setAccount owner (account.updateStorage key value)
              |>.addAccessedStorageKey (owner, key)) with
            substate.refundBalance := newRefund }))
      ((right.lookupAccount owner).option right
        (fun account =>
          { (right.setAccount owner (account.updateStorage key value)
              |>.addAccessedStorageKey (owner, key)) with
            substate.refundBalance :=
              CodeErasedState.sstoreRefundBalance
                (CodeErasedState.initialStorageValue right owner key)
                (CodeErasedState.currentStorageValue right owner key)
                value right.substate.refundBalance }))
  rw [← hNewRefund]
  have hLookup := hRel.accountViews owner
  cases hLeft : left.lookupAccount owner with
  | none =>
      change left.accountMap.find? owner = none at hLeft
      rw [hLeft] at hLookup
      cases hRight : right.lookupAccount owner with
      | none => simpa [hLeft, hRight] using hRel
      | some rightAccount =>
          change right.accountMap.find? owner = some rightAccount at hRight
          rw [hRight] at hLookup
          simp at hLookup
  | some leftAccount =>
      change left.accountMap.find? owner = some leftAccount at hLeft
      rw [hLeft] at hLookup
      cases hRight : right.lookupAccount owner with
      | none =>
          change right.accountMap.find? owner = none at hRight
          rw [hRight] at hLookup
          simp at hLookup
      | some rightAccount =>
          change right.accountMap.find? owner = some rightAccount at hRight
          rw [hRight] at hLookup
          have hAccount : OpenAccount.ofEVM leftAccount =
              OpenAccount.ofEVM rightAccount := by
            simpa using Option.some.inj hLookup
          have hUpdated :=
            hRel.updateAccount owner
              (leftAccount.updateStorage key value)
              (rightAccount.updateStorage key value)
              (updateStorageAccount hAccount key value)
          have hAccessed := hUpdated.addAccessedStorageKey (owner, key)
          simpa [hLeft, hRight, EvmYul.State.setAccount] using
            hAccessed.withRefundBalance newRefund

end StateDataRel

theorem stateBinaryCompatible_tstore :
    StateBinaryCompatible EvmYul.State.tstore := by
  intro left right key value hRel
  exact hRel.tstore key value

theorem stateBinaryCompatible_sstore :
    StateBinaryCompatible EvmYul.State.sstore := by
  intro left right key value hRel
  exact hRel.sstore key value

def SharedQuaternaryCompatible
    (f : EvmYul.SharedState EvmYul.OperationType.EVM → Word → Word → Word →
      Word → EvmYul.SharedState EvmYul.OperationType.EVM) : Prop :=
  ∀ {left right} (a b c d : Word),
    SharedDataRel left right →
      SharedDataRel (f left a b c d) (f right a b c d)

theorem openCompatible_quaternaryCopy
    {f : EvmYul.SharedState EvmYul.OperationType.EVM → Word → Word → Word →
      Word → EvmYul.SharedState EvmYul.OperationType.EVM}
    (hCompatible : SharedQuaternaryCompatible f) :
    OpenCompatibleStep (.quaternaryCopy f) := by
  intro left right leftNext hRel hLeft
  have hStack := hRel.stack_eq
  cases hPop : right.stack.pop4 with
  | none =>
      have hLeftPop : left.stack.pop4 = none := by simpa [hStack]
      simp [PrimStep.run, EvmYul.EVM.quaternaryCopyOp, hLeftPop] at hLeft
  | some values =>
      rcases values with ⟨rest, a, b, c, d⟩
      have hLeftPop : left.stack.pop4 = some (rest, a, b, c, d) := by
        simpa [hStack] using hPop
      simp [PrimStep.run, EvmYul.EVM.quaternaryCopyOp, hLeftPop] at hLeft
      simp only [Id.run, Except.ok.injEq] at hLeft
      subst leftNext
      let leftShared := f left.toSharedState a b c d
      let rightShared := f right.toSharedState a b c d
      have hShared : SharedDataRel leftShared rightShared :=
        hCompatible a b c d hRel.sharedDataRel
      let rightState : EVMState := { right with toSharedState := rightShared }
      refine ⟨rightState.replaceStackAndIncrPC rest, ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.quaternaryCopyOp, hPop,
          rightState, rightShared]
        rfl
      · apply OpenStateRel.replaceStackAndIncrPC
          (hRel.withSharedState hShared)
        rfl

theorem sharedQuaternaryCompatible_extCodeCopy :
    SharedQuaternaryCompatible EvmYul.SharedState.extCodeCopy' := by
  intro left right account destination readStart size hRel
  let address := EvmYul.AccountAddress.ofUInt256 account
  have hCode :
      (left.lookupAccount address).option ByteArray.empty
          EvmYul.State.accountCodeImage =
        (right.lookupAccount address).option ByteArray.empty
          EvmYul.State.accountCodeImage := by
    simpa [EvmYul.State.lookupAccount, OpenAccount.ofEVM,
      EvmYul.State.accountCodeImage] using
      hRel.state.accountValueEq address ByteArray.empty OpenAccount.codeBytes
  have hState := hRel.state.addAccessedAccount address
  constructor
  · simpa [EvmYul.SharedState.extCodeCopy',
      EvmYul.State.addAccessedAccount, address] using hState
  · cases left
    cases right
    rcases hRel.machine with ⟨hActive, hMemory, hReturn, hHReturn⟩
    simp [EvmYul.SharedState.extCodeCopy', address] at hCode ⊢
    simp_all
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem SharedDataRel.logOp
    {left right : EvmYul.SharedState EvmYul.OperationType.EVM}
    (hRel : SharedDataRel left right)
    (offset size : Word) (topics : Array Word) :
    SharedDataRel
      (EvmYul.SharedState.logOp offset size topics left)
      (EvmYul.SharedState.logOp offset size topics right) := by
  constructor
  · exact
      { world := by
          apply OpenWorld.ext_of_fields
          · simpa [OpenWorld.ofEVMState, EvmYul.SharedState.logOp]
              using hRel.state.accounts
          · simp [OpenWorld.ofEVMState, EvmYul.SharedState.logOp,
              hRel.state.substate, hRel.state.executionEnv,
              hRel.machine.memory]
          · simpa [OpenWorld.ofEVMState, EvmYul.SharedState.logOp]
              using hRel.state.createdAccounts
        initialAccounts := by
          simpa [EvmYul.SharedState.logOp] using hRel.state.initialAccounts
        totalGasUsedInBlock := by
          simpa [EvmYul.SharedState.logOp]
            using hRel.state.totalGasUsedInBlock
        transactionReceipts := by
          simpa [EvmYul.SharedState.logOp]
            using hRel.state.transactionReceipts
        executionEnv := by
          simpa [EvmYul.SharedState.logOp] using hRel.state.executionEnv
        blocks := by simpa [EvmYul.SharedState.logOp] using hRel.state.blocks
        genesisBlockHeader := by
          simpa [EvmYul.SharedState.logOp]
            using hRel.state.genesisBlockHeader }
  · cases left
    cases right
    rcases hRel.machine with ⟨hActive, hMemory, hReturn, hHReturn⟩
    simp [EvmYul.SharedState.logOp] at hActive hMemory hReturn hHReturn ⊢
    simp_all
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem openCompatible_log0 : OpenCompatibleStep .log0 := by
  intro left right leftNext hRel hLeft
  have hStack := hRel.stack_eq
  have hEnv := hRel.executionEnv_eq
  cases hPerm : right.executionEnv.perm with
  | false =>
      have hLeftPerm : left.executionEnv.perm = false := by simpa [hEnv]
      simp [PrimStep.run, hLeftPerm] at hLeft
  | true =>
      have hLeftPerm : left.executionEnv.perm = true := by simpa [hEnv]
      cases hPop : right.stack.pop2 with
      | none =>
          have hLeftPop : left.stack.pop2 = none := by simpa [hStack]
          simp [PrimStep.run, hLeftPerm, hLeftPop] at hLeft
      | some values =>
          rcases values with ⟨rest, offset, size⟩
          have hLeftPop : left.stack.pop2 = some (rest, offset, size) := by
            simpa [hStack] using hPop
          simp [PrimStep.run, hLeftPerm, hLeftPop] at hLeft
          subst leftNext
          let leftShared :=
            EvmYul.SharedState.logOp offset size #[] left.toSharedState
          let rightShared :=
            EvmYul.SharedState.logOp offset size #[] right.toSharedState
          have hShared : SharedDataRel leftShared rightShared :=
            hRel.sharedDataRel.logOp offset size #[]
          let rightState : EVMState := { right with toSharedState := rightShared }
          refine ⟨rightState.replaceStackAndIncrPC rest, ?_, ?_⟩
          · simp [PrimStep.run, hPerm, hPop, rightState, rightShared]
          · apply OpenStateRel.replaceStackAndIncrPC
              (hRel.withSharedState hShared)
            rfl

theorem openCompatible_log1 : OpenCompatibleStep .log1 := by
  intro left right leftNext hRel hLeft
  have hStack := hRel.stack_eq
  have hEnv := hRel.executionEnv_eq
  cases hPerm : right.executionEnv.perm with
  | false =>
      have hLeftPerm : left.executionEnv.perm = false := by simpa [hEnv]
      simp [PrimStep.run, hLeftPerm] at hLeft
  | true =>
      have hLeftPerm : left.executionEnv.perm = true := by simpa [hEnv]
      cases hPop : right.stack.pop3 with
      | none =>
          have hLeftPop : left.stack.pop3 = none := by simpa [hStack]
          simp [PrimStep.run, hLeftPerm, hLeftPop] at hLeft
      | some values =>
          rcases values with ⟨rest, offset, size, topic1⟩
          have hLeftPop : left.stack.pop3 =
              some (rest, offset, size, topic1) := by
            simpa [hStack] using hPop
          simp [PrimStep.run, hLeftPerm, hLeftPop] at hLeft
          subst leftNext
          let leftShared :=
            EvmYul.SharedState.logOp offset size #[topic1] left.toSharedState
          let rightShared :=
            EvmYul.SharedState.logOp offset size #[topic1] right.toSharedState
          have hShared : SharedDataRel leftShared rightShared :=
            hRel.sharedDataRel.logOp offset size #[topic1]
          let rightState : EVMState := { right with toSharedState := rightShared }
          refine ⟨rightState.replaceStackAndIncrPC rest, ?_, ?_⟩
          · simp [PrimStep.run, hPerm, hPop, rightState, rightShared]
          · apply OpenStateRel.replaceStackAndIncrPC
              (hRel.withSharedState hShared)
            rfl

theorem openCompatible_log2 : OpenCompatibleStep .log2 := by
  intro left right leftNext hRel hLeft
  have hStack := hRel.stack_eq
  have hEnv := hRel.executionEnv_eq
  cases hPerm : right.executionEnv.perm with
  | false =>
      have hLeftPerm : left.executionEnv.perm = false := by simpa [hEnv]
      simp [PrimStep.run, hLeftPerm] at hLeft
  | true =>
      have hLeftPerm : left.executionEnv.perm = true := by simpa [hEnv]
      cases hPop : right.stack.pop4 with
      | none =>
          have hLeftPop : left.stack.pop4 = none := by simpa [hStack]
          simp [PrimStep.run, hLeftPerm, hLeftPop] at hLeft
      | some values =>
          rcases values with ⟨rest, offset, size, topic1, topic2⟩
          have hLeftPop : left.stack.pop4 =
              some (rest, offset, size, topic1, topic2) := by
            simpa [hStack] using hPop
          simp [PrimStep.run, hLeftPerm, hLeftPop] at hLeft
          subst leftNext
          let leftShared := EvmYul.SharedState.logOp
            offset size #[topic1, topic2] left.toSharedState
          let rightShared := EvmYul.SharedState.logOp
            offset size #[topic1, topic2] right.toSharedState
          have hShared : SharedDataRel leftShared rightShared :=
            hRel.sharedDataRel.logOp offset size #[topic1, topic2]
          let rightState : EVMState := { right with toSharedState := rightShared }
          refine ⟨rightState.replaceStackAndIncrPC rest, ?_, ?_⟩
          · simp [PrimStep.run, hPerm, hPop, rightState, rightShared]
          · apply OpenStateRel.replaceStackAndIncrPC
              (hRel.withSharedState hShared)
            rfl

theorem openCompatible_log3 : OpenCompatibleStep .log3 := by
  intro left right leftNext hRel hLeft
  have hStack := hRel.stack_eq
  have hEnv := hRel.executionEnv_eq
  cases hPerm : right.executionEnv.perm with
  | false =>
      have hLeftPerm : left.executionEnv.perm = false := by simpa [hEnv]
      simp [PrimStep.run, hLeftPerm] at hLeft
  | true =>
      have hLeftPerm : left.executionEnv.perm = true := by simpa [hEnv]
      cases hPop : right.stack.pop5 with
      | none =>
          have hLeftPop : left.stack.pop5 = none := by simpa [hStack]
          simp [PrimStep.run, hLeftPerm, hLeftPop] at hLeft
      | some values =>
          rcases values with ⟨rest, offset, size, topic1, topic2, topic3⟩
          have hLeftPop : left.stack.pop5 =
              some (rest, offset, size, topic1, topic2, topic3) := by
            simpa [hStack] using hPop
          simp [PrimStep.run, hLeftPerm, hLeftPop] at hLeft
          subst leftNext
          let leftShared := EvmYul.SharedState.logOp
            offset size #[topic1, topic2, topic3] left.toSharedState
          let rightShared := EvmYul.SharedState.logOp
            offset size #[topic1, topic2, topic3] right.toSharedState
          have hShared : SharedDataRel leftShared rightShared :=
            hRel.sharedDataRel.logOp offset size #[topic1, topic2, topic3]
          let rightState : EVMState := { right with toSharedState := rightShared }
          refine ⟨rightState.replaceStackAndIncrPC rest, ?_, ?_⟩
          · simp [PrimStep.run, hPerm, hPop, rightState, rightShared]
          · apply OpenStateRel.replaceStackAndIncrPC
              (hRel.withSharedState hShared)
            rfl

theorem openCompatible_log4 : OpenCompatibleStep .log4 := by
  intro left right leftNext hRel hLeft
  have hStack := hRel.stack_eq
  have hEnv := hRel.executionEnv_eq
  cases hPerm : right.executionEnv.perm with
  | false =>
      have hLeftPerm : left.executionEnv.perm = false := by simpa [hEnv]
      simp [PrimStep.run, hLeftPerm] at hLeft
  | true =>
      have hLeftPerm : left.executionEnv.perm = true := by simpa [hEnv]
      cases hPop : right.stack.pop6 with
      | none =>
          have hLeftPop : left.stack.pop6 = none := by simpa [hStack]
          simp [PrimStep.run, hLeftPerm, hLeftPop] at hLeft
      | some values =>
          rcases values with
            ⟨rest, offset, size, topic1, topic2, topic3, topic4⟩
          have hLeftPop : left.stack.pop6 =
              some (rest, offset, size, topic1, topic2, topic3, topic4) := by
            simpa [hStack] using hPop
          simp [PrimStep.run, hLeftPerm, hLeftPop] at hLeft
          subst leftNext
          let leftShared := EvmYul.SharedState.logOp
            offset size #[topic1, topic2, topic3, topic4] left.toSharedState
          let rightShared := EvmYul.SharedState.logOp
            offset size #[topic1, topic2, topic3, topic4] right.toSharedState
          have hShared : SharedDataRel leftShared rightShared :=
            hRel.sharedDataRel.logOp
              offset size #[topic1, topic2, topic3, topic4]
          let rightState : EVMState := { right with toSharedState := rightShared }
          refine ⟨rightState.replaceStackAndIncrPC rest, ?_, ?_⟩
          · simp [PrimStep.run, hPerm, hPop, rightState, rightShared]
          · apply OpenStateRel.replaceStackAndIncrPC
              (hRel.withSharedState hShared)
            rfl

inductive FrameLocalStep : PrimStep → Prop where
  | pure {step : PrimStep} (hPure : PureStackStep step) :
      FrameLocalStep step
  | executionEnv
      (f : EvmYul.ExecutionEnv EvmYul.OperationType.EVM → Word) :
      FrameLocalStep (.executionEnv f)
  | unaryExecutionEnv
      (f : EvmYul.ExecutionEnv EvmYul.OperationType.EVM → Word → Word) :
      FrameLocalStep (.unaryExecutionEnv f)
  | balance : FrameLocalStep (.unaryState EvmYul.State.balance)
  | calldataload :
      FrameLocalStep
        (.unaryState
          (fun state value => (state, EvmYul.State.calldataload state value)))
  | calldatacopy :
      FrameLocalStep (.ternaryCopy EvmYul.SharedState.calldatacopy)
  | codecopy : FrameLocalStep (.ternaryCopy EvmYul.SharedState.codeCopy)
  | extcodesize : FrameLocalStep (.unaryState EvmYul.State.extCodeSize)
  | extcodecopy :
      FrameLocalStep (.quaternaryCopy EvmYul.SharedState.extCodeCopy')
  | extcodehash : FrameLocalStep (.unaryState EvmYul.State.extCodeHash)
  | blockhash :
      FrameLocalStep
        (.unaryState (fun state value => (state, EvmYul.State.blockHash state value)))
  | coinbase :
      FrameLocalStep
        (.state (.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase))
  | timestamp : FrameLocalStep (.state EvmYul.State.timeStamp)
  | number : FrameLocalStep (.state EvmYul.State.number)
  | gaslimit : FrameLocalStep (.state EvmYul.State.gasLimit)
  | chainid : FrameLocalStep (.state EvmYul.State.chainId)
  | selfbalance : FrameLocalStep (.state EvmYul.State.selfbalance)
  | returndatasize :
      FrameLocalStep (.machineState EvmYul.MachineState.returndatasize)
  | mload : FrameLocalStep .mload
  | returndatacopy : FrameLocalStep .returndatacopy
  | mstore :
      FrameLocalStep (.binaryMachineState EvmYul.MachineState.mstore)
  | sload : FrameLocalStep (.unaryState EvmYul.State.sload)
  | sstore : FrameLocalStep (.binaryState EvmYul.State.sstore)
  | mstore8 :
      FrameLocalStep (.binaryMachineState EvmYul.MachineState.mstore8)
  | mcopy :
      FrameLocalStep (.ternaryMachineState EvmYul.MachineState.mcopy)
  | tload : FrameLocalStep (.unaryState EvmYul.State.tload)
  | tstore : FrameLocalStep (.binaryState EvmYul.State.tstore)
  | keccak256 :
      FrameLocalStep
        (.binaryMachineStateWithResult EvmYul.MachineState.keccak256)
  | log0 : FrameLocalStep .log0
  | log1 : FrameLocalStep .log1
  | log2 : FrameLocalStep .log2
  | log3 : FrameLocalStep .log3
  | log4 : FrameLocalStep .log4

theorem FrameLocalStep.openCompatible
    {step : PrimStep} (hLocal : FrameLocalStep step) :
    OpenCompatibleStep step := by
  cases hLocal with
  | pure hPure => exact hPure.openCompatible
  | executionEnv f => exact openCompatible_executionEnv f
  | unaryExecutionEnv f => exact openCompatible_unaryExecutionEnv f
  | balance => exact openCompatible_unaryState stateUnaryCompatible_balance
  | calldataload =>
      exact openCompatible_unaryState
        (stateUnaryCompatible_of_read stateUnaryReadCompatible_calldataload)
  | calldatacopy =>
      exact openCompatible_ternaryCopy sharedTernaryCompatible_calldatacopy
  | codecopy => exact openCompatible_ternaryCopy sharedTernaryCompatible_codeCopy
  | extcodesize =>
      exact openCompatible_unaryState stateUnaryCompatible_extCodeSize
  | extcodecopy =>
      exact openCompatible_quaternaryCopy sharedQuaternaryCompatible_extCodeCopy
  | extcodehash =>
      exact openCompatible_unaryState stateUnaryCompatible_extCodeHash
  | blockhash =>
      exact openCompatible_unaryState
        (stateUnaryCompatible_of_read stateUnaryReadCompatible_blockHash)
  | coinbase => exact openCompatible_state stateReadCompatible_coinBase
  | timestamp => exact openCompatible_state stateReadCompatible_timeStamp
  | number => exact openCompatible_state stateReadCompatible_number
  | gaslimit => exact openCompatible_state stateReadCompatible_gasLimit
  | chainid => exact openCompatible_state stateReadCompatible_chainId
  | selfbalance => exact openCompatible_state stateReadCompatible_selfbalance
  | returndatasize =>
      exact openCompatible_machineState machineReadCompatible_returndatasize
  | mload => exact openCompatible_mload machineUnaryResultCompatible_mload
  | returndatacopy =>
      exact openCompatible_returndatacopy
        machineTernaryCompatible_returndatacopy
  | mstore =>
      exact openCompatible_binaryMachineState machineBinaryCompatible_mstore
  | sload => exact openCompatible_unaryState stateUnaryCompatible_sload
  | sstore => exact openCompatible_binaryState stateBinaryCompatible_sstore
  | mstore8 =>
      exact openCompatible_binaryMachineState machineBinaryCompatible_mstore8
  | mcopy =>
      exact openCompatible_ternaryMachineState machineTernaryCompatible_mcopy
  | tload => exact openCompatible_unaryState stateUnaryCompatible_tload
  | tstore => exact openCompatible_binaryState stateBinaryCompatible_tstore
  | keccak256 =>
      exact openCompatible_binaryMachineStateWithResult
        machineBinaryResultCompatible_keccak256
  | log0 => exact openCompatible_log0
  | log1 => exact openCompatible_log1
  | log2 => exact openCompatible_log2
  | log3 => exact openCompatible_log3
  | log4 => exact openCompatible_log4

def PureStackPrimOp : PrimOp → Prop
  | .add | .mul | .sub | .div | .sdiv | .mod | .smod | .addmod | .mulmod
  | .exp | .signextend | .lt | .gt | .slt | .sgt | .eq | .iszero
  | .and | .or | .xor | .not | .byte | .shl | .shr | .sar
  | .pop
  | .dup1 | .dup2 | .dup3 | .dup4 | .dup5 | .dup6 | .dup7 | .dup8
  | .dup9 | .dup10 | .dup11 | .dup12 | .dup13 | .dup14 | .dup15 | .dup16
  | .swap1 | .swap2 | .swap3 | .swap4 | .swap5 | .swap6 | .swap7 | .swap8
  | .swap9 | .swap10 | .swap11 | .swap12 | .swap13 | .swap14 | .swap15
  | .swap16 => True
  | _ => False

def ProtectedPrimOp : PrimOp → Prop
  | .address | .origin | .caller | .callvalue | .calldataload
  | .calldatasize | .calldatacopy | .codesize | .codecopy | .gasprice
  | .returndatasize | .returndatacopy | .blockhash | .coinbase | .timestamp
  | .number | .prevrandao | .gaslimit | .chainid | .basefee | .blobhash
  | .blobbasefee | .mload | .mstore | .mstore8 | .mcopy | .keccak256 => True
  | _ => False

def WorldPrimOp : PrimOp → Prop
  | .balance | .extcodesize | .extcodecopy | .extcodehash | .selfbalance
  | .sload | .sstore | .tload | .tstore
  | .log0 | .log1 | .log2 | .log3 | .log4 => True
  | _ => False

def FrameLocalPrimOp (op : PrimOp) : Prop :=
  PureStackPrimOp op ∨ ProtectedPrimOp op ∨ WorldPrimOp op

theorem pureStackStep_of_continuingStep
    {op : PrimOp} {step : PrimStep}
    (hPure : PureStackPrimOp op)
    (hStep : op.continuingStep? = some step) :
    FrameLocalStep step := by
  cases op <;>
    simp [PureStackPrimOp, PrimOp.continuingStep?] at hPure hStep
  all_goals cases hStep
  all_goals first
    | exact .pure (.bin _)
    | exact .pure (.un _)
    | exact .pure (.tri _)
    | exact .pure .pop
    | exact .pure (.dup _)
    | exact .pure (.swap _)

theorem protectedStep_of_continuingStep
    {op : PrimOp} {step : PrimStep}
    (hProtected : ProtectedPrimOp op)
    (hStep : op.continuingStep? = some step) :
    FrameLocalStep step := by
  cases op <;>
    simp [ProtectedPrimOp, PrimOp.continuingStep?] at hProtected hStep
  all_goals cases hStep
  all_goals first
    | exact .executionEnv _
    | exact .unaryExecutionEnv _
    | exact .calldataload
    | exact .calldatacopy
    | exact .codecopy
    | exact .blockhash
    | exact .coinbase
    | exact .timestamp
    | exact .number
    | exact .gaslimit
    | exact .chainid
    | exact .returndatasize
    | exact .returndatacopy
    | exact .mload
    | exact .mstore
    | exact .mstore8
    | exact .mcopy
    | exact .keccak256

theorem worldStep_of_continuingStep
    {op : PrimOp} {step : PrimStep}
    (hWorld : WorldPrimOp op)
    (hStep : op.continuingStep? = some step) :
    FrameLocalStep step := by
  cases op <;>
    simp [WorldPrimOp, PrimOp.continuingStep?] at hWorld hStep
  all_goals cases hStep
  all_goals first
    | exact .balance
    | exact .extcodesize
    | exact .extcodecopy
    | exact .extcodehash
    | exact .selfbalance
    | exact .sload
    | exact .sstore
    | exact .tload
    | exact .tstore
    | exact .log0
    | exact .log1
    | exact .log2
    | exact .log3
    | exact .log4

theorem frameLocalStep_of_continuingStep
    {op : PrimOp} {step : PrimStep}
    (hLocal : FrameLocalPrimOp op)
    (hStep : op.continuingStep? = some step) :
    FrameLocalStep step := by
  rcases hLocal with hPure | hProtected | hWorld
  · exact pureStackStep_of_continuingStep hPure hStep
  · exact protectedStep_of_continuingStep hProtected hStep
  · exact worldStep_of_continuingStep hWorld hStep

theorem frameLocalPrimOp_of_continuingStep
    {op : PrimOp} {step : PrimStep}
    (hStep : op.continuingStep? = some step)
    (hMsize : op ≠ .msize) (hInvalid : op ≠ .invalid) :
    FrameLocalPrimOp op := by
  cases op <;>
    simp [FrameLocalPrimOp, PureStackPrimOp, ProtectedPrimOp, WorldPrimOp,
      PrimOp.continuingStep?] at hStep hMsize hInvalid ⊢

theorem continuingPrim_open_success_rel_of_compatible
    {op : PrimOp} {step : PrimStep}
    {gasful openState gasfulNext : EVMState}
    (hStep : op.continuingStep? = some step)
    (hCompatible : OpenCompatibleStep step)
    (hRel : OpenStateRel gasful openState)
    (hGasful :
      op.step (afterEVMInstructionChargeAt gasful) = .ok gasfulNext) :
    ∃ openNext,
      op.step openState = .ok openNext ∧
        OpenStateRel gasfulNext openNext := by
  rw [PrimOp.step_eq_continuingStep_run hStep] at hGasful ⊢
  exact hCompatible
    (afterEVMInstructionChargeAt_openStateRel_left hRel) hGasful

theorem continuingPrim_open_success_rel_of_pureStack
    {op : PrimOp} {step : PrimStep}
    {gasful openState gasfulNext : EVMState}
    (hStep : op.continuingStep? = some step)
    (hPure : PureStackStep step)
    (hRel : OpenStateRel gasful openState)
    (hGasful :
      op.step (afterEVMInstructionChargeAt gasful) = .ok gasfulNext) :
    ∃ openNext,
      op.step openState = .ok openNext ∧
        OpenStateRel gasfulNext openNext := by
  exact continuingPrim_open_success_rel_of_compatible
    hStep hPure.openCompatible hRel hGasful

theorem continuingStep_stackArity?_exists
    {op : PrimOp} {step : PrimStep}
    (hStep : op.continuingStep? = some step) :
    ∃ arity, op.stackArity? = some arity := by
  cases op <;>
    simp [PrimOp.continuingStep?, PrimOp.stackArity?] at hStep ⊢

theorem continuingStep_not_pc
    {op : PrimOp} {step : PrimStep}
    (hStep : op.continuingStep? = some step) :
    op ≠ .pc := by
  intro hPc
  subst op
  simp [PrimOp.continuingStep?] at hStep

theorem continuingStep_not_gas
    {op : PrimOp} {step : PrimStep}
    (hStep : op.continuingStep? = some step) :
    op ≠ .gas := by
  intro hGas
  subst op
  simp [PrimOp.continuingStep?] at hStep

theorem continuingStep_not_externalCallCreate
    {op : PrimOp} {step : PrimStep}
    (hStep : op.continuingStep? = some step) :
    op.isExternalCallCreate = false := by
  cases op <;>
    simp [PrimOp.continuingStep?, PrimOp.isExternalCallCreate] at hStep ⊢

theorem continuingStep_toEVM_isCreate_false
    {op : PrimOp} {step : PrimStep}
    (hStep : op.continuingStep? = some step) :
    EvmYul.Operation.isCreate op.toEVM = false := by
  cases op <;>
    simp [PrimOp.continuingStep?, PrimOp.toEVM,
      EvmYul.Operation.isCreate] at hStep ⊢

theorem continuingStep_haltKind?_none
    {op : PrimOp} {step : PrimStep}
    (hStep : op.continuingStep? = some step) :
    op.haltKind? = none := by
  cases op <;>
    simp [PrimOp.continuingStep?, PrimOp.haltKind?] at hStep ⊢

theorem haltOutputAt_none_of_continuingStep
    {op : PrimOp} {step : PrimStep} (state : EVMState)
    (hStep : op.continuingStep? = some step) :
    haltOutputAt state op.toEVM = none := by
  cases op <;>
    simp [PrimOp.continuingStep?, PrimOp.toEVM, haltOutputAt] at hStep ⊢

theorem continuingPrim_open_success_after_charges
    {op : PrimOp} {step : PrimStep} {state gasfulNext : EVMState}
    (hStep : op.continuingStep? = some step)
    (hMsize : op ≠ .msize)
    (hGasful :
      op.step (afterEVMInstructionChargeAt state) = .ok gasfulNext) :
    ∃ openNext,
      op.step (afterDynamicChargeAt state) = .ok openNext ∧
        SameData gasfulNext openNext := by
  have hRel :=
    sameRuntimeData_afterEVMInstructionCharge_afterDynamic state
  have hMap :=
    PrimOp.step_map_eraseRuntimeControl
      (op := op)
      (target := afterEVMInstructionChargeAt state)
      (source := afterDynamicChargeAt state)
      (continuingStep_stackArity?_exists hStep)
      (continuingStep_not_pc hStep)
      (continuingStep_not_externalCallCreate hStep)
      hRel
  rw [hGasful] at hMap
  cases hOpen : op.step (afterDynamicChargeAt state) with
  | error err =>
      simp [hOpen, Except.map] at hMap
  | ok openNext =>
      have hSameRuntime : SameRuntimeData gasfulNext openNext := by
        simpa [hOpen, Except.map] using hMap
      exact ⟨openNext, rfl, SameRuntimeData.sameData hSameRuntime⟩

theorem raw_continuing_prim_executes_after_charges
    {op : PrimOp} {step : PrimStep}
    {bytes : ByteArray} {pc : Nat} {state openNext : EVMState}
    (hStep : op.continuingStep? = some step)
    (hMsize : op ≠ .msize)
    (hDecode : Compact.decodeAt bytes pc (.prim op))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc)
    (hOpen : op.step (afterDynamicChargeAt state) = .ok openNext) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      []
      (.ok (.running openNext)) := by
  have hGas := continuingStep_not_gas hStep
  have hClosed :
      Assembly.InteractionSemantics.PrimOp.openStep op
          (afterDynamicChargeAt state) =
        Simulation.Interaction.done (.ok openNext) := by
    rw [Assembly.InteractionSemantics.PrimOp.openStep_closed
      (Assembly.InteractionSemantics.PrimOp.externalKind_none_of_continuingStep
        hStep)
      hGas hMsize]
    simp [hOpen]
  have hHalt := continuingStep_haltKind?_none hStep
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim op) trivial hDecode hPc]
  simpa [Compact.Instr.openStepResult, Compact.Instr.openStep,
    Assembly.InteractionSemantics.Target.openStepInstrResult,
    Assembly.Target.stepInstrResultWith,
    Assembly.InteractionSemantics.Target.openStepInstr,
    Assembly.Target.stepInstrWith, hClosed, hHalt,
    Simulation.Interaction.bind, Simulation.Interaction.pure,
    Compact.Instr.haltKind?] using
    (Interaction.Executes.done (.ok (StepResult.running openNext)))

theorem raw_continuing_prim_executes_at
    {op : PrimOp} {step : PrimStep}
    {bytes : ByteArray} {pc : Nat} {state openNext : EVMState}
    (hStep : op.continuingStep? = some step)
    (hMsize : op ≠ .msize)
    (hDecode : Compact.decodeAt bytes pc (.prim op))
    (hPc : state.pc = EvmYul.UInt256.ofNat pc)
    (hOpen : op.step state = .ok openNext) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult bytes 1 state)
      [] (.ok (.running openNext)) := by
  have hGas := continuingStep_not_gas hStep
  have hClosed :
      Assembly.InteractionSemantics.PrimOp.openStep op state =
        Simulation.Interaction.done (.ok openNext) := by
    rw [Assembly.InteractionSemantics.PrimOp.openStep_closed
      (Assembly.InteractionSemantics.PrimOp.externalKind_none_of_continuingStep
        hStep)
      hGas hMsize]
    simp [hOpen]
  have hHalt := continuingStep_haltKind?_none hStep
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim op) trivial hDecode hPc]
  simpa [Compact.Instr.openStepResult, Compact.Instr.openStep,
    Assembly.InteractionSemantics.Target.openStepInstrResult,
    Assembly.Target.stepInstrResultWith,
    Assembly.InteractionSemantics.Target.openStepInstr,
    Assembly.Target.stepInstrWith, hClosed, hHalt,
    Simulation.Interaction.bind, Simulation.Interaction.pure,
    Compact.Instr.haltKind?] using
    (Interaction.Executes.done (.ok (StepResult.running openNext)))

theorem raw_continuing_prim_refines_step_after_charges
    {op : PrimOp} {step : PrimStep}
    {bytes : ByteArray} {pc : Nat} {state gasfulNext : EVMState}
    (hStep : op.continuingStep? = some step)
    (hMsize : op ≠ .msize)
    (hDecode : Compact.decodeAt bytes pc (.prim op))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc)
    (hGasful :
      op.step (afterEVMInstructionChargeAt state) = .ok gasfulNext) :
    ∃ openNext,
      Interaction.Executes
        (Compact.InteractionSemantics.openRunNResult
          bytes 1 (afterDynamicChargeAt state))
        []
        (.ok (.running openNext)) ∧
      SameData gasfulNext openNext := by
  rcases continuingPrim_open_success_after_charges
      hStep hMsize hGasful with
    ⟨openNext, hOpen, hSame⟩
  exact
    ⟨openNext,
      raw_continuing_prim_executes_after_charges
        hStep hMsize hDecode hPc hOpen,
      hSame⟩

def continuingPrimStaticSensitive : PrimOp → Prop
  | .sstore | .tstore | .log0 | .log1 | .log2 | .log3 | .log4 => True
  | _ => False

def continuingPrimStaticPermits (state : EVMState) (op : PrimOp) : Prop :=
  continuingPrimStaticSensitive op → state.executionEnv.perm = true

/-- Continuing primitives whose imported `EvmYul.step` helper can be related
exactly from this module. -/
def continuingPrimEVMStepTransparent : PrimOp → Prop
  | _ => True

theorem evm_step_pop_eq_primStep_run
    (state : EVMState) (arg : Option (Word × Nat)) :
    EvmYul.step (τ := .EVM) .POP arg state = PrimStep.pop.run state := by
  unfold EvmYul.step
  change
    (match state.stack.pop with
      | some ⟨s, _⟩ => .ok <| state.replaceStackAndIncrPC s
      | _ => .error .StackUnderflow) =
      PrimStep.pop.run state
  cases hPop : state.stack.pop <;> simp [PrimStep.run, hPop]

theorem evm_step_mload_eq_primStep_run
    (state : EVMState) (arg : Option (Word × Nat)) :
    EvmYul.step (τ := .EVM) .MLOAD arg state = PrimStep.mload.run state := by
  unfold EvmYul.step
  change
    (match state.stack.pop with
      | some ⟨s, μ₀⟩ =>
          let (v, mState') := state.toMachineState.mload μ₀
          let state' := { state with toMachineState := mState' }
          .ok <| state'.replaceStackAndIncrPC (s.push v)
      | _ => .error .StackUnderflow) =
      PrimStep.mload.run state
  cases hPop : state.stack.pop <;> simp [PrimStep.run, hPop]

theorem evm_step_returndatacopy_eq_primStep_run
    (state : EVMState) (arg : Option (Word × Nat)) :
    EvmYul.step (τ := .EVM) .RETURNDATACOPY arg state =
      PrimStep.returndatacopy.run state := by
  unfold EvmYul.step
  change
    (match state.stack.pop3 with
      | some ⟨stack', μ₀, μ₁, μ₂⟩ =>
          if state.returnData.size < μ₁.toNat + μ₂.toNat then
            .error .InvalidMemoryAccess
          else
            let mState' := state.toMachineState.returndatacopy μ₀ μ₁ μ₂
            let state' := { state with toMachineState := mState' }
            .ok <| state'.replaceStackAndIncrPC stack'
      | _ => .error .StackUnderflow) =
      PrimStep.returndatacopy.run state
  cases hPop : state.stack.pop3 <;> simp [PrimStep.run, hPop]

theorem evm_step_log0_eq_primStep_run
    (state : EVMState) (arg : Option (Word × Nat))
    (hPerm : state.executionEnv.perm = true) :
    EvmYul.step (τ := .EVM) .LOG0 arg state =
      PrimStep.log0.run state := by
  unfold EvmYul.step
  change EvmYul.EVM.log0Op state = PrimStep.log0.run state
  unfold EvmYul.EVM.log0Op
  cases hPop : state.stack.pop2 with
  | none =>
      simp [PrimStep.run, hPerm, hPop]
  | some popped =>
      rcases popped with ⟨rest, μ₀, μ₁⟩
      simp [PrimStep.run, hPerm, hPop]
      rfl

theorem evm_step_log1_eq_primStep_run
    (state : EVMState) (arg : Option (Word × Nat))
    (hPerm : state.executionEnv.perm = true) :
    EvmYul.step (τ := .EVM) .LOG1 arg state =
      PrimStep.log1.run state := by
  unfold EvmYul.step
  change EvmYul.EVM.log1Op state = PrimStep.log1.run state
  unfold EvmYul.EVM.log1Op
  cases hPop : state.stack.pop3 with
  | none =>
      simp [PrimStep.run, hPerm, hPop]
  | some popped =>
      rcases popped with ⟨rest, μ₀, μ₁, μ₂⟩
      simp [PrimStep.run, hPerm, hPop]
      rfl

theorem evm_step_log2_eq_primStep_run
    (state : EVMState) (arg : Option (Word × Nat))
    (hPerm : state.executionEnv.perm = true) :
    EvmYul.step (τ := .EVM) .LOG2 arg state =
      PrimStep.log2.run state := by
  unfold EvmYul.step
  change EvmYul.EVM.log2Op state = PrimStep.log2.run state
  unfold EvmYul.EVM.log2Op
  cases hPop : state.stack.pop4 with
  | none =>
      simp [PrimStep.run, hPerm, hPop]
  | some popped =>
      rcases popped with ⟨rest, μ₀, μ₁, μ₂, μ₃⟩
      simp [PrimStep.run, hPerm, hPop]
      rfl

theorem evm_step_log3_eq_primStep_run
    (state : EVMState) (arg : Option (Word × Nat))
    (hPerm : state.executionEnv.perm = true) :
    EvmYul.step (τ := .EVM) .LOG3 arg state =
      PrimStep.log3.run state := by
  unfold EvmYul.step
  change EvmYul.EVM.log3Op state = PrimStep.log3.run state
  unfold EvmYul.EVM.log3Op
  cases hPop : state.stack.pop5 with
  | none =>
      simp [PrimStep.run, hPerm, hPop]
  | some popped =>
      rcases popped with ⟨rest, μ₀, μ₁, μ₂, μ₃, μ₄⟩
      simp [PrimStep.run, hPerm, hPop]
      rfl

theorem evm_step_log4_eq_primStep_run
    (state : EVMState) (arg : Option (Word × Nat))
    (hPerm : state.executionEnv.perm = true) :
    EvmYul.step (τ := .EVM) .LOG4 arg state =
      PrimStep.log4.run state := by
  unfold EvmYul.step
  change EvmYul.EVM.log4Op state = PrimStep.log4.run state
  unfold EvmYul.EVM.log4Op
  cases hPop : state.stack.pop6 with
  | none =>
      simp [PrimStep.run, hPerm, hPop]
  | some popped =>
      rcases popped with ⟨rest, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅⟩
      simp [PrimStep.run, hPerm, hPop]
      rfl

theorem continuingPrimStaticPermits_of_static_check
    {validJumps : Array Word} {state : EVMState} {op : PrimOp}
    (hStatic : XStaticChecksPass validJumps state)
    (hOp : decodedOperationAt state = op.toEVM) :
    continuingPrimStaticPermits state op := by
  intro hSensitive
  cases hPerm : state.executionEnv.perm
  · exfalso
    exact hStatic.staticOk
      ⟨hPerm, by
        cases op <;>
          simp [continuingPrimStaticSensitive, PrimOp.toEVM] at hSensitive hOp
        all_goals simp [hOp]⟩
  · rfl

theorem evm_step_continuing_prim_after_charges
    {fuel : Nat} {state : EVMState} {op : PrimOp} {step : PrimStep}
    {arg : Option (Word × Nat)}
    (hStep : op.continuingStep? = some step)
    (hTransparent : continuingPrimEVMStepTransparent op)
    (hStaticPermits : continuingPrimStaticPermits state op) :
    EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
        (some (op.toEVM, arg)) (afterMemoryChargeAt state) =
      op.step (afterEVMInstructionChargeAt state) := by
  cases op <;>
    simp [PrimOp.continuingStep?] at hStep
  case returndatacopy =>
    cases hStep
    simp only [EvmYul.EVM.step, PrimOp.toEVM,
      afterEVMInstructionChargeAt, afterMemoryChargeAt, dynamicGasCostAt,
      chargeGas]
    change
      EvmYul.step (τ := .EVM) .RETURNDATACOPY arg
          (afterEVMInstructionChargeAt state) =
        PrimOp.returndatacopy.step (afterEVMInstructionChargeAt state)
    rw [PrimOp.step_eq_continuingStep_run (op := .returndatacopy)
      (step := .returndatacopy) rfl]
    exact
      evm_step_returndatacopy_eq_primStep_run
        (afterEVMInstructionChargeAt state) arg
  case pop =>
    cases hStep
    simp only [EvmYul.EVM.step, PrimOp.toEVM,
      afterEVMInstructionChargeAt, afterMemoryChargeAt, dynamicGasCostAt,
      chargeGas]
    change
      EvmYul.step (τ := .EVM) .POP arg
          (afterEVMInstructionChargeAt state) =
        PrimOp.pop.step (afterEVMInstructionChargeAt state)
    rw [PrimOp.step_eq_continuingStep_run (op := .pop)
      (step := .pop) rfl]
    exact
      evm_step_pop_eq_primStep_run (afterEVMInstructionChargeAt state) arg
  case mload =>
    cases hStep
    simp only [EvmYul.EVM.step, PrimOp.toEVM,
      afterEVMInstructionChargeAt, afterMemoryChargeAt, dynamicGasCostAt,
      chargeGas]
    change
      EvmYul.step (τ := .EVM) .MLOAD arg
          (afterEVMInstructionChargeAt state) =
        PrimOp.mload.step (afterEVMInstructionChargeAt state)
    rw [PrimOp.step_eq_continuingStep_run (op := .mload)
      (step := .mload) rfl]
    exact
      evm_step_mload_eq_primStep_run (afterEVMInstructionChargeAt state) arg
  case sstore =>
    cases hStep
    have hPerm := hStaticPermits (by simp [continuingPrimStaticSensitive])
    have hPermCharged :
        (afterEVMInstructionChargeAt state).executionEnv.perm = true := by
      simpa [afterEVMInstructionChargeAt, afterMemoryChargeAt, chargeGas]
        using hPerm
    simp only [EvmYul.EVM.step, PrimOp.toEVM,
      afterEVMInstructionChargeAt, afterMemoryChargeAt, dynamicGasCostAt,
      chargeGas]
    change
      EvmYul.EVM.binaryStateOp EvmYul.State.sstore
          (afterEVMInstructionChargeAt state) =
        PrimOp.sstore.step (afterEVMInstructionChargeAt state)
    rw [PrimOp.step_eq_continuingStep_run (op := .sstore)
      (step := .binaryState EvmYul.State.sstore) rfl]
    exact
      (PrimStep.run_binaryState_of_permitted EvmYul.State.sstore
        (afterEVMInstructionChargeAt state) hPermCharged).symm
  case tstore =>
    cases hStep
    have hPerm := hStaticPermits (by simp [continuingPrimStaticSensitive])
    have hPermCharged :
        (afterEVMInstructionChargeAt state).executionEnv.perm = true := by
      simpa [afterEVMInstructionChargeAt, afterMemoryChargeAt, chargeGas]
        using hPerm
    simp only [EvmYul.EVM.step, PrimOp.toEVM,
      afterEVMInstructionChargeAt, afterMemoryChargeAt, dynamicGasCostAt,
      chargeGas]
    change
      EvmYul.EVM.binaryStateOp EvmYul.State.tstore
          (afterEVMInstructionChargeAt state) =
        PrimOp.tstore.step (afterEVMInstructionChargeAt state)
    rw [PrimOp.step_eq_continuingStep_run (op := .tstore)
      (step := .binaryState EvmYul.State.tstore) rfl]
    exact
      (PrimStep.run_binaryState_of_permitted EvmYul.State.tstore
        (afterEVMInstructionChargeAt state) hPermCharged).symm
  case log0 =>
    cases hStep
    have hPerm := hStaticPermits (by simp [continuingPrimStaticSensitive])
    have hPermCharged :
        (afterEVMInstructionChargeAt state).executionEnv.perm = true := by
      simpa [afterEVMInstructionChargeAt, afterMemoryChargeAt, chargeGas]
        using hPerm
    simp only [EvmYul.EVM.step, PrimOp.toEVM,
      afterEVMInstructionChargeAt, afterMemoryChargeAt, dynamicGasCostAt,
      chargeGas]
    change
      EvmYul.step (τ := .EVM) .LOG0 arg
          (afterEVMInstructionChargeAt state) =
        PrimOp.log0.step (afterEVMInstructionChargeAt state)
    rw [PrimOp.step_eq_continuingStep_run (op := .log0)
      (step := .log0) rfl]
    exact
      evm_step_log0_eq_primStep_run
        (afterEVMInstructionChargeAt state) arg hPermCharged
  case log1 =>
    cases hStep
    have hPerm := hStaticPermits (by simp [continuingPrimStaticSensitive])
    have hPermCharged :
        (afterEVMInstructionChargeAt state).executionEnv.perm = true := by
      simpa [afterEVMInstructionChargeAt, afterMemoryChargeAt, chargeGas]
        using hPerm
    simp only [EvmYul.EVM.step, PrimOp.toEVM,
      afterEVMInstructionChargeAt, afterMemoryChargeAt, dynamicGasCostAt,
      chargeGas]
    change
      EvmYul.step (τ := .EVM) .LOG1 arg
          (afterEVMInstructionChargeAt state) =
        PrimOp.log1.step (afterEVMInstructionChargeAt state)
    rw [PrimOp.step_eq_continuingStep_run (op := .log1)
      (step := .log1) rfl]
    exact
      evm_step_log1_eq_primStep_run
        (afterEVMInstructionChargeAt state) arg hPermCharged
  case log2 =>
    cases hStep
    have hPerm := hStaticPermits (by simp [continuingPrimStaticSensitive])
    have hPermCharged :
        (afterEVMInstructionChargeAt state).executionEnv.perm = true := by
      simpa [afterEVMInstructionChargeAt, afterMemoryChargeAt, chargeGas]
        using hPerm
    simp only [EvmYul.EVM.step, PrimOp.toEVM,
      afterEVMInstructionChargeAt, afterMemoryChargeAt, dynamicGasCostAt,
      chargeGas]
    change
      EvmYul.step (τ := .EVM) .LOG2 arg
          (afterEVMInstructionChargeAt state) =
        PrimOp.log2.step (afterEVMInstructionChargeAt state)
    rw [PrimOp.step_eq_continuingStep_run (op := .log2)
      (step := .log2) rfl]
    exact
      evm_step_log2_eq_primStep_run
        (afterEVMInstructionChargeAt state) arg hPermCharged
  case log3 =>
    cases hStep
    have hPerm := hStaticPermits (by simp [continuingPrimStaticSensitive])
    have hPermCharged :
        (afterEVMInstructionChargeAt state).executionEnv.perm = true := by
      simpa [afterEVMInstructionChargeAt, afterMemoryChargeAt, chargeGas]
        using hPerm
    simp only [EvmYul.EVM.step, PrimOp.toEVM,
      afterEVMInstructionChargeAt, afterMemoryChargeAt, dynamicGasCostAt,
      chargeGas]
    change
      EvmYul.step (τ := .EVM) .LOG3 arg
          (afterEVMInstructionChargeAt state) =
        PrimOp.log3.step (afterEVMInstructionChargeAt state)
    rw [PrimOp.step_eq_continuingStep_run (op := .log3)
      (step := .log3) rfl]
    exact
      evm_step_log3_eq_primStep_run
        (afterEVMInstructionChargeAt state) arg hPermCharged
  case log4 =>
    cases hStep
    have hPerm := hStaticPermits (by simp [continuingPrimStaticSensitive])
    have hPermCharged :
        (afterEVMInstructionChargeAt state).executionEnv.perm = true := by
      simpa [afterEVMInstructionChargeAt, afterMemoryChargeAt, chargeGas]
        using hPerm
    simp only [EvmYul.EVM.step, PrimOp.toEVM,
      afterEVMInstructionChargeAt, afterMemoryChargeAt, dynamicGasCostAt,
      chargeGas]
    change
      EvmYul.step (τ := .EVM) .LOG4 arg
          (afterEVMInstructionChargeAt state) =
        PrimOp.log4.step (afterEVMInstructionChargeAt state)
    rw [PrimOp.step_eq_continuingStep_run (op := .log4)
      (step := .log4) rfl]
    exact
      evm_step_log4_eq_primStep_run
        (afterEVMInstructionChargeAt state) arg hPermCharged
  all_goals
    cases hStep
    rfl

theorem raw_continuing_prim_refines_evm_step_after_charges
    {fuel : Nat} {op : PrimOp} {step : PrimStep}
    {bytes : ByteArray} {pc : Nat} {state gasfulNext : EVMState}
    {arg : Option (Word × Nat)}
    (hStep : op.continuingStep? = some step)
    (hMsize : op ≠ .msize)
    (hTransparent : continuingPrimEVMStepTransparent op)
    (hStaticPermits : continuingPrimStaticPermits state op)
    (hDecode : Compact.decodeAt bytes pc (.prim op))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc)
    (hGasful :
      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
        (some (op.toEVM, arg)) (afterMemoryChargeAt state) =
          .ok gasfulNext) :
    ∃ openNext,
      Interaction.Executes
        (Compact.InteractionSemantics.openRunNResult
          bytes 1 (afterDynamicChargeAt state))
        []
        (.ok (.running openNext)) ∧
      SameData gasfulNext openNext := by
  have hPrimStep :
      op.step (afterEVMInstructionChargeAt state) = .ok gasfulNext := by
    simpa [evm_step_continuing_prim_after_charges
      (fuel := fuel) (state := state) (op := op) (step := step)
      (arg := arg) hStep hTransparent hStaticPermits] using hGasful
  exact
    raw_continuing_prim_refines_step_after_charges
      (op := op) (step := step) (bytes := bytes)
      (pc := pc) (state := state) (gasfulNext := gasfulNext)
      hStep hMsize hDecode hPc hPrimStep

def openStopStateAt (state : EVMState) : EVMState :=
  { afterDynamicChargeAt state with
    toMachineState :=
      ((afterDynamicChargeAt state).toMachineState.setReturnData
        ByteArray.empty).setHReturn ByteArray.empty }

def openStopHaltAt (state : EVMState) : Halt :=
  { kind := .stop
    state := openStopStateAt state
    output := ByteArray.empty }

def gasfulStopStateAfterCharges (state : EVMState) : EVMState :=
  { afterEVMInstructionChargeAt state with
    toMachineState :=
      ((afterEVMInstructionChargeAt state).toMachineState.setReturnData
        ByteArray.empty).setHReturn ByteArray.empty }

theorem evm_step_stop_after_charges
    {fuel : Nat} {state : EVMState} :
    EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
        (some
          (EvmYul.Operation.STOP,
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).2))
        (afterMemoryChargeAt state) =
      .ok (gasfulStopStateAfterCharges state) := by
  rfl

theorem sameData_gasful_open_stop_after_charges
    (state : EVMState) :
    SameData (gasfulStopStateAfterCharges state) (openStopStateAt state) := by
  cases state
  rfl

theorem SameData.hReturn_eq {left right : EVMState}
    (hSame : SameData left right) :
    left.toMachineState.H_return = right.toMachineState.H_return := by
  simpa [SameData, eraseControl, eraseGas] using
    congrArg (fun state : EVMState => state.toMachineState.H_return) hSame

def binaryMachineStateStepState
    (op : EvmYul.MachineState → Word → Word → EvmYul.MachineState)
    (state : EVMState) : EVMState :=
  match state.stack.pop2 with
  | some ⟨stack, μ₀, μ₁⟩ =>
      let machine := op state.toMachineState μ₀ μ₁
      let state' := { state with toMachineState := machine }
      state'.replaceStackAndIncrPC stack
  | none => state

def openReturnStateAt (state : EVMState) : EVMState :=
  binaryMachineStateStepState
    EvmYul.MachineState.evmReturn (afterDynamicChargeAt state)

def gasfulReturnStateAfterCharges (state : EVMState) : EVMState :=
  binaryMachineStateStepState
    EvmYul.MachineState.evmReturn (afterEVMInstructionChargeAt state)

def openReturnHaltAt (state : EVMState) : Halt :=
  { kind := .return
    state := openReturnStateAt state
    output := (openReturnStateAt state).toMachineState.H_return }

def openRevertStateAt (state : EVMState) : EVMState :=
  binaryMachineStateStepState
    EvmYul.MachineState.evmRevert (afterDynamicChargeAt state)

def gasfulRevertStateAfterCharges (state : EVMState) : EVMState :=
  binaryMachineStateStepState
    EvmYul.MachineState.evmRevert (afterEVMInstructionChargeAt state)

def openRevertHaltAt (state : EVMState) : Halt :=
  { kind := .revert
    state := openRevertStateAt state
    output := (openRevertStateAt state).toMachineState.H_return }

theorem evm_step_return_after_charges
    {fuel : Nat} {state : EVMState} {stack : EvmYul.Stack Word}
    {μ₀ μ₁ : Word}
    (hPop :
      (afterEVMInstructionChargeAt state).stack.pop2 =
        some ⟨stack, μ₀, μ₁⟩) :
    EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
        (some
          (EvmYul.Operation.RETURN,
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).2))
        (afterMemoryChargeAt state) =
      .ok (gasfulReturnStateAfterCharges state) := by
  change
    EvmYul.EVM.binaryMachineStateOp EvmYul.MachineState.evmReturn
      (afterEVMInstructionChargeAt state) =
      .ok (gasfulReturnStateAfterCharges state)
  simp [EvmYul.EVM.binaryMachineStateOp, gasfulReturnStateAfterCharges,
    binaryMachineStateStepState, hPop]
  rfl

theorem evm_step_revert_after_charges
    {fuel : Nat} {state : EVMState} {stack : EvmYul.Stack Word}
    {μ₀ μ₁ : Word}
    (hPop :
      (afterEVMInstructionChargeAt state).stack.pop2 =
        some ⟨stack, μ₀, μ₁⟩) :
    EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
        (some
          (EvmYul.Operation.REVERT,
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).2))
        (afterMemoryChargeAt state) =
      .ok (gasfulRevertStateAfterCharges state) := by
  change
    EvmYul.EVM.binaryMachineStateOp EvmYul.MachineState.evmRevert
      (afterEVMInstructionChargeAt state) =
      .ok (gasfulRevertStateAfterCharges state)
  simp [EvmYul.EVM.binaryMachineStateOp, gasfulRevertStateAfterCharges,
    binaryMachineStateStepState, hPop]
  rfl

theorem sameData_gasful_open_return_after_charges
    (state : EVMState) :
    SameData (gasfulReturnStateAfterCharges state) (openReturnStateAt state) := by
  cases state with
  | mk shared pc stack execLength =>
      cases hPop : stack.pop2 with
      | none =>
          simp [gasfulReturnStateAfterCharges, openReturnStateAt,
            binaryMachineStateStepState, EvmYul.MachineState.evmReturn,
            afterEVMInstructionChargeAt, afterDynamicChargeAt,
            afterMemoryChargeAt, dynamicGasCostAt, chargeGas,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC,
            SameData, eraseControl, eraseGas, hPop]
      | some popped =>
          rcases popped with ⟨rest, μ₀, μ₁⟩
          simp [gasfulReturnStateAfterCharges, openReturnStateAt,
            binaryMachineStateStepState, EvmYul.MachineState.evmReturn,
            afterEVMInstructionChargeAt, afterDynamicChargeAt,
            afterMemoryChargeAt, dynamicGasCostAt, chargeGas,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC,
            SameData, eraseControl, eraseGas, hPop]

theorem sameData_gasful_open_revert_after_charges
    (state : EVMState) :
    SameData (gasfulRevertStateAfterCharges state) (openRevertStateAt state) := by
  cases state with
  | mk shared pc stack execLength =>
      cases hPop : stack.pop2 with
      | none =>
          simp [gasfulRevertStateAfterCharges, openRevertStateAt,
            binaryMachineStateStepState, EvmYul.MachineState.evmRevert,
            EvmYul.MachineState.evmReturn, afterEVMInstructionChargeAt,
            afterDynamicChargeAt, afterMemoryChargeAt, dynamicGasCostAt,
            chargeGas, EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC,
            SameData, eraseControl, eraseGas, hPop]
      | some popped =>
          rcases popped with ⟨rest, μ₀, μ₁⟩
          simp [gasfulRevertStateAfterCharges, openRevertStateAt,
            binaryMachineStateStepState, EvmYul.MachineState.evmRevert,
            EvmYul.MachineState.evmReturn, afterEVMInstructionChargeAt,
            afterDynamicChargeAt, afterMemoryChargeAt, dynamicGasCostAt,
            chargeGas, EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC,
            SameData, eraseControl, eraseGas, hPop]

theorem prim_return_step_after_dynamic_of_pop2
    {state : EVMState} {stack : EvmYul.Stack Word} {μ₀ μ₁ : Word}
    (hPop :
      (afterDynamicChargeAt state).stack.pop2 =
        some ⟨stack, μ₀, μ₁⟩) :
    Assembly.PrimOp.return.step (afterDynamicChargeAt state) =
      .ok (openReturnStateAt state) := by
  change
    EvmYul.EVM.binaryMachineStateOp EvmYul.MachineState.evmReturn
      (afterDynamicChargeAt state) =
      .ok (openReturnStateAt state)
  simp [EvmYul.EVM.binaryMachineStateOp, openReturnStateAt,
    binaryMachineStateStepState, hPop]
  rfl

theorem prim_revert_step_after_dynamic_of_pop2
    {state : EVMState} {stack : EvmYul.Stack Word} {μ₀ μ₁ : Word}
    (hPop :
      (afterDynamicChargeAt state).stack.pop2 =
        some ⟨stack, μ₀, μ₁⟩) :
    Assembly.PrimOp.revert.step (afterDynamicChargeAt state) =
      .ok (openRevertStateAt state) := by
  change
    EvmYul.EVM.binaryMachineStateOp EvmYul.MachineState.evmRevert
      (afterDynamicChargeAt state) =
      .ok (openRevertStateAt state)
  simp [EvmYul.EVM.binaryMachineStateOp, openRevertStateAt,
    binaryMachineStateStepState, hPop]
  rfl

theorem prim_return_step_after_dynamic_stackUnderflow
    {state : EVMState}
    (hShort : state.stack.length < 2) :
    Assembly.PrimOp.return.step (afterDynamicChargeAt state) =
      .error EvmYul.EVM.ExecutionException.StackUnderflow := by
  have hShortCharged :
      (afterDynamicChargeAt state).stack.length < 2 := by
    simpa [afterDynamicChargeAt, afterMemoryChargeAt, chargeGas] using hShort
  have hPop :
      (afterDynamicChargeAt state).stack.pop2 = none := by
    cases hPop : (afterDynamicChargeAt state).stack.pop2 with
    | none => rfl
    | some popped =>
        rcases popped with ⟨rest, μ₀, μ₁⟩
        have hLen := PrimStep.Stack.length_of_pop2_some hPop
        omega
  change
    EvmYul.EVM.binaryMachineStateOp EvmYul.MachineState.evmReturn
      (afterDynamicChargeAt state) =
      .error EvmYul.EVM.ExecutionException.StackUnderflow
  simp [EvmYul.EVM.binaryMachineStateOp, hPop]

theorem prim_revert_step_after_dynamic_stackUnderflow
    {state : EVMState}
    (hShort : state.stack.length < 2) :
    Assembly.PrimOp.revert.step (afterDynamicChargeAt state) =
      .error EvmYul.EVM.ExecutionException.StackUnderflow := by
  have hShortCharged :
      (afterDynamicChargeAt state).stack.length < 2 := by
    simpa [afterDynamicChargeAt, afterMemoryChargeAt, chargeGas] using hShort
  have hPop :
      (afterDynamicChargeAt state).stack.pop2 = none := by
    cases hPop : (afterDynamicChargeAt state).stack.pop2 with
    | none => rfl
    | some popped =>
        rcases popped with ⟨rest, μ₀, μ₁⟩
        have hLen := PrimStep.Stack.length_of_pop2_some hPop
        omega
  change
    EvmYul.EVM.binaryMachineStateOp EvmYul.MachineState.evmRevert
      (afterDynamicChargeAt state) =
      .error EvmYul.EVM.ExecutionException.StackUnderflow
  simp [EvmYul.EVM.binaryMachineStateOp, hPop]

theorem afterDynamic_pop2_of_afterEVMInstruction_pop2
    {state : EVMState} {stack : EvmYul.Stack Word} {μ₀ μ₁ : Word}
    (hPop :
      (afterEVMInstructionChargeAt state).stack.pop2 =
        some ⟨stack, μ₀, μ₁⟩) :
    (afterDynamicChargeAt state).stack.pop2 =
      some ⟨stack, μ₀, μ₁⟩ := by
  cases state
  simpa [afterEVMInstructionChargeAt, afterDynamicChargeAt,
    afterMemoryChargeAt, dynamicGasCostAt, chargeGas] using hPop

theorem afterDynamic_pop2_of_return_step_ok
    {fuel : Nat} {state gasfulFinal : EVMState}
    (hStep :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          (EvmYul.Operation.RETURN,
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).2))
        (afterMemoryChargeAt state) = .ok gasfulFinal) :
    ∃ (stack : EvmYul.Stack Word) (μ₀ μ₁ : Word),
      (afterDynamicChargeAt state).stack.pop2 = some ⟨stack, μ₀, μ₁⟩ := by
  cases fuel with
  | zero =>
      simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      cases hPop :
          (afterEVMInstructionChargeAt state).stack.pop2 with
      | none =>
          have hBad :
              EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
                (some
                  (EvmYul.Operation.RETURN,
                    ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
                      (EvmYul.Operation.STOP, none)).2))
                (afterMemoryChargeAt state) =
                  .error .StackUnderflow := by
            change
              EvmYul.EVM.binaryMachineStateOp
                EvmYul.MachineState.evmReturn
                (afterEVMInstructionChargeAt state) =
                  .error .StackUnderflow
            simp [EvmYul.EVM.binaryMachineStateOp, hPop]
          rw [hBad] at hStep
          cases hStep
      | some popped =>
          rcases popped with ⟨stack, μ₀, μ₁⟩
          exact ⟨stack, μ₀, μ₁,
            afterDynamic_pop2_of_afterEVMInstruction_pop2 hPop⟩

theorem afterDynamic_pop2_of_revert_step_ok
    {fuel : Nat} {state gasfulFinal : EVMState}
    (hStep :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          (EvmYul.Operation.REVERT,
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).2))
        (afterMemoryChargeAt state) = .ok gasfulFinal) :
    ∃ (stack : EvmYul.Stack Word) (μ₀ μ₁ : Word),
      (afterDynamicChargeAt state).stack.pop2 = some ⟨stack, μ₀, μ₁⟩ := by
  cases fuel with
  | zero =>
      simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      cases hPop :
          (afterEVMInstructionChargeAt state).stack.pop2 with
      | none =>
          have hBad :
              EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
                (some
                  (EvmYul.Operation.REVERT,
                    ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
                      (EvmYul.Operation.STOP, none)).2))
                (afterMemoryChargeAt state) =
                  .error .StackUnderflow := by
            change
              EvmYul.EVM.binaryMachineStateOp
                EvmYul.MachineState.evmRevert
                (afterEVMInstructionChargeAt state) =
                  .error .StackUnderflow
            simp [EvmYul.EVM.binaryMachineStateOp, hPop]
          rw [hBad] at hStep
          cases hStep
      | some popped =>
          rcases popped with ⟨stack, μ₀, μ₁⟩
          exact ⟨stack, μ₀, μ₁,
            afterDynamic_pop2_of_afterEVMInstruction_pop2 hPop⟩

/-- `STOP` is a successful halting frame result after the same checked gas and
exception prefix. The theorem leaves the concrete `EVM.step` result explicit,
so it does not unfold the imported opcode dispatcher or introduce finalization
semantics beyond the current frame. -/
theorem x_stop_success_after_charges
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hStop : decodedOperationAt state = EvmYul.Operation.STOP)
    {gasfulFinal : EVMState}
    (hStep :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          (EvmYul.Operation.STOP,
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).2))
        (afterMemoryChargeAt state) = .ok gasfulFinal) :
    EvmYul.EVM.X (fuel + 1) validJumps state =
      .ok (.success gasfulFinal ByteArray.empty) := by
  have hOp' :
      ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
        (EvmYul.Operation.STOP, none)).1 =
        EvmYul.Operation.STOP := by
    simpa [decodedOperationAt] using hStop
  have hMemoryGas' :
      ¬ state.gasAvailable.toNat <
        EvmYul.EVM.memoryExpansionCost state EvmYul.Operation.STOP := by
    simpa [hOp'] using
      hPrefix.static.stackLimit.memoryAccess.jumps.stack.gas.memoryGas_raw
  have hDynamicGas' :
      ¬ (state.gasAvailable -
          EvmYul.UInt256.ofNat
            (EvmYul.EVM.memoryExpansionCost state
              EvmYul.Operation.STOP)).toNat <
        EvmYul.EVM.C'
          { state with
            gasAvailable :=
              state.gasAvailable -
                EvmYul.UInt256.ofNat
                  (EvmYul.EVM.memoryExpansionCost state
                    EvmYul.Operation.STOP) }
          EvmYul.Operation.STOP := by
    simpa [hOp'] using
      hPrefix.static.stackLimit.memoryAccess.jumps.stack.gas.dynamicGas_raw
  have hOpcodeValid' :
      EvmYul.EVM.δ EvmYul.Operation.STOP ≠ none := by
    simpa [hOp'] using
      hPrefix.static.stackLimit.memoryAccess.jumps.stack.opcodeValid_raw
  have hStackEnough' :
      ¬ state.stack.length <
        (EvmYul.EVM.δ EvmYul.Operation.STOP).getD 0 := by
    simpa [hOp'] using
      hPrefix.static.stackLimit.memoryAccess.jumps.stack.stackEnough_raw
  have hStackLimitOk' :
      ¬ 1024 <
        state.stack.length -
          (EvmYul.EVM.δ EvmYul.Operation.STOP).getD 0 +
          (EvmYul.EVM.α EvmYul.Operation.STOP).getD 0 := by
    simpa [stackOverflowAt, decodedOperationAt, hOp'] using
      hPrefix.static.stackLimit.stackLimitOk
  have hStep' :
      EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            { state with
              gasAvailable :=
                state.gasAvailable -
                  EvmYul.UInt256.ofNat
                    (EvmYul.EVM.memoryExpansionCost state
                      EvmYul.Operation.STOP) }
            EvmYul.Operation.STOP)
          (some
            (EvmYul.Operation.STOP,
              ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
                (EvmYul.Operation.STOP, none)).2))
          { state with
            gasAvailable :=
              state.gasAvailable -
                EvmYul.UInt256.ofNat
                  (EvmYul.EVM.memoryExpansionCost state
                    EvmYul.Operation.STOP) } =
        .ok gasfulFinal := by
    simpa [dynamicGasCostAt, afterMemoryChargeAt, memoryExpansionCostAt,
      decodedOperationAt, hOp', chargeGas] using hStep
  simp [EvmYul.EVM.X, hOp', hMemoryGas', hDynamicGas',
    hOpcodeValid', hStackEnough', hStackLimitOk',
    hStep', EvmYul.Operation.isCreate,
    afterMemoryChargeAt, dynamicGasCostAt,
    memoryExpansionCostAt, decodedOperationAt, chargeGas]

theorem sameData_stop_step_after_charges
    {fuel : Nat} {state gasfulFinal : EVMState}
    (hStep :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          (EvmYul.Operation.STOP,
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).2))
        (afterMemoryChargeAt state) = .ok gasfulFinal) :
    SameData gasfulFinal (openStopStateAt state) := by
  cases fuel with
  | zero =>
      simp [EvmYul.EVM.step] at hStep
  | succ f =>
      rw [evm_step_stop_after_charges (fuel := f) (state := state)] at hStep
      cases hStep
      exact sameData_gasful_open_stop_after_charges state

theorem x_return_success_after_charges
    {fuel : Nat} {validJumps : Array Word} {state gasfulFinal : EVMState}
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hReturn : decodedOperationAt state = EvmYul.Operation.RETURN)
    (hStep :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          (EvmYul.Operation.RETURN,
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).2))
        (afterMemoryChargeAt state) = .ok gasfulFinal) :
    EvmYul.EVM.X (fuel + 1) validJumps state =
      .ok (.success gasfulFinal gasfulFinal.toMachineState.H_return) := by
  have hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt state) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          state.stack[2]?.getD (EvmYul.UInt256.ofNat 0)) := by
    intro hCreate
    simpa [hReturn, EvmYul.Operation.isCreate] using hCreate.1
  have hOp' :
      ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
        (EvmYul.Operation.STOP, none)).1 =
        EvmYul.Operation.RETURN := by
    simpa [decodedOperationAt] using hReturn
  have hStep' :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok gasfulFinal := by
    change EvmYul.EVM.step fuel (dynamicGasCostAt state)
      (some
        (((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)).1,
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)).2))
      (afterMemoryChargeAt state) = .ok gasfulFinal
    rw [hOp']
    exact hStep
  simpa [xPostStepExceptResult, xPostStepResult, haltOutputAt, hReturn] using
    (x_after_prechecks_of_step_result
      (fuel := fuel) (validJumps := validJumps) (state := state)
      (stepResult := .ok gasfulFinal) hPrefix hCreateOk hStep')

theorem x_revert_success_after_charges
    {fuel : Nat} {validJumps : Array Word} {state gasfulFinal : EVMState}
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hRevert : decodedOperationAt state = EvmYul.Operation.REVERT)
    (hStep :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          (EvmYul.Operation.REVERT,
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).2))
        (afterMemoryChargeAt state) = .ok gasfulFinal) :
    EvmYul.EVM.X (fuel + 1) validJumps state =
      .ok (.revert gasfulFinal.gasAvailable
        gasfulFinal.toMachineState.H_return) := by
  have hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt state) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          state.stack[2]?.getD (EvmYul.UInt256.ofNat 0)) := by
    intro hCreate
    simpa [hRevert, EvmYul.Operation.isCreate] using hCreate.1
  have hOp' :
      ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
        (EvmYul.Operation.STOP, none)).1 =
        EvmYul.Operation.REVERT := by
    simpa [decodedOperationAt] using hRevert
  have hStep' :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok gasfulFinal := by
    change EvmYul.EVM.step fuel (dynamicGasCostAt state)
      (some
        (((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)).1,
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)).2))
      (afterMemoryChargeAt state) = .ok gasfulFinal
    rw [hOp']
    exact hStep
  simpa [xPostStepExceptResult, xPostStepResult, haltOutputAt, hRevert] using
    (x_after_prechecks_of_step_result
      (fuel := fuel) (validJumps := validJumps) (state := state)
      (stepResult := .ok gasfulFinal) hPrefix hCreateOk hStep')

theorem sameData_return_step_after_charges
    {fuel : Nat} {state gasfulFinal : EVMState}
    (hStep :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          (EvmYul.Operation.RETURN,
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).2))
        (afterMemoryChargeAt state) = .ok gasfulFinal) :
    SameData gasfulFinal (openReturnStateAt state) := by
  cases fuel with
  | zero =>
      simp [EvmYul.EVM.step] at hStep
  | succ f =>
      cases hPop :
          (afterEVMInstructionChargeAt state).stack.pop2 with
      | none =>
          have hBad :
              EvmYul.EVM.step (f + 1) (dynamicGasCostAt state)
                (some
                  (EvmYul.Operation.RETURN,
                    ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
                      (EvmYul.Operation.STOP, none)).2))
                (afterMemoryChargeAt state) =
                  .error .StackUnderflow := by
            change
              EvmYul.EVM.binaryMachineStateOp
                EvmYul.MachineState.evmReturn
                (afterEVMInstructionChargeAt state) =
                  .error .StackUnderflow
            simp [EvmYul.EVM.binaryMachineStateOp, hPop]
          rw [hBad] at hStep
          cases hStep
      | some popped =>
          rcases popped with ⟨stack, μ₀, μ₁⟩
          rw [evm_step_return_after_charges
            (fuel := f) (state := state) hPop] at hStep
          cases hStep
          exact sameData_gasful_open_return_after_charges state

theorem sameData_revert_step_after_charges
    {fuel : Nat} {state gasfulFinal : EVMState}
    (hStep :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          (EvmYul.Operation.REVERT,
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).2))
        (afterMemoryChargeAt state) = .ok gasfulFinal) :
    SameData gasfulFinal (openRevertStateAt state) := by
  cases fuel with
  | zero =>
      simp [EvmYul.EVM.step] at hStep
  | succ f =>
      cases hPop :
          (afterEVMInstructionChargeAt state).stack.pop2 with
      | none =>
          have hBad :
              EvmYul.EVM.step (f + 1) (dynamicGasCostAt state)
                (some
                  (EvmYul.Operation.REVERT,
                    ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
                      (EvmYul.Operation.STOP, none)).2))
                (afterMemoryChargeAt state) =
                  .error .StackUnderflow := by
            change
              EvmYul.EVM.binaryMachineStateOp
                EvmYul.MachineState.evmRevert
                (afterEVMInstructionChargeAt state) =
                  .error .StackUnderflow
            simp [EvmYul.EVM.binaryMachineStateOp, hPop]
          rw [hBad] at hStep
          cases hStep
      | some popped =>
          rcases popped with ⟨stack, μ₀, μ₁⟩
          rw [evm_step_revert_after_charges
            (fuel := f) (state := state) hPop] at hStep
          cases hStep
          exact sameData_gasful_open_revert_after_charges state

theorem raw_stop_executes_after_charges
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hDecode : Compact.decodeAt bytes pc (.prim .stop))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      []
      (.ok (.halted (openStopHaltAt state))) := by
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim .stop) trivial hDecode hPc]
  exact Interaction.Executes.done _

theorem raw_invalid_instruction_executes_after_charges
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hDecode : Compact.decodeAt bytes pc (.prim .invalid))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      []
      (.error EvmYul.EVM.ExecutionException.InvalidInstruction) := by
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim .invalid) trivial hDecode hPc]
  simpa [Compact.Instr.openStepResult, Compact.Instr.openStep,
    Assembly.InteractionSemantics.Target.openStepInstrResult,
    Assembly.Target.stepInstrResultWith,
    Assembly.InteractionSemantics.Target.openStepInstr,
    Assembly.Target.stepInstrWith,
    Assembly.InteractionSemantics.PrimOp.openStep,
    Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
    Assembly.PrimStep.run,
    Simulation.Interaction.bind,
    Simulation.Interaction.bind_done_error] using
    (Interaction.Executes.done
      (.error EvmYul.EVM.ExecutionException.InvalidInstruction :
        Except EVMException StepResult))

theorem stack_get?_of_pop3
    {α : Type} {stack rest : EvmYul.Stack α} {a b c : α}
    (hPop : EvmYul.Stack.pop3 stack = some (rest, a, b, c)) :
    stack[1]? = some b ∧ stack[2]? = some c := by
  cases stack with
  | nil => simp [EvmYul.Stack.pop3] at hPop
  | cons x xs =>
      cases xs with
      | nil => simp [EvmYul.Stack.pop3] at hPop
      | cons y ys =>
          cases ys with
          | nil => simp [EvmYul.Stack.pop3] at hPop
          | cons z zs =>
              simp [EvmYul.Stack.pop3] at hPop ⊢
              rcases hPop with ⟨hRest, hA, hB, hC⟩
              subst rest
              subst a
              subst b
              subst c
              simp

theorem exists_pop3_of_three_le
    {α : Type} {stack : EvmYul.Stack α}
    (h : 3 ≤ stack.length) :
    ∃ rest a b c, EvmYul.Stack.pop3 stack = some (rest, a, b, c) := by
  cases stack with
  | nil => simp at h
  | cons a rest =>
      cases rest with
      | nil => simp at h
      | cons b tail =>
          cases tail with
          | nil => simp at h
          | cons c suffix => exact ⟨suffix, a, b, c, rfl⟩

theorem exists_pop4_of_four_le
    {α : Type} {stack : EvmYul.Stack α}
    (h : 4 ≤ stack.length) :
    ∃ rest a b c d,
      EvmYul.Stack.pop4 stack = some (rest, a, b, c, d) := by
  cases stack with
  | nil => simp at h
  | cons a rest =>
      cases rest with
      | nil => simp at h
      | cons b tail =>
          cases tail with
          | nil => simp at h
          | cons c suffix =>
              cases suffix with
              | nil => simp at h
              | cons d rest => exact ⟨rest, a, b, c, d, rfl⟩

theorem stack_get?_two_of_pop7
    {α : Type} {stack rest : EvmYul.Stack α} {a b c d e f g : α}
    (hPop :
      EvmYul.Stack.pop7 stack = some (rest, a, b, c, d, e, f, g)) :
    stack[2]? = some c := by
  cases stack with
  | nil => simp [EvmYul.Stack.pop7] at hPop
  | cons x xs =>
      cases xs with
      | nil => simp [EvmYul.Stack.pop7] at hPop
      | cons y ys =>
          cases ys with
          | nil => simp [EvmYul.Stack.pop7] at hPop
          | cons z zs =>
              cases zs with
              | nil => simp [EvmYul.Stack.pop7] at hPop
              | cons w ws =>
                  cases ws with
                  | nil => simp [EvmYul.Stack.pop7] at hPop
                  | cons u us =>
                      cases us with
                      | nil => simp [EvmYul.Stack.pop7] at hPop
                      | cons v vs =>
                          cases vs with
                          | nil => simp [EvmYul.Stack.pop7] at hPop
                          | cons q rest' =>
                              simp [EvmYul.Stack.pop7] at hPop ⊢
                              rcases hPop with
                                ⟨hRest, hA, hB, hC, hD, hE, hF, hG⟩
                              subst rest
                              subst a
                              subst b
                              subst c
                              subst d
                              subst e
                              subst f
                              subst g
                              simp

theorem exists_pop7_of_seven_le
    {α : Type} {stack : EvmYul.Stack α}
    (h : 7 ≤ stack.length) :
    ∃ rest a b c d e f g,
      EvmYul.Stack.pop7 stack = some (rest, a, b, c, d, e, f, g) := by
  cases stack with
  | nil => simp at h
  | cons a s1 =>
      cases s1 with
      | nil => simp at h
      | cons b s2 =>
          cases s2 with
          | nil => simp at h
          | cons c s3 =>
              cases s3 with
              | nil => simp at h
              | cons d s4 =>
                  cases s4 with
                  | nil => simp at h
                  | cons e s5 =>
                      cases s5 with
                      | nil => simp at h
                      | cons f s6 =>
                          cases s6 with
                          | nil => simp at h
                          | cons g rest =>
                              exact ⟨rest, a, b, c, d, e, f, g, rfl⟩

theorem raw_invalid_returndatacopy_executes_after_charges
    {validJumps : Array Word} {bytes : ByteArray} {pc : Nat}
    {state : EVMState}
    (hPrefix : XJumpChecksPass validJumps state)
    (hInvalid : invalidReturnDataCopyAt state)
    (hDecode : Compact.decodeAt bytes pc (.prim .returndatacopy))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      []
      (.error EvmYul.EVM.ExecutionException.InvalidMemoryAccess) := by
  rcases hInvalid with ⟨hOp, hBounds⟩
  have hNotLt : ¬ state.stack.length < 3 := by
    simpa [hOp, EvmYul.EVM.δ] using hPrefix.stack.stackEnough
  have hLen : 3 ≤ state.stack.length := by
    omega
  rcases exists_pop3_of_three_le (α := Word) hLen with
    ⟨rest, μ₀, μ₁, μ₂, hPop⟩
  have hIdx := stack_get?_of_pop3 hPop
  have hBounds' :
      state.returnData.size < μ₁.toNat + μ₂.toNat := by
    simpa [hIdx.1, hIdx.2] using hBounds
  have hPopCharged :
      (afterDynamicChargeAt state).stack.pop3 =
        some (rest, μ₀, μ₁, μ₂) := by
    simpa [afterDynamicChargeAt, afterMemoryChargeAt, chargeGas] using hPop
  have hBoundsCharged :
      (afterDynamicChargeAt state).returnData.size <
        μ₁.toNat + μ₂.toNat := by
    simpa [afterDynamicChargeAt, afterMemoryChargeAt, chargeGas] using hBounds'
  have hPrim :
      PrimOp.returndatacopy.step (afterDynamicChargeAt state) =
        .error EvmYul.EVM.ExecutionException.InvalidMemoryAccess := by
    simp [PrimOp.step, PrimOp.continuingStep?, PrimStep.run,
      hPopCharged, hBoundsCharged]
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim .returndatacopy) trivial hDecode hPc]
  simpa [Compact.Instr.openStepResult, Compact.Instr.openStep,
    Assembly.InteractionSemantics.Target.openStepInstrResult,
    Assembly.Target.stepInstrResultWith,
    Assembly.InteractionSemantics.Target.openStepInstr,
    Assembly.Target.stepInstrWith,
    Assembly.InteractionSemantics.PrimOp.openStep,
    Assembly.PrimOp.toEVM,
    Simulation.ExternalKind.ofEVMOperation?,
    Simulation.CallKind.ofEVMOperation?,
    Simulation.CreateKind.ofEVMOperation?, hPrim,
    Simulation.Interaction.bind,
    Simulation.Interaction.bind_done_error,
    Assembly.PrimOp.haltKind?, Compact.Instr.haltKind?] using
    (Interaction.Executes.done
      (.error EvmYul.EVM.ExecutionException.InvalidMemoryAccess :
        Except EVMException StepResult))

theorem stack_pop_none_of_length_lt_one
    {α : Type} {stack : EvmYul.Stack α}
    (hShort : stack.length < 1) :
    stack.pop = none := by
  cases hPop : stack.pop with
  | none => rfl
  | some popped =>
      rcases popped with ⟨rest, a⟩
      have hLen := PrimStep.Stack.length_of_pop_some hPop
      omega

theorem stack_pop2_none_of_length_lt_two
    {α : Type} {stack : EvmYul.Stack α}
    (hShort : stack.length < 2) :
    stack.pop2 = none := by
  cases hPop : stack.pop2 with
  | none => rfl
  | some popped =>
      rcases popped with ⟨rest, a, b⟩
      have hLen := PrimStep.Stack.length_of_pop2_some hPop
      omega

theorem stack_pop3_none_of_length_lt_three
    {α : Type} {stack : EvmYul.Stack α}
    (hShort : stack.length < 3) :
    stack.pop3 = none := by
  cases hPop : stack.pop3 with
  | none => rfl
  | some popped =>
      rcases popped with ⟨rest, a, b, c⟩
      have hLen := PrimStep.Stack.length_of_pop3_some hPop
      omega

theorem stack_pop4_none_of_length_lt_four
    {α : Type} {stack : EvmYul.Stack α}
    (hShort : stack.length < 4) :
    stack.pop4 = none := by
  cases hPop : stack.pop4 with
  | none => rfl
  | some popped =>
      rcases popped with ⟨rest, a, b, c, d⟩
      have hLen := PrimStep.Stack.length_of_pop4_some hPop
      omega

theorem stack_pop5_none_of_length_lt_five
    {α : Type} {stack : EvmYul.Stack α}
    (hShort : stack.length < 5) :
    stack.pop5 = none := by
  cases hPop : stack.pop5 with
  | none => rfl
  | some popped =>
      rcases popped with ⟨rest, a, b, c, d, e⟩
      have hLen := PrimStep.Stack.length_of_pop5_some hPop
      omega

theorem stack_pop6_none_of_length_lt_six
    {α : Type} {stack : EvmYul.Stack α}
    (hShort : stack.length < 6) :
    stack.pop6 = none := by
  cases hPop : stack.pop6 with
  | none => rfl
  | some popped =>
      rcases popped with ⟨rest, a, b, c, d, e, f⟩
      have hLen := PrimStep.Stack.length_of_pop6_some hPop
      omega

theorem stack_pop7_none_of_length_lt_seven
    {α : Type} {stack : EvmYul.Stack α}
    (hShort : stack.length < 7) :
    stack.pop7 = none := by
  cases hPop : stack.pop7 with
  | none => rfl
  | some popped =>
      rcases popped with ⟨rest, a, b, c, d, e, f, g⟩
      have hLen := PrimStep.Stack.length_of_pop7_some hPop
      omega

theorem primStep_run_stackUnderflow_of_short
    {step : PrimStep} {state : EVMState}
    (hPerm :
      match step with
      | .binaryState _ | .log0 | .log1 | .log2 | .log3 | .log4 =>
          state.executionEnv.perm = true
      | _ => True)
    (hShort : state.stack.length < step.inputArity) :
    step.run state = .error EvmYul.EVM.ExecutionException.StackUnderflow := by
  cases step with
  | bin f =>
      simpa [PrimStep.run, PrimStep.inputArity, EvmYul.EVM.execBinOp,
        stack_pop2_none_of_length_lt_two hShort]
  | un f =>
      simpa [PrimStep.run, PrimStep.inputArity, EvmYul.EVM.execUnOp,
        stack_pop_none_of_length_lt_one hShort]
  | tri f =>
      simpa [PrimStep.run, PrimStep.inputArity, EvmYul.EVM.execTriOp,
        stack_pop3_none_of_length_lt_three hShort]
  | executionEnv f =>
      simp [PrimStep.inputArity] at hShort
  | unaryExecutionEnv f =>
      simpa [PrimStep.run, PrimStep.inputArity,
        EvmYul.EVM.unaryExecutionEnvOp,
        stack_pop_none_of_length_lt_one hShort]
  | machineState f =>
      simp [PrimStep.inputArity] at hShort
  | binaryMachineState f =>
      simpa [PrimStep.run, PrimStep.inputArity,
        EvmYul.EVM.binaryMachineStateOp,
        stack_pop2_none_of_length_lt_two hShort]
  | binaryMachineStateWithResult f =>
      simpa [PrimStep.run, PrimStep.inputArity,
        EvmYul.EVM.binaryMachineStateOp',
        stack_pop2_none_of_length_lt_two hShort]
  | ternaryMachineState f =>
      simpa [PrimStep.run, PrimStep.inputArity,
        EvmYul.EVM.ternaryMachineStateOp,
        stack_pop3_none_of_length_lt_three hShort]
  | state f =>
      simp [PrimStep.inputArity] at hShort
  | unaryState f =>
      simpa [PrimStep.run, PrimStep.inputArity,
        EvmYul.EVM.unaryStateOp,
        stack_pop_none_of_length_lt_one hShort]
  | binaryState f =>
      simpa [PrimStep.run, PrimStep.inputArity, hPerm,
        EvmYul.EVM.binaryStateOp,
        stack_pop2_none_of_length_lt_two hShort]
  | ternaryCopy f =>
      simpa [PrimStep.run, PrimStep.inputArity,
        EvmYul.EVM.ternaryCopyOp,
        stack_pop3_none_of_length_lt_three hShort]
  | quaternaryCopy f =>
      simpa [PrimStep.run, PrimStep.inputArity,
        EvmYul.EVM.quaternaryCopyOp,
        stack_pop4_none_of_length_lt_four hShort]
  | pop =>
      simpa [PrimStep.run, PrimStep.inputArity,
        stack_pop_none_of_length_lt_one hShort]
  | mload =>
      simpa [PrimStep.run, PrimStep.inputArity,
        stack_pop_none_of_length_lt_one hShort]
  | returndatacopy =>
      simpa [PrimStep.run, PrimStep.inputArity,
        stack_pop3_none_of_length_lt_three hShort]
  | dup n =>
      simp [PrimStep.inputArity] at hShort
      have hTop :
          (state.stack.take n).length ≠ n := by
        simp [List.length_take]
        omega
      simpa [PrimStep.run, PrimStep.inputArity, EvmYul.dup, hTop]
  | swap n =>
      simp [PrimStep.inputArity] at hShort
      have hTop :
          (state.stack.take (n + 1)).length ≠ n + 1 := by
        simp [List.length_take]
        omega
      simpa [PrimStep.run, PrimStep.inputArity, EvmYul.swap, hTop]
  | log0 =>
      simpa [PrimStep.run, PrimStep.inputArity, hPerm,
        stack_pop2_none_of_length_lt_two hShort]
  | log1 =>
      simpa [PrimStep.run, PrimStep.inputArity, hPerm,
        stack_pop3_none_of_length_lt_three hShort]
  | log2 =>
      simpa [PrimStep.run, PrimStep.inputArity, hPerm,
        stack_pop4_none_of_length_lt_four hShort]
  | log3 =>
      simpa [PrimStep.run, PrimStep.inputArity, hPerm,
        stack_pop5_none_of_length_lt_five hShort]
  | log4 =>
      simpa [PrimStep.run, PrimStep.inputArity, hPerm,
        stack_pop6_none_of_length_lt_six hShort]
  | invalid =>
      simp [PrimStep.inputArity] at hShort

theorem continuingPrim_step_stackUnderflow_of_short
    {op : PrimOp} {step : PrimStep} {state : EVMState}
    (hStep : op.continuingStep? = some step)
    (hStaticPermits : continuingPrimStaticPermits state op)
    (hShort : state.stack.length < (EvmYul.EVM.δ op.toEVM).getD 0) :
    op.step state = .error EvmYul.EVM.ExecutionException.StackUnderflow := by
  rw [PrimOp.step_eq_continuingStep_run hStep]
  apply primStep_run_stackUnderflow_of_short
  · cases op <;>
      simp [PrimOp.continuingStep?, continuingPrimStaticSensitive,
        continuingPrimStaticPermits] at hStep hStaticPermits ⊢
    all_goals
      subst step
      simp [hStaticPermits]
  · rcases PrimOp.continuingStep?_delta_alpha hStep with ⟨hDelta, _⟩
    simpa [hDelta] using hShort

theorem raw_continuing_prim_stackUnderflow_executes_after_charges
    {op : PrimOp} {step : PrimStep}
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hStep : op.continuingStep? = some step)
    (hMsize : op ≠ .msize)
    (hStaticPermits : continuingPrimStaticPermits state op)
    (hShort :
      state.stack.length < (EvmYul.EVM.δ op.toEVM).getD 0)
    (hDecode : Compact.decodeAt bytes pc (.prim op))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      []
      (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
  have hShortCharged :
      (afterDynamicChargeAt state).stack.length <
        (EvmYul.EVM.δ op.toEVM).getD 0 := by
    simpa [afterDynamicChargeAt, afterMemoryChargeAt, chargeGas] using hShort
  have hStaticPermitsCharged :
      continuingPrimStaticPermits (afterDynamicChargeAt state) op := by
    intro hSensitive
    simpa [afterDynamicChargeAt, afterMemoryChargeAt, chargeGas] using
      hStaticPermits hSensitive
  have hPrim :
      op.step (afterDynamicChargeAt state) =
        .error EvmYul.EVM.ExecutionException.StackUnderflow :=
    continuingPrim_step_stackUnderflow_of_short
      hStep hStaticPermitsCharged hShortCharged
  have hClosed :
      Assembly.InteractionSemantics.PrimOp.openStep op
          (afterDynamicChargeAt state) =
        Simulation.Interaction.done
          (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
    rw [Assembly.InteractionSemantics.PrimOp.openStep_closed
      (Assembly.InteractionSemantics.PrimOp.externalKind_none_of_continuingStep
        hStep)
      (continuingStep_not_gas hStep) hMsize]
    simp [hPrim]
  have hHalt := continuingStep_haltKind?_none hStep
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim op) trivial hDecode hPc]
  simpa [Compact.Instr.openStepResult, Compact.Instr.openStep,
    Assembly.InteractionSemantics.Target.openStepInstrResult,
    Assembly.Target.stepInstrResultWith,
    Assembly.InteractionSemantics.Target.openStepInstr,
    Assembly.Target.stepInstrWith, hClosed, hHalt,
    Simulation.Interaction.bind,
    Simulation.Interaction.bind_done_error,
    Compact.Instr.haltKind?] using
    (Interaction.Executes.done
      (.error EvmYul.EVM.ExecutionException.StackUnderflow :
        Except EVMException StepResult))

theorem continuingPrimStaticSensitive_not_msize
    {op : PrimOp}
    (hSensitive : continuingPrimStaticSensitive op) :
    op ≠ .msize := by
  cases op <;> simp [continuingPrimStaticSensitive] at hSensitive ⊢

theorem continuingPrim_step_staticModeViolation_of_static
    {op : PrimOp} {step : PrimStep} {state : EVMState}
    (hStep : op.continuingStep? = some step)
    (hSensitive : continuingPrimStaticSensitive op)
    (hPerm : state.executionEnv.perm = false) :
    op.step state =
      .error EvmYul.EVM.ExecutionException.StaticModeViolation := by
  rw [PrimOp.step_eq_continuingStep_run hStep]
  cases op <;>
    simp [PrimOp.continuingStep?, continuingPrimStaticSensitive]
      at hStep hSensitive
  all_goals
    cases hStep
    simp [PrimStep.run, hPerm]

theorem staticModeViolationAt_of_continuingPrim_static
    {op : PrimOp} {state : EVMState}
    (hDecodedOp : decodedOperationAt state = op.toEVM)
    (hSensitive : continuingPrimStaticSensitive op)
    (hPerm : state.executionEnv.perm = false) :
    staticModeViolationAt state := by
  cases op <;>
    simp [continuingPrimStaticSensitive, staticModeViolationAt,
      PrimOp.toEVM, hDecodedOp, hPerm] at hSensitive ⊢

theorem raw_continuing_prim_staticModeViolation_executes_after_charges
    {op : PrimOp} {step : PrimStep}
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hStep : op.continuingStep? = some step)
    (hSensitive : continuingPrimStaticSensitive op)
    (hPerm : state.executionEnv.perm = false)
    (hDecode : Compact.decodeAt bytes pc (.prim op))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      []
      (.error EvmYul.EVM.ExecutionException.StaticModeViolation) := by
  have hPermCharged :
      (afterDynamicChargeAt state).executionEnv.perm = false := by
    simpa [afterDynamicChargeAt, afterMemoryChargeAt, chargeGas] using hPerm
  have hPrim :
      op.step (afterDynamicChargeAt state) =
        .error EvmYul.EVM.ExecutionException.StaticModeViolation :=
    continuingPrim_step_staticModeViolation_of_static
      hStep hSensitive hPermCharged
  have hClosed :
      Assembly.InteractionSemantics.PrimOp.openStep op
          (afterDynamicChargeAt state) =
        Simulation.Interaction.done
          (.error EvmYul.EVM.ExecutionException.StaticModeViolation) := by
    rw [Assembly.InteractionSemantics.PrimOp.openStep_closed
      (Assembly.InteractionSemantics.PrimOp.externalKind_none_of_continuingStep
        hStep)
      (continuingStep_not_gas hStep)
      (continuingPrimStaticSensitive_not_msize hSensitive)]
    simp [hPrim]
  have hHalt := continuingStep_haltKind?_none hStep
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim op) trivial hDecode hPc]
  simpa [Compact.Instr.openStepResult, Compact.Instr.openStep,
    Assembly.InteractionSemantics.Target.openStepInstrResult,
    Assembly.Target.stepInstrResultWith,
    Assembly.InteractionSemantics.Target.openStepInstr,
    Assembly.Target.stepInstrWith, hClosed, hHalt,
    Simulation.Interaction.bind,
    Simulation.Interaction.bind_done_error,
    Compact.Instr.haltKind?] using
    (Interaction.Executes.done
      (.error EvmYul.EVM.ExecutionException.StaticModeViolation :
        Except EVMException StepResult))

theorem create_operands_of_stackEnough
    {validJumps : Array Word} {state : EVMState}
    (hPrefix : XStackLimitChecksPass validJumps state)
    (hCreate : decodedOperationAt state = EvmYul.Operation.CREATE) :
    ∃ rest operands,
      Simulation.CreateKind.evmOperands? .create state.stack =
        some (rest, operands) := by
  have hNotShort : ¬ state.stack.length < 3 := by
    simpa [hCreate, EvmYul.EVM.δ] using
      hPrefix.memoryAccess.jumps.stack.stackEnough
  have hLen : 3 ≤ state.stack.length := by
    omega
  rcases exists_pop3_of_three_le (α := Word) hLen with
    ⟨rest, value, initOffset, initSize, hPop⟩
  refine
    ⟨rest,
      { value := value
        initOffset := initOffset
        initSize := initSize
        saltArg := EvmYul.UInt256.ofNat 0 }, ?_⟩
  simp [Simulation.CreateKind.evmOperands?, hPop]

theorem create2_operands_of_stackEnough
    {validJumps : Array Word} {state : EVMState}
    (hPrefix : XStackLimitChecksPass validJumps state)
    (hCreate2 : decodedOperationAt state = EvmYul.Operation.CREATE2) :
    ∃ rest operands,
      Simulation.CreateKind.evmOperands? .create2 state.stack =
        some (rest, operands) := by
  have hNotShort : ¬ state.stack.length < 4 := by
    simpa [hCreate2, EvmYul.EVM.δ] using
      hPrefix.memoryAccess.jumps.stack.stackEnough
  have hLen : 4 ≤ state.stack.length := by
    omega
  rcases exists_pop4_of_four_le (α := Word) hLen with
    ⟨rest, value, initOffset, initSize, salt, hPop⟩
  refine
    ⟨rest,
      { value := value
        initOffset := initOffset
        initSize := initSize
        saltArg := salt }, ?_⟩
  simp [Simulation.CreateKind.evmOperands?, hPop]

theorem call_operands_of_stackEnough
    {validJumps : Array Word} {state : EVMState}
    (hPrefix : XStackLimitChecksPass validJumps state)
    (hCall : decodedOperationAt state = EvmYul.Operation.CALL) :
    ∃ rest operands,
      Simulation.CallKind.evmOperands? .call state.stack =
        some (rest, operands) := by
  have hNotShort : ¬ state.stack.length < 7 := by
    simpa [hCall, EvmYul.EVM.δ] using
      hPrefix.memoryAccess.jumps.stack.stackEnough
  have hLen : 7 ≤ state.stack.length := by
    omega
  rcases exists_pop7_of_seven_le (α := Word) hLen with
    ⟨rest, gas, address, value, inputOffset, inputSize,
      outputOffset, outputSize, hPop⟩
  refine
    ⟨rest,
      { requestedGas := gas
        address := address
        valueArg := value
        inputOffset := inputOffset
        inputSize := inputSize
        outputOffset := outputOffset
        outputSize := outputSize }, ?_⟩
  simp [Simulation.CallKind.evmOperands?, hPop]

theorem call_valueArg_ne_zero_of_operands
    {state : EVMState} {rest : EvmYul.Stack Word}
    {operands : Simulation.CallOperands}
    (hOperands :
      Simulation.CallKind.evmOperands? .call state.stack =
        some (rest, operands))
    (hStackValue :
      state.stack[2]? ≠ some (EvmYul.UInt256.ofNat 0)) :
    operands.valueArg ≠ EvmYul.UInt256.ofNat 0 := by
  unfold Simulation.CallKind.evmOperands? at hOperands
  cases hPop : state.stack.pop7 with
  | none => simp [hPop] at hOperands
  | some popped =>
      rcases popped with
        ⟨parsedRest, gas, address, value, inputOffset, inputSize,
          outputOffset, outputSize⟩
      simp [hPop] at hOperands
      rcases hOperands with ⟨rfl, rfl⟩
      have hStackValueAt :=
        stack_get?_two_of_pop7 (stack := state.stack) hPop
      intro hValue
      exact hStackValue (by simpa [hStackValueAt, hValue])

theorem raw_create_staticModeViolation_executes_after_charges
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    {rest : EvmYul.Stack Word} {operands : Simulation.CreateOperands}
    (hOperands :
      Simulation.CreateKind.evmOperands? .create state.stack =
        some (rest, operands))
    (hPerm : state.executionEnv.perm = false)
    (hDecode : Compact.decodeAt bytes pc (.prim .create))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      []
      (.error EvmYul.EVM.ExecutionException.StaticModeViolation) := by
  have hOperandsCharged :
      Simulation.CreateKind.evmOperands? .create
          (afterDynamicChargeAt state).stack =
        some (rest, operands) := by
    simpa [afterDynamicChargeAt, afterMemoryChargeAt, chargeGas] using
      hOperands
  have hPermCharged :
      (Simulation.ExternalFrame.ofShared
          (afterDynamicChargeAt state).toSharedState).permission = false := by
    simpa [Simulation.ExternalFrame.ofShared, afterDynamicChargeAt,
      afterMemoryChargeAt, chargeGas] using hPerm
  have hOpen :
      Assembly.InteractionSemantics.PrimOp.openStep
          .create (afterDynamicChargeAt state) =
        Simulation.Interaction.done
          (.error EvmYul.EVM.ExecutionException.StaticModeViolation) := by
    simp [Assembly.InteractionSemantics.PrimOp.openStep,
      Assembly.InteractionSemantics.PrimOp.createStep,
      Assembly.PrimOp.toEVM,
      Simulation.ExternalKind.ofEVMOperation?,
      Simulation.CallKind.ofEVMOperation?,
      Simulation.CreateKind.ofEVMOperation?,
      hOperandsCharged, hPermCharged]
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim .create) trivial hDecode hPc]
  simpa [Compact.Instr.openStepResult, Compact.Instr.openStep,
    Assembly.InteractionSemantics.Target.openStepInstrResult,
    Assembly.Target.stepInstrResultWith,
    Assembly.InteractionSemantics.Target.openStepInstr,
    Assembly.Target.stepInstrWith, hOpen,
    Simulation.Interaction.bind,
    Simulation.Interaction.bind_done_error,
    Assembly.PrimOp.haltKind?, Compact.Instr.haltKind?] using
    (Interaction.Executes.done
      (.error EvmYul.EVM.ExecutionException.StaticModeViolation :
        Except EVMException StepResult))

theorem raw_create2_staticModeViolation_executes_after_charges
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    {rest : EvmYul.Stack Word} {operands : Simulation.CreateOperands}
    (hOperands :
      Simulation.CreateKind.evmOperands? .create2 state.stack =
        some (rest, operands))
    (hPerm : state.executionEnv.perm = false)
    (hDecode : Compact.decodeAt bytes pc (.prim .create2))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      []
      (.error EvmYul.EVM.ExecutionException.StaticModeViolation) := by
  have hOperandsCharged :
      Simulation.CreateKind.evmOperands? .create2
          (afterDynamicChargeAt state).stack =
        some (rest, operands) := by
    simpa [afterDynamicChargeAt, afterMemoryChargeAt, chargeGas] using
      hOperands
  have hPermCharged :
      (Simulation.ExternalFrame.ofShared
          (afterDynamicChargeAt state).toSharedState).permission = false := by
    simpa [Simulation.ExternalFrame.ofShared, afterDynamicChargeAt,
      afterMemoryChargeAt, chargeGas] using hPerm
  have hOpen :
      Assembly.InteractionSemantics.PrimOp.openStep
          .create2 (afterDynamicChargeAt state) =
        Simulation.Interaction.done
          (.error EvmYul.EVM.ExecutionException.StaticModeViolation) := by
    simp [Assembly.InteractionSemantics.PrimOp.openStep,
      Assembly.InteractionSemantics.PrimOp.createStep,
      Assembly.PrimOp.toEVM,
      Simulation.ExternalKind.ofEVMOperation?,
      Simulation.CallKind.ofEVMOperation?,
      Simulation.CreateKind.ofEVMOperation?,
      hOperandsCharged, hPermCharged]
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim .create2) trivial hDecode hPc]
  simpa [Compact.Instr.openStepResult, Compact.Instr.openStep,
    Assembly.InteractionSemantics.Target.openStepInstrResult,
    Assembly.Target.stepInstrResultWith,
    Assembly.InteractionSemantics.Target.openStepInstr,
    Assembly.Target.stepInstrWith, hOpen,
    Simulation.Interaction.bind,
    Simulation.Interaction.bind_done_error,
    Assembly.PrimOp.haltKind?, Compact.Instr.haltKind?] using
    (Interaction.Executes.done
      (.error EvmYul.EVM.ExecutionException.StaticModeViolation :
        Except EVMException StepResult))

theorem raw_call_staticModeViolation_executes_after_charges
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    {rest : EvmYul.Stack Word} {operands : Simulation.CallOperands}
    (hOperands :
      Simulation.CallKind.evmOperands? .call state.stack =
        some (rest, operands))
    (hPerm : state.executionEnv.perm = false)
    (hValue :
      operands.valueArg ≠ EvmYul.UInt256.ofNat 0)
    (hDecode : Compact.decodeAt bytes pc (.prim .call))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      []
      (.error EvmYul.EVM.ExecutionException.StaticModeViolation) := by
  have hOperandsCharged :
      Simulation.CallKind.evmOperands? .call
          (afterDynamicChargeAt state).stack =
        some (rest, operands) := by
    simpa [afterDynamicChargeAt, afterMemoryChargeAt, chargeGas] using
      hOperands
  have hAllowed :
      Simulation.CallKind.allowedIn .call
          (Simulation.ExternalFrame.ofShared
            (afterDynamicChargeAt state).toSharedState)
          operands = false := by
    have hValueBeq :
        (operands.valueArg == EvmYul.UInt256.ofNat 0) = false := by
      generalize hArg : operands.valueArg = valueArg
      cases valueArg with
      | mk value =>
          have hValueNat : value ≠ 0 := by
            intro hZero
            apply hValue
            rw [hArg]
            cases hZero
            simp [EvmYul.UInt256.ofNat, Id.run]
          simp [EvmYul.instBEqUInt256,
            EvmYul.instBEqUInt256.beq,
            EvmYul.UInt256.ofNat, Id.run] at hValue ⊢
          exact hValueNat
    simp [Simulation.CallKind.allowedIn, Simulation.ExternalFrame.ofShared,
      afterDynamicChargeAt, afterMemoryChargeAt, chargeGas, hPerm,
      hValueBeq]
  have hOpen :
      Assembly.InteractionSemantics.PrimOp.openStep
          .call (afterDynamicChargeAt state) =
        Simulation.Interaction.done
          (.error EvmYul.EVM.ExecutionException.StaticModeViolation) := by
    simp [Assembly.InteractionSemantics.PrimOp.openStep,
      Assembly.InteractionSemantics.PrimOp.callStep,
      Assembly.PrimOp.toEVM,
      Simulation.ExternalKind.ofEVMOperation?,
      Simulation.CallKind.ofEVMOperation?,
      Simulation.CreateKind.ofEVMOperation?,
      hOperandsCharged, hAllowed]
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim .call) trivial hDecode hPc]
  simpa [Compact.Instr.openStepResult, Compact.Instr.openStep,
    Assembly.InteractionSemantics.Target.openStepInstrResult,
    Assembly.Target.stepInstrResultWith,
    Assembly.InteractionSemantics.Target.openStepInstr,
    Assembly.Target.stepInstrWith, hOpen,
    Simulation.Interaction.bind,
    Simulation.Interaction.bind_done_error,
    Assembly.PrimOp.haltKind?, Compact.Instr.haltKind?] using
    (Interaction.Executes.done
      (.error EvmYul.EVM.ExecutionException.StaticModeViolation :
        Except EVMException StepResult))

def gasfulSelfdestructNext (state : EVMState)
    (recipient : Word) (rest : EvmYul.Stack Word) : EVMState :=
  EvmYul.EVM.selfdestructState
    (afterEVMInstructionChargeAt state) recipient rest

def openSelfdestructNext (state : EVMState)
    (recipient : Word) (rest : EvmYul.Stack Word) : EVMState :=
  EvmYul.EVM.selfdestructState
    (afterDynamicChargeAt state) recipient rest

theorem evm_step_selfdestruct_eq_next
    (fuel : Nat) (state : EVMState)
    (recipient : Word) (rest : EvmYul.Stack Word)
    (hStack : state.stack = recipient :: rest) :
    EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
        (some (EvmYul.Operation.SELFDESTRUCT, none))
        (afterMemoryChargeAt state) =
      .ok (gasfulSelfdestructNext state recipient rest) := by
  simp [EvmYul.EVM.step, gasfulSelfdestructNext,
    afterEVMInstructionChargeAt, afterMemoryChargeAt,
    afterDynamicChargeAt, chargeGas, hStack,
    EvmYul.EVM.step_selfdestruct_of_stack]
  exact EvmYul.EVM.step_selfdestruct_of_stack _ recipient rest rfl

theorem raw_selfdestruct_success_executes_after_charges
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    {recipient : Word} {rest : EvmYul.Stack Word}
    (hPerm : state.executionEnv.perm = true)
    (hStack : state.stack = recipient :: rest)
    (hDecode : Compact.decodeAt bytes pc (.prim .selfdestruct))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      []
      (.ok
        (.halted
          { kind := .selfdestruct
            state := openSelfdestructNext state recipient rest
            output := ByteArray.empty })) := by
  have hPermCharged :
      (afterDynamicChargeAt state).executionEnv.perm = true := by
    simpa [afterDynamicChargeAt, afterMemoryChargeAt, chargeGas] using hPerm
  have hStackCharged :
      (afterDynamicChargeAt state).stack = recipient :: rest := by
    simpa [afterDynamicChargeAt, afterMemoryChargeAt, chargeGas] using hStack
  have hPrim :
      Assembly.PrimOp.selfdestruct.step (afterDynamicChargeAt state) =
        .ok (openSelfdestructNext state recipient rest) := by
    rw [Assembly.PrimOp.step_selfdestruct_of_permitted _ hPermCharged]
    exact EvmYul.EVM.step_selfdestruct_of_stack _ recipient rest hStackCharged
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim .selfdestruct) trivial hDecode hPc]
  simp [Compact.Instr.openStepResult, Compact.Instr.openStep,
    Assembly.InteractionSemantics.Target.openStepInstr,
    Assembly.Target.stepInstrWith,
    Assembly.InteractionSemantics.PrimOp.openStep,
    Assembly.PrimOp.toEVM,
    Simulation.ExternalKind.ofEVMOperation?, hPrim,
    Assembly.PrimOp.haltKind?, Compact.Instr.haltKind?,
    Assembly.HaltKind.output, Simulation.Interaction.bind]
  exact Interaction.Executes.done _

theorem selfdestructNext_sameData
    (state : EVMState) (recipient : Word) (rest : EvmYul.Stack Word) :
    SameData (gasfulSelfdestructNext state recipient rest)
      (openSelfdestructNext state recipient rest) := by
  cases state
  rfl

theorem raw_selfdestruct_staticModeViolation_executes_after_charges
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hPerm : state.executionEnv.perm = false)
    (hDecode : Compact.decodeAt bytes pc (.prim .selfdestruct))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      []
      (.error EvmYul.EVM.ExecutionException.StaticModeViolation) := by
  have hPermCharged :
      (afterDynamicChargeAt state).executionEnv.perm = false := by
    simpa [afterDynamicChargeAt, afterMemoryChargeAt, chargeGas] using hPerm
  have hPrim :
      Assembly.PrimOp.selfdestruct.step (afterDynamicChargeAt state) =
        .error EvmYul.EVM.ExecutionException.StaticModeViolation := by
    simp [Assembly.PrimOp.step_selfdestruct_of_static _ hPermCharged]
  have hOpen :
      Assembly.InteractionSemantics.PrimOp.openStep
          .selfdestruct (afterDynamicChargeAt state) =
        Simulation.Interaction.done
          (.error EvmYul.EVM.ExecutionException.StaticModeViolation) := by
    simp [Assembly.InteractionSemantics.PrimOp.openStep,
      Assembly.PrimOp.toEVM,
      Simulation.ExternalKind.ofEVMOperation?,
      Simulation.CallKind.ofEVMOperation?,
      Simulation.CreateKind.ofEVMOperation?, hPrim]
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim .selfdestruct) trivial hDecode hPc]
  simpa [Compact.Instr.openStepResult, Compact.Instr.openStep,
    Assembly.InteractionSemantics.Target.openStepInstrResult,
    Assembly.Target.stepInstrResultWith,
    Assembly.InteractionSemantics.Target.openStepInstr,
    Assembly.Target.stepInstrWith, hOpen,
    Simulation.Interaction.bind,
    Simulation.Interaction.bind_done_error,
    Assembly.PrimOp.haltKind?, Compact.Instr.haltKind?] using
    (Interaction.Executes.done
      (.error EvmYul.EVM.ExecutionException.StaticModeViolation :
        Except EVMException StepResult))

theorem evm_step_selfdestruct_stackUnderflow_of_pop_none
    (state : EVMState) (hPop : state.stack.pop = none) :
    EvmYul.step (τ := .EVM) .SELFDESTRUCT none state =
      .error EvmYul.EVM.ExecutionException.StackUnderflow := by
  cases state with
  | mk shared pc stack execLength =>
      cases stack with
      | nil => rfl
      | cons recipient tail =>
          simp [EvmYul.Stack.pop] at hPop

theorem raw_selfdestruct_stackUnderflow_executes_after_charges
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hPerm : state.executionEnv.perm = true)
    (hShort : state.stack.length < 1)
    (hDecode : Compact.decodeAt bytes pc (.prim .selfdestruct))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      []
      (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
  have hPermCharged :
      (afterDynamicChargeAt state).executionEnv.perm = true := by
    simpa [afterDynamicChargeAt, afterMemoryChargeAt, chargeGas] using hPerm
  have hShortCharged :
      (afterDynamicChargeAt state).stack.length < 1 := by
    simpa [afterDynamicChargeAt, afterMemoryChargeAt, chargeGas] using hShort
  have hPop : (afterDynamicChargeAt state).stack.pop = none :=
    stack_pop_none_of_length_lt_one hShortCharged
  have hEvm :
      EvmYul.step (τ := .EVM) .SELFDESTRUCT none
          (afterDynamicChargeAt state) =
        .error EvmYul.EVM.ExecutionException.StackUnderflow := by
    exact evm_step_selfdestruct_stackUnderflow_of_pop_none
      (afterDynamicChargeAt state) hPop
  have hPrim :
      Assembly.PrimOp.selfdestruct.step (afterDynamicChargeAt state) =
        .error EvmYul.EVM.ExecutionException.StackUnderflow := by
    rw [Assembly.PrimOp.step_selfdestruct_of_permitted _ hPermCharged]
    exact hEvm
  have hOpen :
      Assembly.InteractionSemantics.PrimOp.openStep
          .selfdestruct (afterDynamicChargeAt state) =
        Simulation.Interaction.done
          (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
    simp [Assembly.InteractionSemantics.PrimOp.openStep,
      Assembly.PrimOp.toEVM,
      Simulation.ExternalKind.ofEVMOperation?,
      Simulation.CallKind.ofEVMOperation?,
      Simulation.CreateKind.ofEVMOperation?, hPrim]
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim .selfdestruct) trivial hDecode hPc]
  simpa [Compact.Instr.openStepResult, Compact.Instr.openStep,
    Assembly.InteractionSemantics.Target.openStepInstrResult,
    Assembly.Target.stepInstrResultWith,
    Assembly.InteractionSemantics.Target.openStepInstr,
    Assembly.Target.stepInstrWith, hOpen,
    Simulation.Interaction.bind,
    Simulation.Interaction.bind_done_error,
    Assembly.PrimOp.haltKind?, Compact.Instr.haltKind?] using
    (Interaction.Executes.done
      (.error EvmYul.EVM.ExecutionException.StackUnderflow :
        Except EVMException StepResult))

theorem raw_return_stackUnderflow_executes_after_charges
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hShort : state.stack.length < 2)
    (hDecode : Compact.decodeAt bytes pc (.prim .return))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      []
      (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
  have hPrim :
      Assembly.PrimOp.return.step (afterDynamicChargeAt state) =
        .error EvmYul.EVM.ExecutionException.StackUnderflow :=
    prim_return_step_after_dynamic_stackUnderflow hShort
  have hOpen :
      Assembly.InteractionSemantics.PrimOp.openStep
          .return (afterDynamicChargeAt state) =
        Simulation.Interaction.done
          (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
    simp [Assembly.InteractionSemantics.PrimOp.openStep,
      Assembly.PrimOp.toEVM,
      Simulation.ExternalKind.ofEVMOperation?,
      Simulation.CallKind.ofEVMOperation?,
      Simulation.CreateKind.ofEVMOperation?, hPrim]
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim .return) trivial hDecode hPc]
  simpa [Compact.Instr.openStepResult, Compact.Instr.openStep,
    Assembly.InteractionSemantics.Target.openStepInstrResult,
    Assembly.Target.stepInstrResultWith,
    Assembly.InteractionSemantics.Target.openStepInstr,
    Assembly.Target.stepInstrWith, hOpen,
    Simulation.Interaction.bind,
    Simulation.Interaction.bind_done_error,
    Assembly.PrimOp.haltKind?, Compact.Instr.haltKind?] using
    (Interaction.Executes.done
      (.error EvmYul.EVM.ExecutionException.StackUnderflow :
        Except EVMException StepResult))

theorem raw_revert_stackUnderflow_executes_after_charges
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hShort : state.stack.length < 2)
    (hDecode : Compact.decodeAt bytes pc (.prim .revert))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      []
      (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
  have hPrim :
      Assembly.PrimOp.revert.step (afterDynamicChargeAt state) =
        .error EvmYul.EVM.ExecutionException.StackUnderflow :=
    prim_revert_step_after_dynamic_stackUnderflow hShort
  have hOpen :
      Assembly.InteractionSemantics.PrimOp.openStep
          .revert (afterDynamicChargeAt state) =
        Simulation.Interaction.done
          (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
    simp [Assembly.InteractionSemantics.PrimOp.openStep,
      Assembly.PrimOp.toEVM,
      Simulation.ExternalKind.ofEVMOperation?,
      Simulation.CallKind.ofEVMOperation?,
      Simulation.CreateKind.ofEVMOperation?, hPrim]
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim .revert) trivial hDecode hPc]
  simpa [Compact.Instr.openStepResult, Compact.Instr.openStep,
    Assembly.InteractionSemantics.Target.openStepInstrResult,
    Assembly.Target.stepInstrResultWith,
    Assembly.InteractionSemantics.Target.openStepInstr,
    Assembly.Target.stepInstrWith, hOpen,
    Simulation.Interaction.bind,
    Simulation.Interaction.bind_done_error,
    Assembly.PrimOp.haltKind?, Compact.Instr.haltKind?] using
    (Interaction.Executes.done
      (.error EvmYul.EVM.ExecutionException.StackUnderflow :
        Except EVMException StepResult))

theorem raw_jump_stackUnderflow_executes_after_charges
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hShort : state.stack.length < 1)
    (hDecode : Compact.decodeAt bytes pc .jump)
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      []
      (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
  have hPop : (afterDynamicChargeAt state).stack.pop = none := by
    simpa [afterDynamicChargeAt, afterMemoryChargeAt, chargeGas] using
      stack_pop_none_of_length_lt_one hShort
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .jump) trivial hDecode hPc]
  simpa [Compact.Instr.openStepResult, Compact.Instr.openStep,
    Assembly.InteractionSemantics.Target.openStepInstrResult,
    Assembly.Target.stepInstrResultWith,
    Assembly.InteractionSemantics.Target.openStepInstr,
    Assembly.Target.stepInstrWith, hPop,
    Simulation.Interaction.bind,
    Simulation.Interaction.bind_done_error,
    Compact.Instr.haltKind?] using
    (Interaction.Executes.done
      (.error EvmYul.EVM.ExecutionException.StackUnderflow :
        Except EVMException StepResult))

theorem raw_jumpi_stackUnderflow_executes_after_charges
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hShort : state.stack.length < 2)
    (hDecode : Compact.decodeAt bytes pc .jumpi)
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      []
      (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
  have hPop : (afterDynamicChargeAt state).stack.pop2 = none := by
    simpa [afterDynamicChargeAt, afterMemoryChargeAt, chargeGas] using
      stack_pop2_none_of_length_lt_two hShort
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .jumpi) trivial hDecode hPc]
  simpa [Compact.Instr.openStepResult, Compact.Instr.openStep,
    Assembly.InteractionSemantics.Target.openStepInstrResult,
    Assembly.Target.stepInstrResultWith,
    Assembly.InteractionSemantics.Target.openStepInstr,
    Assembly.Target.stepInstrWith, hPop,
    Simulation.Interaction.bind,
    Simulation.Interaction.bind_done_error,
    Compact.Instr.haltKind?] using
    (Interaction.Executes.done
      (.error EvmYul.EVM.ExecutionException.StackUnderflow :
        Except EVMException StepResult))

theorem raw_create_stackUnderflow_executes_after_charges
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hShort : state.stack.length < 3)
    (hDecode : Compact.decodeAt bytes pc (.prim .create))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      []
      (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
  have hPop : (afterDynamicChargeAt state).stack.pop3 = none := by
    simpa [afterDynamicChargeAt, afterMemoryChargeAt, chargeGas] using
      stack_pop3_none_of_length_lt_three hShort
  have hOperands :
      Simulation.CreateKind.evmOperands? .create
          (afterDynamicChargeAt state).stack = none := by
    simp [Simulation.CreateKind.evmOperands?, hPop]
  have hOpen :
      Assembly.InteractionSemantics.PrimOp.openStep
          .create (afterDynamicChargeAt state) =
        Simulation.Interaction.done
          (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
    simp [Assembly.InteractionSemantics.PrimOp.openStep,
      Assembly.InteractionSemantics.PrimOp.createStep,
      Assembly.PrimOp.toEVM,
      Simulation.ExternalKind.ofEVMOperation?,
      Simulation.CallKind.ofEVMOperation?,
      Simulation.CreateKind.ofEVMOperation?, hOperands]
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim .create) trivial hDecode hPc]
  simpa [Compact.Instr.openStepResult, Compact.Instr.openStep,
    Assembly.InteractionSemantics.Target.openStepInstrResult,
    Assembly.Target.stepInstrResultWith,
    Assembly.InteractionSemantics.Target.openStepInstr,
    Assembly.Target.stepInstrWith, hOpen,
    Simulation.Interaction.bind,
    Simulation.Interaction.bind_done_error,
    Assembly.PrimOp.haltKind?, Compact.Instr.haltKind?] using
    (Interaction.Executes.done
      (.error EvmYul.EVM.ExecutionException.StackUnderflow :
        Except EVMException StepResult))

theorem raw_create2_stackUnderflow_executes_after_charges
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hShort : state.stack.length < 4)
    (hDecode : Compact.decodeAt bytes pc (.prim .create2))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      []
      (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
  have hPop : (afterDynamicChargeAt state).stack.pop4 = none := by
    simpa [afterDynamicChargeAt, afterMemoryChargeAt, chargeGas] using
      stack_pop4_none_of_length_lt_four hShort
  have hOperands :
      Simulation.CreateKind.evmOperands? .create2
          (afterDynamicChargeAt state).stack = none := by
    simp [Simulation.CreateKind.evmOperands?, hPop]
  have hOpen :
      Assembly.InteractionSemantics.PrimOp.openStep
          .create2 (afterDynamicChargeAt state) =
        Simulation.Interaction.done
          (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
    simp [Assembly.InteractionSemantics.PrimOp.openStep,
      Assembly.InteractionSemantics.PrimOp.createStep,
      Assembly.PrimOp.toEVM,
      Simulation.ExternalKind.ofEVMOperation?,
      Simulation.CallKind.ofEVMOperation?,
      Simulation.CreateKind.ofEVMOperation?, hOperands]
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim .create2) trivial hDecode hPc]
  simpa [Compact.Instr.openStepResult, Compact.Instr.openStep,
    Assembly.InteractionSemantics.Target.openStepInstrResult,
    Assembly.Target.stepInstrResultWith,
    Assembly.InteractionSemantics.Target.openStepInstr,
    Assembly.Target.stepInstrWith, hOpen,
    Simulation.Interaction.bind,
    Simulation.Interaction.bind_done_error,
    Assembly.PrimOp.haltKind?, Compact.Instr.haltKind?] using
    (Interaction.Executes.done
      (.error EvmYul.EVM.ExecutionException.StackUnderflow :
        Except EVMException StepResult))

theorem raw_call_stackUnderflow_executes_after_charges
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hShort : state.stack.length < 7)
    (hDecode : Compact.decodeAt bytes pc (.prim .call))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      []
      (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
  have hPop : (afterDynamicChargeAt state).stack.pop7 = none := by
    simpa [afterDynamicChargeAt, afterMemoryChargeAt, chargeGas] using
      stack_pop7_none_of_length_lt_seven hShort
  have hOperands :
      Simulation.CallKind.evmOperands? .call
          (afterDynamicChargeAt state).stack = none := by
    simp [Simulation.CallKind.evmOperands?, hPop]
  have hOpen :
      Assembly.InteractionSemantics.PrimOp.openStep
          .call (afterDynamicChargeAt state) =
        Simulation.Interaction.done
          (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
    simp [Assembly.InteractionSemantics.PrimOp.openStep,
      Assembly.InteractionSemantics.PrimOp.callStep,
      Assembly.PrimOp.toEVM,
      Simulation.ExternalKind.ofEVMOperation?,
      Simulation.CallKind.ofEVMOperation?,
      Simulation.CreateKind.ofEVMOperation?, hOperands]
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim .call) trivial hDecode hPc]
  simpa [Compact.Instr.openStepResult, Compact.Instr.openStep,
    Assembly.InteractionSemantics.Target.openStepInstrResult,
    Assembly.Target.stepInstrResultWith,
    Assembly.InteractionSemantics.Target.openStepInstr,
    Assembly.Target.stepInstrWith, hOpen,
    Simulation.Interaction.bind,
    Simulation.Interaction.bind_done_error,
    Assembly.PrimOp.haltKind?, Compact.Instr.haltKind?] using
    (Interaction.Executes.done
      (.error EvmYul.EVM.ExecutionException.StackUnderflow :
        Except EVMException StepResult))

theorem raw_callcode_stackUnderflow_executes_after_charges
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hShort : state.stack.length < 7)
    (hDecode : Compact.decodeAt bytes pc (.prim .callcode))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      []
      (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
  have hPop : (afterDynamicChargeAt state).stack.pop7 = none := by
    simpa [afterDynamicChargeAt, afterMemoryChargeAt, chargeGas] using
      stack_pop7_none_of_length_lt_seven hShort
  have hOperands :
      Simulation.CallKind.evmOperands? .callcode
          (afterDynamicChargeAt state).stack = none := by
    simp [Simulation.CallKind.evmOperands?, hPop]
  have hOpen :
      Assembly.InteractionSemantics.PrimOp.openStep
          .callcode (afterDynamicChargeAt state) =
        Simulation.Interaction.done
          (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
    simp [Assembly.InteractionSemantics.PrimOp.openStep,
      Assembly.InteractionSemantics.PrimOp.callStep,
      Assembly.PrimOp.toEVM,
      Simulation.ExternalKind.ofEVMOperation?,
      Simulation.CallKind.ofEVMOperation?,
      Simulation.CreateKind.ofEVMOperation?, hOperands]
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim .callcode) trivial hDecode hPc]
  simpa [Compact.Instr.openStepResult, Compact.Instr.openStep,
    Assembly.InteractionSemantics.Target.openStepInstrResult,
    Assembly.Target.stepInstrResultWith,
    Assembly.InteractionSemantics.Target.openStepInstr,
    Assembly.Target.stepInstrWith, hOpen,
    Simulation.Interaction.bind,
    Simulation.Interaction.bind_done_error,
    Assembly.PrimOp.haltKind?, Compact.Instr.haltKind?] using
    (Interaction.Executes.done
      (.error EvmYul.EVM.ExecutionException.StackUnderflow :
        Except EVMException StepResult))

theorem raw_delegatecall_stackUnderflow_executes_after_charges
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hShort : state.stack.length < 6)
    (hDecode : Compact.decodeAt bytes pc (.prim .delegatecall))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      []
      (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
  have hPop : (afterDynamicChargeAt state).stack.pop6 = none := by
    simpa [afterDynamicChargeAt, afterMemoryChargeAt, chargeGas] using
      stack_pop6_none_of_length_lt_six hShort
  have hOperands :
      Simulation.CallKind.evmOperands? .delegatecall
          (afterDynamicChargeAt state).stack = none := by
    simp [Simulation.CallKind.evmOperands?, hPop]
  have hOpen :
      Assembly.InteractionSemantics.PrimOp.openStep
          .delegatecall (afterDynamicChargeAt state) =
        Simulation.Interaction.done
          (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
    simp [Assembly.InteractionSemantics.PrimOp.openStep,
      Assembly.InteractionSemantics.PrimOp.callStep,
      Assembly.PrimOp.toEVM,
      Simulation.ExternalKind.ofEVMOperation?,
      Simulation.CallKind.ofEVMOperation?,
      Simulation.CreateKind.ofEVMOperation?, hOperands]
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim .delegatecall) trivial hDecode hPc]
  simpa [Compact.Instr.openStepResult, Compact.Instr.openStep,
    Assembly.InteractionSemantics.Target.openStepInstrResult,
    Assembly.Target.stepInstrResultWith,
    Assembly.InteractionSemantics.Target.openStepInstr,
    Assembly.Target.stepInstrWith, hOpen,
    Simulation.Interaction.bind,
    Simulation.Interaction.bind_done_error,
    Assembly.PrimOp.haltKind?, Compact.Instr.haltKind?] using
    (Interaction.Executes.done
      (.error EvmYul.EVM.ExecutionException.StackUnderflow :
        Except EVMException StepResult))

theorem raw_staticcall_stackUnderflow_executes_after_charges
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hShort : state.stack.length < 6)
    (hDecode : Compact.decodeAt bytes pc (.prim .staticcall))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      []
      (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
  have hPop : (afterDynamicChargeAt state).stack.pop6 = none := by
    simpa [afterDynamicChargeAt, afterMemoryChargeAt, chargeGas] using
      stack_pop6_none_of_length_lt_six hShort
  have hOperands :
      Simulation.CallKind.evmOperands? .staticcall
          (afterDynamicChargeAt state).stack = none := by
    simp [Simulation.CallKind.evmOperands?, hPop]
  have hOpen :
      Assembly.InteractionSemantics.PrimOp.openStep
          .staticcall (afterDynamicChargeAt state) =
        Simulation.Interaction.done
          (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
    simp [Assembly.InteractionSemantics.PrimOp.openStep,
      Assembly.InteractionSemantics.PrimOp.callStep,
      Assembly.PrimOp.toEVM,
      Simulation.ExternalKind.ofEVMOperation?,
      Simulation.CallKind.ofEVMOperation?,
      Simulation.CreateKind.ofEVMOperation?, hOperands]
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim .staticcall) trivial hDecode hPc]
  simpa [Compact.Instr.openStepResult, Compact.Instr.openStep,
    Assembly.InteractionSemantics.Target.openStepInstrResult,
    Assembly.Target.stepInstrResultWith,
    Assembly.InteractionSemantics.Target.openStepInstr,
    Assembly.Target.stepInstrWith, hOpen,
    Simulation.Interaction.bind,
    Simulation.Interaction.bind_done_error,
    Assembly.PrimOp.haltKind?, Compact.Instr.haltKind?] using
    (Interaction.Executes.done
      (.error EvmYul.EVM.ExecutionException.StackUnderflow :
        Except EVMException StepResult))

theorem raw_return_executes_after_charges
    {fuel : Nat} {bytes : ByteArray} {pc : Nat}
    {state gasfulFinal : EVMState}
    (hDecode : Compact.decodeAt bytes pc (.prim .return))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc)
    (hStep :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          (EvmYul.Operation.RETURN,
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).2))
        (afterMemoryChargeAt state) = .ok gasfulFinal) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      []
      (.ok (.halted
        { kind := .return
          state := openReturnStateAt state
          output := gasfulFinal.toMachineState.H_return })) := by
  rcases afterDynamic_pop2_of_return_step_ok hStep with
    ⟨stack, μ₀, μ₁, hPop⟩
  have hPrim :
      Assembly.PrimOp.return.step (afterDynamicChargeAt state) =
        .ok (openReturnStateAt state) :=
    prim_return_step_after_dynamic_of_pop2 hPop
  have hOpen :
      Assembly.InteractionSemantics.PrimOp.openStep
          .return (afterDynamicChargeAt state) =
        Simulation.Interaction.done (.ok (openReturnStateAt state)) := by
    simp [Assembly.InteractionSemantics.PrimOp.openStep,
      Assembly.PrimOp.toEVM,
      Simulation.ExternalKind.ofEVMOperation?,
      Simulation.CallKind.ofEVMOperation?,
      Simulation.CreateKind.ofEVMOperation?, hPrim]
  have hExec :
      Interaction.Executes
        (Compact.InteractionSemantics.openRunNResult
          bytes 1 (afterDynamicChargeAt state))
        []
        (.ok (.halted (openReturnHaltAt state))) := by
    rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
      (instr := .prim .return) trivial hDecode hPc]
    simpa [Compact.Instr.openStepResult, Compact.Instr.openStep, hPrim,
      Assembly.InteractionSemantics.Target.openStepInstrResult,
      Assembly.Target.stepInstrResultWith,
      Assembly.InteractionSemantics.Target.openStepInstr,
      Assembly.Target.stepInstrWith, hOpen,
      Simulation.Interaction.bind,
      Simulation.Interaction.pure,
      Simulation.Interaction.bind_done_ok,
      Assembly.PrimOp.haltKind?, Compact.Instr.haltKind?,
      HaltKind.output, openReturnHaltAt] using
      (Interaction.Executes.done
        (.ok (StepResult.halted (openReturnHaltAt state))))
  have hOutput :
      gasfulFinal.toMachineState.H_return =
        (openReturnStateAt state).toMachineState.H_return :=
    SameData.hReturn_eq (sameData_return_step_after_charges hStep)
  simpa [openReturnHaltAt, hOutput.symm] using hExec

theorem raw_revert_executes_after_charges
    {fuel : Nat} {bytes : ByteArray} {pc : Nat}
    {state gasfulFinal : EVMState}
    (hDecode : Compact.decodeAt bytes pc (.prim .revert))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc)
    (hStep :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          (EvmYul.Operation.REVERT,
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).2))
        (afterMemoryChargeAt state) = .ok gasfulFinal) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      []
      (.ok (.halted
        { kind := .revert
          state := openRevertStateAt state
          output := gasfulFinal.toMachineState.H_return })) := by
  rcases afterDynamic_pop2_of_revert_step_ok hStep with
    ⟨stack, μ₀, μ₁, hPop⟩
  have hPrim :
      Assembly.PrimOp.revert.step (afterDynamicChargeAt state) =
        .ok (openRevertStateAt state) :=
    prim_revert_step_after_dynamic_of_pop2 hPop
  have hOpen :
      Assembly.InteractionSemantics.PrimOp.openStep
          .revert (afterDynamicChargeAt state) =
        Simulation.Interaction.done (.ok (openRevertStateAt state)) := by
    simp [Assembly.InteractionSemantics.PrimOp.openStep,
      Assembly.PrimOp.toEVM,
      Simulation.ExternalKind.ofEVMOperation?,
      Simulation.CallKind.ofEVMOperation?,
      Simulation.CreateKind.ofEVMOperation?, hPrim]
  have hExec :
      Interaction.Executes
        (Compact.InteractionSemantics.openRunNResult
          bytes 1 (afterDynamicChargeAt state))
        []
        (.ok (.halted (openRevertHaltAt state))) := by
    rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
      (instr := .prim .revert) trivial hDecode hPc]
    simpa [Compact.Instr.openStepResult, Compact.Instr.openStep, hPrim,
      Assembly.InteractionSemantics.Target.openStepInstrResult,
      Assembly.Target.stepInstrResultWith,
      Assembly.InteractionSemantics.Target.openStepInstr,
      Assembly.Target.stepInstrWith, hOpen,
      Simulation.Interaction.bind,
      Simulation.Interaction.pure,
      Simulation.Interaction.bind_done_ok,
      Assembly.PrimOp.haltKind?, Compact.Instr.haltKind?,
      HaltKind.output, openRevertHaltAt] using
      (Interaction.Executes.done
        (.ok (StepResult.halted (openRevertHaltAt state))))
  have hOutput :
      gasfulFinal.toMachineState.H_return =
        (openRevertStateAt state).toMachineState.H_return :=
    SameData.hReturn_eq (sameData_revert_step_after_charges hStep)
  simpa [openRevertHaltAt, hOutput.symm] using hExec

def callTargetAddress (operands : CallOperands) : EvmYul.AccountAddress :=
  EvmYul.AccountAddress.ofUInt256 operands.address

def callRecipientAddress (kind : CallKind) (preCostState : EVMState)
    (operands : CallOperands) : EvmYul.AccountAddress :=
  match kind with
  | .call | .staticcall => callTargetAddress operands
  | .callcode | .delegatecall => preCostState.executionEnv.codeOwner

def callValue (kind : CallKind) (operands : CallOperands) : Word :=
  (kind.canonicalOperands operands).valueArg

def callForwardedGas (kind : CallKind) (preCostState : EVMState)
    (operands : CallOperands) : Nat :=
  EvmYul.EVM.Ccallgas
    (callTargetAddress operands)
    (callRecipientAddress kind preCostState operands)
    (callValue kind operands)
    operands.requestedGas
    preCostState.accountMap
    preCostState.toMachineState
    preCostState.substate

def callParentGasCost (kind : CallKind) (preCostState : EVMState)
    (operands : CallOperands) : Nat :=
  EvmYul.EVM.Ccall
    (callTargetAddress operands)
    (callRecipientAddress kind preCostState operands)
    (callValue kind operands)
    operands.requestedGas
    preCostState.accountMap
    preCostState.toMachineState
    preCostState.substate

def callFinalGas (preCostState : EVMState) (parentGasCost : Nat)
    (returnedGas : Word) : Word :=
  (preCostState.gasAvailable - EvmYul.UInt256.ofNat parentGasCost) +
    returnedGas

theorem dynamicGasCostAt_call_args_eq_parentGasCost
    (kind : CallKind) (state : EVMState) (operands : CallOperands)
    (rest : EvmYul.Stack Word)
    (hOp : decodedOperationAt state = kind.toEVMOperation)
    (hStack : state.stack = kind.args operands ++ rest) :
    dynamicGasCostAt state =
      callParentGasCost kind (afterMemoryChargeAt state)
        (kind.canonicalOperands operands) := by
  cases kind <;>
    simp [dynamicGasCostAt, callParentGasCost, callTargetAddress,
      callRecipientAddress, callValue, hOp, hStack, CallKind.args,
      CallKind.canonicalOperands, CallKind.toEVMOperation, EvmYul.EVM.C',
      afterMemoryChargeAt, chargeGas, EvmYul.UInt256.ofNat]
  all_goals rfl

theorem stack_eq_of_pop6
    {α : Type} {stack rest : EvmYul.Stack α}
    {a b c d e f : α}
    (hPop : stack.pop6 = some (rest, a, b, c, d, e, f)) :
    stack = a :: b :: c :: d :: e :: f :: rest := by
  cases stack with
  | nil => simp [EvmYul.Stack.pop6] at hPop
  | cons x xs =>
      cases xs with
      | nil => simp [EvmYul.Stack.pop6] at hPop
      | cons y ys =>
          cases ys with
          | nil => simp [EvmYul.Stack.pop6] at hPop
          | cons z zs =>
              cases zs with
              | nil => simp [EvmYul.Stack.pop6] at hPop
              | cons w ws =>
                  cases ws with
                  | nil => simp [EvmYul.Stack.pop6] at hPop
                  | cons v vs =>
                      cases vs with
                      | nil => simp [EvmYul.Stack.pop6] at hPop
                      | cons u us =>
                          simp [EvmYul.Stack.pop6] at hPop
                          rcases hPop with
                            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
                          rfl

theorem stack_eq_of_pop7
    {α : Type} {stack rest : EvmYul.Stack α}
    {a b c d e f g : α}
    (hPop : stack.pop7 = some (rest, a, b, c, d, e, f, g)) :
    stack = a :: b :: c :: d :: e :: f :: g :: rest := by
  cases stack with
  | nil => simp [EvmYul.Stack.pop7] at hPop
  | cons x xs =>
      cases xs with
      | nil => simp [EvmYul.Stack.pop7] at hPop
      | cons y ys =>
          cases ys with
          | nil => simp [EvmYul.Stack.pop7] at hPop
          | cons z zs =>
              cases zs with
              | nil => simp [EvmYul.Stack.pop7] at hPop
              | cons w ws =>
                  cases ws with
                  | nil => simp [EvmYul.Stack.pop7] at hPop
                  | cons v vs =>
                      cases vs with
                      | nil => simp [EvmYul.Stack.pop7] at hPop
                      | cons u us =>
                          cases us with
                          | nil => simp [EvmYul.Stack.pop7] at hPop
                          | cons t ts =>
                              simp [EvmYul.Stack.pop7] at hPop
                              rcases hPop with
                                ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
                              rfl

theorem CallKind.stack_eq_args_append_of_evmOperands
    {kind : CallKind} {stack rest : EvmYul.Stack EvmYul.UInt256}
    {operands : CallOperands}
    (hOperands : kind.evmOperands? stack = some (rest, operands)) :
    stack = kind.args operands ++ rest := by
  cases kind with
  | call =>
      unfold CallKind.evmOperands? at hOperands
      cases hPop : stack.pop7 with
      | none => simp [hPop] at hOperands
      | some popped =>
          rcases popped with
            ⟨parsedRest, gas, address, value, inputOffset, inputSize,
              outputOffset, outputSize⟩
          simp [hPop] at hOperands
          rcases hOperands with ⟨rfl, rfl⟩
          simpa [CallKind.args] using stack_eq_of_pop7 hPop
  | callcode =>
      unfold CallKind.evmOperands? at hOperands
      cases hPop : stack.pop7 with
      | none => simp [hPop] at hOperands
      | some popped =>
          rcases popped with
            ⟨parsedRest, gas, address, value, inputOffset, inputSize,
              outputOffset, outputSize⟩
          simp [hPop] at hOperands
          rcases hOperands with ⟨rfl, rfl⟩
          simpa [CallKind.args] using stack_eq_of_pop7 hPop
  | delegatecall =>
      unfold CallKind.evmOperands? at hOperands
      cases hPop : stack.pop6 with
      | none => simp [hPop] at hOperands
      | some popped =>
          rcases popped with
            ⟨parsedRest, gas, address, inputOffset, inputSize,
              outputOffset, outputSize⟩
          simp [hPop] at hOperands
          rcases hOperands with ⟨rfl, rfl⟩
          simpa [CallKind.args] using stack_eq_of_pop6 hPop
  | staticcall =>
      unfold CallKind.evmOperands? at hOperands
      cases hPop : stack.pop6 with
      | none => simp [hPop] at hOperands
      | some popped =>
          rcases popped with
            ⟨parsedRest, gas, address, inputOffset, inputSize,
              outputOffset, outputSize⟩
          simp [hPop] at hOperands
          rcases hOperands with ⟨rfl, rfl⟩
          simpa [CallKind.args] using stack_eq_of_pop6 hPop

theorem CallKind.canonicalOperands_eq_of_evmOperands
    {kind : CallKind} {stack rest : EvmYul.Stack EvmYul.UInt256}
    {operands : CallOperands}
    (hOperands : kind.evmOperands? stack = some (rest, operands)) :
    kind.canonicalOperands operands = operands := by
  have hStack :=
    CallKind.stack_eq_args_append_of_evmOperands hOperands
  rw [hStack] at hOperands
  simpa using hOperands

/-- Gas accounting for a CALL-family external boundary. The child execution is
not verified here; `returnedGas` is supplied by the open strategy response that
models the child frame. -/
structure CallBoundaryAccounting
    (kind : CallKind) (preCostState : EVMState)
    (operands : CallOperands) (parentGasCost forwardedGas : Nat)
    (returnedGas finalGas : Word) : Prop where
  parentGasCost_eq :
    parentGasCost = callParentGasCost kind preCostState operands
  forwardedGas_eq :
    forwardedGas = callForwardedGas kind preCostState operands
  finalGas_eq :
    finalGas = callFinalGas preCostState parentGasCost returnedGas

theorem callBoundaryAccounting_canonical
    (kind : CallKind) (preCostState : EVMState)
    (operands : CallOperands) (returnedGas : Word) :
    CallBoundaryAccounting kind preCostState operands
      (callParentGasCost kind preCostState operands)
      (callForwardedGas kind preCostState operands)
      returnedGas
      (callFinalGas preCostState
        (callParentGasCost kind preCostState operands) returnedGas) where
  parentGasCost_eq := rfl
  forwardedGas_eq := rfl
  finalGas_eq := rfl

def callResponseFinalGas (kind : CallKind) (preCostState : EVMState)
    (operands : CallOperands) (response : CallResponse) : Word :=
  callFinalGas preCostState (callParentGasCost kind preCostState operands)
    response.returnedGas

def CallResponseGasAccounting
    (kind : CallKind) (preCostState : EVMState)
    (operands : CallOperands) (response : CallResponse)
    (finalGas : Word) : Prop :=
  CallBoundaryAccounting kind preCostState operands
    (callParentGasCost kind preCostState operands)
    (callForwardedGas kind preCostState operands)
    response.returnedGas
    finalGas

theorem callResponseGasAccounting_canonical
    (kind : CallKind) (preCostState : EVMState)
    (operands : CallOperands) (response : CallResponse) :
    CallResponseGasAccounting kind preCostState operands response
      (callResponseFinalGas kind preCostState operands response) := by
  simpa [CallResponseGasAccounting, callResponseFinalGas] using
    callBoundaryAccounting_canonical kind preCostState operands
      response.returnedGas

theorem callResponseGasAccounting_finalGas_eq
    {kind : CallKind} {preCostState : EVMState}
    {operands : CallOperands} {response : CallResponse}
    {finalGas : Word}
    (hGas :
      CallResponseGasAccounting kind preCostState operands response
        finalGas) :
    finalGas = callResponseFinalGas kind preCostState operands response := by
  simpa [CallResponseGasAccounting, callResponseFinalGas] using
    hGas.finalGas_eq

theorem uint256_add_sub_left (base final : EvmYul.UInt256) :
    base + (final - base) = final := by
  cases base with
  | mk base =>
    cases final with
    | mk final =>
      change EvmYul.UInt256.mk (base + (final - base)) =
        EvmYul.UInt256.mk final
      congr 1
      abel

theorem call_result_status_bool
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {gas source recipient target value apparentValue inputOffset inputSize
      outputOffset outputSize status : EvmYul.UInt256}
    {permission : Bool} {state result : EVMState}
    (hCall :
      EvmYul.EVM.call fuel gasCost blobVersionedHashes gas source recipient
        target value apparentValue inputOffset inputSize outputOffset outputSize
        permission state = .ok (status, result)) :
    ∃ success : Bool, status = Bool.toUInt256 success := by
  cases fuel with
  | zero =>
      simp [EvmYul.EVM.call] at hCall
  | succ fuel =>
      simp only [EvmYul.EVM.call] at hCall
      split at hCall
      · generalize hTheta :
          EvmYul.EVM.Θ fuel blobVersionedHashes state.createdAccounts
            state.genesisBlockHeader state.blocks state.accountMap state.σ₀
            { totalGasUsedInBlock := state.totalGasUsedInBlock
              transactionReceipts := state.transactionReceipts }
            (state.addAccessedAccount
              (EvmYul.AccountAddress.ofUInt256 target)).substate
            (EvmYul.AccountAddress.ofUInt256 source)
            state.executionEnv.sender
            (EvmYul.AccountAddress.ofUInt256 recipient)
            (EvmYul.toExecute .EVM state.accountMap
              (EvmYul.AccountAddress.ofUInt256 target))
            (EvmYul.UInt256.ofNat
              (EvmYul.EVM.Ccallgas
                (EvmYul.AccountAddress.ofUInt256 target)
                (EvmYul.AccountAddress.ofUInt256 recipient)
                value gas state.accountMap state.toMachineState
                state.substate))
            (EvmYul.UInt256.ofNat state.executionEnv.gasPrice)
            value apparentValue
            (state.memory.readWithPadding inputOffset.toNat inputSize.toNat)
            (state.executionEnv.depth + 1) state.executionEnv.header
            permission = thetaResult at hCall
        cases thetaResult with
        | error error => simp_all
        | ok resultTheta =>
            simp at hCall
            split at hCall
            · exact ⟨false, hCall.1.symm⟩
            · exact ⟨true, hCall.1.symm⟩
      · simp at hCall
        exact ⟨false, hCall.1.symm⟩

theorem call_result_pc
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {gas source recipient target value apparentValue inputOffset inputSize
      outputOffset outputSize status : EvmYul.UInt256}
    {permission : Bool} {state result : EVMState}
    (hCall :
      EvmYul.EVM.call fuel gasCost blobVersionedHashes gas source recipient
        target value apparentValue inputOffset inputSize outputOffset outputSize
        permission state = .ok (status, result)) :
    result.pc = state.pc := by
  cases fuel with
  | zero =>
      simp [EvmYul.EVM.call] at hCall
  | succ fuel =>
      simp only [EvmYul.EVM.call] at hCall
      split at hCall
      · generalize hTheta :
          EvmYul.EVM.Θ fuel blobVersionedHashes state.createdAccounts
            state.genesisBlockHeader state.blocks state.accountMap state.σ₀
            { totalGasUsedInBlock := state.totalGasUsedInBlock
              transactionReceipts := state.transactionReceipts }
            (state.addAccessedAccount
              (EvmYul.AccountAddress.ofUInt256 target)).substate
            (EvmYul.AccountAddress.ofUInt256 source)
            state.executionEnv.sender
            (EvmYul.AccountAddress.ofUInt256 recipient)
            (EvmYul.toExecute .EVM state.accountMap
              (EvmYul.AccountAddress.ofUInt256 target))
            (EvmYul.UInt256.ofNat
              (EvmYul.EVM.Ccallgas
                (EvmYul.AccountAddress.ofUInt256 target)
                (EvmYul.AccountAddress.ofUInt256 recipient)
                value gas state.accountMap state.toMachineState
                state.substate))
            (EvmYul.UInt256.ofNat state.executionEnv.gasPrice)
            value apparentValue
            (state.memory.readWithPadding inputOffset.toNat inputSize.toNat)
            (state.executionEnv.depth + 1) state.executionEnv.header
            permission = thetaResult at hCall
        cases thetaResult with
        | error error => simp_all
        | ok resultTheta =>
            simp at hCall
            split at hCall <;> rcases hCall with ⟨_, rfl⟩ <;> rfl
      · simp at hCall
        rcases hCall with ⟨_, rfl⟩
        rfl

def callReturnedGasFromResult
    (kind : CallKind) (preCostState : EVMState)
    (operands : CallOperands) (result : EVMState) : EvmYul.UInt256 :=
  result.gasAvailable -
    (preCostState.gasAvailable -
      EvmYul.UInt256.ofNat
        (callParentGasCost kind preCostState operands))

/-- Build the open CALL response represented by an actual concrete parent
result. `returnedGas` is the gas credited back after the checked parent cost;
the mutable world and return bytes are projected from that concrete result. -/
def callResponseFromResult
    (kind : CallKind) (preCostState : EVMState)
    (operands : CallOperands) (success : Bool)
    (result : EVMState) : CallResponse where
  success := success
  returnData := result.returnData
  postWorld := OpenWorld.ofEVMShared result.toSharedState
  returnedGas :=
    callReturnedGasFromResult kind preCostState operands result

theorem callResponseFromResult_finalGas
    (kind : CallKind) (preCostState : EVMState)
    (operands : CallOperands) (success : Bool)
    (result : EVMState) :
    callResponseFinalGas kind preCostState operands
        (callResponseFromResult kind preCostState operands success result) =
      result.gasAvailable := by
  apply uint256_add_sub_left

theorem call_result_openSameData
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {gas source recipient target value apparentValue inputOffset inputSize
      outputOffset outputSize status returnedGas : EvmYul.UInt256}
    {permission success : Bool} {state result : EVMState}
    {rest : EvmYul.Stack EvmYul.UInt256}
    (hCall :
      EvmYul.EVM.call fuel gasCost blobVersionedHashes gas source recipient
        target value apparentValue inputOffset inputSize outputOffset outputSize
        permission state = .ok (status, result))
    (hStatus : status = Bool.toUInt256 success) :
    OpenSameData
      (result.replaceStackAndIncrPC (rest.push status))
      (InteractionSemantics.EVMState.finishCall
        (chargeGas state gasCost) rest
        { inputOffset := inputOffset
          inputSize := inputSize
          outputOffset := outputOffset
          outputSize := outputSize }
        { success := success
          returnData := result.returnData
          postWorld := OpenWorld.ofEVMShared result.toSharedState
          returnedGas := returnedGas }) := by
  have hResponseStatus :
      ({ success := success
         returnData := result.returnData
         postWorld := OpenWorld.ofEVMShared result.toSharedState
         returnedGas := returnedGas } : CallResponse).statusWord = status := by
    simpa [CallResponse.statusWord, Bool.toUInt256] using hStatus.symm
  cases fuel with
  | zero =>
      simp [EvmYul.EVM.call] at hCall
  | succ fuel =>
      simp only [EvmYul.EVM.call] at hCall
      split at hCall
      · generalize hTheta :
          EvmYul.EVM.Θ fuel blobVersionedHashes state.createdAccounts
            state.genesisBlockHeader state.blocks state.accountMap state.σ₀
            { totalGasUsedInBlock := state.totalGasUsedInBlock
              transactionReceipts := state.transactionReceipts }
            (state.addAccessedAccount
              (EvmYul.AccountAddress.ofUInt256 target)).substate
            (EvmYul.AccountAddress.ofUInt256 source)
            state.executionEnv.sender
            (EvmYul.AccountAddress.ofUInt256 recipient)
            (EvmYul.toExecute .EVM state.accountMap
              (EvmYul.AccountAddress.ofUInt256 target))
            (EvmYul.UInt256.ofNat
              (EvmYul.EVM.Ccallgas
                (EvmYul.AccountAddress.ofUInt256 target)
                (EvmYul.AccountAddress.ofUInt256 recipient)
                value gas state.accountMap state.toMachineState
                state.substate))
            (EvmYul.UInt256.ofNat state.executionEnv.gasPrice)
            value apparentValue
            (state.memory.readWithPadding inputOffset.toNat inputSize.toNat)
            (state.executionEnv.depth + 1) state.executionEnv.header
            permission = thetaResult at hCall
        cases thetaResult with
        | error error => simp_all
        | ok resultTheta =>
            simp at hCall
            split at hCall
            · rcases hCall with ⟨hStatusResult, hResult⟩
              subst result
              constructor
              · simp [InteractionSemantics.EVMState.finishCall,
                  InteractionSemantics.EVMState.installWorld,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC, chargeGas,
                  OpenWorld.ofEVMShared, OpenWorld.installEVMShared]
              · simp [eraseOpenWorldData,
                  InteractionSemantics.EVMState.finishCall,
                  InteractionSemantics.EVMState.installWorld,
                  CallLocal.finishMachine, chargeGas, eraseControl, eraseGas,
                  EvmYul.MachineState.finishExternalCall,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC, OpenWorld.installEVMShared,
                  OpenWorld.installEVM, EvmYul.Stack.push,
                  CallResponse.statusWord, Bool.toUInt256, hStatus]
            · rcases hCall with ⟨hStatusResult, hResult⟩
              subst result
              constructor
              · simp [InteractionSemantics.EVMState.finishCall,
                  InteractionSemantics.EVMState.installWorld,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC, chargeGas,
                  OpenWorld.ofEVMShared, OpenWorld.installEVMShared]
              · simp [eraseOpenWorldData,
                  InteractionSemantics.EVMState.finishCall,
                  InteractionSemantics.EVMState.installWorld,
                  CallLocal.finishMachine, chargeGas, eraseControl, eraseGas,
                  EvmYul.MachineState.finishExternalCall,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC, OpenWorld.installEVMShared,
                  OpenWorld.installEVM, EvmYul.Stack.push,
                  CallResponse.statusWord, Bool.toUInt256, hStatus]
      · simp at hCall
        rcases hCall with ⟨hStatusResult, hResult⟩
        subst result
        constructor
        · simp [InteractionSemantics.EVMState.finishCall,
            InteractionSemantics.EVMState.installWorld,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC, chargeGas,
            OpenWorld.ofEVMShared, OpenWorld.installEVMShared]
        · simp [eraseOpenWorldData,
            InteractionSemantics.EVMState.finishCall,
            InteractionSemantics.EVMState.installWorld,
            CallLocal.finishMachine, chargeGas, eraseControl, eraseGas,
            EvmYul.MachineState.finishExternalCall,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC, OpenWorld.installEVMShared,
            OpenWorld.installEVM, EvmYul.Stack.push,
            CallResponse.statusWord, Bool.toUInt256, hStatus]

/-- Relates the concrete post-CALL parent frame to the open post-CALL frame.
The open frame keeps source/Yul semantics cost-model-free; the concrete frame's
gas is checked against the response's returned child gas here. -/
structure CallResponseStateRel
    (kind : CallKind) (preCostState : EVMState)
    (operands : CallOperands) (response : CallResponse)
    (gasfulState openState : EVMState) : Prop where
  openData : OpenSameData gasfulState openState
  pc_eq : gasfulState.pc = openState.pc
  gasAccounting :
    CallResponseGasAccounting kind preCostState operands response
      gasfulState.gasAvailable

theorem CallResponseStateRel.openStateRel
    {kind : CallKind} {preCostState : EVMState}
    {operands : CallOperands} {response : CallResponse}
    {gasfulState openState : EVMState}
    (hRel : CallResponseStateRel kind preCostState operands response
      gasfulState openState) :
    OpenStateRel gasfulState openState :=
  ⟨hRel.openData, hRel.pc_eq⟩

theorem callResponseStateRel_of_openSameData
    {kind : CallKind} {preCostState : EVMState}
    {operands : CallOperands} {response : CallResponse}
    {gasfulState openState : EVMState}
    (hOpen : OpenSameData gasfulState openState)
    (hPc : gasfulState.pc = openState.pc)
    (hGas :
      gasfulState.gasAvailable =
        callResponseFinalGas kind preCostState operands response) :
    CallResponseStateRel kind preCostState operands response
      gasfulState openState := by
  refine ⟨hOpen, hPc, ?_⟩
  rw [hGas]
  exact
    callResponseGasAccounting_canonical kind preCostState operands
      response

theorem callResponseStateRel_of_sameData
    {kind : CallKind} {preCostState : EVMState}
    {operands : CallOperands} {response : CallResponse}
    {gasfulState openState : EVMState}
    (hSame : SameData gasfulState openState)
    (hPc : gasfulState.pc = openState.pc)
    (hGas :
      gasfulState.gasAvailable =
        callResponseFinalGas kind preCostState operands response) :
    CallResponseStateRel kind preCostState operands response
      gasfulState openState := by
  exact
    callResponseStateRel_of_openSameData
      (OpenSameData.of_sameData hSame) hPc hGas

theorem callResponseStateRel_of_call_result
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {gas source recipient target value apparentValue inputOffset inputSize
      outputOffset outputSize status : EvmYul.UInt256}
    {permission success : Bool} {state result : EVMState}
    {rest : EvmYul.Stack EvmYul.UInt256}
    (kind : CallKind) (operands : CallOperands)
    (hParentCost :
      gasCost = callParentGasCost kind state operands)
    (hCall :
      EvmYul.EVM.call fuel gasCost blobVersionedHashes gas source recipient
        target value apparentValue inputOffset inputSize outputOffset outputSize
        permission state = .ok (status, result))
    (hStatus : status = Bool.toUInt256 success) :
    CallResponseStateRel kind state operands
      (callResponseFromResult kind state operands success result)
      (result.replaceStackAndIncrPC (rest.push status))
      (InteractionSemantics.EVMState.finishCall
        (chargeGas state (callParentGasCost kind state operands)) rest
        { inputOffset := inputOffset
          inputSize := inputSize
          outputOffset := outputOffset
          outputSize := outputSize }
        (callResponseFromResult kind state operands success result)) := by
  apply callResponseStateRel_of_openSameData
  · simpa [callResponseFromResult, hParentCost] using
      (call_result_openSameData
        (returnedGas :=
          callReturnedGasFromResult kind state operands result)
        hCall hStatus)
  · simp [InteractionSemantics.EVMState.finishCall,
      InteractionSemantics.EVMState.installWorld,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, chargeGas, call_result_pc hCall]
  · simpa [EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] using
      (callResponseFromResult_finalGas
        kind state operands success result).symm

def callInputState (state : EVMState) : EVMState :=
  { state with execLength := state.execLength + 1 }

@[simp] theorem callParentGasCost_callInputState
    (kind : CallKind) (state : EVMState) (operands : CallOperands) :
    callParentGasCost kind (callInputState state) operands =
      callParentGasCost kind state operands := by
  cases kind <;> rfl

@[simp] theorem callForwardedGas_callInputState
    (kind : CallKind) (state : EVMState) (operands : CallOperands) :
    callForwardedGas kind (callInputState state) operands =
      callForwardedGas kind state operands := by
  cases kind <;> rfl

theorem finishCall_callInputState_openSameData
    (state : EVMState) (cost : Nat)
    (rest : EvmYul.Stack EvmYul.UInt256)
    (callLocal : CallLocal) (response : CallResponse) :
    OpenSameData
      (InteractionSemantics.EVMState.finishCall
        (chargeGas (callInputState state) cost) rest callLocal response)
      (InteractionSemantics.EVMState.finishCall
        (chargeGas state cost) rest callLocal response) := by
  constructor
  · simp [InteractionSemantics.EVMState.finishCall,
      InteractionSemantics.EVMState.installWorld,
      EvmYul.EVM.State.incrPC, chargeGas, callInputState,
      OpenWorld.ofEVMShared, OpenWorld.installEVMShared]
  · simp [eraseOpenWorldData,
      InteractionSemantics.EVMState.finishCall,
      InteractionSemantics.EVMState.installWorld,
      CallLocal.finishMachine, chargeGas, callInputState,
      eraseControl, eraseGas, EvmYul.EVM.State.incrPC,
      OpenWorld.installEVMShared, OpenWorld.installEVM,
      EvmYul.Stack.push]

def concreteCall
    (kind : CallKind) (fuel gasCost : Nat)
    (state : EVMState) (operands : CallOperands) :=
  match kind with
  | .call =>
      EvmYul.EVM.call fuel gasCost state.executionEnv.blobVersionedHashes
        operands.requestedGas (.ofNat state.executionEnv.codeOwner)
        operands.address operands.address operands.valueArg operands.valueArg
        operands.inputOffset operands.inputSize operands.outputOffset
        operands.outputSize state.executionEnv.perm state
  | .callcode =>
      EvmYul.EVM.call fuel gasCost state.executionEnv.blobVersionedHashes
        operands.requestedGas (.ofNat state.executionEnv.codeOwner)
        (.ofNat state.executionEnv.codeOwner) operands.address
        operands.valueArg operands.valueArg operands.inputOffset
        operands.inputSize operands.outputOffset operands.outputSize
        state.executionEnv.perm state
  | .delegatecall =>
      EvmYul.EVM.call fuel gasCost state.executionEnv.blobVersionedHashes
        operands.requestedGas (.ofNat state.executionEnv.source)
        (.ofNat state.executionEnv.codeOwner) operands.address
        (EvmYul.UInt256.ofNat 0) state.executionEnv.weiValue
        operands.inputOffset operands.inputSize operands.outputOffset
        operands.outputSize state.executionEnv.perm state
  | .staticcall =>
      EvmYul.EVM.call fuel gasCost state.executionEnv.blobVersionedHashes
        operands.requestedGas (.ofNat state.executionEnv.codeOwner)
        operands.address operands.address (EvmYul.UInt256.ofNat 0)
        (EvmYul.UInt256.ofNat 0) operands.inputOffset operands.inputSize
        operands.outputOffset operands.outputSize false state

def concreteCallStep
    (kind : CallKind) (fuel gasCost : Nat)
    (state : EVMState) (rest : EvmYul.Stack EvmYul.UInt256)
    (operands : CallOperands) : Except EVMException EVMState :=
  match fuel with
  | 0 => .error .OutOfFuel
  | childFuel + 1 => do
      let (status, result) ←
        concreteCall kind childFuel gasCost (callInputState state) operands
      .ok (result.replaceStackAndIncrPC (rest.push status))

section ConcreteCallStep

local instance optionExceptLift :
    MonadLift Option (Except EVMException) :=
  ⟨Option.option (.error .StackUnderflow) .ok⟩

private theorem optionLiftSome {α : Type} (value : α) :
    (liftM (some value) : Except EVMException α) = .ok value := by
  rfl

theorem evm_step_call_eq_concreteCallStep
    (kind : CallKind) (fuel gasCost : Nat)
    (state : EVMState) (rest : EvmYul.Stack EvmYul.UInt256)
    (operands : CallOperands) (arg : Option (EvmYul.UInt256 × Nat))
    (hStack : state.stack = kind.args operands ++ rest) :
    EvmYul.EVM.step fuel gasCost (some (kind.toEVMOperation, arg)) state =
      concreteCallStep kind fuel gasCost state rest operands := by
  cases fuel <;> cases kind <;>
    simp [EvmYul.EVM.step, concreteCallStep, concreteCall,
      callInputState, CallKind.args, CallKind.toEVMOperation, hStack,
      EvmYul.Stack.pop6, EvmYul.Stack.pop7, EvmYul.Stack.push,
      EvmYul.UInt256.ofNat, Id.run, liftM, optionLiftSome]

end ConcreteCallStep

theorem concreteCall_responseStateRel
    {kind : CallKind} {fuel gasCost : Nat}
    {state result : EVMState} {operands : CallOperands}
    {status : EvmYul.UInt256} {rest : EvmYul.Stack EvmYul.UInt256}
    (hParentCost :
      gasCost = callParentGasCost kind state operands)
    (hCall :
      concreteCall kind fuel gasCost state operands = .ok (status, result)) :
    ∃ success : Bool,
      CallResponseStateRel kind state operands
        (callResponseFromResult kind state operands success result)
        (result.replaceStackAndIncrPC (rest.push status))
        (InteractionSemantics.EVMState.finishCall
          (chargeGas state (callParentGasCost kind state operands)) rest
          operands.callLocal
          (callResponseFromResult kind state operands success result)) := by
  cases kind with
  | call =>
      have hCall' := hCall
      simp only [concreteCall] at hCall'
      obtain ⟨success, hStatus⟩ := call_result_status_bool hCall'
      refine ⟨success, ?_⟩
      simpa [CallOperands.callLocal] using
        (callResponseStateRel_of_call_result
          .call operands hParentCost hCall' hStatus)
  | callcode =>
      have hCall' := hCall
      simp only [concreteCall] at hCall'
      obtain ⟨success, hStatus⟩ := call_result_status_bool hCall'
      refine ⟨success, ?_⟩
      simpa [CallOperands.callLocal] using
        (callResponseStateRel_of_call_result
          .callcode operands hParentCost hCall' hStatus)
  | delegatecall =>
      have hCall' := hCall
      simp only [concreteCall] at hCall'
      obtain ⟨success, hStatus⟩ := call_result_status_bool hCall'
      refine ⟨success, ?_⟩
      simpa [CallOperands.callLocal] using
        (callResponseStateRel_of_call_result
          .delegatecall operands hParentCost hCall' hStatus)
  | staticcall =>
      have hCall' := hCall
      simp only [concreteCall] at hCall'
      obtain ⟨success, hStatus⟩ := call_result_status_bool hCall'
      refine ⟨success, ?_⟩
      simpa [CallOperands.callLocal] using
        (callResponseStateRel_of_call_result
          .staticcall operands hParentCost hCall' hStatus)

theorem evm_step_call_responseStateRel
    {kind : CallKind} {fuel gasCost : Nat}
    {state gasfulNext : EVMState} {operands : CallOperands}
    {rest : EvmYul.Stack EvmYul.UInt256}
    {arg : Option (EvmYul.UInt256 × Nat)}
    (hStack : state.stack = kind.args operands ++ rest)
    (hParentCost :
      gasCost =
        callParentGasCost kind (callInputState state) operands)
    (hStep :
      EvmYul.EVM.step fuel gasCost
        (some (kind.toEVMOperation, arg)) state = .ok gasfulNext) :
    ∃ response : CallResponse,
      CallResponseStateRel kind (callInputState state) operands response
        gasfulNext
        (InteractionSemantics.EVMState.finishCall
          (chargeGas (callInputState state)
            (callParentGasCost kind (callInputState state) operands))
          rest operands.callLocal response) := by
  rw [evm_step_call_eq_concreteCallStep
    kind fuel gasCost state rest operands arg hStack] at hStep
  cases fuel with
  | zero =>
      simp [concreteCallStep] at hStep
  | succ childFuel =>
      simp only [concreteCallStep] at hStep
      generalize hCall :
        concreteCall kind childFuel gasCost (callInputState state) operands =
          callResult at hStep
      cases callResult with
      | error error => simp_all
      | ok pair =>
          rcases pair with ⟨status, result⟩
          simp at hStep
          subst gasfulNext
          obtain ⟨success, hRel⟩ :=
            concreteCall_responseStateRel
              (rest := rest) hParentCost hCall
          exact
            ⟨callResponseFromResult kind (callInputState state)
                operands success result,
              hRel⟩

theorem evm_step_call_responseStateRel_at
    {fuel : Nat} {state gasfulNext : EVMState}
    {rest : EvmYul.Stack EvmYul.UInt256}
    {operands : CallOperands}
    {arg : Option (EvmYul.UInt256 × Nat)}
    (kind : CallKind)
    (hOp : decodedOperationAt state = kind.toEVMOperation)
    (hOperands :
      kind.evmOperands? state.stack = some (rest, operands))
    (hStep :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some (kind.toEVMOperation, arg)) (afterMemoryChargeAt state) =
          .ok gasfulNext) :
    ∃ response : CallResponse,
      CallResponseStateRel kind (afterMemoryChargeAt state) operands response
        gasfulNext
        (InteractionSemantics.EVMState.finishCall
          (afterDynamicChargeAt state) rest operands.callLocal response) := by
  have hStack :=
    CallKind.stack_eq_args_append_of_evmOperands hOperands
  have hCanonical :=
    CallKind.canonicalOperands_eq_of_evmOperands hOperands
  have hParentBase :=
    dynamicGasCostAt_call_args_eq_parentGasCost
      kind state operands rest hOp hStack
  have hStackMemory :
      (afterMemoryChargeAt state).stack = kind.args operands ++ rest := by
    simpa [afterMemoryChargeAt, chargeGas] using hStack
  have hParentCost :
      dynamicGasCostAt state =
        callParentGasCost kind
          (callInputState (afterMemoryChargeAt state)) operands := by
    simpa [callInputState, callParentGasCost, callTargetAddress,
      callRecipientAddress, callValue, hCanonical] using hParentBase
  have hParentMemory :
      dynamicGasCostAt state =
        callParentGasCost kind (afterMemoryChargeAt state) operands := by
    simpa [hCanonical] using hParentBase
  obtain ⟨response, hResponse⟩ :=
    evm_step_call_responseStateRel
      hStackMemory hParentCost hStep
  have hOpenResponse :
      OpenSameData gasfulNext
        (InteractionSemantics.EVMState.finishCall
          (chargeGas (callInputState (afterMemoryChargeAt state))
            (dynamicGasCostAt state))
          rest operands.callLocal response) := by
    simpa [hParentCost] using hResponse.openData
  have hOpenControl :=
    finishCall_callInputState_openSameData
      (afterMemoryChargeAt state) (dynamicGasCostAt state)
      rest operands.callLocal response
  have hOpen :
      OpenSameData gasfulNext
        (InteractionSemantics.EVMState.finishCall
          (afterDynamicChargeAt state) rest operands.callLocal response) := by
    simpa [afterDynamicChargeAt] using
      hOpenResponse.trans hOpenControl
  have hPc :
      gasfulNext.pc =
        (InteractionSemantics.EVMState.finishCall
          (afterDynamicChargeAt state) rest operands.callLocal response).pc := by
    simpa [hParentCost, afterDynamicChargeAt,
      InteractionSemantics.EVMState.finishCall,
      InteractionSemantics.EVMState.installWorld,
      EvmYul.EVM.State.incrPC, chargeGas, callInputState] using
      hResponse.pc_eq
  have hGasInput :=
    callResponseGasAccounting_finalGas_eq hResponse.gasAccounting
  have hGas :
      gasfulNext.gasAvailable =
        callResponseFinalGas kind (afterMemoryChargeAt state)
          operands response := by
    simpa [callResponseFinalGas, callInputState, hParentMemory] using
      hGasInput
  exact
    ⟨response, callResponseStateRel_of_openSameData hOpen hPc hGas⟩

def callPrimOp : CallKind → PrimOp
  | .call => .call
  | .callcode => .callcode
  | .delegatecall => .delegatecall
  | .staticcall => .staticcall

def callExternalQuery (kind : CallKind) (state : EVMState)
    (operands : CallOperands) : Query :=
    .external (OpenWorld.ofEVMShared state.toSharedState)
      (.call
        ((ExternalFrame.ofShared state.toSharedState).callRequest
          kind operands))

def callExternalExchange (kind : CallKind) (state : EVMState)
    (operands : CallOperands) (response : CallResponse) :
    Interaction.Exchange where
  query := callExternalQuery kind state operands
  answer := response

theorem callStep_external_executes
    {kind : CallKind} {state : EVMState}
    {rest : EvmYul.Stack Word} {operands : CallOperands}
    {response : CallResponse}
    (hOperands : kind.evmOperands? state.stack = some (rest, operands))
    (hAllowed :
      kind.allowedIn (ExternalFrame.ofShared state.toSharedState)
        operands = true) :
    Interaction.Executes
      (InteractionSemantics.PrimOp.callStep kind state)
      [callExternalExchange kind state operands response]
      (.ok
        (InteractionSemantics.EVMState.finishCall
          state rest operands.callLocal response)) := by
  unfold InteractionSemantics.PrimOp.callStep
  simpa [hOperands, hAllowed, callExternalExchange, callExternalQuery] using
    (Interaction.Executes.request
      (query := callExternalQuery kind state operands)
      response
      (Interaction.Executes.done
        (.ok
          (InteractionSemantics.EVMState.finishCall
            state rest operands.callLocal response))))

theorem raw_call_external_executes_after_charges
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    {rest : EvmYul.Stack Word} {operands : CallOperands}
    {response : CallResponse} (kind : CallKind)
    (hOperands :
      kind.evmOperands? state.stack = some (rest, operands))
    (hAllowed :
      kind.allowedIn
          (ExternalFrame.ofShared
            (afterDynamicChargeAt state).toSharedState)
          operands = true)
    (hDecode : Compact.decodeAt bytes pc (.prim (callPrimOp kind)))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      [callExternalExchange kind (afterDynamicChargeAt state)
        operands response]
      (.ok
        (.running
          (InteractionSemantics.EVMState.finishCall
            (afterDynamicChargeAt state) rest operands.callLocal
            response))) := by
  have hOperandsCharged :
      kind.evmOperands? (afterDynamicChargeAt state).stack =
        some (rest, operands) := by
    simpa [afterDynamicChargeAt, afterMemoryChargeAt, chargeGas] using
      hOperands
  have hStep :=
    callStep_external_executes
      (kind := kind) (state := afterDynamicChargeAt state)
      (rest := rest) (operands := operands) (response := response)
      hOperandsCharged hAllowed
  have hMapped :
      Interaction.Executes
        (Simulation.Interaction.bind
          (InteractionSemantics.PrimOp.callStep kind
            (afterDynamicChargeAt state))
          (fun state' =>
            Simulation.Interaction.pure (StepResult.running state')))
        [callExternalExchange kind (afterDynamicChargeAt state)
          operands response]
        (.ok
          (.running
            (InteractionSemantics.EVMState.finishCall
              (afterDynamicChargeAt state) rest operands.callLocal
              response))) := by
    let openNext :=
      InteractionSemantics.EVMState.finishCall
        (afterDynamicChargeAt state) rest operands.callLocal response
    have hRest :
        Interaction.Executes
          (Simulation.Interaction.pure
            (Error := EVMException) (StepResult.running openNext))
          []
          ((.ok (StepResult.running openNext)) :
            Except EVMException StepResult) := by
      simpa [Simulation.Interaction.pure] using
        (Interaction.Executes.done
          (.ok (StepResult.running openNext) :
            Except EVMException StepResult))
    exact
      Interaction.Executes.bind_ok hStep hRest
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim (callPrimOp kind)) trivial hDecode hPc]
  cases kind <;>
    simpa [callPrimOp, Compact.Instr.openStepResult,
      Compact.Instr.openStep,
      Assembly.InteractionSemantics.Target.openStepInstrResult,
      Assembly.Target.stepInstrResultWith,
      Assembly.InteractionSemantics.Target.openStepInstr,
      Assembly.Target.stepInstrWith,
      Assembly.InteractionSemantics.PrimOp.openStep,
      Simulation.ExternalKind.ofEVMOperation?,
      Simulation.CallKind.ofEVMOperation?,
      Simulation.CreateKind.ofEVMOperation?,
      Simulation.Interaction.bind,
      Simulation.Interaction.bind_done_ok,
      Assembly.PrimOp.haltKind?, Compact.Instr.haltKind?] using hMapped

theorem stack_eq_of_pop3
    {α : Type} {stack rest : EvmYul.Stack α}
    {a b c : α}
    (hPop : stack.pop3 = some (rest, a, b, c)) :
    stack = a :: b :: c :: rest := by
  cases stack with
  | nil => simp [EvmYul.Stack.pop3] at hPop
  | cons x xs =>
      cases xs with
      | nil => simp [EvmYul.Stack.pop3] at hPop
      | cons y ys =>
          cases ys with
          | nil => simp [EvmYul.Stack.pop3] at hPop
          | cons z zs =>
              simp [EvmYul.Stack.pop3] at hPop
              rcases hPop with ⟨rfl, rfl, rfl, rfl⟩
              rfl

theorem stack_eq_of_pop4
    {α : Type} {stack rest : EvmYul.Stack α}
    {a b c d : α}
    (hPop : stack.pop4 = some (rest, a, b, c, d)) :
    stack = a :: b :: c :: d :: rest := by
  cases stack with
  | nil => simp [EvmYul.Stack.pop4] at hPop
  | cons x xs =>
      cases xs with
      | nil => simp [EvmYul.Stack.pop4] at hPop
      | cons y ys =>
          cases ys with
          | nil => simp [EvmYul.Stack.pop4] at hPop
          | cons z zs =>
              cases zs with
              | nil => simp [EvmYul.Stack.pop4] at hPop
              | cons w ws =>
                  simp [EvmYul.Stack.pop4] at hPop
                  rcases hPop with ⟨rfl, rfl, rfl, rfl, rfl⟩
                  rfl

theorem CreateKind.stack_eq_args_append_of_evmOperands
    {kind : CreateKind} {stack rest : EvmYul.Stack EvmYul.UInt256}
    {operands : CreateOperands}
    (hOperands : kind.evmOperands? stack = some (rest, operands)) :
    stack = kind.args operands ++ rest := by
  cases kind with
  | create =>
      unfold CreateKind.evmOperands? at hOperands
      cases hPop : stack.pop3 with
      | none => simp [hPop] at hOperands
      | some popped =>
          rcases popped with ⟨parsedRest, value, initOffset, initSize⟩
          simp [hPop] at hOperands
          rcases hOperands with ⟨rfl, rfl⟩
          simpa [CreateKind.args] using stack_eq_of_pop3 hPop
  | create2 =>
      unfold CreateKind.evmOperands? at hOperands
      cases hPop : stack.pop4 with
      | none => simp [hPop] at hOperands
      | some popped =>
          rcases popped with
            ⟨parsedRest, value, initOffset, initSize, salt⟩
          simp [hPop] at hOperands
          rcases hOperands with ⟨rfl, rfl⟩
          simpa [CreateKind.args] using stack_eq_of_pop4 hPop

theorem CreateKind.canonicalOperands_eq_of_evmOperands
    {kind : CreateKind} {stack rest : EvmYul.Stack EvmYul.UInt256}
    {operands : CreateOperands}
    (hOperands : kind.evmOperands? stack = some (rest, operands)) :
    kind.canonicalOperands operands = operands := by
  have hStack :=
    CreateKind.stack_eq_args_append_of_evmOperands hOperands
  rw [hStack] at hOperands
  simpa using hOperands

def createParentGasCost (kind : CreateKind)
    (operands : CreateOperands) : Nat :=
  match kind with
  | .create =>
      GasConstants.Gcreate + EvmYul.EVM.R operands.initSize.toNat
  | .create2 =>
      GasConstants.Gcreate +
        GasConstants.Gkeccak256word *
          ((operands.initSize.toNat + 31) / 32) +
        EvmYul.EVM.R operands.initSize.toNat

def createForwardedGas (preCostState : EVMState)
    (parentGasCost : Nat) : Word :=
  EvmYul.UInt256.ofNat
    (EvmYul.EVM.L
      (preCostState.gasAvailable -
        EvmYul.UInt256.ofNat parentGasCost).toNat)

def createFinalGas (preCostState : EVMState) (parentGasCost : Nat)
    (returnedGas : Word) : Word :=
  EvmYul.UInt256.ofNat
    ((preCostState.gasAvailable - EvmYul.UInt256.ofNat parentGasCost).toNat -
      EvmYul.EVM.L
        (preCostState.gasAvailable -
          EvmYul.UInt256.ofNat parentGasCost).toNat +
      returnedGas.toNat)

theorem dynamicGasCostAt_create_args_eq_parentGasCost
    (kind : CreateKind) (state : EVMState) (operands : CreateOperands)
    (rest : EvmYul.Stack Word)
    (hOp : decodedOperationAt state = kind.toEVMOperation)
    (hStack : state.stack = kind.args operands ++ rest) :
    dynamicGasCostAt state =
      createParentGasCost kind (kind.canonicalOperands operands) := by
  cases kind <;>
    simp [dynamicGasCostAt, createParentGasCost, hOp, hStack,
      CreateKind.args, CreateKind.canonicalOperands, EvmYul.EVM.C',
      CreateKind.toEVMOperation, afterMemoryChargeAt, chargeGas]

/-- Gas accounting for CREATE/CREATE2 external creation. The child init-code
execution remains the open strategy response; this records EIP-150 parent gas
withholding and returned gas. -/
structure CreateBoundaryAccounting
    (kind : CreateKind) (preCostState : EVMState)
    (operands : CreateOperands) (parentGasCost : Nat)
    (forwardedGas returnedGas finalGas : Word) : Prop where
  parentGasCost_eq :
    parentGasCost = createParentGasCost kind operands
  forwardedGas_eq :
    forwardedGas = createForwardedGas preCostState parentGasCost
  finalGas_eq :
    finalGas = createFinalGas preCostState parentGasCost returnedGas

theorem createBoundaryAccounting_canonical
    (kind : CreateKind) (preCostState : EVMState)
    (operands : CreateOperands) (returnedGas : Word) :
    CreateBoundaryAccounting kind preCostState operands
      (createParentGasCost kind operands)
      (createForwardedGas preCostState (createParentGasCost kind operands))
      returnedGas
      (createFinalGas preCostState
        (createParentGasCost kind operands) returnedGas) where
  parentGasCost_eq := rfl
  forwardedGas_eq := rfl
  finalGas_eq := rfl

def createResponseFinalGas (kind : CreateKind) (preCostState : EVMState)
    (operands : CreateOperands) (response : CreateResponse) : Word :=
  createFinalGas preCostState (createParentGasCost kind operands)
    response.returnedGas

def CreateResponseGasAccounting
    (kind : CreateKind) (preCostState : EVMState)
    (operands : CreateOperands) (response : CreateResponse)
    (finalGas : Word) : Prop :=
  CreateBoundaryAccounting kind preCostState operands
    (createParentGasCost kind operands)
    (createForwardedGas preCostState (createParentGasCost kind operands))
    response.returnedGas
    finalGas

theorem createResponseGasAccounting_canonical
    (kind : CreateKind) (preCostState : EVMState)
    (operands : CreateOperands) (response : CreateResponse) :
    CreateResponseGasAccounting kind preCostState operands response
      (createResponseFinalGas kind preCostState operands response) := by
  simpa [CreateResponseGasAccounting, createResponseFinalGas] using
    createBoundaryAccounting_canonical kind preCostState operands
      response.returnedGas

theorem createResponseGasAccounting_finalGas_eq
    {kind : CreateKind} {preCostState : EVMState}
    {operands : CreateOperands} {response : CreateResponse}
    {finalGas : Word}
    (hGas :
      CreateResponseGasAccounting kind preCostState operands response
        finalGas) :
    finalGas = createResponseFinalGas kind preCostState operands response := by
  simpa [CreateResponseGasAccounting, createResponseFinalGas] using
    hGas.finalGas_eq

/-- Relates the concrete post-CREATE parent frame to the open post-CREATE
frame. As for CALL, returned child gas is response metadata, not persistent
open-world state. -/
structure CreateResponseStateRel
    (kind : CreateKind) (preCostState : EVMState)
    (operands : CreateOperands) (response : CreateResponse)
    (gasfulState openState : EVMState) : Prop where
  openData : OpenSameData gasfulState openState
  pc_eq : gasfulState.pc = openState.pc
  gasAccounting :
    CreateResponseGasAccounting kind preCostState operands response
      gasfulState.gasAvailable

theorem CreateResponseStateRel.openStateRel
    {kind : CreateKind} {preCostState : EVMState}
    {operands : CreateOperands} {response : CreateResponse}
    {gasfulState openState : EVMState}
    (hRel : CreateResponseStateRel kind preCostState operands response
      gasfulState openState) :
    OpenStateRel gasfulState openState :=
  ⟨hRel.openData, hRel.pc_eq⟩

theorem createResponseStateRel_of_openSameData
    {kind : CreateKind} {preCostState : EVMState}
    {operands : CreateOperands} {response : CreateResponse}
    {gasfulState openState : EVMState}
    (hOpen : OpenSameData gasfulState openState)
    (hPc : gasfulState.pc = openState.pc)
    (hGas :
      gasfulState.gasAvailable =
        createResponseFinalGas kind preCostState operands response) :
    CreateResponseStateRel kind preCostState operands response
      gasfulState openState := by
  refine ⟨hOpen, hPc, ?_⟩
  rw [hGas]
  exact
    createResponseGasAccounting_canonical kind preCostState operands
      response

theorem createResponseStateRel_of_sameData
    {kind : CreateKind} {preCostState : EVMState}
    {operands : CreateOperands} {response : CreateResponse}
    {gasfulState openState : EVMState}
    (hSame : SameData gasfulState openState)
    (hPc : gasfulState.pc = openState.pc)
    (hGas :
      gasfulState.gasAvailable =
        createResponseFinalGas kind preCostState operands response) :
    CreateResponseStateRel kind preCostState operands response
      gasfulState openState := by
  exact
    createResponseStateRel_of_openSameData
      (OpenSameData.of_sameData hSame) hPc hGas

abbrev ConcreteCreateResult :=
  EvmYul.AccountAddress × EVMState × EvmYul.UInt256 × Bool ×
    ByteArray

abbrev CreateLambdaResult :=
  EvmYul.AccountAddress ×
    Batteries.RBSet EvmYul.AccountAddress compare × EvmYul.AccountMap .EVM ×
      EvmYul.UInt256 × EvmYul.Substate × Bool × ByteArray

/-- The child-frame invocation used by concrete CREATE/CREATE2. Naming this
boundary keeps the parent-step proof explicit about child success or failure. -/
def createLambda
    (kind : CreateKind) (fuel : Nat) (state : EVMState)
    (operands : CreateOperands) : Except EVMException CreateLambdaResult :=
  let initCode :=
    state.memory.readWithPadding
      operands.initOffset.toNat operands.initSize.toNat
  let salt : Option ByteArray :=
    match kind with
    | .create => none
    | .create2 => some (EvmYul.UInt256.toByteArray operands.saltArg)
  let env := state.executionEnv
  let creator := env.codeOwner
  let creatorAccount : EvmYul.Account .EVM :=
    state.accountMap.find? creator |>.getD default
  let incrementedAccounts :=
    state.accountMap.insert creator
      { creatorAccount with nonce := creatorAccount.nonce + ⟨1⟩ }
  EvmYul.EVM.Lambda fuel env.blobVersionedHashes
    state.createdAccounts state.genesisBlockHeader state.blocks
    incrementedAccounts state.σ₀
    { totalGasUsedInBlock := state.totalGasUsedInBlock
      transactionReceipts := state.transactionReceipts }
    state.substate creator env.sender
    (.ofNat (EvmYul.EVM.L state.gasAvailable.toNat))
    (.ofNat env.gasPrice) operands.value initCode
    (.ofNat (env.depth + 1)) salt env.header env.perm

/-- The concrete child result and parent-world update before CREATE's final
memory, return-data, gas, PC, and stack updates. -/
def concreteCreate
    (kind : CreateKind) (fuel gasCost : Nat)
    (state : EVMState) (operands : CreateOperands) : ConcreteCreateResult :=
  let charged := chargeGas state gasCost
  let initCode :=
    charged.memory.readWithPadding
      operands.initOffset.toNat operands.initSize.toNat
  let env := charged.executionEnv
  let creator := env.codeOwner
  let depth := env.depth
  let accounts := charged.accountMap
  let creatorAccount : EvmYul.Account .EVM :=
    accounts.find? creator |>.getD default
  if creatorAccount.nonce.toNat ≥ 2 ^ 64 - 1 then
    (default, charged,
      .ofNat (EvmYul.EVM.L charged.gasAvailable.toNat), false, .empty)
  else if
      operands.value ≤
          (accounts.find? creator |>.option ⟨0⟩ (·.balance)) ∧
        depth < 1024 ∧ initCode.size ≤ 49152 then
    match createLambda kind fuel charged operands with
    | .ok (address, createdAccounts, accountMap, returnedGas,
        substate, success, returnData) =>
        (address,
          { charged with
            accountMap := accountMap
            substate := substate
            createdAccounts := createdAccounts },
          returnedGas, success, returnData)
    | .error _ =>
        (default, { charged with accountMap := ∅ },
          EvmYul.UInt256.ofNat 0, false, .empty)
  else
    (default, charged,
      .ofNat (EvmYul.EVM.L charged.gasAvailable.toNat), false, .empty)

def createResultAddress
    (state : EVMState) (operands : CreateOperands)
    (address : EvmYul.AccountAddress) (success : Bool) : EvmYul.UInt256 :=
  let balance :=
    state.accountMap.find? state.executionEnv.codeOwner
      |>.option ⟨0⟩ (·.balance)
  let initCode :=
    state.memory.readWithPadding
      operands.initOffset.toNat operands.initSize.toNat
  if success = false ∨ state.executionEnv.depth = 1024 ∨
      operands.value > balance ∨ initCode.size > 49152 then
    EvmYul.UInt256.ofNat 0
  else
    EvmYul.UInt256.ofNat address

def createResponseFromConcrete
    (charged result : EVMState) (operands : CreateOperands)
    (address : EvmYul.AccountAddress) (returnedGas : EvmYul.UInt256)
    (success : Bool) (returnData : ByteArray) : CreateResponse where
  address := createResultAddress charged operands address success
  returnData := if success then .empty else returnData
  postWorld := OpenWorld.ofEVMShared result.toSharedState
  returnedGas := returnedGas

def finishConcreteCreate
    (charged result : EVMState) (rest : EvmYul.Stack EvmYul.UInt256)
    (operands : CreateOperands) (address : EvmYul.AccountAddress)
    (returnedGas : EvmYul.UInt256) (success : Bool)
    (returnData : ByteArray) : EVMState :=
  let status := createResultAddress charged operands address success
  let newReturnData := if success then .empty else returnData
  let result :=
    { result with
      activeWords :=
        .ofNat
          (EvmYul.MachineState.M charged.activeWords.toNat
            operands.initOffset.toNat operands.initSize.toNat)
      returnData := newReturnData
      H_return := ByteArray.empty
      gasAvailable :=
        .ofNat
          (charged.gasAvailable.toNat -
            EvmYul.EVM.L charged.gasAvailable.toNat +
            returnedGas.toNat) }
  result.replaceStackAndIncrPC (rest.push status)

/-- One concrete CREATE/CREATE2 step after stack parsing, including the
parent-frame OOG check on returned child gas. -/
def concreteCreateStep
    (kind : CreateKind) (fuel gasCost : Nat)
    (state : EVMState) (rest : EvmYul.Stack EvmYul.UInt256)
    (operands : CreateOperands) : Except EVMException EVMState :=
  match fuel with
  | 0 => .error .OutOfFuel
  | childFuel + 1 =>
      let input := callInputState state
      let charged := chargeGas input gasCost
      let (address, result, returnedGas, success, returnData) :=
        concreteCreate kind childFuel gasCost input operands
      if (charged.gasAvailable + returnedGas).toNat <
          EvmYul.EVM.L charged.gasAvailable.toNat then
        .error .OutOfGass
      else
        .ok
          (finishConcreteCreate charged result rest operands address
            returnedGas success returnData)

/-- EVMYulLean's imported gasful CREATE/CREATE2 dispatcher is exactly the
named concrete parent/child decomposition above. -/
theorem evm_step_create_eq_concreteCreateStep
    (kind : CreateKind) (fuel gasCost : Nat)
    (state : EVMState) (rest : EvmYul.Stack EvmYul.UInt256)
    (operands : CreateOperands) (arg : Option (EvmYul.UInt256 × Nat))
    (hStack : state.stack = kind.args operands ++ rest) :
    EvmYul.EVM.step fuel gasCost (some (kind.toEVMOperation, arg)) state =
      concreteCreateStep kind fuel gasCost state rest operands := by
  cases fuel with
  | zero =>
      cases kind <;>
        simp [EvmYul.EVM.step, concreteCreateStep,
          CreateKind.toEVMOperation]
  | succ childFuel =>
      let charged := chargeGas (callInputState state) gasCost
      generalize hLambda :
        createLambda kind childFuel charged operands = lambdaResult
      cases lambdaResult with
      | error error =>
          dsimp [charged, chargeGas, callInputState] at hLambda
          cases kind <;>
            simp [EvmYul.EVM.step, concreteCreateStep, concreteCreate,
              finishConcreteCreate,
              createLambda, createResultAddress, callInputState, chargeGas,
              CreateKind.args, CreateKind.toEVMOperation, hStack,
              EvmYul.Stack.pop3, EvmYul.Stack.pop4, EvmYul.Stack.push,
              EvmYul.UInt256.ofNat, Id.run] at hLambda ⊢
          all_goals rw [hLambda] <;> simp_all
      | ok value =>
          rcases value with ⟨address, createdAccounts, accountMap,
            returnedGas, substate, success, returnData⟩
          dsimp [charged, chargeGas, callInputState] at hLambda
          cases kind <;>
            simp [EvmYul.EVM.step, concreteCreateStep, concreteCreate,
              finishConcreteCreate,
              createLambda, createResultAddress, callInputState, chargeGas,
              CreateKind.args, CreateKind.toEVMOperation, hStack,
              EvmYul.Stack.pop3, EvmYul.Stack.pop4, EvmYul.Stack.push,
              EvmYul.UInt256.ofNat, Id.run] at hLambda ⊢
          all_goals rw [hLambda] <;> simp_all

theorem finishConcreteCreate_world
    (charged result : EVMState) (rest : EvmYul.Stack EvmYul.UInt256)
    (operands : CreateOperands) (address : EvmYul.AccountAddress)
    (returnedGas : EvmYul.UInt256) (success : Bool)
    (returnData : ByteArray) :
    OpenWorld.ofEVMShared
        (finishConcreteCreate charged result rest operands address
          returnedGas success returnData).toSharedState =
      OpenWorld.ofEVMShared
        (InteractionSemantics.EVMState.finishCreate charged rest
          operands.createLocal
          (createResponseFromConcrete charged result operands address
            returnedGas success returnData)).toSharedState := by
  change OpenWorld.ofEVMShared result.toSharedState =
    OpenWorld.ofEVMShared
      (OpenWorld.installEVMShared charged.toSharedState
        (OpenWorld.ofEVMShared result.toSharedState))
  exact
    (OpenWorld.ofEVMShared_installEVMShared charged.toSharedState
      (OpenWorld.ofEVMShared result.toSharedState)).symm

theorem concreteCreate_result_openSameData
    {kind : CreateKind} {fuel gasCost : Nat}
    {state result : EVMState} {operands : CreateOperands}
    {address : EvmYul.AccountAddress} {returnedGas : EvmYul.UInt256}
    {success : Bool} {returnData : ByteArray}
    {rest : EvmYul.Stack EvmYul.UInt256}
    (hCreate :
      concreteCreate kind fuel gasCost state operands =
        (address, result, returnedGas, success, returnData)) :
    OpenSameData
      (finishConcreteCreate (chargeGas state gasCost) result rest operands
        address returnedGas success returnData)
      (InteractionSemantics.EVMState.finishCreate
        (chargeGas state gasCost) rest operands.createLocal
        (createResponseFromConcrete (chargeGas state gasCost) result operands
          address returnedGas success returnData)) := by
  unfold concreteCreate at hCreate
  dsimp only at hCreate
  split at hCreate
  · simp at hCreate
    rcases hCreate with ⟨rfl, rfl, rfl, rfl, rfl⟩
    constructor
    · exact finishConcreteCreate_world _ _ _ _ _ _ _ _
    · simp [eraseOpenWorldData, finishConcreteCreate,
        createResponseFromConcrete,
        InteractionSemantics.EVMState.finishCreate,
        InteractionSemantics.EVMState.installWorld,
        CreateLocal.finishMachine, eraseControl, eraseGas,
        CreateOperands.createLocal, EvmYul.MachineState.finishExternalCall,
        EvmYul.MachineState.M, EvmYul.writeBytes,
        EvmYul.UInt256.ofNat, EvmYul.UInt256.toNat, ByteArray.write, Id.run,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, OpenWorld.installEVMShared,
        OpenWorld.installEVM, EvmYul.Stack.push]
  · split at hCreate
    · generalize hLambda :
        createLambda kind fuel (chargeGas state gasCost) operands = lambdaResult
          at hCreate
      cases lambdaResult with
      | error error =>
          simp at hCreate
          rcases hCreate with ⟨rfl, rfl, rfl, rfl, rfl⟩
          constructor
          · exact finishConcreteCreate_world _ _ _ _ _ _ _ _
          · simp [finishConcreteCreate, createResponseFromConcrete,
              InteractionSemantics.EVMState.finishCreate,
              InteractionSemantics.EVMState.installWorld,
              CreateLocal.finishMachine, CreateOperands.createLocal,
              eraseOpenWorldData, eraseControl, eraseGas,
              EvmYul.MachineState.finishExternalCall,
              EvmYul.MachineState.M, EvmYul.writeBytes,
              EvmYul.UInt256.ofNat, EvmYul.UInt256.toNat, ByteArray.write,
              Id.run, EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC, OpenWorld.ofEVMShared,
              OpenWorld.installEVMShared, OpenWorld.installEVM,
              EvmYul.Stack.push]
      | ok value =>
          rcases value with ⟨childAddress, createdAccounts, accountMap,
            childReturnedGas, substate, childSuccess, childReturnData⟩
          simp at hCreate
          rcases hCreate with ⟨rfl, rfl, rfl, rfl, rfl⟩
          constructor
          · exact finishConcreteCreate_world _ _ _ _ _ _ _ _
          · simp [finishConcreteCreate, createResponseFromConcrete,
              InteractionSemantics.EVMState.finishCreate,
              InteractionSemantics.EVMState.installWorld,
              CreateLocal.finishMachine, CreateOperands.createLocal,
              eraseOpenWorldData, eraseControl, eraseGas,
              EvmYul.MachineState.finishExternalCall,
              EvmYul.MachineState.M, EvmYul.writeBytes,
              EvmYul.UInt256.ofNat, EvmYul.UInt256.toNat, ByteArray.write,
              Id.run, EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC, OpenWorld.ofEVMShared,
              OpenWorld.installEVMShared, OpenWorld.installEVM,
              EvmYul.Stack.push]
    · simp at hCreate
      rcases hCreate with ⟨rfl, rfl, rfl, rfl, rfl⟩
      constructor
      · exact finishConcreteCreate_world _ _ _ _ _ _ _ _
      · simp [finishConcreteCreate, createResponseFromConcrete,
          InteractionSemantics.EVMState.finishCreate,
          InteractionSemantics.EVMState.installWorld,
          CreateLocal.finishMachine, CreateOperands.createLocal,
          eraseOpenWorldData, eraseControl, eraseGas,
          EvmYul.MachineState.finishExternalCall,
          EvmYul.MachineState.M, EvmYul.writeBytes,
          EvmYul.UInt256.ofNat, EvmYul.UInt256.toNat, ByteArray.write,
          Id.run, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, OpenWorld.ofEVMShared,
          OpenWorld.installEVMShared, OpenWorld.installEVM,
          EvmYul.Stack.push]

theorem concreteCreate_result_pc
    {kind : CreateKind} {fuel gasCost : Nat}
    {state result : EVMState} {operands : CreateOperands}
    {address : EvmYul.AccountAddress} {returnedGas : EvmYul.UInt256}
    {success : Bool} {returnData : ByteArray}
    (hCreate :
      concreteCreate kind fuel gasCost state operands =
        (address, result, returnedGas, success, returnData)) :
    result.pc = state.pc := by
  unfold concreteCreate at hCreate
  dsimp only at hCreate
  split at hCreate
  · simp at hCreate
    rcases hCreate with ⟨rfl, rfl, rfl, rfl, rfl⟩
    rfl
  · split at hCreate
    · generalize hLambda :
        createLambda kind fuel (chargeGas state gasCost) operands = lambdaResult
          at hCreate
      cases lambdaResult with
      | error error =>
          simp at hCreate
          rcases hCreate with ⟨rfl, rfl, rfl, rfl, rfl⟩
          rfl
      | ok value =>
          rcases value with ⟨childAddress, createdAccounts, accountMap,
            childReturnedGas, substate, childSuccess, childReturnData⟩
          simp at hCreate
          rcases hCreate with ⟨rfl, rfl, rfl, rfl, rfl⟩
          rfl
    · simp at hCreate
      rcases hCreate with ⟨rfl, rfl, rfl, rfl, rfl⟩
      rfl

theorem createResponseFromConcrete_finalGas
    (kind : CreateKind) (state result : EVMState)
    (operands : CreateOperands) (gasCost : Nat)
    (address : EvmYul.AccountAddress) (returnedGas : EvmYul.UInt256)
    (success : Bool) (returnData : ByteArray)
    (rest : EvmYul.Stack EvmYul.UInt256)
    (hParentCost : gasCost = createParentGasCost kind operands) :
    createResponseFinalGas kind state operands
        (createResponseFromConcrete (chargeGas state gasCost) result operands
          address returnedGas success returnData) =
      (finishConcreteCreate (chargeGas state gasCost) result rest operands
        address returnedGas success returnData).gasAvailable := by
  simp [createResponseFinalGas, createResponseFromConcrete, createFinalGas,
    finishConcreteCreate, chargeGas, hParentCost,
    EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]

theorem finishCreate_callInputState_openSameData
    (state : EVMState) (cost : Nat)
    (rest : EvmYul.Stack EvmYul.UInt256)
    (createLocal : CreateLocal) (response : CreateResponse) :
    OpenSameData
      (InteractionSemantics.EVMState.finishCreate
        (chargeGas (callInputState state) cost) rest createLocal response)
      (InteractionSemantics.EVMState.finishCreate
        (chargeGas state cost) rest createLocal response) := by
  constructor
  · simp [InteractionSemantics.EVMState.finishCreate,
      InteractionSemantics.EVMState.installWorld,
      EvmYul.EVM.State.incrPC, chargeGas, callInputState,
      OpenWorld.ofEVMShared, OpenWorld.installEVMShared]
  · simp [eraseOpenWorldData,
      InteractionSemantics.EVMState.finishCreate,
      InteractionSemantics.EVMState.installWorld,
      chargeGas, callInputState, eraseControl, eraseGas,
      EvmYul.EVM.State.incrPC, OpenWorld.installEVMShared,
      OpenWorld.installEVM, EvmYul.Stack.push]

theorem concreteCreate_responseStateRel
    {kind : CreateKind} {fuel gasCost : Nat}
    {state result : EVMState} {operands : CreateOperands}
    {address : EvmYul.AccountAddress} {returnedGas : EvmYul.UInt256}
    {success : Bool} {returnData : ByteArray}
    {rest : EvmYul.Stack EvmYul.UInt256}
    (hParentCost : gasCost = createParentGasCost kind operands)
    (hCreate :
      concreteCreate kind fuel gasCost state operands =
        (address, result, returnedGas, success, returnData)) :
    CreateResponseStateRel kind state operands
      (createResponseFromConcrete (chargeGas state gasCost) result operands
        address returnedGas success returnData)
      (finishConcreteCreate (chargeGas state gasCost) result rest operands
        address returnedGas success returnData)
      (InteractionSemantics.EVMState.finishCreate
        (chargeGas state (createParentGasCost kind operands)) rest
        operands.createLocal
        (createResponseFromConcrete (chargeGas state gasCost) result operands
          address returnedGas success returnData)) := by
  apply createResponseStateRel_of_openSameData
  · simpa [hParentCost] using concreteCreate_result_openSameData hCreate
  · simp [finishConcreteCreate,
      InteractionSemantics.EVMState.finishCreate,
      InteractionSemantics.EVMState.installWorld,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, chargeGas,
      concreteCreate_result_pc hCreate]
  · exact
      (createResponseFromConcrete_finalGas kind state result operands gasCost
        address returnedGas success returnData rest hParentCost).symm

theorem evm_step_create_responseStateRel
    {kind : CreateKind} {fuel gasCost : Nat}
    {state gasfulNext : EVMState} {operands : CreateOperands}
    {rest : EvmYul.Stack EvmYul.UInt256}
    {arg : Option (EvmYul.UInt256 × Nat)}
    (hStack : state.stack = kind.args operands ++ rest)
    (hParentCost : gasCost = createParentGasCost kind operands)
    (hStep :
      EvmYul.EVM.step fuel gasCost
        (some (kind.toEVMOperation, arg)) state = .ok gasfulNext) :
    ∃ response : CreateResponse,
      CreateResponseStateRel kind (callInputState state) operands response
        gasfulNext
        (InteractionSemantics.EVMState.finishCreate
          (chargeGas (callInputState state)
            (createParentGasCost kind operands))
          rest operands.createLocal response) := by
  rw [evm_step_create_eq_concreteCreateStep
    kind fuel gasCost state rest operands arg hStack] at hStep
  cases fuel with
  | zero =>
      simp [concreteCreateStep] at hStep
  | succ childFuel =>
      simp only [concreteCreateStep] at hStep
      generalize hCreate :
        concreteCreate kind childFuel gasCost (callInputState state) operands =
          createResult at hStep
      rcases createResult with
        ⟨address, result, returnedGas, success, returnData⟩
      split at hStep
      · simp at hStep
      · simp at hStep
        subst gasfulNext
        let response :=
          createResponseFromConcrete
            (chargeGas (callInputState state) gasCost) result operands
            address returnedGas success returnData
        refine ⟨response, ?_⟩
        exact concreteCreate_responseStateRel hParentCost hCreate

theorem evm_step_create_responseStateRel_at
    {fuel : Nat} {state gasfulNext : EVMState}
    {rest : EvmYul.Stack EvmYul.UInt256}
    {operands : CreateOperands}
    {arg : Option (EvmYul.UInt256 × Nat)}
    (kind : CreateKind)
    (hOp : decodedOperationAt state = kind.toEVMOperation)
    (hOperands :
      kind.evmOperands? state.stack = some (rest, operands))
    (hStep :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some (kind.toEVMOperation, arg)) (afterMemoryChargeAt state) =
          .ok gasfulNext) :
    ∃ response : CreateResponse,
      CreateResponseStateRel kind (afterMemoryChargeAt state) operands response
        gasfulNext
        (InteractionSemantics.EVMState.finishCreate
          (afterDynamicChargeAt state) rest operands.createLocal response) := by
  have hStack :=
    CreateKind.stack_eq_args_append_of_evmOperands hOperands
  have hCanonical :=
    CreateKind.canonicalOperands_eq_of_evmOperands hOperands
  have hParentBase :=
    dynamicGasCostAt_create_args_eq_parentGasCost
      kind state operands rest hOp hStack
  have hStackMemory :
      (afterMemoryChargeAt state).stack = kind.args operands ++ rest := by
    simpa [afterMemoryChargeAt, chargeGas] using hStack
  have hParentCost :
      dynamicGasCostAt state = createParentGasCost kind operands := by
    simpa [hCanonical] using hParentBase
  obtain ⟨response, hResponse⟩ :=
    evm_step_create_responseStateRel
      hStackMemory hParentCost hStep
  have hOpenResponse :
      OpenSameData gasfulNext
        (InteractionSemantics.EVMState.finishCreate
          (chargeGas (callInputState (afterMemoryChargeAt state))
            (dynamicGasCostAt state))
          rest operands.createLocal response) := by
    simpa [hParentCost] using hResponse.openData
  have hOpenControl :=
    finishCreate_callInputState_openSameData
      (afterMemoryChargeAt state) (dynamicGasCostAt state)
      rest operands.createLocal response
  have hOpen :
      OpenSameData gasfulNext
        (InteractionSemantics.EVMState.finishCreate
          (afterDynamicChargeAt state) rest operands.createLocal response) := by
    simpa [afterDynamicChargeAt] using
      hOpenResponse.trans hOpenControl
  have hPc :
      gasfulNext.pc =
        (InteractionSemantics.EVMState.finishCreate
          (afterDynamicChargeAt state) rest operands.createLocal response).pc := by
    simpa [hParentCost, afterDynamicChargeAt,
      InteractionSemantics.EVMState.finishCreate,
      InteractionSemantics.EVMState.installWorld,
      EvmYul.EVM.State.incrPC, chargeGas, callInputState] using
      hResponse.pc_eq
  have hGasInput :=
    createResponseGasAccounting_finalGas_eq hResponse.gasAccounting
  have hGas :
      gasfulNext.gasAvailable =
        createResponseFinalGas kind (afterMemoryChargeAt state)
          operands response := by
    simpa [createResponseFinalGas, callInputState] using hGasInput
  exact
    ⟨response, createResponseStateRel_of_openSameData hOpen hPc hGas⟩

def createPrimOp : CreateKind → PrimOp
  | .create => .create
  | .create2 => .create2

def createExternalQuery (kind : CreateKind) (state : EVMState)
    (operands : CreateOperands) : Query :=
    .external (OpenWorld.ofEVMShared state.toSharedState)
      (.create
        ((ExternalFrame.ofShared state.toSharedState).createRequest
          kind operands))

def createExternalExchange (kind : CreateKind) (state : EVMState)
    (operands : CreateOperands) (response : CreateResponse) :
    Interaction.Exchange where
  query := createExternalQuery kind state operands
  answer := response

theorem createStep_external_executes
    {kind : CreateKind} {state : EVMState}
    {rest : EvmYul.Stack Word} {operands : CreateOperands}
    {response : CreateResponse}
    (hOperands : kind.evmOperands? state.stack = some (rest, operands))
    (hPermission :
      (ExternalFrame.ofShared state.toSharedState).permission = true) :
    Interaction.Executes
      (InteractionSemantics.PrimOp.createStep kind state)
      [createExternalExchange kind state operands response]
      (.ok
        (InteractionSemantics.EVMState.finishCreate
          state rest operands.createLocal response)) := by
  unfold InteractionSemantics.PrimOp.createStep
  simpa [hOperands, hPermission, createExternalExchange, createExternalQuery] using
    (Interaction.Executes.request
      (query := createExternalQuery kind state operands)
      response
      (Interaction.Executes.done
        (.ok
          (InteractionSemantics.EVMState.finishCreate
            state rest operands.createLocal response))))

theorem raw_create_external_executes_after_charges
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    {rest : EvmYul.Stack Word} {operands : CreateOperands}
    {response : CreateResponse} (kind : CreateKind)
    (hOperands :
      kind.evmOperands? state.stack = some (rest, operands))
    (hPermission :
      (ExternalFrame.ofShared
        (afterDynamicChargeAt state).toSharedState).permission = true)
    (hDecode : Compact.decodeAt bytes pc (.prim (createPrimOp kind)))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult
        bytes 1 (afterDynamicChargeAt state))
      [createExternalExchange kind (afterDynamicChargeAt state)
        operands response]
      (.ok
        (.running
          (InteractionSemantics.EVMState.finishCreate
            (afterDynamicChargeAt state) rest operands.createLocal
            response))) := by
  have hOperandsCharged :
      kind.evmOperands? (afterDynamicChargeAt state).stack =
        some (rest, operands) := by
    simpa [afterDynamicChargeAt, afterMemoryChargeAt, chargeGas] using
      hOperands
  have hStep :=
    createStep_external_executes
      (kind := kind) (state := afterDynamicChargeAt state)
      (rest := rest) (operands := operands) (response := response)
      hOperandsCharged hPermission
  have hMapped :
      Interaction.Executes
        (Simulation.Interaction.bind
          (InteractionSemantics.PrimOp.createStep kind
            (afterDynamicChargeAt state))
          (fun state' =>
            Simulation.Interaction.pure (StepResult.running state')))
        [createExternalExchange kind (afterDynamicChargeAt state)
          operands response]
        (.ok
          (.running
            (InteractionSemantics.EVMState.finishCreate
              (afterDynamicChargeAt state) rest operands.createLocal
              response))) := by
    let openNext :=
      InteractionSemantics.EVMState.finishCreate
        (afterDynamicChargeAt state) rest operands.createLocal response
    have hRest :
        Interaction.Executes
          (Simulation.Interaction.pure
            (Error := EVMException) (StepResult.running openNext))
          []
          ((.ok (StepResult.running openNext)) :
            Except EVMException StepResult) := by
      simpa [Simulation.Interaction.pure] using
        (Interaction.Executes.done
          (.ok (StepResult.running openNext) :
            Except EVMException StepResult))
    exact
      Interaction.Executes.bind_ok hStep hRest
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim (createPrimOp kind)) trivial hDecode hPc]
  cases kind <;>
    simpa [createPrimOp, Compact.Instr.openStepResult,
      Compact.Instr.openStep,
      Assembly.InteractionSemantics.Target.openStepInstrResult,
      Assembly.Target.stepInstrResultWith,
      Assembly.InteractionSemantics.Target.openStepInstr,
      Assembly.Target.stepInstrWith,
      Assembly.InteractionSemantics.PrimOp.openStep,
      Simulation.ExternalKind.ofEVMOperation?,
      Simulation.CallKind.ofEVMOperation?,
      Simulation.CreateKind.ofEVMOperation?,
      Simulation.Interaction.bind,
      Simulation.Interaction.bind_done_ok,
      Assembly.PrimOp.haltKind?, Compact.Instr.haltKind?] using hMapped

inductive DoneRel :
    Except EVMException (EvmYul.EVM.ExecutionResult EVMState) →
    Except EVMException StepResult → Prop where
  | success {gasful openState output haltKind} :
      SameData gasful openState →
      DoneRel
        (.ok (.success gasful output))
        (.ok (.halted
          { kind := haltKind, state := openState, output := output }))
  | revert {gas output openState} :
      DoneRel
        (.ok (.revert gas output))
        (.ok (.halted
          { kind := .revert, state := openState, output := output }))
  | sameError {err} :
      DoneRel (.error err) (.error err)

/-- A gasful `EVM.X` result refines an open bytecode interaction either by
reaching a related terminal leaf, or by explicitly interrupting with a target
precheck that the open raw-bytecode model intentionally leaves unchecked after
an open transcript prefix. -/
inductive RunRefinesOpen
    (gasful : Except EVMException (EvmYul.EVM.ExecutionResult EVMState))
    (openRun : Interaction EVMException StepResult) :
    Interaction.Transcript → Prop where
  | completed {transcript openDone} :
      Interaction.Executes openRun transcript openDone →
      DoneRel gasful openDone →
      RunRefinesOpen gasful openRun transcript
  | outOfGas {transcript} :
      gasful = .error EvmYul.EVM.ExecutionException.OutOfGass →
      Interaction.Follows openRun transcript →
      RunRefinesOpen gasful openRun transcript
  | outOfFuel {transcript} :
      gasful = .error EvmYul.EVM.ExecutionException.OutOfFuel →
      Interaction.Follows openRun transcript →
      RunRefinesOpen gasful openRun transcript
  | badJumpDestination {transcript} :
      gasful = .error EvmYul.EVM.ExecutionException.BadJumpDestination →
      Interaction.Follows openRun transcript →
      RunRefinesOpen gasful openRun transcript
  | stackOverflow {transcript} :
      gasful = .error EvmYul.EVM.ExecutionException.StackOverflow →
      Interaction.Follows openRun transcript →
      RunRefinesOpen gasful openRun transcript

theorem runRefinesOpen_of_executes
    {gasful : Except EVMException (EvmYul.EVM.ExecutionResult EVMState)}
    {openRun : Interaction EVMException StepResult}
    {transcript : Interaction.Transcript}
    {openDone : Except EVMException StepResult}
    (hExec : Interaction.Executes openRun transcript openDone)
    (hDone : DoneRel gasful openDone) :
    RunRefinesOpen gasful openRun transcript :=
  .completed hExec hDone

theorem runRefinesOpen_bind_running_prefix
    {gasful tailGasful :
      Except EVMException (EvmYul.EVM.ExecutionResult EVMState)}
    {first : Interaction EVMException StepResult}
    {nextState : EVMState}
    {tail : EVMState → Interaction EVMException StepResult}
    {firstTranscript tailTranscript : Interaction.Transcript}
    (hGasful : gasful = tailGasful)
    (hFirst :
      Interaction.Executes first firstTranscript
        (.ok (.running nextState)))
    (hTail :
      RunRefinesOpen tailGasful (tail nextState) tailTranscript) :
    RunRefinesOpen gasful
      (Simulation.Interaction.bind first
        (fun result =>
          match result with
          | .running state => tail state
          | .halted halt =>
              Simulation.Interaction.pure
                (Error := EVMException) (.halted halt)))
      (firstTranscript ++ tailTranscript) := by
  cases hGasful
  cases hTail with
  | completed hExec hDone =>
      apply RunRefinesOpen.completed
      · exact Interaction.Executes.bind_ok hFirst hExec
      · exact hDone
  | outOfGas hGas hFollow =>
      apply RunRefinesOpen.outOfGas hGas
      exact Interaction.Follows.bind_ok hFirst hFollow
  | outOfFuel hFuel hFollow =>
      apply RunRefinesOpen.outOfFuel hFuel
      exact Interaction.Follows.bind_ok hFirst hFollow
  | badJumpDestination hBad hFollow =>
      apply RunRefinesOpen.badJumpDestination hBad
      exact Interaction.Follows.bind_ok hFirst hFollow
  | stackOverflow hOverflow hFollow =>
      apply RunRefinesOpen.stackOverflow hOverflow
      exact Interaction.Follows.bind_ok hFirst hFollow

theorem runRefinesOpen_of_x_after_prechecks_step_result
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    {stepResult : Except EVMException EVMState}
    {openRun : Interaction EVMException StepResult}
    {transcript : Interaction.Transcript}
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt state) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          state.stack[2]?.getD (EvmYul.UInt256.ofNat 0)))
    (hStep :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = stepResult)
    (hBridge :
      RunRefinesOpen
        (xPostStepExceptResult fuel validJumps
          (decodedOperationAt state) stepResult)
        openRun transcript) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      openRun transcript := by
  rw [x_after_prechecks_of_step_result
    (fuel := fuel) (validJumps := validJumps) (state := state)
    (stepResult := stepResult) hPrefix hCreateOk hStep]
  exact hBridge

theorem runRefinesOpen_of_x_after_prechecks_step_error_executes
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    {err : EVMException}
    {openRun : Interaction EVMException StepResult}
    {transcript : Interaction.Transcript}
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt state) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          state.stack[2]?.getD (EvmYul.UInt256.ofNat 0)))
    (hStep :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .error err)
    (hExec :
      Interaction.Executes openRun transcript (.error err)) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      openRun transcript := by
  apply runRefinesOpen_of_x_after_prechecks_step_result
    (fuel := fuel) (validJumps := validJumps) (state := state)
    (stepResult := .error err) hPrefix hCreateOk hStep
  exact runRefinesOpen_of_executes hExec DoneRel.sameError

theorem runRefinesOpen_running_step_rel
    {stepFuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {gasful gasfulNext openState openNext : EVMState}
    {op : EvmYul.Operation .EVM}
    {firstTranscript tailTranscript : Interaction.Transcript}
    (hPrefix : XSstoreStipendChecksPass validJumps gasful)
    (hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt gasful) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          gasful.stack[2]?.getD (EvmYul.UInt256.ofNat 0)))
    (hDecodedOp : decodedOperationAt gasful = op)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt gasful)
        (some
          ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt gasful) = .ok gasfulNext)
    (hHalt : haltOutputAt gasfulNext op = none)
    (hFirst :
      Interaction.Executes
        (Compact.InteractionSemantics.openRunNResult bytes 1 openState)
        firstTranscript (.ok (.running openNext)))
    (hCont :
      RunRefinesOpen
        (EvmYul.EVM.X stepFuel validJumps gasfulNext)
        (Compact.InteractionSemantics.openRunNResult
          bytes stepFuel openNext)
        tailTranscript) :
    RunRefinesOpen
      (EvmYul.EVM.X (stepFuel + 1) validJumps gasful)
      (Compact.InteractionSemantics.openRunNResult
        bytes (stepFuel + 1) openState)
      (firstTranscript ++ tailTranscript) := by
  have hPostRun :
      RunRefinesOpen
        (EvmYul.EVM.X stepFuel validJumps gasfulNext)
        (Compact.InteractionSemantics.openRunNResult
          bytes (stepFuel + 1) openState)
        (firstTranscript ++ tailTranscript) := by
    rw [show stepFuel + 1 = 1 + stepFuel by omega]
    rw [Compact.InteractionSemantics.openRunNResult_add]
    exact
      runRefinesOpen_bind_running_prefix
        (gasful := EvmYul.EVM.X stepFuel validJumps gasfulNext)
        (tailGasful := EvmYul.EVM.X stepFuel validJumps gasfulNext)
        (first := Compact.InteractionSemantics.openRunNResult
          bytes 1 openState)
        (nextState := openNext)
        (tail := fun state =>
          Compact.InteractionSemantics.openRunNResult bytes stepFuel state)
        (firstTranscript := firstTranscript)
        (tailTranscript := tailTranscript)
        rfl hFirst hCont
  have hPostBridge :
      RunRefinesOpen
        (xPostStepExceptResult stepFuel validJumps
          (decodedOperationAt gasful) (.ok gasfulNext))
        (Compact.InteractionSemantics.openRunNResult
          bytes (stepFuel + 1) openState)
        (firstTranscript ++ tailTranscript) := by
    simpa [xPostStepExceptResult, xPostStepResult, hDecodedOp,
      hHalt] using hPostRun
  exact
    runRefinesOpen_of_x_after_prechecks_step_result
      (fuel := stepFuel) (validJumps := validJumps) (state := gasful)
      (stepResult := .ok gasfulNext)
      hPrefix hCreateOk hStep hPostBridge

theorem runRefinesOpen_continuing_success_rel
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {gasful openState gasfulNext : EVMState}
    {op : PrimOp} {step : PrimStep} {arg : Option (Word × Nat)}
    {tailTranscript : Interaction.Transcript}
    (hRel : OpenStateRel gasful openState)
    (hPrefix : XSstoreStipendChecksPass validJumps gasful)
    (hDecodedPair :
      ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
        (EvmYul.Operation.STOP, none)) = (op.toEVM, arg))
    (hStep : op.continuingStep? = some step)
    (hCompatible : OpenCompatibleStep step)
    (hMsize : op ≠ .msize)
    (hTransparent : continuingPrimEVMStepTransparent op)
    (hDecode : Compact.decodeAt bytes pc (.prim op))
    (hPc : openState.pc = EvmYul.UInt256.ofNat pc)
    (hGasful :
      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt gasful)
        (some (op.toEVM, arg)) (afterMemoryChargeAt gasful) =
          .ok gasfulNext)
    (hCont :
      ∀ openNext,
        OpenStateRel gasfulNext openNext →
          RunRefinesOpen
            (EvmYul.EVM.X (fuel + 1) validJumps gasfulNext)
            (Compact.InteractionSemantics.openRunNResult
              bytes (fuel + 1) openNext)
            tailTranscript) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1 + 1) validJumps gasful)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1 + 1) openState)
      tailTranscript := by
  have hDecodedOp : decodedOperationAt gasful = op.toEVM := by
    simpa [decodedOperationAt, hDecodedPair]
  have hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt gasful) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          gasful.stack[2]?.getD (EvmYul.UInt256.ofNat 0)) := by
    intro hBad
    have hCreateFalse :
        EvmYul.Operation.isCreate (decodedOperationAt gasful) = false := by
      simpa [hDecodedOp] using continuingStep_toEVM_isCreate_false hStep
    simp [hCreateFalse] at hBad
  have hStaticPermits : continuingPrimStaticPermits gasful op :=
    continuingPrimStaticPermits_of_static_check hPrefix.static hDecodedOp
  have hPrimGasful :
      op.step (afterEVMInstructionChargeAt gasful) = .ok gasfulNext := by
    rw [← hGasful]
    exact (evm_step_continuing_prim_after_charges
      (fuel := fuel) (arg := arg)
      hStep hTransparent hStaticPermits).symm
  rcases continuingPrim_open_success_rel_of_compatible
      hStep hCompatible hRel hPrimGasful with
    ⟨openNext, hOpen, hNextRel⟩
  have hFirst := raw_continuing_prim_executes_at
    hStep hMsize hDecode hPc hOpen
  have hStepActual :
      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt gasful)
        (some
          ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt gasful) = .ok gasfulNext := by
    simpa [hDecodedPair] using hGasful
  have hHalt := haltOutputAt_none_of_continuingStep gasfulNext hStep
  simpa using
    (runRefinesOpen_running_step_rel
      (stepFuel := fuel + 1) (validJumps := validJumps)
      (bytes := bytes) (gasful := gasful) (gasfulNext := gasfulNext)
      (openState := openState) (openNext := openNext)
      (op := op.toEVM)
      hPrefix hCreateOk hDecodedOp hStepActual hHalt hFirst
      (hCont openNext hNextRel))

theorem runRefinesOpen_continuing_pureStack_success_rel
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {gasful openState gasfulNext : EVMState}
    {op : PrimOp} {step : PrimStep} {arg : Option (Word × Nat)}
    {tailTranscript : Interaction.Transcript}
    (hRel : OpenStateRel gasful openState)
    (hPrefix : XSstoreStipendChecksPass validJumps gasful)
    (hDecodedPair :
      ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
        (EvmYul.Operation.STOP, none)) = (op.toEVM, arg))
    (hStep : op.continuingStep? = some step)
    (hPure : PureStackStep step)
    (hMsize : op ≠ .msize)
    (hTransparent : continuingPrimEVMStepTransparent op)
    (hDecode : Compact.decodeAt bytes pc (.prim op))
    (hPc : openState.pc = EvmYul.UInt256.ofNat pc)
    (hGasful :
      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt gasful)
        (some (op.toEVM, arg)) (afterMemoryChargeAt gasful) =
          .ok gasfulNext)
    (hCont :
      ∀ openNext,
        OpenStateRel gasfulNext openNext →
          RunRefinesOpen
            (EvmYul.EVM.X (fuel + 1) validJumps gasfulNext)
            (Compact.InteractionSemantics.openRunNResult
              bytes (fuel + 1) openNext)
            tailTranscript) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1 + 1) validJumps gasful)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1 + 1) openState)
      tailTranscript := by
  exact runRefinesOpen_continuing_success_rel
    hRel hPrefix hDecodedPair hStep hPure.openCompatible hMsize
    hTransparent hDecode hPc hGasful hCont

theorem runRefinesOpen_continuing_frameLocal_success_rel
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {gasful openState gasfulNext : EVMState}
    {op : PrimOp} {step : PrimStep} {arg : Option (Word × Nat)}
    {tailTranscript : Interaction.Transcript}
    (hRel : OpenStateRel gasful openState)
    (hPrefix : XSstoreStipendChecksPass validJumps gasful)
    (hDecodedPair :
      ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
        (EvmYul.Operation.STOP, none)) = (op.toEVM, arg))
    (hStep : op.continuingStep? = some step)
    (hLocal : FrameLocalStep step)
    (hMsize : op ≠ .msize)
    (hTransparent : continuingPrimEVMStepTransparent op)
    (hDecode : Compact.decodeAt bytes pc (.prim op))
    (hPc : openState.pc = EvmYul.UInt256.ofNat pc)
    (hGasful :
      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt gasful)
        (some (op.toEVM, arg)) (afterMemoryChargeAt gasful) =
          .ok gasfulNext)
    (hCont :
      ∀ openNext,
        OpenStateRel gasfulNext openNext →
          RunRefinesOpen
            (EvmYul.EVM.X (fuel + 1) validJumps gasfulNext)
            (Compact.InteractionSemantics.openRunNResult
              bytes (fuel + 1) openNext)
            tailTranscript) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1 + 1) validJumps gasful)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1 + 1) openState)
      tailTranscript := by
  exact runRefinesOpen_continuing_success_rel
    hRel hPrefix hDecodedPair hStep hLocal.openCompatible hMsize
    hTransparent hDecode hPc hGasful hCont

theorem runRefinesOpen_continuing_frameLocalPrim_success_rel
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {gasful openState gasfulNext : EVMState}
    {op : PrimOp} {step : PrimStep} {arg : Option (Word × Nat)}
    {tailTranscript : Interaction.Transcript}
    (hRel : OpenStateRel gasful openState)
    (hPrefix : XSstoreStipendChecksPass validJumps gasful)
    (hDecodedPair :
      ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
        (EvmYul.Operation.STOP, none)) = (op.toEVM, arg))
    (hStep : op.continuingStep? = some step)
    (hLocal : FrameLocalPrimOp op)
    (hMsize : op ≠ .msize)
    (hTransparent : continuingPrimEVMStepTransparent op)
    (hDecode : Compact.decodeAt bytes pc (.prim op))
    (hPc : openState.pc = EvmYul.UInt256.ofNat pc)
    (hGasful :
      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt gasful)
        (some (op.toEVM, arg)) (afterMemoryChargeAt gasful) =
          .ok gasfulNext)
    (hCont :
      ∀ openNext,
        OpenStateRel gasfulNext openNext →
          RunRefinesOpen
            (EvmYul.EVM.X (fuel + 1) validJumps gasfulNext)
            (Compact.InteractionSemantics.openRunNResult
              bytes (fuel + 1) openNext)
            tailTranscript) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1 + 1) validJumps gasful)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1 + 1) openState)
      tailTranscript := by
  exact runRefinesOpen_continuing_frameLocal_success_rel
    hRel hPrefix hDecodedPair hStep
    (frameLocalStep_of_continuingStep hLocal hStep)
    hMsize hTransparent hDecode hPc hGasful hCont

theorem runRefinesOpen_continuing_nonResource_success_rel
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {gasful openState gasfulNext : EVMState}
    {op : PrimOp} {step : PrimStep} {arg : Option (Word × Nat)}
    {tailTranscript : Interaction.Transcript}
    (hRel : OpenStateRel gasful openState)
    (hPrefix : XSstoreStipendChecksPass validJumps gasful)
    (hDecodedPair :
      ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
        (EvmYul.Operation.STOP, none)) = (op.toEVM, arg))
    (hStep : op.continuingStep? = some step)
    (hMsize : op ≠ .msize) (hInvalid : op ≠ .invalid)
    (hTransparent : continuingPrimEVMStepTransparent op)
    (hDecode : Compact.decodeAt bytes pc (.prim op))
    (hPc : openState.pc = EvmYul.UInt256.ofNat pc)
    (hGasful :
      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt gasful)
        (some (op.toEVM, arg)) (afterMemoryChargeAt gasful) =
          .ok gasfulNext)
    (hCont :
      ∀ openNext,
        OpenStateRel gasfulNext openNext →
          RunRefinesOpen
            (EvmYul.EVM.X (fuel + 1) validJumps gasfulNext)
            (Compact.InteractionSemantics.openRunNResult
              bytes (fuel + 1) openNext)
            tailTranscript) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1 + 1) validJumps gasful)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1 + 1) openState)
      tailTranscript := by
  exact runRefinesOpen_continuing_frameLocalPrim_success_rel
    hRel hPrefix hDecodedPair hStep
    (frameLocalPrimOp_of_continuingStep hStep hMsize hInvalid)
    hMsize hTransparent hDecode hPc hGasful hCont

theorem runRefinesOpen_pc_success_rel
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {gasful openState : EVMState}
    {arg : Option (Word × Nat)}
    {tailTranscript : Interaction.Transcript}
    (hPrefix : XSstoreStipendChecksPass validJumps gasful)
    (hDecodedPair :
      ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
        (EvmYul.Operation.STOP, none)) = (EvmYul.Operation.PC, arg))
    (hDecode : Compact.decodeAt bytes pc (.prim .pc))
    (hPc : openState.pc = EvmYul.UInt256.ofNat pc)
    (hCont :
      RunRefinesOpen
        (EvmYul.EVM.X (fuel + 1) validJumps (gasfulPcNext gasful))
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1) (openPcNextAt openState))
        tailTranscript) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1 + 1) validJumps gasful)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1 + 1) openState)
      tailTranscript := by
  have hDecodedOp : decodedOperationAt gasful = EvmYul.Operation.PC := by
    simpa [decodedOperationAt, hDecodedPair]
  have hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt gasful) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          gasful.stack[2]?.getD (EvmYul.UInt256.ofNat 0)) := by
    simp [hDecodedOp, EvmYul.Operation.isCreate]
  have hStepActual :
      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt gasful)
        (some
          ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt gasful) = .ok (gasfulPcNext gasful) := by
    simpa [hDecodedPair] using evm_step_pc_eq_next fuel gasful arg
  have hFirst := raw_pc_success_executes_at hDecode hPc
  simpa using
    (runRefinesOpen_running_step_rel
      (stepFuel := fuel + 1) (validJumps := validJumps)
      (bytes := bytes) (gasful := gasful)
      (gasfulNext := gasfulPcNext gasful)
      (openState := openState) (openNext := openPcNextAt openState)
      (op := EvmYul.Operation.PC)
      hPrefix hCreateOk hDecodedOp hStepActual
      (by simp [haltOutputAt]) hFirst hCont)

theorem runRefinesOpen_push_success_rel
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc width : Nat} {gasful openState : EVMState}
    {value : Word} {op : EvmYul.Operation .EVM}
    {tailTranscript : Interaction.Transcript}
    (hPrefix : XSstoreStipendChecksPass validJumps gasful)
    (hFits : Compact.FitsWidth width value.toNat)
    (hOp : Compact.pushOp? width = some op)
    (hDecodedPair :
      ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
        (EvmYul.Operation.STOP, none)) = (op, some (value, width)))
    (hDecode : Compact.decodeAt bytes pc (.push width value))
    (hPc : openState.pc = EvmYul.UInt256.ofNat pc)
    (hCont :
      RunRefinesOpen
        (EvmYul.EVM.X (fuel + 1) validJumps
          (gasfulPushNext width value gasful))
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1) (openPushNextAt width value openState))
        tailTranscript) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1 + 1) validJumps gasful)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1 + 1) openState)
      tailTranscript := by
  have hDecodedOp : decodedOperationAt gasful = op := by
    simpa [decodedOperationAt, hDecodedPair]
  have hCreateFalse : EvmYul.Operation.isCreate op = false :=
    pushOp_isCreate_false hFits hOp
  have hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt gasful) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          gasful.stack[2]?.getD (EvmYul.UInt256.ofNat 0)) := by
    simp [hDecodedOp, hCreateFalse]
  have hStepActual :
      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt gasful)
        (some
          ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt gasful) =
          .ok (gasfulPushNext width value gasful) := by
    simpa [hDecodedPair] using
      evm_step_push_eq_next fuel gasful value hFits hOp
  have hHalt :
      haltOutputAt (gasfulPushNext width value gasful) op = none :=
    pushOp_haltOutputAt_none _ hFits hOp
  have hFirst := raw_push_success_executes_at hFits hDecode hPc
  simpa using
    (runRefinesOpen_running_step_rel
      (stepFuel := fuel + 1) (validJumps := validJumps)
      (bytes := bytes) (gasful := gasful)
      (gasfulNext := gasfulPushNext width value gasful)
      (openState := openState)
      (openNext := openPushNextAt width value openState)
      (op := op)
      hPrefix hCreateOk hDecodedOp hStepActual hHalt hFirst hCont)

theorem runRefinesOpen_jump_success_rel
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {gasful openState : EVMState}
    {arg : Option (Word × Nat)} {rest : EvmYul.Stack Word} {dest : Word}
    {tailTranscript : Interaction.Transcript}
    (hPrefix : XSstoreStipendChecksPass validJumps gasful)
    (hDecodedPair :
      ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
        (EvmYul.Operation.STOP, none)) = (EvmYul.Operation.JUMP, arg))
    (hGasfulStack : gasful.stack = dest :: rest)
    (hOpenStack : openState.stack = dest :: rest)
    (hDecode : Compact.decodeAt bytes pc .jump)
    (hPc : openState.pc = EvmYul.UInt256.ofNat pc)
    (hCont :
      RunRefinesOpen
        (EvmYul.EVM.X (fuel + 1) validJumps
          (gasfulJumpNext gasful rest dest))
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1) (openJumpNextAt openState rest dest))
        tailTranscript) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1 + 1) validJumps gasful)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1 + 1) openState)
      tailTranscript := by
  have hDecodedOp : decodedOperationAt gasful = EvmYul.Operation.JUMP := by
    simpa [decodedOperationAt, hDecodedPair]
  have hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt gasful) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          gasful.stack[2]?.getD (EvmYul.UInt256.ofNat 0)) := by
    simp [hDecodedOp, EvmYul.Operation.isCreate]
  have hStepActual :
      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt gasful)
        (some
          ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt gasful) =
          .ok (gasfulJumpNext gasful rest dest) := by
    simpa [hDecodedPair] using
      evm_step_jump_eq_next fuel gasful arg rest dest hGasfulStack
  have hFirst :=
    raw_jump_success_executes_at hOpenStack hDecode hPc
  simpa using
    (runRefinesOpen_running_step_rel
      (stepFuel := fuel + 1) (validJumps := validJumps)
      (bytes := bytes) (gasful := gasful)
      (gasfulNext := gasfulJumpNext gasful rest dest)
      (openState := openState)
      (openNext := openJumpNextAt openState rest dest)
      (op := EvmYul.Operation.JUMP)
      hPrefix hCreateOk hDecodedOp hStepActual
      (by simp [haltOutputAt]) hFirst hCont)

theorem runRefinesOpen_jumpi_success_rel
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {gasful openState : EVMState}
    {arg : Option (Word × Nat)} {rest : EvmYul.Stack Word}
    {dest cond : Word} {tailTranscript : Interaction.Transcript}
    (hPrefix : XSstoreStipendChecksPass validJumps gasful)
    (hDecodedPair :
      ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
        (EvmYul.Operation.STOP, none)) = (EvmYul.Operation.JUMPI, arg))
    (hGasfulStack : gasful.stack = dest :: cond :: rest)
    (hOpenStack : openState.stack = dest :: cond :: rest)
    (hDecode : Compact.decodeAt bytes pc .jumpi)
    (hPc : openState.pc = EvmYul.UInt256.ofNat pc)
    (hCont :
      RunRefinesOpen
        (EvmYul.EVM.X (fuel + 1) validJumps
          (gasfulJumpiNext gasful rest dest cond))
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1) (openJumpiNextAt openState rest dest cond))
        tailTranscript) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1 + 1) validJumps gasful)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1 + 1) openState)
      tailTranscript := by
  have hDecodedOp : decodedOperationAt gasful = EvmYul.Operation.JUMPI := by
    simpa [decodedOperationAt, hDecodedPair]
  have hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt gasful) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          gasful.stack[2]?.getD (EvmYul.UInt256.ofNat 0)) := by
    simp [hDecodedOp, EvmYul.Operation.isCreate]
  have hStepActual :
      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt gasful)
        (some
          ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt gasful) =
          .ok (gasfulJumpiNext gasful rest dest cond) := by
    simpa [hDecodedPair] using
      evm_step_jumpi_eq_next fuel gasful arg rest dest cond hGasfulStack
  have hFirst :=
    raw_jumpi_success_executes_at hOpenStack hDecode hPc
  simpa using
    (runRefinesOpen_running_step_rel
      (stepFuel := fuel + 1) (validJumps := validJumps)
      (bytes := bytes) (gasful := gasful)
      (gasfulNext := gasfulJumpiNext gasful rest dest cond)
      (openState := openState)
      (openNext := openJumpiNextAt openState rest dest cond)
      (op := EvmYul.Operation.JUMPI)
      hPrefix hCreateOk hDecodedOp hStepActual
      (by simp [haltOutputAt]) hFirst hCont)

theorem runRefinesOpen_jumpdest_success_rel
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {gasful openState : EVMState}
    {arg : Option (Word × Nat)}
    {tailTranscript : Interaction.Transcript}
    (hPrefix : XSstoreStipendChecksPass validJumps gasful)
    (hDecodedPair :
      ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
        (EvmYul.Operation.STOP, none)) =
          (EvmYul.Operation.JUMPDEST, arg))
    (hDecode : Compact.decodeAt bytes pc .jumpdest)
    (hPc : openState.pc = EvmYul.UInt256.ofNat pc)
    (hCont :
      RunRefinesOpen
        (EvmYul.EVM.X (fuel + 1) validJumps
          (afterEVMInstructionChargeAt gasful).incrPC)
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1) (openJumpdestNextAt openState))
        tailTranscript) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1 + 1) validJumps gasful)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1 + 1) openState)
      tailTranscript := by
  have hDecodedOp : decodedOperationAt gasful = EvmYul.Operation.JUMPDEST := by
    simpa [decodedOperationAt, hDecodedPair]
  have hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt gasful) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          gasful.stack[2]?.getD (EvmYul.UInt256.ofNat 0)) := by
    simp [hDecodedOp, EvmYul.Operation.isCreate]
  have hStepActual :
      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt gasful)
        (some
          ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt gasful) =
          .ok (afterEVMInstructionChargeAt gasful).incrPC := by
    simpa [hDecodedPair] using evm_step_jumpdest_eq_next fuel gasful arg
  have hFirst := raw_jumpdest_executes_at hDecode hPc
  simpa using
    (runRefinesOpen_running_step_rel
      (stepFuel := fuel + 1) (validJumps := validJumps)
      (bytes := bytes) (gasful := gasful)
      (gasfulNext := (afterEVMInstructionChargeAt gasful).incrPC)
      (openState := openState)
      (openNext := openJumpdestNextAt openState)
      (op := EvmYul.Operation.JUMPDEST)
      hPrefix hCreateOk hDecodedOp hStepActual
      (by simp [haltOutputAt]) hFirst hCont)

/-- Compose one actual charged `GAS` or `MSIZE` step. The first transcript
exchange is the concrete value observed after memory and dynamic gas charges. -/
theorem runRefinesOpen_resource_success
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    {arg : Option (Word × Nat)}
    {tailTranscript : Interaction.Transcript}
    (kind : ResourceQuery)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hDecodedPair :
      ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
        (EvmYul.Operation.STOP, none)) =
          ((resourcePrimOp kind).toEVM, arg))
    (hDecode :
      Compact.decodeAt bytes pc (.prim (resourcePrimOp kind)))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc)
    (hCont :
      RunRefinesOpen
        (EvmYul.EVM.X (fuel + 1) validJumps
          (gasfulResourceNext kind state))
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1) (openResourceNext kind state))
        tailTranscript) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1 + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1 + 1) (afterDynamicChargeAt state))
      (InteractionConcreteResources.resourceExchange kind
          (InteractionConcreteResources.resourceValue kind
            (afterDynamicChargeAt state)) :: tailTranscript) := by
  have hDecodedOp :
      decodedOperationAt state = (resourcePrimOp kind).toEVM := by
    simpa [decodedOperationAt, hDecodedPair]
  have hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt state) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          state.stack[2]?.getD (EvmYul.UInt256.ofNat 0)) := by
    intro hBad
    cases kind <;>
      simp [resourcePrimOp, PrimOp.toEVM, hDecodedOp,
        EvmYul.Operation.isCreate] at hBad
  have hFirst :
      Interaction.Executes
        (Compact.InteractionSemantics.openRunNResult
          bytes 1 (afterDynamicChargeAt state))
        [InteractionConcreteResources.resourceExchange kind
          (InteractionConcreteResources.resourceValue kind
            (afterDynamicChargeAt state))]
        (.ok (.running (openResourceNext kind state))) := by
    cases kind with
    | gas =>
        simpa [afterDynamicChargeAt, resourceResult_eq_running] using
          (raw_gas_observation_executes_after_charge
            (bytes := bytes) (pc := pc)
            (state := afterMemoryChargeAt state)
            (cost := dynamicGasCostAt state) hDecode hPc)
    | msize =>
        simpa [afterDynamicChargeAt, resourceResult_eq_running] using
          (raw_msize_observation_executes_after_charge
            (bytes := bytes) (pc := pc)
            (state := afterMemoryChargeAt state)
            (cost := dynamicGasCostAt state) hDecode hPc)
  have hPostRun :
      RunRefinesOpen
        (EvmYul.EVM.X (fuel + 1) validJumps
          (gasfulResourceNext kind state))
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1 + 1) (afterDynamicChargeAt state))
        (InteractionConcreteResources.resourceExchange kind
            (InteractionConcreteResources.resourceValue kind
              (afterDynamicChargeAt state)) :: tailTranscript) := by
    rw [show fuel + 1 + 1 = 1 + (fuel + 1) by omega]
    rw [Compact.InteractionSemantics.openRunNResult_add]
    simpa using
      (runRefinesOpen_bind_running_prefix
        (gasful := EvmYul.EVM.X (fuel + 1) validJumps
          (gasfulResourceNext kind state))
        (tailGasful := EvmYul.EVM.X (fuel + 1) validJumps
          (gasfulResourceNext kind state))
        (first := Compact.InteractionSemantics.openRunNResult
          bytes 1 (afterDynamicChargeAt state))
        (nextState := openResourceNext kind state)
        (tail := fun openNext =>
          Compact.InteractionSemantics.openRunNResult
            bytes (fuel + 1) openNext)
        (firstTranscript :=
          [InteractionConcreteResources.resourceExchange kind
            (InteractionConcreteResources.resourceValue kind
              (afterDynamicChargeAt state))])
        (tailTranscript := tailTranscript)
        rfl hFirst hCont)
  have hPostBridge :
      RunRefinesOpen
        (xPostStepExceptResult (fuel + 1) validJumps
          (decodedOperationAt state)
          (.ok (gasfulResourceNext kind state)))
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1 + 1) (afterDynamicChargeAt state))
        (InteractionConcreteResources.resourceExchange kind
            (InteractionConcreteResources.resourceValue kind
              (afterDynamicChargeAt state)) :: tailTranscript) := by
    cases kind <;>
      simpa [xPostStepExceptResult, xPostStepResult, hDecodedOp,
        resourcePrimOp, PrimOp.toEVM, haltOutputAt] using hPostRun
  have hStepActual :
      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) =
          .ok (gasfulResourceNext kind state) := by
    simpa [hDecodedPair] using
      evm_step_resource_eq kind fuel state arg
  exact
    runRefinesOpen_of_x_after_prechecks_step_result
      (fuel := fuel + 1) (validJumps := validJumps) (state := state)
      (stepResult := .ok (gasfulResourceNext kind state))
      hPrefix hCreateOk hStepActual hPostBridge

theorem runRefinesOpen_resource_success_rel
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {gasful openState : EVMState}
    {arg : Option (Word × Nat)}
    {tailTranscript : Interaction.Transcript}
    (kind : ResourceQuery)
    (hPrefix : XSstoreStipendChecksPass validJumps gasful)
    (hDecodedPair :
      ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
        (EvmYul.Operation.STOP, none)) =
          ((resourcePrimOp kind).toEVM, arg))
    (hDecode : Compact.decodeAt bytes pc (.prim (resourcePrimOp kind)))
    (hPc : openState.pc = EvmYul.UInt256.ofNat pc)
    (hCont :
      RunRefinesOpen
        (EvmYul.EVM.X (fuel + 1) validJumps
          (gasfulResourceNext kind gasful))
        (Compact.InteractionSemantics.openRunNResult bytes (fuel + 1)
          (openResourceNextAt kind
            (InteractionConcreteResources.resourceValue kind
              (afterDynamicChargeAt gasful)) openState))
        tailTranscript) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1 + 1) validJumps gasful)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1 + 1) openState)
      (InteractionConcreteResources.resourceExchange kind
          (InteractionConcreteResources.resourceValue kind
            (afterDynamicChargeAt gasful)) :: tailTranscript) := by
  have hDecodedOp :
      decodedOperationAt gasful = (resourcePrimOp kind).toEVM := by
    simpa [decodedOperationAt, hDecodedPair]
  have hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt gasful) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          gasful.stack[2]?.getD (EvmYul.UInt256.ofNat 0)) := by
    intro hBad
    cases kind <;>
      simp [resourcePrimOp, PrimOp.toEVM, hDecodedOp,
        EvmYul.Operation.isCreate] at hBad
  have hFirst :=
    raw_resource_observation_executes_at kind
      (InteractionConcreteResources.resourceValue kind
        (afterDynamicChargeAt gasful)) hDecode hPc
  have hPostRun :
      RunRefinesOpen
        (EvmYul.EVM.X (fuel + 1) validJumps
          (gasfulResourceNext kind gasful))
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1 + 1) openState)
        (InteractionConcreteResources.resourceExchange kind
            (InteractionConcreteResources.resourceValue kind
              (afterDynamicChargeAt gasful)) :: tailTranscript) := by
    rw [show fuel + 1 + 1 = 1 + (fuel + 1) by omega]
    rw [Compact.InteractionSemantics.openRunNResult_add]
    simpa using
      (runRefinesOpen_bind_running_prefix
        (gasful := EvmYul.EVM.X (fuel + 1) validJumps
          (gasfulResourceNext kind gasful))
        (tailGasful := EvmYul.EVM.X (fuel + 1) validJumps
          (gasfulResourceNext kind gasful))
        (first := Compact.InteractionSemantics.openRunNResult
          bytes 1 openState)
        (nextState := openResourceNextAt kind
          (InteractionConcreteResources.resourceValue kind
            (afterDynamicChargeAt gasful)) openState)
        (tail := fun openNext =>
          Compact.InteractionSemantics.openRunNResult
            bytes (fuel + 1) openNext)
        (firstTranscript :=
          [InteractionConcreteResources.resourceExchange kind
            (InteractionConcreteResources.resourceValue kind
              (afterDynamicChargeAt gasful))])
        (tailTranscript := tailTranscript)
        rfl hFirst hCont)
  have hPostBridge :
      RunRefinesOpen
        (xPostStepExceptResult (fuel + 1) validJumps
          (decodedOperationAt gasful)
          (.ok (gasfulResourceNext kind gasful)))
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1 + 1) openState)
        (InteractionConcreteResources.resourceExchange kind
            (InteractionConcreteResources.resourceValue kind
              (afterDynamicChargeAt gasful)) :: tailTranscript) := by
    cases kind <;>
      simpa [xPostStepExceptResult, xPostStepResult, hDecodedOp,
        resourcePrimOp, PrimOp.toEVM, haltOutputAt] using hPostRun
  have hStepActual :
      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt gasful)
        (some
          ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt gasful) =
          .ok (gasfulResourceNext kind gasful) := by
    simpa [hDecodedPair] using
      evm_step_resource_eq kind fuel gasful arg
  exact
    runRefinesOpen_of_x_after_prechecks_step_result
      (fuel := fuel + 1) (validJumps := validJumps) (state := gasful)
      (stepResult := .ok (gasfulResourceNext kind gasful))
      hPrefix hCreateOk hStepActual hPostBridge

theorem runRefinesOpen_pc_success
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    {arg : Option (Word × Nat)}
    {tailTranscript : Interaction.Transcript}
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hDecodedPair :
      ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
        (EvmYul.Operation.STOP, none)) = (EvmYul.Operation.PC, arg))
    (hDecode : Compact.decodeAt bytes pc (.prim .pc))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc)
    (hCont :
      RunRefinesOpen
        (EvmYul.EVM.X (fuel + 1) validJumps (gasfulPcNext state))
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1) (openPcNext state))
        tailTranscript) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1 + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1 + 1) (afterDynamicChargeAt state))
      tailTranscript := by
  have hDecodedOp : decodedOperationAt state = EvmYul.Operation.PC := by
    simpa [decodedOperationAt, hDecodedPair]
  have hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt state) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          state.stack[2]?.getD (EvmYul.UInt256.ofNat 0)) := by
    simp [hDecodedOp, EvmYul.Operation.isCreate]
  have hFirst :=
    raw_pc_success_executes_after_charges
      (bytes := bytes) (pc := pc) (state := state) hDecode hPc
  have hPostRun :
      RunRefinesOpen
        (EvmYul.EVM.X (fuel + 1) validJumps (gasfulPcNext state))
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1 + 1) (afterDynamicChargeAt state))
        tailTranscript := by
    rw [show fuel + 1 + 1 = 1 + (fuel + 1) by omega]
    rw [Compact.InteractionSemantics.openRunNResult_add]
    simpa using
      (runRefinesOpen_bind_running_prefix
        (gasful := EvmYul.EVM.X (fuel + 1) validJumps
          (gasfulPcNext state))
        (tailGasful := EvmYul.EVM.X (fuel + 1) validJumps
          (gasfulPcNext state))
        (first := Compact.InteractionSemantics.openRunNResult
          bytes 1 (afterDynamicChargeAt state))
        (nextState := openPcNext state)
        (tail := fun openNext =>
          Compact.InteractionSemantics.openRunNResult
            bytes (fuel + 1) openNext)
        (firstTranscript := []) (tailTranscript := tailTranscript)
        rfl hFirst hCont)
  have hPostBridge :
      RunRefinesOpen
        (xPostStepExceptResult (fuel + 1) validJumps
          (decodedOperationAt state) (.ok (gasfulPcNext state)))
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1 + 1) (afterDynamicChargeAt state))
        tailTranscript := by
    simpa [xPostStepExceptResult, xPostStepResult, hDecodedOp,
      haltOutputAt] using hPostRun
  have hStepActual :
      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok (gasfulPcNext state) := by
    simpa [hDecodedPair] using evm_step_pc_eq_next fuel state arg
  exact
    runRefinesOpen_of_x_after_prechecks_step_result
      (fuel := fuel + 1) (validJumps := validJumps) (state := state)
      (stepResult := .ok (gasfulPcNext state))
      hPrefix hCreateOk hStepActual hPostBridge

theorem runRefinesOpen_push_success
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc width : Nat} {state : EVMState}
    {value : Word} {op : EvmYul.Operation .EVM}
    {tailTranscript : Interaction.Transcript}
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hFits : Compact.FitsWidth width value.toNat)
    (hOp : Compact.pushOp? width = some op)
    (hDecodedPair :
      ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
        (EvmYul.Operation.STOP, none)) = (op, some (value, width)))
    (hDecode : Compact.decodeAt bytes pc (.push width value))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc)
    (hCont :
      RunRefinesOpen
        (EvmYul.EVM.X (fuel + 1) validJumps
          (gasfulPushNext width value state))
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1) (openPushNext width value state))
        tailTranscript) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1 + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1 + 1) (afterDynamicChargeAt state))
      tailTranscript := by
  have hDecodedOp : decodedOperationAt state = op := by
    simpa [decodedOperationAt, hDecodedPair]
  have hCreateFalse : EvmYul.Operation.isCreate op = false :=
    pushOp_isCreate_false hFits hOp
  have hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt state) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          state.stack[2]?.getD (EvmYul.UInt256.ofNat 0)) := by
    simp [hDecodedOp, hCreateFalse]
  have hFirst :=
    raw_push_success_executes_after_charges
      (bytes := bytes) (pc := pc) (state := state) hFits hDecode hPc
  have hPostRun :
      RunRefinesOpen
        (EvmYul.EVM.X (fuel + 1) validJumps
          (gasfulPushNext width value state))
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1 + 1) (afterDynamicChargeAt state))
        tailTranscript := by
    rw [show fuel + 1 + 1 = 1 + (fuel + 1) by omega]
    rw [Compact.InteractionSemantics.openRunNResult_add]
    simpa using
      (runRefinesOpen_bind_running_prefix
        (gasful := EvmYul.EVM.X (fuel + 1) validJumps
          (gasfulPushNext width value state))
        (tailGasful := EvmYul.EVM.X (fuel + 1) validJumps
          (gasfulPushNext width value state))
        (first := Compact.InteractionSemantics.openRunNResult
          bytes 1 (afterDynamicChargeAt state))
        (nextState := openPushNext width value state)
        (tail := fun openNext =>
          Compact.InteractionSemantics.openRunNResult
            bytes (fuel + 1) openNext)
        (firstTranscript := []) (tailTranscript := tailTranscript)
        rfl hFirst hCont)
  have hHalt :
      haltOutputAt (gasfulPushNext width value state) op = none :=
    pushOp_haltOutputAt_none _ hFits hOp
  have hPostBridge :
      RunRefinesOpen
        (xPostStepExceptResult (fuel + 1) validJumps
          (decodedOperationAt state)
          (.ok (gasfulPushNext width value state)))
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1 + 1) (afterDynamicChargeAt state))
        tailTranscript := by
    simpa [xPostStepExceptResult, xPostStepResult, hDecodedOp,
      hHalt] using hPostRun
  have hStepActual :
      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) =
          .ok (gasfulPushNext width value state) := by
    simpa [hDecodedPair] using
      evm_step_push_eq_next fuel state value hFits hOp
  exact
    runRefinesOpen_of_x_after_prechecks_step_result
      (fuel := fuel + 1) (validJumps := validJumps) (state := state)
      (stepResult := .ok (gasfulPushNext width value state))
      hPrefix hCreateOk hStepActual hPostBridge

theorem runRefinesOpen_jump_success
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    {arg : Option (Word × Nat)} {rest : EvmYul.Stack Word} {dest : Word}
    {tailTranscript : Interaction.Transcript}
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hDecodedPair :
      ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
        (EvmYul.Operation.STOP, none)) = (EvmYul.Operation.JUMP, arg))
    (hStack : state.stack = dest :: rest)
    (hDecode : Compact.decodeAt bytes pc .jump)
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc)
    (hCont :
      RunRefinesOpen
        (EvmYul.EVM.X (fuel + 1) validJumps
          (gasfulJumpNext state rest dest))
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1) (openJumpNext state rest dest))
        tailTranscript) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1 + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1 + 1) (afterDynamicChargeAt state))
      tailTranscript := by
  have hDecodedOp :
      decodedOperationAt state = EvmYul.Operation.JUMP := by
    simpa [decodedOperationAt, hDecodedPair]
  have hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt state) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          state.stack[2]?.getD (EvmYul.UInt256.ofNat 0)) := by
    simp [hDecodedOp, EvmYul.Operation.isCreate]
  have hFirst :=
    raw_jump_success_executes_after_charges
      (bytes := bytes) (pc := pc) (state := state)
      (rest := rest) (dest := dest) hStack hDecode hPc
  have hPostRun :
      RunRefinesOpen
        (EvmYul.EVM.X (fuel + 1) validJumps
          (gasfulJumpNext state rest dest))
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1 + 1) (afterDynamicChargeAt state))
        tailTranscript := by
    rw [show fuel + 1 + 1 = 1 + (fuel + 1) by omega]
    rw [Compact.InteractionSemantics.openRunNResult_add]
    simpa using
      (runRefinesOpen_bind_running_prefix
        (gasful := EvmYul.EVM.X (fuel + 1) validJumps
          (gasfulJumpNext state rest dest))
        (tailGasful := EvmYul.EVM.X (fuel + 1) validJumps
          (gasfulJumpNext state rest dest))
        (first := Compact.InteractionSemantics.openRunNResult
          bytes 1 (afterDynamicChargeAt state))
        (nextState := openJumpNext state rest dest)
        (tail := fun openNext =>
          Compact.InteractionSemantics.openRunNResult
            bytes (fuel + 1) openNext)
        (firstTranscript := []) (tailTranscript := tailTranscript)
        rfl hFirst hCont)
  have hPostBridge :
      RunRefinesOpen
        (xPostStepExceptResult (fuel + 1) validJumps
          (decodedOperationAt state)
          (.ok (gasfulJumpNext state rest dest)))
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1 + 1) (afterDynamicChargeAt state))
        tailTranscript := by
    simpa [xPostStepExceptResult, xPostStepResult, hDecodedOp,
      haltOutputAt] using hPostRun
  have hStepActual :
      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) =
          .ok (gasfulJumpNext state rest dest) := by
    simpa [hDecodedPair] using
      evm_step_jump_eq_next fuel state arg rest dest hStack
  exact
    runRefinesOpen_of_x_after_prechecks_step_result
      (fuel := fuel + 1) (validJumps := validJumps) (state := state)
      (stepResult := .ok (gasfulJumpNext state rest dest))
      hPrefix hCreateOk hStepActual hPostBridge

theorem runRefinesOpen_jumpi_success
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    {arg : Option (Word × Nat)} {rest : EvmYul.Stack Word}
    {dest cond : Word} {tailTranscript : Interaction.Transcript}
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hDecodedPair :
      ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
        (EvmYul.Operation.STOP, none)) = (EvmYul.Operation.JUMPI, arg))
    (hStack : state.stack = dest :: cond :: rest)
    (hDecode : Compact.decodeAt bytes pc .jumpi)
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc)
    (hCont :
      RunRefinesOpen
        (EvmYul.EVM.X (fuel + 1) validJumps
          (gasfulJumpiNext state rest dest cond))
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1) (openJumpiNext state rest dest cond))
        tailTranscript) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1 + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1 + 1) (afterDynamicChargeAt state))
      tailTranscript := by
  have hDecodedOp :
      decodedOperationAt state = EvmYul.Operation.JUMPI := by
    simpa [decodedOperationAt, hDecodedPair]
  have hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt state) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          state.stack[2]?.getD (EvmYul.UInt256.ofNat 0)) := by
    simp [hDecodedOp, EvmYul.Operation.isCreate]
  have hFirst :=
    raw_jumpi_success_executes_after_charges
      (bytes := bytes) (pc := pc) (state := state)
      (rest := rest) (dest := dest) (cond := cond) hStack hDecode hPc
  have hPostRun :
      RunRefinesOpen
        (EvmYul.EVM.X (fuel + 1) validJumps
          (gasfulJumpiNext state rest dest cond))
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1 + 1) (afterDynamicChargeAt state))
        tailTranscript := by
    rw [show fuel + 1 + 1 = 1 + (fuel + 1) by omega]
    rw [Compact.InteractionSemantics.openRunNResult_add]
    simpa using
      (runRefinesOpen_bind_running_prefix
        (gasful := EvmYul.EVM.X (fuel + 1) validJumps
          (gasfulJumpiNext state rest dest cond))
        (tailGasful := EvmYul.EVM.X (fuel + 1) validJumps
          (gasfulJumpiNext state rest dest cond))
        (first := Compact.InteractionSemantics.openRunNResult
          bytes 1 (afterDynamicChargeAt state))
        (nextState := openJumpiNext state rest dest cond)
        (tail := fun openNext =>
          Compact.InteractionSemantics.openRunNResult
            bytes (fuel + 1) openNext)
        (firstTranscript := []) (tailTranscript := tailTranscript)
        rfl hFirst hCont)
  have hPostBridge :
      RunRefinesOpen
        (xPostStepExceptResult (fuel + 1) validJumps
          (decodedOperationAt state)
          (.ok (gasfulJumpiNext state rest dest cond)))
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1 + 1) (afterDynamicChargeAt state))
        tailTranscript := by
    simpa [xPostStepExceptResult, xPostStepResult, hDecodedOp,
      haltOutputAt] using hPostRun
  have hStepActual :
      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) =
          .ok (gasfulJumpiNext state rest dest cond) := by
    simpa [hDecodedPair] using
      evm_step_jumpi_eq_next fuel state arg rest dest cond hStack
  exact
    runRefinesOpen_of_x_after_prechecks_step_result
      (fuel := fuel + 1) (validJumps := validJumps) (state := state)
      (stepResult := .ok (gasfulJumpiNext state rest dest cond))
      hPrefix hCreateOk hStepActual hPostBridge

theorem runRefinesOpen_jumpdest_step
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state gasfulNext : EVMState}
    {transcript : Interaction.Transcript}
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hJumpdest : decodedOperationAt state = EvmYul.Operation.JUMPDEST)
    (hStep :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          (EvmYul.Operation.JUMPDEST,
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).2))
        (afterMemoryChargeAt state) = .ok gasfulNext)
    (hDecode : Compact.decodeAt bytes pc .jumpdest)
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc)
    (hCont :
      RunRefinesOpen
        (EvmYul.EVM.X fuel validJumps gasfulNext)
        (Compact.InteractionSemantics.openRunNResult
          bytes fuel (afterDynamicChargeAt state).incrPC)
        transcript) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) (afterDynamicChargeAt state))
      transcript := by
  rw [x_jumpdest_continues_after_charges hPrefix hJumpdest hStep]
  have hFirst :
      Interaction.Executes
        (Compact.InteractionSemantics.openStepResult
          bytes (afterDynamicChargeAt state))
        []
        (.ok (.running (afterDynamicChargeAt state).incrPC)) := by
    rw [Compact.openStepResultEqInstrOfDecodeAt
      (instr := .jumpdest) trivial hDecode hPc]
    exact Interaction.Executes.done _
  cases hCont with
  | completed hExec hDone =>
      apply RunRefinesOpen.completed
      · rw [Compact.InteractionSemantics.openRunNResult_succ]
        simpa using
          (Interaction.Executes.bind_ok
            (first := Compact.InteractionSemantics.openStepResult
              bytes (afterDynamicChargeAt state))
            (next := fun result =>
              match result with
              | .running mid =>
                  Compact.InteractionSemantics.openRunNResult bytes fuel mid
              | .halted halt => Interaction.pure (.halted halt))
            hFirst hExec)
      · exact hDone
  | outOfGas hGas hFollow =>
      apply RunRefinesOpen.outOfGas hGas
      rw [Compact.InteractionSemantics.openRunNResult_succ]
      simpa using
        (Interaction.Follows.bind_ok
          (first := Compact.InteractionSemantics.openStepResult
            bytes (afterDynamicChargeAt state))
            (next := fun result =>
              match result with
              | .running mid =>
                  Compact.InteractionSemantics.openRunNResult bytes fuel mid
              | .halted halt => Interaction.pure (.halted halt))
            hFirst hFollow)
  | outOfFuel hFuel hFollow =>
      apply RunRefinesOpen.outOfFuel hFuel
      rw [Compact.InteractionSemantics.openRunNResult_succ]
      simpa using
        (Interaction.Follows.bind_ok
          (first := Compact.InteractionSemantics.openStepResult
            bytes (afterDynamicChargeAt state))
          (next := fun result =>
            match result with
            | .running mid =>
                Compact.InteractionSemantics.openRunNResult bytes fuel mid
            | .halted halt => Interaction.pure (.halted halt))
          hFirst hFollow)
  | badJumpDestination hBad hFollow =>
      apply RunRefinesOpen.badJumpDestination hBad
      rw [Compact.InteractionSemantics.openRunNResult_succ]
      simpa using
        (Interaction.Follows.bind_ok
          (first := Compact.InteractionSemantics.openStepResult
            bytes (afterDynamicChargeAt state))
          (next := fun result =>
            match result with
            | .running mid =>
                Compact.InteractionSemantics.openRunNResult bytes fuel mid
            | .halted halt => Interaction.pure (.halted halt))
          hFirst hFollow)
  | stackOverflow hOverflow hFollow =>
      apply RunRefinesOpen.stackOverflow hOverflow
      rw [Compact.InteractionSemantics.openRunNResult_succ]
      simpa using
        (Interaction.Follows.bind_ok
          (first := Compact.InteractionSemantics.openStepResult
            bytes (afterDynamicChargeAt state))
          (next := fun result =>
            match result with
            | .running mid =>
                Compact.InteractionSemantics.openRunNResult bytes fuel mid
            | .halted halt => Interaction.pure (.halted halt))
          hFirst hFollow)

theorem runRefinesOpen_stop_success
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state gasfulFinal : EVMState}
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hStop : decodedOperationAt state = EvmYul.Operation.STOP)
    (hStep :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          (EvmYul.Operation.STOP,
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).2))
        (afterMemoryChargeAt state) = .ok gasfulFinal)
    (hDecode : Compact.decodeAt bytes pc (.prim .stop))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) (afterDynamicChargeAt state))
      [] := by
  rw [x_stop_success_after_charges hPrefix hStop hStep]
  have hOne :=
    raw_stop_executes_after_charges
      (bytes := bytes) (pc := pc) (state := state) hDecode hPc
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_halted_add_executes
      (extra := fuel) hOne
  apply RunRefinesOpen.completed
  · simpa [Nat.add_comm] using hExec
  · exact DoneRel.success (sameData_stop_step_after_charges hStep)

theorem runRefinesOpen_invalid_instruction_after_gas_checks
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hGas : XGasChecksPass state)
    (hInvalid : EvmYul.EVM.δ (decodedOperationAt state) = none)
    (hDecode : Compact.decodeAt bytes pc (.prim .invalid))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) (afterDynamicChargeAt state))
      [] := by
  rw [x_invalid_instruction_after_gas_checks
    (fuel := fuel) (validJumps := validJumps) (state := state)
    hGas hInvalid]
  have hOne :=
    raw_invalid_instruction_executes_after_charges
      (bytes := bytes) (pc := pc) (state := state) hDecode hPc
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_error_add_executes
      (extra := fuel) hOne
  apply RunRefinesOpen.completed
  · simpa [Nat.add_comm] using hExec
  · exact DoneRel.sameError

theorem runRefinesOpen_invalid_returndatacopy_after_jump_checks
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hPrefix : XJumpChecksPass validJumps state)
    (hInvalid : invalidReturnDataCopyAt state)
    (hDecode : Compact.decodeAt bytes pc (.prim .returndatacopy))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) (afterDynamicChargeAt state))
      [] := by
  rw [x_invalid_returndatacopy_after_jump_checks
    (fuel := fuel) (validJumps := validJumps) (state := state)
    hPrefix hInvalid]
  have hOne :=
    raw_invalid_returndatacopy_executes_after_charges
      (validJumps := validJumps) (bytes := bytes)
      (pc := pc) (state := state) hPrefix hInvalid hDecode hPc
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_error_add_executes
      (extra := fuel) hOne
  apply RunRefinesOpen.completed
  · simpa [Nat.add_comm] using hExec
  · exact DoneRel.sameError

theorem runRefinesOpen_continuing_prim_stackUnderflow_after_gas_checks
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    {op : PrimOp} {step : PrimStep} {arg : Option (Word × Nat)}
    (hGas : XGasChecksPass state)
    (hDecodedPair :
      ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
        (EvmYul.Operation.STOP, none)) = (op.toEVM, arg))
    (hStep : op.continuingStep? = some step)
    (hMsize : op ≠ .msize)
    (hStaticPermits : continuingPrimStaticPermits state op)
    (hShort :
      state.stack.length < (EvmYul.EVM.δ op.toEVM).getD 0)
    (hDecode : Compact.decodeAt bytes pc (.prim op))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) (afterDynamicChargeAt state))
      [] := by
  have hDecodedOp : decodedOperationAt state = op.toEVM := by
    simpa [decodedOperationAt, hDecodedPair]
  have hOpcodeValidOp :
      EvmYul.EVM.δ op.toEVM ≠ none := by
    cases op <;>
      simp [PrimOp.continuingStep?, PrimOp.toEVM, EvmYul.EVM.δ]
        at hStep hShort ⊢
  have hOpcodeValid :
      EvmYul.EVM.δ (decodedOperationAt state) ≠ none := by
    simpa [hDecodedOp] using hOpcodeValidOp
  have hShortDecoded :
      state.stack.length <
        (EvmYul.EVM.δ (decodedOperationAt state)).getD 0 := by
    simpa [hDecodedOp] using hShort
  rw [x_stack_underflow_after_gas_opcode_check
    (fuel := fuel) (validJumps := validJumps) (state := state)
    hGas hOpcodeValid hShortDecoded]
  have hOne :=
    raw_continuing_prim_stackUnderflow_executes_after_charges
      (op := op) (step := step) (bytes := bytes)
      (pc := pc) (state := state)
      hStep hMsize hStaticPermits hShort hDecode hPc
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_error_add_executes
      (extra := fuel) hOne
  apply RunRefinesOpen.completed
  · simpa [Nat.add_comm] using hExec
  · exact DoneRel.sameError

theorem runRefinesOpen_return_stackUnderflow_after_gas_checks
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hGas : XGasChecksPass state)
    (hReturn : decodedOperationAt state = EvmYul.Operation.RETURN)
    (hShort : state.stack.length < 2)
    (hDecode : Compact.decodeAt bytes pc (.prim .return))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) (afterDynamicChargeAt state))
      [] := by
  have hOpcodeValid :
      EvmYul.EVM.δ (decodedOperationAt state) ≠ none := by
    simp [hReturn, EvmYul.EVM.δ]
  have hShortDecoded :
      state.stack.length <
        (EvmYul.EVM.δ (decodedOperationAt state)).getD 0 := by
    simpa [hReturn, EvmYul.EVM.δ] using hShort
  rw [x_stack_underflow_after_gas_opcode_check
    (fuel := fuel) (validJumps := validJumps) (state := state)
    hGas hOpcodeValid hShortDecoded]
  have hOne :=
    raw_return_stackUnderflow_executes_after_charges
      (bytes := bytes) (pc := pc) (state := state)
      hShort hDecode hPc
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_error_add_executes
      (extra := fuel) hOne
  apply RunRefinesOpen.completed
  · simpa [Nat.add_comm] using hExec
  · exact DoneRel.sameError

theorem runRefinesOpen_revert_stackUnderflow_after_gas_checks
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hGas : XGasChecksPass state)
    (hRevert : decodedOperationAt state = EvmYul.Operation.REVERT)
    (hShort : state.stack.length < 2)
    (hDecode : Compact.decodeAt bytes pc (.prim .revert))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) (afterDynamicChargeAt state))
      [] := by
  have hOpcodeValid :
      EvmYul.EVM.δ (decodedOperationAt state) ≠ none := by
    simp [hRevert, EvmYul.EVM.δ]
  have hShortDecoded :
      state.stack.length <
        (EvmYul.EVM.δ (decodedOperationAt state)).getD 0 := by
    simpa [hRevert, EvmYul.EVM.δ] using hShort
  rw [x_stack_underflow_after_gas_opcode_check
    (fuel := fuel) (validJumps := validJumps) (state := state)
    hGas hOpcodeValid hShortDecoded]
  have hOne :=
    raw_revert_stackUnderflow_executes_after_charges
      (bytes := bytes) (pc := pc) (state := state)
      hShort hDecode hPc
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_error_add_executes
      (extra := fuel) hOne
  apply RunRefinesOpen.completed
  · simpa [Nat.add_comm] using hExec
  · exact DoneRel.sameError

theorem runRefinesOpen_jump_stackUnderflow_after_gas_checks
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hGas : XGasChecksPass state)
    (hJump : decodedOperationAt state = EvmYul.Operation.JUMP)
    (hShort : state.stack.length < 1)
    (hDecode : Compact.decodeAt bytes pc .jump)
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) (afterDynamicChargeAt state))
      [] := by
  have hOpcodeValid :
      EvmYul.EVM.δ (decodedOperationAt state) ≠ none := by
    simp [hJump, EvmYul.EVM.δ]
  have hShortDecoded :
      state.stack.length <
        (EvmYul.EVM.δ (decodedOperationAt state)).getD 0 := by
    simpa [hJump, EvmYul.EVM.δ] using hShort
  rw [x_stack_underflow_after_gas_opcode_check
    (fuel := fuel) (validJumps := validJumps) (state := state)
    hGas hOpcodeValid hShortDecoded]
  have hOne :=
    raw_jump_stackUnderflow_executes_after_charges
      (bytes := bytes) (pc := pc) (state := state)
      hShort hDecode hPc
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_error_add_executes
      (extra := fuel) hOne
  apply RunRefinesOpen.completed
  · simpa [Nat.add_comm] using hExec
  · exact DoneRel.sameError

theorem runRefinesOpen_jumpi_stackUnderflow_after_gas_checks
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hGas : XGasChecksPass state)
    (hJumpi : decodedOperationAt state = EvmYul.Operation.JUMPI)
    (hShort : state.stack.length < 2)
    (hDecode : Compact.decodeAt bytes pc .jumpi)
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) (afterDynamicChargeAt state))
      [] := by
  have hOpcodeValid :
      EvmYul.EVM.δ (decodedOperationAt state) ≠ none := by
    simp [hJumpi, EvmYul.EVM.δ]
  have hShortDecoded :
      state.stack.length <
        (EvmYul.EVM.δ (decodedOperationAt state)).getD 0 := by
    simpa [hJumpi, EvmYul.EVM.δ] using hShort
  rw [x_stack_underflow_after_gas_opcode_check
    (fuel := fuel) (validJumps := validJumps) (state := state)
    hGas hOpcodeValid hShortDecoded]
  have hOne :=
    raw_jumpi_stackUnderflow_executes_after_charges
      (bytes := bytes) (pc := pc) (state := state)
      hShort hDecode hPc
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_error_add_executes
      (extra := fuel) hOne
  apply RunRefinesOpen.completed
  · simpa [Nat.add_comm] using hExec
  · exact DoneRel.sameError

theorem runRefinesOpen_create_stackUnderflow_after_gas_checks
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hGas : XGasChecksPass state)
    (hCreate : decodedOperationAt state = EvmYul.Operation.CREATE)
    (hShort : state.stack.length < 3)
    (hDecode : Compact.decodeAt bytes pc (.prim .create))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) (afterDynamicChargeAt state))
      [] := by
  have hOpcodeValid :
      EvmYul.EVM.δ (decodedOperationAt state) ≠ none := by
    simp [hCreate, EvmYul.EVM.δ]
  have hShortDecoded :
      state.stack.length <
        (EvmYul.EVM.δ (decodedOperationAt state)).getD 0 := by
    simpa [hCreate, EvmYul.EVM.δ] using hShort
  rw [x_stack_underflow_after_gas_opcode_check
    (fuel := fuel) (validJumps := validJumps) (state := state)
    hGas hOpcodeValid hShortDecoded]
  have hOne :=
    raw_create_stackUnderflow_executes_after_charges
      (bytes := bytes) (pc := pc) (state := state)
      hShort hDecode hPc
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_error_add_executes
      (extra := fuel) hOne
  apply RunRefinesOpen.completed
  · simpa [Nat.add_comm] using hExec
  · exact DoneRel.sameError

theorem runRefinesOpen_create2_stackUnderflow_after_gas_checks
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hGas : XGasChecksPass state)
    (hCreate2 : decodedOperationAt state = EvmYul.Operation.CREATE2)
    (hShort : state.stack.length < 4)
    (hDecode : Compact.decodeAt bytes pc (.prim .create2))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) (afterDynamicChargeAt state))
      [] := by
  have hOpcodeValid :
      EvmYul.EVM.δ (decodedOperationAt state) ≠ none := by
    simp [hCreate2, EvmYul.EVM.δ]
  have hShortDecoded :
      state.stack.length <
        (EvmYul.EVM.δ (decodedOperationAt state)).getD 0 := by
    simpa [hCreate2, EvmYul.EVM.δ] using hShort
  rw [x_stack_underflow_after_gas_opcode_check
    (fuel := fuel) (validJumps := validJumps) (state := state)
    hGas hOpcodeValid hShortDecoded]
  have hOne :=
    raw_create2_stackUnderflow_executes_after_charges
      (bytes := bytes) (pc := pc) (state := state)
      hShort hDecode hPc
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_error_add_executes
      (extra := fuel) hOne
  apply RunRefinesOpen.completed
  · simpa [Nat.add_comm] using hExec
  · exact DoneRel.sameError

theorem runRefinesOpen_call_stackUnderflow_after_gas_checks
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hGas : XGasChecksPass state)
    (hCall : decodedOperationAt state = EvmYul.Operation.CALL)
    (hShort : state.stack.length < 7)
    (hDecode : Compact.decodeAt bytes pc (.prim .call))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) (afterDynamicChargeAt state))
      [] := by
  have hOpcodeValid :
      EvmYul.EVM.δ (decodedOperationAt state) ≠ none := by
    simp [hCall, EvmYul.EVM.δ]
  have hShortDecoded :
      state.stack.length <
        (EvmYul.EVM.δ (decodedOperationAt state)).getD 0 := by
    simpa [hCall, EvmYul.EVM.δ] using hShort
  rw [x_stack_underflow_after_gas_opcode_check
    (fuel := fuel) (validJumps := validJumps) (state := state)
    hGas hOpcodeValid hShortDecoded]
  have hOne :=
    raw_call_stackUnderflow_executes_after_charges
      (bytes := bytes) (pc := pc) (state := state)
      hShort hDecode hPc
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_error_add_executes
      (extra := fuel) hOne
  apply RunRefinesOpen.completed
  · simpa [Nat.add_comm] using hExec
  · exact DoneRel.sameError

theorem runRefinesOpen_callcode_stackUnderflow_after_gas_checks
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hGas : XGasChecksPass state)
    (hCallcode : decodedOperationAt state = EvmYul.Operation.CALLCODE)
    (hShort : state.stack.length < 7)
    (hDecode : Compact.decodeAt bytes pc (.prim .callcode))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) (afterDynamicChargeAt state))
      [] := by
  have hOpcodeValid :
      EvmYul.EVM.δ (decodedOperationAt state) ≠ none := by
    simp [hCallcode, EvmYul.EVM.δ]
  have hShortDecoded :
      state.stack.length <
        (EvmYul.EVM.δ (decodedOperationAt state)).getD 0 := by
    simpa [hCallcode, EvmYul.EVM.δ] using hShort
  rw [x_stack_underflow_after_gas_opcode_check
    (fuel := fuel) (validJumps := validJumps) (state := state)
    hGas hOpcodeValid hShortDecoded]
  have hOne :=
    raw_callcode_stackUnderflow_executes_after_charges
      (bytes := bytes) (pc := pc) (state := state)
      hShort hDecode hPc
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_error_add_executes
      (extra := fuel) hOne
  apply RunRefinesOpen.completed
  · simpa [Nat.add_comm] using hExec
  · exact DoneRel.sameError

theorem runRefinesOpen_delegatecall_stackUnderflow_after_gas_checks
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hGas : XGasChecksPass state)
    (hDelegatecall :
      decodedOperationAt state = EvmYul.Operation.DELEGATECALL)
    (hShort : state.stack.length < 6)
    (hDecode : Compact.decodeAt bytes pc (.prim .delegatecall))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) (afterDynamicChargeAt state))
      [] := by
  have hOpcodeValid :
      EvmYul.EVM.δ (decodedOperationAt state) ≠ none := by
    simp [hDelegatecall, EvmYul.EVM.δ]
  have hShortDecoded :
      state.stack.length <
        (EvmYul.EVM.δ (decodedOperationAt state)).getD 0 := by
    simpa [hDelegatecall, EvmYul.EVM.δ] using hShort
  rw [x_stack_underflow_after_gas_opcode_check
    (fuel := fuel) (validJumps := validJumps) (state := state)
    hGas hOpcodeValid hShortDecoded]
  have hOne :=
    raw_delegatecall_stackUnderflow_executes_after_charges
      (bytes := bytes) (pc := pc) (state := state)
      hShort hDecode hPc
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_error_add_executes
      (extra := fuel) hOne
  apply RunRefinesOpen.completed
  · simpa [Nat.add_comm] using hExec
  · exact DoneRel.sameError

theorem runRefinesOpen_staticcall_stackUnderflow_after_gas_checks
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hGas : XGasChecksPass state)
    (hStaticcall : decodedOperationAt state = EvmYul.Operation.STATICCALL)
    (hShort : state.stack.length < 6)
    (hDecode : Compact.decodeAt bytes pc (.prim .staticcall))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) (afterDynamicChargeAt state))
      [] := by
  have hOpcodeValid :
      EvmYul.EVM.δ (decodedOperationAt state) ≠ none := by
    simp [hStaticcall, EvmYul.EVM.δ]
  have hShortDecoded :
      state.stack.length <
        (EvmYul.EVM.δ (decodedOperationAt state)).getD 0 := by
    simpa [hStaticcall, EvmYul.EVM.δ] using hShort
  rw [x_stack_underflow_after_gas_opcode_check
    (fuel := fuel) (validJumps := validJumps) (state := state)
    hGas hOpcodeValid hShortDecoded]
  have hOne :=
    raw_staticcall_stackUnderflow_executes_after_charges
      (bytes := bytes) (pc := pc) (state := state)
      hShort hDecode hPc
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_error_add_executes
      (extra := fuel) hOne
  apply RunRefinesOpen.completed
  · simpa [Nat.add_comm] using hExec
  · exact DoneRel.sameError

theorem runRefinesOpen_selfdestruct_stackUnderflow_after_gas_checks
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hGas : XGasChecksPass state)
    (hSelfdestruct :
      decodedOperationAt state = EvmYul.Operation.SELFDESTRUCT)
    (hPerm : state.executionEnv.perm = true)
    (hShort : state.stack.length < 1)
    (hDecode : Compact.decodeAt bytes pc (.prim .selfdestruct))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) (afterDynamicChargeAt state))
      [] := by
  have hOpcodeValid :
      EvmYul.EVM.δ (decodedOperationAt state) ≠ none := by
    simp [hSelfdestruct, EvmYul.EVM.δ]
  have hShortDecoded :
      state.stack.length <
        (EvmYul.EVM.δ (decodedOperationAt state)).getD 0 := by
    simpa [hSelfdestruct, EvmYul.EVM.δ] using hShort
  rw [x_stack_underflow_after_gas_opcode_check
    (fuel := fuel) (validJumps := validJumps) (state := state)
    hGas hOpcodeValid hShortDecoded]
  have hOne :=
    raw_selfdestruct_stackUnderflow_executes_after_charges
      (bytes := bytes) (pc := pc) (state := state)
      hPerm hShort hDecode hPc
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_error_add_executes
      (extra := fuel) hOne
  apply RunRefinesOpen.completed
  · simpa [Nat.add_comm] using hExec
  · exact DoneRel.sameError

theorem runRefinesOpen_continuing_prim_staticModeViolation_after_stack_limit_checks
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    {op : PrimOp} {step : PrimStep} {arg : Option (Word × Nat)}
    (hPrefix : XStackLimitChecksPass validJumps state)
    (hDecodedPair :
      ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
        (EvmYul.Operation.STOP, none)) = (op.toEVM, arg))
    (hStep : op.continuingStep? = some step)
    (hSensitive : continuingPrimStaticSensitive op)
    (hPerm : state.executionEnv.perm = false)
    (hDecode : Compact.decodeAt bytes pc (.prim op))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) (afterDynamicChargeAt state))
      [] := by
  have hDecodedOp : decodedOperationAt state = op.toEVM := by
    simpa [decodedOperationAt, hDecodedPair]
  have hStatic :
      staticModeViolationAt state :=
    staticModeViolationAt_of_continuingPrim_static
      hDecodedOp hSensitive hPerm
  rw [x_static_mode_violation_after_stack_limit_checks
    (fuel := fuel) (validJumps := validJumps) (state := state)
    hPrefix hStatic]
  have hOne :=
    raw_continuing_prim_staticModeViolation_executes_after_charges
      (op := op) (step := step) (bytes := bytes)
      (pc := pc) (state := state)
      hStep hSensitive hPerm hDecode hPc
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_error_add_executes
      (extra := fuel) hOne
  apply RunRefinesOpen.completed
  · simpa [Nat.add_comm] using hExec
  · exact DoneRel.sameError

theorem runRefinesOpen_create_staticModeViolation_after_stack_limit_checks
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hPrefix : XStackLimitChecksPass validJumps state)
    (hCreate : decodedOperationAt state = EvmYul.Operation.CREATE)
    (hPerm : state.executionEnv.perm = false)
    (hDecode : Compact.decodeAt bytes pc (.prim .create))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) (afterDynamicChargeAt state))
      [] := by
  have hStatic : staticModeViolationAt state :=
    ⟨hPerm, Or.inl hCreate⟩
  rw [x_static_mode_violation_after_stack_limit_checks
    (fuel := fuel) (validJumps := validJumps) (state := state)
    hPrefix hStatic]
  rcases create_operands_of_stackEnough hPrefix hCreate with
    ⟨rest, operands, hOperands⟩
  have hOne :=
    raw_create_staticModeViolation_executes_after_charges
      (bytes := bytes) (pc := pc) (state := state)
      (rest := rest) (operands := operands)
      hOperands hPerm hDecode hPc
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_error_add_executes
      (extra := fuel) hOne
  apply RunRefinesOpen.completed
  · simpa [Nat.add_comm] using hExec
  · exact DoneRel.sameError

theorem runRefinesOpen_create2_staticModeViolation_after_stack_limit_checks
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hPrefix : XStackLimitChecksPass validJumps state)
    (hCreate2 : decodedOperationAt state = EvmYul.Operation.CREATE2)
    (hPerm : state.executionEnv.perm = false)
    (hDecode : Compact.decodeAt bytes pc (.prim .create2))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) (afterDynamicChargeAt state))
      [] := by
  have hStatic : staticModeViolationAt state :=
    ⟨hPerm, Or.inr (Or.inl hCreate2)⟩
  rw [x_static_mode_violation_after_stack_limit_checks
    (fuel := fuel) (validJumps := validJumps) (state := state)
    hPrefix hStatic]
  rcases create2_operands_of_stackEnough hPrefix hCreate2 with
    ⟨rest, operands, hOperands⟩
  have hOne :=
    raw_create2_staticModeViolation_executes_after_charges
      (bytes := bytes) (pc := pc) (state := state)
      (rest := rest) (operands := operands)
      hOperands hPerm hDecode hPc
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_error_add_executes
      (extra := fuel) hOne
  apply RunRefinesOpen.completed
  · simpa [Nat.add_comm] using hExec
  · exact DoneRel.sameError

theorem runRefinesOpen_call_staticModeViolation_after_stack_limit_checks
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hPrefix : XStackLimitChecksPass validJumps state)
    (hCall : decodedOperationAt state = EvmYul.Operation.CALL)
    (hPerm : state.executionEnv.perm = false)
    (hStackValue :
      state.stack[2]? ≠ some (EvmYul.UInt256.ofNat 0))
    (hDecode : Compact.decodeAt bytes pc (.prim .call))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) (afterDynamicChargeAt state))
      [] := by
  have hStatic : staticModeViolationAt state := by
    simp [staticModeViolationAt, hPerm, hCall, hStackValue]
  rw [x_static_mode_violation_after_stack_limit_checks
    (fuel := fuel) (validJumps := validJumps) (state := state)
    hPrefix hStatic]
  rcases call_operands_of_stackEnough hPrefix hCall with
    ⟨rest, operands, hOperands⟩
  have hValue :
      operands.valueArg ≠ EvmYul.UInt256.ofNat 0 :=
    call_valueArg_ne_zero_of_operands hOperands hStackValue
  have hOne :=
    raw_call_staticModeViolation_executes_after_charges
      (bytes := bytes) (pc := pc) (state := state)
      (rest := rest) (operands := operands)
      hOperands hPerm hValue hDecode hPc
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_error_add_executes
      (extra := fuel) hOne
  apply RunRefinesOpen.completed
  · simpa [Nat.add_comm] using hExec
  · exact DoneRel.sameError

theorem runRefinesOpen_selfdestruct_staticModeViolation_after_stack_limit_checks
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hPrefix : XStackLimitChecksPass validJumps state)
    (hSelfdestruct :
      decodedOperationAt state = EvmYul.Operation.SELFDESTRUCT)
    (hPerm : state.executionEnv.perm = false)
    (hDecode : Compact.decodeAt bytes pc (.prim .selfdestruct))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) (afterDynamicChargeAt state))
      [] := by
  have hStatic : staticModeViolationAt state := by
    simp [staticModeViolationAt, hPerm, hSelfdestruct]
  rw [x_static_mode_violation_after_stack_limit_checks
    (fuel := fuel) (validJumps := validJumps) (state := state)
    hPrefix hStatic]
  have hOne :=
    raw_selfdestruct_staticModeViolation_executes_after_charges
      (bytes := bytes) (pc := pc) (state := state)
      hPerm hDecode hPc
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_error_add_executes
      (extra := fuel) hOne
  apply RunRefinesOpen.completed
  · simpa [Nat.add_comm] using hExec
  · exact DoneRel.sameError

theorem runRefinesOpen_selfdestruct_success
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    {recipient : Word} {rest : EvmYul.Stack Word}
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hDecodedPair :
      ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
        (EvmYul.Operation.STOP, none)) =
          (EvmYul.Operation.SELFDESTRUCT, none))
    (hPerm : state.executionEnv.perm = true)
    (hStack : state.stack = recipient :: rest)
    (hDecode : Compact.decodeAt bytes pc (.prim .selfdestruct))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1 + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1 + 1) (afterDynamicChargeAt state))
      [] := by
  have hDecodedOp :
      decodedOperationAt state = EvmYul.Operation.SELFDESTRUCT := by
    simpa [decodedOperationAt, hDecodedPair]
  have hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt state) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          state.stack[2]?.getD (EvmYul.UInt256.ofNat 0)) := by
    simp [hDecodedOp, EvmYul.Operation.isCreate]
  have hOne :=
    raw_selfdestruct_success_executes_after_charges
      (bytes := bytes) (pc := pc) (state := state)
      (recipient := recipient) (rest := rest)
      hPerm hStack hDecode hPc
  have hExec :
      Interaction.Executes
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1 + 1) (afterDynamicChargeAt state))
        []
        (.ok
          (.halted
            { kind := .selfdestruct
              state := openSelfdestructNext state recipient rest
              output := ByteArray.empty })) := by
    have hExtended :=
      Compact.InteractionSemantics.openRunNResult_halted_add_executes
        (extra := fuel + 1) hOne
    simpa [show 1 + (fuel + 1) = fuel + 1 + 1 by omega] using hExtended
  have hPostBridge :
      RunRefinesOpen
        (xPostStepExceptResult (fuel + 1) validJumps
          (decodedOperationAt state)
          (.ok (gasfulSelfdestructNext state recipient rest)))
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1 + 1) (afterDynamicChargeAt state))
        [] := by
    apply RunRefinesOpen.completed hExec
    simpa [xPostStepExceptResult, xPostStepResult, hDecodedOp,
      haltOutputAt] using
      (DoneRel.success
        (selfdestructNext_sameData state recipient rest)
        (output := ByteArray.empty) (haltKind := Assembly.HaltKind.selfdestruct))
  have hStepActual :
      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) =
          .ok (gasfulSelfdestructNext state recipient rest) := by
    simpa [hDecodedPair] using
      evm_step_selfdestruct_eq_next fuel state recipient rest hStack
  exact
    runRefinesOpen_of_x_after_prechecks_step_result
      (fuel := fuel + 1) (validJumps := validJumps) (state := state)
      (stepResult := .ok (gasfulSelfdestructNext state recipient rest))
      hPrefix hCreateOk hStepActual hPostBridge

theorem runRefinesOpen_return_success
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state gasfulFinal : EVMState}
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hReturn : decodedOperationAt state = EvmYul.Operation.RETURN)
    (hStep :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          (EvmYul.Operation.RETURN,
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).2))
        (afterMemoryChargeAt state) = .ok gasfulFinal)
    (hDecode : Compact.decodeAt bytes pc (.prim .return))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) (afterDynamicChargeAt state))
      [] := by
  rw [x_return_success_after_charges hPrefix hReturn hStep]
  have hOne :=
    raw_return_executes_after_charges
      (bytes := bytes) (pc := pc) (state := state)
      (gasfulFinal := gasfulFinal) hDecode hPc hStep
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_halted_add_executes
      (extra := fuel) hOne
  apply RunRefinesOpen.completed
  · simpa [Nat.add_comm] using hExec
  · exact DoneRel.success (sameData_return_step_after_charges hStep)

theorem runRefinesOpen_revert_success
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state gasfulFinal : EVMState}
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hRevert : decodedOperationAt state = EvmYul.Operation.REVERT)
    (hStep :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          (EvmYul.Operation.REVERT,
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)).2))
        (afterMemoryChargeAt state) = .ok gasfulFinal)
    (hDecode : Compact.decodeAt bytes pc (.prim .revert))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) (afterDynamicChargeAt state))
      [] := by
  rw [x_revert_success_after_charges hPrefix hRevert hStep]
  have hOne :=
    raw_revert_executes_after_charges
      (bytes := bytes) (pc := pc) (state := state)
      (gasfulFinal := gasfulFinal) hDecode hPc hStep
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_halted_add_executes
      (extra := fuel) hOne
  apply RunRefinesOpen.completed
  · simpa [Nat.add_comm] using hExec
  · exact DoneRel.revert

theorem runRefinesOpen_continuing_prim_success
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state gasfulNext : EVMState}
    {op : PrimOp} {step : PrimStep} {arg : Option (Word × Nat)}
    {transcript : Interaction.Transcript}
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hDecodedPair :
      ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
        (EvmYul.Operation.STOP, none)) = (op.toEVM, arg))
    (hStep : op.continuingStep? = some step)
    (hMsize : op ≠ .msize)
    (hTransparent : continuingPrimEVMStepTransparent op)
    (hDecode : Compact.decodeAt bytes pc (.prim op))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc)
    (hGasful :
      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
        (some (op.toEVM, arg)) (afterMemoryChargeAt state) =
          .ok gasfulNext)
    (hCont :
      ∀ openNext,
        SameData gasfulNext openNext →
          RunRefinesOpen
            (EvmYul.EVM.X (fuel + 1) validJumps gasfulNext)
            (Compact.InteractionSemantics.openRunNResult
              bytes (fuel + 1) openNext)
            transcript) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1 + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1 + 1) (afterDynamicChargeAt state))
      transcript := by
  have hDecodedOp : decodedOperationAt state = op.toEVM := by
    simpa [decodedOperationAt, hDecodedPair]
  have hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt state) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          state.stack[2]?.getD (EvmYul.UInt256.ofNat 0)) := by
    intro hBad
    have hCreateFalse :
        EvmYul.Operation.isCreate (decodedOperationAt state) = false := by
      simpa [hDecodedOp] using
        continuingStep_toEVM_isCreate_false hStep
    simp [hCreateFalse] at hBad
  have hStaticPermits : continuingPrimStaticPermits state op :=
    continuingPrimStaticPermits_of_static_check hPrefix.static hDecodedOp
  rcases raw_continuing_prim_refines_evm_step_after_charges
      (fuel := fuel) (op := op) (step := step)
      (bytes := bytes) (pc := pc) (state := state)
      (gasfulNext := gasfulNext) (arg := arg)
      hStep hMsize hTransparent hStaticPermits hDecode hPc hGasful with
    ⟨openNext, hFirst, hSame⟩
  have hTail := hCont openNext hSame
  have hPostRun :
      RunRefinesOpen
        (EvmYul.EVM.X (fuel + 1) validJumps gasfulNext)
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1 + 1) (afterDynamicChargeAt state))
        transcript := by
    cases hTail with
    | completed hExec hDone =>
        apply RunRefinesOpen.completed
        · rw [show fuel + 1 + 1 = 1 + (fuel + 1) by omega]
          rw [Compact.InteractionSemantics.openRunNResult_add]
          simpa using
            (Interaction.Executes.bind_ok
              (first := Compact.InteractionSemantics.openRunNResult
                bytes 1 (afterDynamicChargeAt state))
              (next := fun result =>
                match result with
                | .running mid =>
                    Compact.InteractionSemantics.openRunNResult
                      bytes (fuel + 1) mid
                | .halted halt => Interaction.pure (.halted halt))
              hFirst hExec)
        · exact hDone
    | outOfGas hGas hFollow =>
        apply RunRefinesOpen.outOfGas hGas
        rw [show fuel + 1 + 1 = 1 + (fuel + 1) by omega]
        rw [Compact.InteractionSemantics.openRunNResult_add]
        simpa using
          (Interaction.Follows.bind_ok
            (first := Compact.InteractionSemantics.openRunNResult
              bytes 1 (afterDynamicChargeAt state))
            (next := fun result =>
              match result with
              | .running mid =>
                  Compact.InteractionSemantics.openRunNResult
                    bytes (fuel + 1) mid
              | .halted halt => Interaction.pure (.halted halt))
            hFirst hFollow)
    | outOfFuel hFuel hFollow =>
        apply RunRefinesOpen.outOfFuel hFuel
        rw [show fuel + 1 + 1 = 1 + (fuel + 1) by omega]
        rw [Compact.InteractionSemantics.openRunNResult_add]
        simpa using
          (Interaction.Follows.bind_ok
            (first := Compact.InteractionSemantics.openRunNResult
              bytes 1 (afterDynamicChargeAt state))
            (next := fun result =>
              match result with
              | .running mid =>
                  Compact.InteractionSemantics.openRunNResult
                    bytes (fuel + 1) mid
              | .halted halt => Interaction.pure (.halted halt))
            hFirst hFollow)
    | badJumpDestination hBad hFollow =>
        apply RunRefinesOpen.badJumpDestination hBad
        rw [show fuel + 1 + 1 = 1 + (fuel + 1) by omega]
        rw [Compact.InteractionSemantics.openRunNResult_add]
        simpa using
          (Interaction.Follows.bind_ok
            (first := Compact.InteractionSemantics.openRunNResult
              bytes 1 (afterDynamicChargeAt state))
            (next := fun result =>
              match result with
              | .running mid =>
                  Compact.InteractionSemantics.openRunNResult
                    bytes (fuel + 1) mid
              | .halted halt => Interaction.pure (.halted halt))
            hFirst hFollow)
    | stackOverflow hOverflow hFollow =>
        apply RunRefinesOpen.stackOverflow hOverflow
        rw [show fuel + 1 + 1 = 1 + (fuel + 1) by omega]
        rw [Compact.InteractionSemantics.openRunNResult_add]
        simpa using
          (Interaction.Follows.bind_ok
            (first := Compact.InteractionSemantics.openRunNResult
              bytes 1 (afterDynamicChargeAt state))
            (next := fun result =>
              match result with
              | .running mid =>
                  Compact.InteractionSemantics.openRunNResult
                    bytes (fuel + 1) mid
              | .halted halt => Interaction.pure (.halted halt))
            hFirst hFollow)
  have hPostBridge :
      RunRefinesOpen
        (xPostStepExceptResult (fuel + 1) validJumps
          (decodedOperationAt state) (.ok gasfulNext))
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1 + 1) (afterDynamicChargeAt state))
        transcript := by
    simpa [xPostStepExceptResult, xPostStepResult, hDecodedOp,
      haltOutputAt_none_of_continuingStep gasfulNext hStep] using hPostRun
  have hStepActual :
      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok gasfulNext := by
    simpa [hDecodedPair] using hGasful
  exact
    runRefinesOpen_of_x_after_prechecks_step_result
      (fuel := fuel + 1) (validJumps := validJumps) (state := state)
      (stepResult := .ok gasfulNext)
      hPrefix hCreateOk hStepActual hPostBridge

theorem runRefinesOpen_call_external_success
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state gasfulNext : EVMState}
    {rest : EvmYul.Stack Word} {operands : CallOperands}
    {response : CallResponse} {arg : Option (Word × Nat)}
    {transcript : Interaction.Transcript}
    (kind : CallKind)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hDecodedPair :
      ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
        (EvmYul.Operation.STOP, none)) = (kind.toEVMOperation, arg))
    (hOperands :
      kind.evmOperands? state.stack = some (rest, operands))
    (hAllowed :
      kind.allowedIn
          (ExternalFrame.ofShared
            (afterDynamicChargeAt state).toSharedState)
          operands = true)
    (hDecode : Compact.decodeAt bytes pc (.prim (callPrimOp kind)))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc)
    (hGasful :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some (kind.toEVMOperation, arg)) (afterMemoryChargeAt state) =
          .ok gasfulNext)
    (hResponse :
      CallResponseStateRel kind (afterMemoryChargeAt state) operands
        response gasfulNext
        (InteractionSemantics.EVMState.finishCall
          (afterDynamicChargeAt state) rest operands.callLocal response))
    (hCont :
      CallResponseStateRel kind (afterMemoryChargeAt state) operands
          response gasfulNext
          (InteractionSemantics.EVMState.finishCall
            (afterDynamicChargeAt state) rest operands.callLocal response) →
        RunRefinesOpen
          (EvmYul.EVM.X fuel validJumps gasfulNext)
          (Compact.InteractionSemantics.openRunNResult
            bytes fuel
            (InteractionSemantics.EVMState.finishCall
              (afterDynamicChargeAt state) rest operands.callLocal
              response))
          transcript) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) (afterDynamicChargeAt state))
      (callExternalExchange kind (afterDynamicChargeAt state)
        operands response :: transcript) := by
  have hDecodedOp : decodedOperationAt state = kind.toEVMOperation := by
    simpa [decodedOperationAt, hDecodedPair]
  have hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt state) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          state.stack[2]?.getD (EvmYul.UInt256.ofNat 0)) := by
    intro hBad
    cases kind <;>
      simp [hDecodedOp, CallKind.toEVMOperation,
        EvmYul.Operation.isCreate] at hBad
  have hGasfulTail :
      xPostStepExceptResult fuel validJumps
          (decodedOperationAt state) (.ok gasfulNext) =
        EvmYul.EVM.X fuel validJumps gasfulNext := by
    cases kind <;>
      simp [xPostStepExceptResult, xPostStepResult, hDecodedOp,
        CallKind.toEVMOperation, haltOutputAt]
  have hFirst :=
    raw_call_external_executes_after_charges
      (bytes := bytes) (pc := pc) (state := state)
      (rest := rest) (operands := operands) (response := response)
      kind hOperands hAllowed hDecode hPc
  have hTail := hCont hResponse
  have hPostBridge :
      RunRefinesOpen
        (xPostStepExceptResult fuel validJumps
          (decodedOperationAt state) (.ok gasfulNext))
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1) (afterDynamicChargeAt state))
        (callExternalExchange kind (afterDynamicChargeAt state)
          operands response :: transcript) := by
    rw [show fuel + 1 = 1 + fuel by omega]
    rw [Compact.InteractionSemantics.openRunNResult_add]
    simpa [hGasfulTail] using
      (runRefinesOpen_bind_running_prefix
        (gasful := EvmYul.EVM.X fuel validJumps gasfulNext)
        (tailGasful := EvmYul.EVM.X fuel validJumps gasfulNext)
        (first := Compact.InteractionSemantics.openRunNResult
          bytes 1 (afterDynamicChargeAt state))
        (nextState :=
          InteractionSemantics.EVMState.finishCall
            (afterDynamicChargeAt state) rest operands.callLocal response)
        (tail := fun openNext =>
          Compact.InteractionSemantics.openRunNResult bytes fuel openNext)
        (firstTranscript :=
          [callExternalExchange kind (afterDynamicChargeAt state)
            operands response])
        (tailTranscript := transcript)
        rfl hFirst hTail)
  have hStepActual :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok gasfulNext := by
    simpa [hDecodedPair] using hGasful
  exact
    runRefinesOpen_of_x_after_prechecks_step_result
      (fuel := fuel) (validJumps := validJumps) (state := state)
      (stepResult := .ok gasfulNext)
      hPrefix hCreateOk hStepActual hPostBridge

theorem runRefinesOpen_call_external_success_actual
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state gasfulNext : EVMState}
    {rest : EvmYul.Stack Word} {operands : CallOperands}
    {arg : Option (Word × Nat)}
    (kind : CallKind)
    (tailTranscript : CallResponse → Interaction.Transcript)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hDecodedPair :
      ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
        (EvmYul.Operation.STOP, none)) = (kind.toEVMOperation, arg))
    (hOperands :
      kind.evmOperands? state.stack = some (rest, operands))
    (hAllowed :
      kind.allowedIn
          (ExternalFrame.ofShared
            (afterDynamicChargeAt state).toSharedState)
          operands = true)
    (hDecode : Compact.decodeAt bytes pc (.prim (callPrimOp kind)))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc)
    (hGasful :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some (kind.toEVMOperation, arg)) (afterMemoryChargeAt state) =
          .ok gasfulNext)
    (hCont :
      ∀ response,
        CallResponseStateRel kind (afterMemoryChargeAt state) operands
            response gasfulNext
            (InteractionSemantics.EVMState.finishCall
              (afterDynamicChargeAt state) rest operands.callLocal response) →
          RunRefinesOpen
            (EvmYul.EVM.X fuel validJumps gasfulNext)
            (Compact.InteractionSemantics.openRunNResult
              bytes fuel
              (InteractionSemantics.EVMState.finishCall
                (afterDynamicChargeAt state) rest operands.callLocal
                response))
            (tailTranscript response)) :
    ∃ response,
      RunRefinesOpen
        (EvmYul.EVM.X (fuel + 1) validJumps state)
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1) (afterDynamicChargeAt state))
        (callExternalExchange kind (afterDynamicChargeAt state)
          operands response :: tailTranscript response) := by
  have hDecodedOp : decodedOperationAt state = kind.toEVMOperation := by
    simpa [decodedOperationAt, hDecodedPair]
  obtain ⟨response, hResponse⟩ :=
    evm_step_call_responseStateRel_at
      kind hDecodedOp hOperands hGasful
  refine ⟨response, ?_⟩
  exact
    runRefinesOpen_call_external_success
      kind hPrefix hDecodedPair hOperands hAllowed hDecode hPc hGasful
      hResponse (hCont response)

theorem runRefinesOpen_create_external_success
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state gasfulNext : EVMState}
    {rest : EvmYul.Stack Word} {operands : CreateOperands}
    {response : CreateResponse} {arg : Option (Word × Nat)}
    {transcript : Interaction.Transcript}
    (kind : CreateKind)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt state) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          state.stack[2]?.getD (EvmYul.UInt256.ofNat 0)))
    (hDecodedPair :
      ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
        (EvmYul.Operation.STOP, none)) = (kind.toEVMOperation, arg))
    (hOperands :
      kind.evmOperands? state.stack = some (rest, operands))
    (hPermission :
      (ExternalFrame.ofShared
        (afterDynamicChargeAt state).toSharedState).permission = true)
    (hDecode : Compact.decodeAt bytes pc (.prim (createPrimOp kind)))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc)
    (hGasful :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some (kind.toEVMOperation, arg)) (afterMemoryChargeAt state) =
          .ok gasfulNext)
    (hResponse :
      CreateResponseStateRel kind (afterMemoryChargeAt state) operands
        response gasfulNext
        (InteractionSemantics.EVMState.finishCreate
          (afterDynamicChargeAt state) rest operands.createLocal response))
    (hCont :
      CreateResponseStateRel kind (afterMemoryChargeAt state) operands
          response gasfulNext
          (InteractionSemantics.EVMState.finishCreate
            (afterDynamicChargeAt state) rest operands.createLocal response) →
        RunRefinesOpen
          (EvmYul.EVM.X fuel validJumps gasfulNext)
          (Compact.InteractionSemantics.openRunNResult
            bytes fuel
            (InteractionSemantics.EVMState.finishCreate
              (afterDynamicChargeAt state) rest operands.createLocal
              response))
          transcript) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) (afterDynamicChargeAt state))
      (createExternalExchange kind (afterDynamicChargeAt state)
        operands response :: transcript) := by
  have hDecodedOp : decodedOperationAt state = kind.toEVMOperation := by
    simpa [decodedOperationAt, hDecodedPair]
  have hGasfulTail :
      xPostStepExceptResult fuel validJumps
          (decodedOperationAt state) (.ok gasfulNext) =
        EvmYul.EVM.X fuel validJumps gasfulNext := by
    cases kind <;>
      simp [xPostStepExceptResult, xPostStepResult, hDecodedOp,
        CreateKind.toEVMOperation, haltOutputAt]
  have hFirst :=
    raw_create_external_executes_after_charges
      (bytes := bytes) (pc := pc) (state := state)
      (rest := rest) (operands := operands) (response := response)
      kind hOperands hPermission hDecode hPc
  have hTail := hCont hResponse
  have hPostBridge :
      RunRefinesOpen
        (xPostStepExceptResult fuel validJumps
          (decodedOperationAt state) (.ok gasfulNext))
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1) (afterDynamicChargeAt state))
        (createExternalExchange kind (afterDynamicChargeAt state)
          operands response :: transcript) := by
    rw [show fuel + 1 = 1 + fuel by omega]
    rw [Compact.InteractionSemantics.openRunNResult_add]
    simpa [hGasfulTail] using
      (runRefinesOpen_bind_running_prefix
        (gasful := EvmYul.EVM.X fuel validJumps gasfulNext)
        (tailGasful := EvmYul.EVM.X fuel validJumps gasfulNext)
        (first := Compact.InteractionSemantics.openRunNResult
          bytes 1 (afterDynamicChargeAt state))
        (nextState :=
          InteractionSemantics.EVMState.finishCreate
            (afterDynamicChargeAt state) rest operands.createLocal response)
        (tail := fun openNext =>
          Compact.InteractionSemantics.openRunNResult bytes fuel openNext)
        (firstTranscript :=
          [createExternalExchange kind (afterDynamicChargeAt state)
            operands response])
        (tailTranscript := transcript)
        rfl hFirst hTail)
  have hStepActual :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok gasfulNext := by
    simpa [hDecodedPair] using hGasful
  exact
    runRefinesOpen_of_x_after_prechecks_step_result
      (fuel := fuel) (validJumps := validJumps) (state := state)
      (stepResult := .ok gasfulNext)
      hPrefix hCreateOk hStepActual hPostBridge

theorem runRefinesOpen_create_external_success_actual
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {state gasfulNext : EVMState}
    {rest : EvmYul.Stack Word} {operands : CreateOperands}
    {arg : Option (Word × Nat)}
    (kind : CreateKind)
    (tailTranscript : CreateResponse → Interaction.Transcript)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt state) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          state.stack[2]?.getD (EvmYul.UInt256.ofNat 0)))
    (hDecodedPair :
      ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
        (EvmYul.Operation.STOP, none)) = (kind.toEVMOperation, arg))
    (hOperands :
      kind.evmOperands? state.stack = some (rest, operands))
    (hPermission :
      (ExternalFrame.ofShared
        (afterDynamicChargeAt state).toSharedState).permission = true)
    (hDecode : Compact.decodeAt bytes pc (.prim (createPrimOp kind)))
    (hPc : (afterDynamicChargeAt state).pc = EvmYul.UInt256.ofNat pc)
    (hGasful :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some (kind.toEVMOperation, arg)) (afterMemoryChargeAt state) =
          .ok gasfulNext)
    (hCont :
      ∀ response,
        CreateResponseStateRel kind (afterMemoryChargeAt state) operands
            response gasfulNext
            (InteractionSemantics.EVMState.finishCreate
              (afterDynamicChargeAt state) rest operands.createLocal response) →
          RunRefinesOpen
            (EvmYul.EVM.X fuel validJumps gasfulNext)
            (Compact.InteractionSemantics.openRunNResult
              bytes fuel
              (InteractionSemantics.EVMState.finishCreate
                (afterDynamicChargeAt state) rest operands.createLocal
                response))
            (tailTranscript response)) :
    ∃ response,
      RunRefinesOpen
        (EvmYul.EVM.X (fuel + 1) validJumps state)
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1) (afterDynamicChargeAt state))
        (createExternalExchange kind (afterDynamicChargeAt state)
          operands response :: tailTranscript response) := by
  have hDecodedOp : decodedOperationAt state = kind.toEVMOperation := by
    simpa [decodedOperationAt, hDecodedPair]
  obtain ⟨response, hResponse⟩ :=
    evm_step_create_responseStateRel_at
      kind hDecodedOp hOperands hGasful
  refine ⟨response, ?_⟩
  exact
    runRefinesOpen_create_external_success
      kind hPrefix hCreateOk hDecodedPair hOperands hPermission hDecode hPc
      hGasful hResponse (hCont response)

theorem runRefinesOpen_outOfGas_prefix
    {openRun : Interaction EVMException StepResult}
    {transcript : Interaction.Transcript}
    (hFollows : Interaction.Follows openRun transcript) :
    RunRefinesOpen
      (.error EvmYul.EVM.ExecutionException.OutOfGass)
      openRun transcript :=
  .outOfGas rfl hFollows

theorem runRefinesOpen_outOfFuel_prefix
    {openRun : Interaction EVMException StepResult}
    {transcript : Interaction.Transcript}
    (hFollows : Interaction.Follows openRun transcript) :
    RunRefinesOpen
      (.error EvmYul.EVM.ExecutionException.OutOfFuel)
      openRun transcript :=
  .outOfFuel rfl hFollows

theorem runRefinesOpen_zero
    {validJumps : Array Word} {state : EVMState}
    {openRun : Interaction EVMException StepResult} :
    RunRefinesOpen (EvmYul.EVM.X 0 validJumps state) openRun [] := by
  apply RunRefinesOpen.outOfFuel rfl
  exact Interaction.Follows.nil openRun

theorem runRefinesOpen_badJumpDestination_prefix
    {openRun : Interaction EVMException StepResult}
    {transcript : Interaction.Transcript}
    (hFollows : Interaction.Follows openRun transcript) :
    RunRefinesOpen
      (.error EvmYul.EVM.ExecutionException.BadJumpDestination)
      openRun transcript :=
  .badJumpDestination rfl hFollows

theorem runRefinesOpen_stackOverflow_prefix
    {openRun : Interaction EVMException StepResult}
    {transcript : Interaction.Transcript}
    (hFollows : Interaction.Follows openRun transcript) :
    RunRefinesOpen
      (.error EvmYul.EVM.ExecutionException.StackOverflow)
      openRun transcript :=
  .stackOverflow rfl hFollows

theorem runRefinesOpen_outOfGas_before_memory_charge
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    {openRun : Interaction EVMException StepResult}
    (hGas : state.gasAvailable.toNat < memoryExpansionCostAt state) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      openRun [] := by
  exact
    RunRefinesOpen.outOfGas
      (x_outOfGas_before_memory_charge
        (fuel := fuel) (validJumps := validJumps) hGas)
      (Interaction.Follows.nil openRun)

theorem runRefinesOpen_outOfGas_before_dynamic_charge
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    {openRun : Interaction EVMException StepResult}
    (hMemoryGas :
      ¬ state.gasAvailable.toNat < memoryExpansionCostAt state)
    (hDynamicGas :
      (afterMemoryChargeAt state).gasAvailable.toNat <
        dynamicGasCostAt state) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      openRun [] := by
  exact
    RunRefinesOpen.outOfGas
      (x_outOfGas_before_dynamic_charge
        (fuel := fuel) (validJumps := validJumps)
        hMemoryGas hDynamicGas)
      (Interaction.Follows.nil openRun)

theorem runRefinesOpen_bad_jump_destination_after_stack_check
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    {openRun : Interaction EVMException StepResult}
    (hPrefix : XOpcodeStackChecksPass state)
    (hBadJump : badJumpAt validJumps state) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      openRun [] := by
  exact
    RunRefinesOpen.badJumpDestination
      (x_bad_jump_destination_after_stack_check
        (fuel := fuel) (validJumps := validJumps)
        (state := state) hPrefix
        (by simpa [badJumpAt] using hBadJump))
      (Interaction.Follows.nil openRun)

theorem runRefinesOpen_bad_jumpi_destination_after_stack_check
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    {openRun : Interaction EVMException StepResult}
    (hPrefix : XOpcodeStackChecksPass state)
    (hBadJumpi : badJumpiAt validJumps state) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      openRun [] := by
  exact
    RunRefinesOpen.badJumpDestination
      (x_bad_jumpi_destination_after_stack_check
        (fuel := fuel) (validJumps := validJumps)
        (state := state) hPrefix
        (by simpa [badJumpiAt] using hBadJumpi))
      (Interaction.Follows.nil openRun)

theorem runRefinesOpen_stackOverflow_after_memory_access_checks
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    {openRun : Interaction EVMException StepResult}
    (hPrefix : XMemoryAccessChecksPass validJumps state)
    (hOverflow : stackOverflowAt state) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      openRun [] := by
  exact
    RunRefinesOpen.stackOverflow
      (x_stack_overflow_after_memory_access_checks
        (fuel := fuel) (validJumps := validJumps)
        (state := state) hPrefix hOverflow)
      (Interaction.Follows.nil openRun)

theorem runRefinesOpen_sstore_stipend_outOfGas
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    {openRun : Interaction EVMException StepResult}
    (hPrefix : XStaticChecksPass validJumps state)
    (hSstore : sstoreStipendOutOfGasAt state) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      openRun [] := by
  exact
    RunRefinesOpen.outOfGas
      (x_sstore_stipend_outOfGas_after_static_check
        (fuel := fuel) (validJumps := validJumps)
        hPrefix hSstore)
      (Interaction.Follows.nil openRun)

theorem runRefinesOpen_create_initcode_outOfGas
    {fuel : Nat} {validJumps : Array Word} {state : EVMState}
    {openRun : Interaction EVMException StepResult}
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hCreate :
      decodedOperationAt state = EvmYul.Operation.CREATE ∨
        decodedOperationAt state = EvmYul.Operation.CREATE2)
    (hTooLarge :
      (EvmYul.UInt256.ofNat 49152) <
        state.stack[2]?.getD (EvmYul.UInt256.ofNat 0)) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps state)
      openRun [] := by
  exact
    RunRefinesOpen.outOfGas
      (x_create_initcode_outOfGas_after_sstore_check
        (fuel := fuel) (validJumps := validJumps)
        hPrefix hCreate hTooLarge)
      (Interaction.Follows.nil openRun)

end GasfulBridge
end Assembly
end EvmCompiler
