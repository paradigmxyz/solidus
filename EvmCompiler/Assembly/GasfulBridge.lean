import EvmCompiler.Assembly.Compact
import EvmCompiler.Assembly.InteractionConcreteResources

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

theorem sameData_afterEVMInstructionCharge_afterDynamic
    (state : EVMState) :
    SameData (afterEVMInstructionChargeAt state)
      (afterDynamicChargeAt state) := by
  cases state
  rfl

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

/-- Continuing primitives whose imported `EvmYul.step` helper can currently be
related exactly from this module.  `LOG0..4` go through EVMYulLean's private
`evmLogOp` helper, so they need upstream/public helper equalities before joining
this exact-delegation theorem. -/
def continuingPrimEVMStepTransparent : PrimOp → Prop
  | .log0 | .log1 | .log2 | .log3 | .log4 => False
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
    cases hTransparent
  case log1 =>
    cases hTransparent
  case log2 =>
    cases hTransparent
  case log3 =>
    cases hTransparent
  case log4 =>
    cases hTransparent
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

/-- Gas accounting for CREATE/CREATE2 external creation. The child init-code
execution remains the open strategy response; this records EIP-150 parent gas
withholding and returned gas. -/
structure CreateBoundaryAccounting
    (preCostState : EVMState) (parentGasCost : Nat)
    (forwardedGas returnedGas finalGas : Word) : Prop where
  forwardedGas_eq :
    forwardedGas = createForwardedGas preCostState parentGasCost
  finalGas_eq :
    finalGas = createFinalGas preCostState parentGasCost returnedGas

theorem createBoundaryAccounting_canonical
    (preCostState : EVMState) (parentGasCost : Nat)
    (returnedGas : Word) :
    CreateBoundaryAccounting preCostState parentGasCost
      (createForwardedGas preCostState parentGasCost)
      returnedGas
      (createFinalGas preCostState parentGasCost returnedGas) where
  forwardedGas_eq := rfl
  finalGas_eq := rfl

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
reaching a related terminal leaf, or by explicitly interrupting with
out-of-gas after an open transcript prefix. -/
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

theorem runRefinesOpen_of_executes
    {gasful : Except EVMException (EvmYul.EVM.ExecutionResult EVMState)}
    {openRun : Interaction EVMException StepResult}
    {transcript : Interaction.Transcript}
    {openDone : Except EVMException StepResult}
    (hExec : Interaction.Executes openRun transcript openDone)
    (hDone : DoneRel gasful openDone) :
    RunRefinesOpen gasful openRun transcript :=
  .completed hExec hDone

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

theorem runRefinesOpen_outOfGas_prefix
    {openRun : Interaction EVMException StepResult}
    {transcript : Interaction.Transcript}
    (hFollows : Interaction.Follows openRun transcript) :
    RunRefinesOpen
      (.error EvmYul.EVM.ExecutionException.OutOfGass)
      openRun transcript :=
  .outOfGas rfl hFollows

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
