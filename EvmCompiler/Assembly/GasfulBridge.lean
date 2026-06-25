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

theorem runRefinesOpen_outOfGas_prefix
    {openRun : Interaction EVMException StepResult}
    {transcript : Interaction.Transcript}
    (hFollows : Interaction.Follows openRun transcript) :
    RunRefinesOpen
      (.error EvmYul.EVM.ExecutionException.OutOfGass)
      openRun transcript :=
  .outOfGas rfl hFollows

end GasfulBridge
end Assembly
end EvmCompiler
