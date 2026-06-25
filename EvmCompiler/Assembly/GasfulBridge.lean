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
