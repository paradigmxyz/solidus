import EvmCompiler.Assembly.GasfulBridgeDecode

namespace EvmCompiler.Assembly.GasfulBridge

open Simulation

/-!
Recursive gasful/open frame bridge.

The code invariant is deliberately frame-local and responder-agnostic. A
closed-world executor may establish it from its own reachable-frame/image
invariant without coupling this module to a registry or transaction model.
-/

structure FrameCodeAt (bytes : ByteArray) (state : EVMState) : Prop where
  code_eq : state.executionEnv.code = bytes
  supported : SupportedDecodeAt bytes state.pc

structure CurrentInstruction
    (bytes : ByteArray) (gasful openState : EVMState) where
  pc : Nat
  instr : Compact.Instr
  valid : instr.Valid
  decode : Compact.decodeAt bytes pc instr
  open_pc : openState.pc = EvmYul.UInt256.ofNat pc
  decoded : EvmYul.Operation .EVM × Option (Word × Nat)
  instr_decoded : instr.decoded? = some decoded
  gasful_decoded :
    EvmYul.EVM.decode gasful.executionEnv.code gasful.pc = some decoded

theorem currentInstruction_of_frameCodeAt
    {bytes : ByteArray} {gasful openState : EVMState}
    (hCode : FrameCodeAt bytes gasful)
    (hRel : OpenStateRel gasful openState) :
    Nonempty (CurrentInstruction bytes gasful openState) := by
  obtain ⟨instr, hValid, hAt⟩ :=
    compact_decodeAt_of_supported hCode.supported
  rcases hAt with ⟨decoded, hInstrDecoded, hBytesDecoded⟩
  let pc := gasful.pc.toNat
  have hOpenPc : openState.pc = EvmYul.UInt256.ofNat pc := by
    rw [← hRel.pc_eq]
    exact (EvmYul.UInt256.ofNat_toNat gasful.pc).symm
  have hGasfulDecoded :
      EvmYul.EVM.decode gasful.executionEnv.code gasful.pc =
        some decoded := by
    rw [hCode.code_eq]
    simpa [pc] using hBytesDecoded
  exact ⟨
    { pc := pc
      instr := instr
      valid := hValid
      decode := by simpa [pc] using ⟨decoded, hInstrDecoded, hBytesDecoded⟩
      open_pc := hOpenPc
      decoded := decoded
      instr_decoded := hInstrDecoded
      gasful_decoded := hGasfulDecoded }⟩

theorem CurrentInstruction.decodedPair
    {bytes : ByteArray} {gasful openState : EVMState}
    (current : CurrentInstruction bytes gasful openState) :
    ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
      (EvmYul.Operation.STOP, none)) = current.decoded := by
  rw [current.gasful_decoded]
  rfl

theorem CurrentInstruction.decodedOperation
    {bytes : ByteArray} {gasful openState : EVMState}
    (current : CurrentInstruction bytes gasful openState) :
    decodedOperationAt gasful = current.decoded.1 := by
  simp [decodedOperationAt, current.decodedPair]

theorem operation_eq_invalid_of_delta_none
    {op : EvmYul.Operation .EVM}
    (hInvalid : EvmYul.EVM.δ op = none) :
    op = EvmYul.Operation.INVALID := by
  cases op with
  | StopArith op => cases op <;> simp [EvmYul.EVM.δ] at hInvalid
  | CompBit op => cases op <;> simp [EvmYul.EVM.δ] at hInvalid
  | Keccak op => cases op; simp [EvmYul.EVM.δ] at hInvalid
  | Env op => cases op <;> simp [EvmYul.EVM.δ] at hInvalid
  | Block op => cases op <;> simp [EvmYul.EVM.δ] at hInvalid
  | StackMemFlow op => cases op <;> simp [EvmYul.EVM.δ] at hInvalid
  | Push op => cases op <;> simp [EvmYul.EVM.δ] at hInvalid
  | Dup op => cases op <;> simp [EvmYul.EVM.δ] at hInvalid
  | Exchange op => cases op <;> simp [EvmYul.EVM.δ] at hInvalid
  | Log op => cases op <;> simp [EvmYul.EVM.δ] at hInvalid
  | System op => cases op <;> simp [EvmYul.EVM.δ] at hInvalid ⊢

theorem compact_instr_eq_invalid_of_decoded
    {instr : Compact.Instr}
    {decoded : EvmYul.Operation .EVM × Option (Word × Nat)}
    (hValid : instr.Valid)
    (hDecoded : instr.decoded? = some decoded)
    (hInvalid : decoded.1 = EvmYul.Operation.INVALID) :
    instr = .prim .invalid := by
  cases instr with
  | push width value =>
      simp [Compact.Instr.Valid] at hValid
      have hPositive := hValid.1
      have hWidth := hValid.2.1
      interval_cases width <;>
        simp [Compact.Instr.decoded?, Compact.pushOp?] at hDecoded <;>
        subst decoded <;> simp at hInvalid
  | jump =>
      simp [Compact.Instr.decoded?] at hDecoded
      subst decoded
      simp at hInvalid
  | jumpi =>
      simp [Compact.Instr.decoded?] at hDecoded
      subst decoded
      simp at hInvalid
  | jumpdest =>
      simp [Compact.Instr.decoded?] at hDecoded
      subst decoded
      simp at hInvalid
  | prim op =>
      cases op <;>
        simp [Compact.Instr.decoded?, PrimOp.toEVM] at hDecoded <;>
        subst decoded <;> simp at hInvalid ⊢

theorem CurrentInstruction.instr_eq_invalid_of_delta_none
    {bytes : ByteArray} {gasful openState : EVMState}
    (current : CurrentInstruction bytes gasful openState)
    (hInvalid : EvmYul.EVM.δ (decodedOperationAt gasful) = none) :
    current.instr = .prim .invalid := by
  apply compact_instr_eq_invalid_of_decoded current.valid current.instr_decoded
  apply operation_eq_invalid_of_delta_none
  simpa [current.decodedOperation] using hInvalid

theorem raw_prim_error_executes_at
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    {op : PrimOp} {err : EVMException}
    (hDecode : Compact.decodeAt bytes pc (.prim op))
    (hPc : state.pc = EvmYul.UInt256.ofNat pc)
    (hOpen :
      Assembly.InteractionSemantics.PrimOp.openStep op state =
        Simulation.Interaction.done (.error err)) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult bytes 1 state)
      [] (.error err) := by
  rw [Compact.InteractionSemantics.openRunNResult_one_eq_instr
    (instr := .prim op) trivial hDecode hPc]
  simpa [Compact.Instr.openStepResult, Compact.Instr.openStep,
    Assembly.InteractionSemantics.Target.openStepInstrResult,
    Assembly.Target.stepInstrResultWith,
    Assembly.InteractionSemantics.Target.openStepInstr,
    Assembly.Target.stepInstrWith, hOpen,
    Simulation.Interaction.bind,
    Simulation.Interaction.bind_done_error] using
    (Interaction.Executes.done (.error err : Except EVMException StepResult))

theorem raw_invalid_instruction_executes_at
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hDecode : Compact.decodeAt bytes pc (.prim .invalid))
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult bytes 1 state)
      []
      (.error EvmYul.EVM.ExecutionException.InvalidInstruction) := by
  apply raw_prim_error_executes_at hDecode hPc
  simp [Assembly.InteractionSemantics.PrimOp.openStep,
    Assembly.PrimOp.toEVM,
    Simulation.ExternalKind.ofEVMOperation?,
    Simulation.CallKind.ofEVMOperation?,
    Simulation.CreateKind.ofEVMOperation?,
    Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
    Assembly.PrimStep.run]

theorem runRefinesOpen_invalid_instruction_rel
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {pc : Nat} {gasful openState : EVMState}
    (hRel : OpenStateRel gasful openState)
    (hGas : XGasChecksPass gasful)
    (hInvalid : EvmYul.EVM.δ (decodedOperationAt gasful) = none)
    (hDecode : Compact.decodeAt bytes pc (.prim .invalid))
    (hPc : gasful.pc = EvmYul.UInt256.ofNat pc) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps gasful)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) openState)
      [] := by
  rw [x_invalid_instruction_after_gas_checks
    (fuel := fuel) (validJumps := validJumps) (state := gasful)
    hGas hInvalid]
  have hOne :=
    raw_invalid_instruction_executes_at
      (bytes := bytes) (pc := pc) (state := openState) hDecode (by
        rw [← hRel.pc_eq]
        exact hPc)
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_error_add_executes
      (extra := fuel) hOne
  apply RunRefinesOpen.completed
  · simpa [Nat.add_comm] using hExec
  · exact DoneRel.sameError

/-- Parent-frame states reached by successful, non-halting concrete EVM
steps. CALL/CREATE remain ordinary parent transitions here; their child
execution and returned gas are already contained in the actual `EVM.step`
result and the response relations used by the one-step bridge. -/
inductive FrameReachable
    (validJumps : Array Word) (initial : EVMState) : EVMState → Prop where
  | initial : FrameReachable validJumps initial initial
  | next {current next : EVMState} {stepFuel : Nat}
      (reachable : FrameReachable validJumps initial current)
      (hPrefix : XSstoreStipendChecksPass validJumps current)
      (step :
        EvmYul.EVM.step stepFuel (dynamicGasCostAt current)
          (some
            ((EvmYul.EVM.decode current.executionEnv.code current.pc).getD
              (EvmYul.Operation.STOP, none)))
          (afterMemoryChargeAt current) = .ok next)
      (continues : haltOutputAt next (decodedOperationAt current) = none) :
      FrameReachable validJumps initial next

def FrameCodeInvariant
    (bytes : ByteArray) (validJumps : Array Word) (initial : EVMState) : Prop :=
  ∀ state, FrameReachable validJumps initial state → FrameCodeAt bytes state

/-- One recursive EVM frame step, parameterized only by the continuation
theorem for any related concrete/open successor. This is the remaining local
dispatcher boundary; no responder, registry, or transaction finalizer appears
in it. -/
def OneStepRefinement
    (bytes : ByteArray) (validJumps : Array Word) (initial : EVMState) : Prop :=
  ∀ (fuel : Nat) (gasful openState : EVMState),
    FrameReachable validJumps initial gasful →
    OpenStateRel gasful openState →
    (∀ gasfulNext openNext,
      FrameReachable validJumps initial gasfulNext →
      OpenStateRel gasfulNext openNext →
      ∃ transcript,
        RunRefinesOpen
          (EvmYul.EVM.X fuel validJumps gasfulNext)
          (Compact.InteractionSemantics.openRunNResult
            bytes fuel openNext)
          transcript) →
    ∃ transcript,
      RunRefinesOpen
        (EvmYul.EVM.X (fuel + 1) validJumps gasful)
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1) openState)
        transcript

/-- The undispatched local obligation after concrete memory/dynamic gas checks
and opcode validity have succeeded. Keeping this boundary explicit allows the
recursive theorem to discharge OOG and `INVALID` without assuming either away,
while the remaining stack/jump/static/success cases are proved independently. -/
def PostOpcodeRefinement
    (bytes : ByteArray) (validJumps : Array Word) (initial : EVMState) : Prop :=
  ∀ (fuel : Nat) (gasful openState : EVMState),
    FrameReachable validJumps initial gasful →
    OpenStateRel gasful openState →
    XGasChecksPass gasful →
    EvmYul.EVM.δ (decodedOperationAt gasful) ≠ none →
    CurrentInstruction bytes gasful openState →
    (∀ gasfulNext openNext,
      FrameReachable validJumps initial gasfulNext →
      OpenStateRel gasfulNext openNext →
      ∃ transcript,
        RunRefinesOpen
          (EvmYul.EVM.X fuel validJumps gasfulNext)
          (Compact.InteractionSemantics.openRunNResult
            bytes fuel openNext)
          transcript) →
    ∃ transcript,
      RunRefinesOpen
        (EvmYul.EVM.X (fuel + 1) validJumps gasful)
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1) openState)
        transcript

theorem oneStepRefinement_of_postOpcode
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (hCode : FrameCodeInvariant bytes validJumps initial)
    (hPost : PostOpcodeRefinement bytes validJumps initial) :
    OneStepRefinement bytes validJumps initial := by
  intro fuel gasful openState hReach hRel hCont
  obtain ⟨current⟩ :=
    currentInstruction_of_frameCodeAt (hCode gasful hReach) hRel
  by_cases hMemoryGas :
      gasful.gasAvailable.toNat < memoryExpansionCostAt gasful
  · exact ⟨[], runRefinesOpen_outOfGas_before_memory_charge hMemoryGas⟩
  by_cases hDynamicGas :
      (afterMemoryChargeAt gasful).gasAvailable.toNat <
        dynamicGasCostAt gasful
  · exact ⟨[], runRefinesOpen_outOfGas_before_dynamic_charge
      hMemoryGas hDynamicGas⟩
  let hGas : XGasChecksPass gasful := ⟨hMemoryGas, hDynamicGas⟩
  by_cases hInvalid : EvmYul.EVM.δ (decodedOperationAt gasful) = none
  · have hInstr := current.instr_eq_invalid_of_delta_none hInvalid
    have hDecode :
        Compact.decodeAt bytes current.pc (.prim .invalid) := by
      rw [← hInstr]
      exact current.decode
    have hPc : gasful.pc = EvmYul.UInt256.ofNat current.pc := by
      exact hRel.pc_eq.trans current.open_pc
    exact ⟨[], runRefinesOpen_invalid_instruction_rel
      hRel hGas hInvalid hDecode hPc⟩
  · exact hPost fuel gasful openState hReach hRel hGas hInvalid current hCont

/-- Generic fuel recursion once the checked local one-step dispatcher is
available. The theorem returns the exact open transcript selected by actual
GAS/MSIZE values and concrete CALL/CREATE child results. -/
theorem runRefinesOpen_recursive_of_oneStep
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (hStep : OneStepRefinement bytes validJumps initial)
    (fuel : Nat) {gasful openState : EVMState}
    (hReach : FrameReachable validJumps initial gasful)
    (hRel : OpenStateRel gasful openState) :
    ∃ transcript,
      RunRefinesOpen
        (EvmYul.EVM.X fuel validJumps gasful)
        (Compact.InteractionSemantics.openRunNResult bytes fuel openState)
        transcript := by
  induction fuel generalizing gasful openState with
  | zero =>
      exact ⟨[], runRefinesOpen_zero⟩
  | succ fuel ih =>
      apply hStep fuel gasful openState hReach hRel
      intro gasfulNext openNext hReachNext hRelNext
      exact ih hReachNext hRelNext

/-- Recursive frame bridge with OOG and invalid-opcode behavior already
discharged. The remaining premise begins at an opcode-valid charged frame and
is independent of any closed-world responder or transaction finalization. -/
theorem runRefinesOpen_recursive_of_postOpcode
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (hCode : FrameCodeInvariant bytes validJumps initial)
    (hPost : PostOpcodeRefinement bytes validJumps initial)
    (fuel : Nat) {gasful openState : EVMState}
    (hReach : FrameReachable validJumps initial gasful)
    (hRel : OpenStateRel gasful openState) :
    ∃ transcript,
      RunRefinesOpen
        (EvmYul.EVM.X fuel validJumps gasful)
        (Compact.InteractionSemantics.openRunNResult bytes fuel openState)
        transcript := by
  exact runRefinesOpen_recursive_of_oneStep
    (oneStepRefinement_of_postOpcode hCode hPost)
    fuel hReach hRel

end EvmCompiler.Assembly.GasfulBridge
