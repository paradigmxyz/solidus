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

theorem compact_instr_eq_returndatacopy_of_decoded
    {instr : Compact.Instr}
    {decoded : EvmYul.Operation .EVM × Option (Word × Nat)}
    (hValid : instr.Valid)
    (hDecoded : instr.decoded? = some decoded)
    (hOp : decoded.1 = EvmYul.Operation.RETURNDATACOPY) :
    instr = .prim .returndatacopy := by
  cases instr with
  | push width value =>
      simp [Compact.Instr.Valid] at hValid
      have hPositive := hValid.1
      have hWidth := hValid.2.1
      interval_cases width <;>
        simp [Compact.Instr.decoded?, Compact.pushOp?] at hDecoded <;>
        subst decoded <;> simp at hOp
  | jump =>
      simp [Compact.Instr.decoded?] at hDecoded
      subst decoded
      simp at hOp
  | jumpi =>
      simp [Compact.Instr.decoded?] at hDecoded
      subst decoded
      simp at hOp
  | jumpdest =>
      simp [Compact.Instr.decoded?] at hDecoded
      subst decoded
      simp at hOp
  | prim op =>
      cases op <;>
        simp [Compact.Instr.decoded?, PrimOp.toEVM] at hDecoded <;>
        subst decoded <;> simp at hOp ⊢

theorem compact_instr_eq_prim_of_decoded
    {instr : Compact.Instr} {op : PrimOp}
    {decoded : EvmYul.Operation .EVM × Option (Word × Nat)}
    (hValid : instr.Valid)
    (hDecoded : instr.decoded? = some decoded)
    (hOp : decoded.1 = op.toEVM) :
    instr = .prim op := by
  cases instr with
  | push width value =>
      simp [Compact.Instr.Valid] at hValid
      have hPositive := hValid.1
      have hWidth := hValid.2.1
      interval_cases width <;>
        simp [Compact.Instr.decoded?, Compact.pushOp?] at hDecoded <;>
        subst decoded <;>
        have h := congrArg PrimOp.ofEVM? hOp <;>
        rw [PrimOp.ofEVM?_toEVM] at h <;>
        change none = some op at h <;> cases h
  | jump =>
      simp [Compact.Instr.decoded?] at hDecoded
      subst decoded
      have h := congrArg PrimOp.ofEVM? hOp
      rw [PrimOp.ofEVM?_toEVM] at h
      change none = some op at h
      cases h
  | jumpi =>
      simp [Compact.Instr.decoded?] at hDecoded
      subst decoded
      have h := congrArg PrimOp.ofEVM? hOp
      rw [PrimOp.ofEVM?_toEVM] at h
      change none = some op at h
      cases h
  | jumpdest =>
      simp [Compact.Instr.decoded?] at hDecoded
      subst decoded
      have h := congrArg PrimOp.ofEVM? hOp
      rw [PrimOp.ofEVM?_toEVM] at h
      change none = some op at h
      cases h
  | prim currentOp =>
      simp [Compact.Instr.decoded?] at hDecoded
      subst decoded
      have h := congrArg PrimOp.ofEVM? hOp
      simp [PrimOp.ofEVM?_toEVM] at h
      subst currentOp
      rfl

theorem CurrentInstruction.instr_eq_invalid_of_delta_none
    {bytes : ByteArray} {gasful openState : EVMState}
    (current : CurrentInstruction bytes gasful openState)
    (hInvalid : EvmYul.EVM.δ (decodedOperationAt gasful) = none) :
    current.instr = .prim .invalid := by
  apply compact_instr_eq_invalid_of_decoded current.valid current.instr_decoded
  apply operation_eq_invalid_of_delta_none
  simpa [current.decodedOperation] using hInvalid

theorem CurrentInstruction.instr_eq_returndatacopy
    {bytes : ByteArray} {gasful openState : EVMState}
    (current : CurrentInstruction bytes gasful openState)
    (hOp : decodedOperationAt gasful = EvmYul.Operation.RETURNDATACOPY) :
    current.instr = .prim .returndatacopy := by
  apply compact_instr_eq_returndatacopy_of_decoded
    current.valid current.instr_decoded
  simpa [current.decodedOperation] using hOp

theorem CurrentInstruction.instr_eq_prim
    {bytes : ByteArray} {gasful openState : EVMState}
    (current : CurrentInstruction bytes gasful openState)
    {op : PrimOp} (hOp : decodedOperationAt gasful = op.toEVM) :
    current.instr = .prim op := by
  apply compact_instr_eq_prim_of_decoded current.valid current.instr_decoded
  simpa [current.decodedOperation] using hOp

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

theorem raw_continuing_prim_stack_short_executes_at
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    {op : PrimOp} {step : PrimStep}
    (hStep : op.continuingStep? = some step)
    (hShort : state.stack.length < (EvmYul.EVM.δ op.toEVM).getD 0)
    (hDecode : Compact.decodeAt bytes pc (.prim op))
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    ∃ err,
      err ≠ EvmYul.EVM.ExecutionException.OutOfFuel ∧
      Interaction.Executes
        (Compact.InteractionSemantics.openRunNResult bytes 1 state)
        [] (.error err) := by
  have hMsize : op ≠ .msize := by
    intro hOp
    subst op
    simp [PrimOp.toEVM, EvmYul.EVM.δ] at hShort
  by_cases hSensitive : continuingPrimStaticSensitive op
  · by_cases hPerm : state.executionEnv.perm = false
    · let hPrim := continuingPrim_step_staticModeViolation_of_static
        hStep hSensitive hPerm
      refine ⟨EvmYul.EVM.ExecutionException.StaticModeViolation, ?_⟩
      constructor
      · intro h
        cases h
      · apply raw_prim_error_executes_at hDecode hPc
        rw [Assembly.InteractionSemantics.PrimOp.openStep_closed
          (Assembly.InteractionSemantics.PrimOp.externalKind_none_of_continuingStep
            hStep)
          (continuingStep_not_gas hStep) hMsize]
        simp [hPrim]
    · have hPermTrue : state.executionEnv.perm = true := by
        cases h : state.executionEnv.perm <;> simp_all
      have hStaticPermits : continuingPrimStaticPermits state op :=
        fun _ => hPermTrue
      let hPrim := continuingPrim_step_stackUnderflow_of_short
        hStep hStaticPermits hShort
      refine ⟨EvmYul.EVM.ExecutionException.StackUnderflow, ?_⟩
      constructor
      · intro h
        cases h
      · apply raw_prim_error_executes_at hDecode hPc
        rw [Assembly.InteractionSemantics.PrimOp.openStep_closed
          (Assembly.InteractionSemantics.PrimOp.externalKind_none_of_continuingStep
            hStep)
          (continuingStep_not_gas hStep) hMsize]
        simp [hPrim]
  · have hStaticPermits : continuingPrimStaticPermits state op := by
      intro h
      exact False.elim (hSensitive h)
    let hPrim := continuingPrim_step_stackUnderflow_of_short
      hStep hStaticPermits hShort
    refine ⟨EvmYul.EVM.ExecutionException.StackUnderflow, ?_⟩
    constructor
    · intro h
      cases h
    · apply raw_prim_error_executes_at hDecode hPc
      rw [Assembly.InteractionSemantics.PrimOp.openStep_closed
        (Assembly.InteractionSemantics.PrimOp.externalKind_none_of_continuingStep
          hStep)
        (continuingStep_not_gas hStep) hMsize]
      simp [hPrim]

theorem raw_noncontinuing_prim_stack_short_executes_at
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    {op : PrimOp}
    (hNone : op.continuingStep? = none)
    (hShort : state.stack.length < (EvmYul.EVM.δ op.toEVM).getD 0)
    (hDecode : Compact.decodeAt bytes pc (.prim op))
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    ∃ err,
      err ≠ EvmYul.EVM.ExecutionException.OutOfFuel ∧
      Interaction.Executes
        (Compact.InteractionSemantics.openRunNResult bytes 1 state)
        [] (.error err) := by
  cases op <;> simp [PrimOp.continuingStep?] at hNone
  all_goals simp [PrimOp.toEVM, EvmYul.EVM.δ] at hShort
  case create =>
    have hPop := stack_pop3_none_of_length_lt_three hShort
    refine ⟨EvmYul.EVM.ExecutionException.StackUnderflow, ?_⟩
    constructor
    · intro h
      cases h
    · apply raw_prim_error_executes_at hDecode hPc
      simp [Assembly.InteractionSemantics.PrimOp.openStep,
        Assembly.InteractionSemantics.PrimOp.createStep,
        PrimOp.toEVM, Simulation.ExternalKind.ofEVMOperation?,
        Simulation.CallKind.ofEVMOperation?,
        Simulation.CreateKind.ofEVMOperation?,
        Simulation.CreateKind.evmOperands?, hPop]
  case create2 =>
    have hPop := stack_pop4_none_of_length_lt_four hShort
    refine ⟨EvmYul.EVM.ExecutionException.StackUnderflow, ?_⟩
    constructor
    · intro h
      cases h
    · apply raw_prim_error_executes_at hDecode hPc
      simp [Assembly.InteractionSemantics.PrimOp.openStep,
        Assembly.InteractionSemantics.PrimOp.createStep,
        PrimOp.toEVM, Simulation.ExternalKind.ofEVMOperation?,
        Simulation.CallKind.ofEVMOperation?,
        Simulation.CreateKind.ofEVMOperation?,
        Simulation.CreateKind.evmOperands?, hPop]
  case call =>
    have hPop := stack_pop7_none_of_length_lt_seven hShort
    refine ⟨EvmYul.EVM.ExecutionException.StackUnderflow, ?_⟩
    constructor
    · intro h
      cases h
    · apply raw_prim_error_executes_at hDecode hPc
      simp [Assembly.InteractionSemantics.PrimOp.openStep,
        Assembly.InteractionSemantics.PrimOp.callStep,
        PrimOp.toEVM, Simulation.ExternalKind.ofEVMOperation?,
        Simulation.CallKind.ofEVMOperation?,
        Simulation.CallKind.evmOperands?, hPop]
  case callcode =>
    have hPop := stack_pop7_none_of_length_lt_seven hShort
    refine ⟨EvmYul.EVM.ExecutionException.StackUnderflow, ?_⟩
    constructor
    · intro h
      cases h
    · apply raw_prim_error_executes_at hDecode hPc
      simp [Assembly.InteractionSemantics.PrimOp.openStep,
        Assembly.InteractionSemantics.PrimOp.callStep,
        PrimOp.toEVM, Simulation.ExternalKind.ofEVMOperation?,
        Simulation.CallKind.ofEVMOperation?,
        Simulation.CallKind.evmOperands?, hPop]
  case delegatecall =>
    have hPop := stack_pop6_none_of_length_lt_six hShort
    refine ⟨EvmYul.EVM.ExecutionException.StackUnderflow, ?_⟩
    constructor
    · intro h
      cases h
    · apply raw_prim_error_executes_at hDecode hPc
      simp [Assembly.InteractionSemantics.PrimOp.openStep,
        Assembly.InteractionSemantics.PrimOp.callStep,
        PrimOp.toEVM, Simulation.ExternalKind.ofEVMOperation?,
        Simulation.CallKind.ofEVMOperation?,
        Simulation.CallKind.evmOperands?, hPop]
  case staticcall =>
    have hPop := stack_pop6_none_of_length_lt_six hShort
    refine ⟨EvmYul.EVM.ExecutionException.StackUnderflow, ?_⟩
    constructor
    · intro h
      cases h
    · apply raw_prim_error_executes_at hDecode hPc
      simp [Assembly.InteractionSemantics.PrimOp.openStep,
        Assembly.InteractionSemantics.PrimOp.callStep,
        PrimOp.toEVM, Simulation.ExternalKind.ofEVMOperation?,
        Simulation.CallKind.ofEVMOperation?,
        Simulation.CallKind.evmOperands?, hPop]
  case «return» =>
    have hPop := stack_pop2_none_of_length_lt_two hShort
    have hPrim :
        PrimOp.return.step state =
          .error EvmYul.EVM.ExecutionException.StackUnderflow := by
      change EvmYul.EVM.binaryMachineStateOp EvmYul.MachineState.evmReturn
        state = .error EvmYul.EVM.ExecutionException.StackUnderflow
      simp [EvmYul.EVM.binaryMachineStateOp, hPop]
    refine ⟨EvmYul.EVM.ExecutionException.StackUnderflow, ?_⟩
    constructor
    · intro h
      cases h
    · apply raw_prim_error_executes_at hDecode hPc
      simp [Assembly.InteractionSemantics.PrimOp.openStep,
        PrimOp.toEVM, Simulation.ExternalKind.ofEVMOperation?,
        Simulation.CallKind.ofEVMOperation?,
        Simulation.CreateKind.ofEVMOperation?, hPrim]
  case revert =>
    have hPop := stack_pop2_none_of_length_lt_two hShort
    have hPrim :
        PrimOp.revert.step state =
          .error EvmYul.EVM.ExecutionException.StackUnderflow := by
      change EvmYul.EVM.binaryMachineStateOp EvmYul.MachineState.evmRevert
        state = .error EvmYul.EVM.ExecutionException.StackUnderflow
      simp [EvmYul.EVM.binaryMachineStateOp, hPop]
    refine ⟨EvmYul.EVM.ExecutionException.StackUnderflow, ?_⟩
    constructor
    · intro h
      cases h
    · apply raw_prim_error_executes_at hDecode hPc
      simp [Assembly.InteractionSemantics.PrimOp.openStep,
        PrimOp.toEVM, Simulation.ExternalKind.ofEVMOperation?,
        Simulation.CallKind.ofEVMOperation?,
        Simulation.CreateKind.ofEVMOperation?, hPrim]
  case selfdestruct =>
    have hPop : state.stack.pop = none := by
      rw [hShort]
      rfl
    cases hPerm : state.executionEnv.perm
    · refine ⟨EvmYul.EVM.ExecutionException.StaticModeViolation, ?_⟩
      constructor
      · intro h
        cases h
      · apply raw_prim_error_executes_at hDecode hPc
        simp [Assembly.InteractionSemantics.PrimOp.openStep,
          PrimOp.toEVM, Simulation.ExternalKind.ofEVMOperation?,
          Simulation.CallKind.ofEVMOperation?,
          Simulation.CreateKind.ofEVMOperation?,
          PrimOp.step_selfdestruct_of_static _ hPerm]
    · refine ⟨EvmYul.EVM.ExecutionException.StackUnderflow, ?_⟩
      constructor
      · intro h
        cases h
      · have hPrim :
            PrimOp.selfdestruct.step state =
              .error EvmYul.EVM.ExecutionException.StackUnderflow := by
          rw [PrimOp.step_selfdestruct_of_permitted _ hPerm]
          exact evm_step_selfdestruct_stackUnderflow_of_pop_none state hPop
        apply raw_prim_error_executes_at hDecode hPc
        simp [Assembly.InteractionSemantics.PrimOp.openStep,
          PrimOp.toEVM, Simulation.ExternalKind.ofEVMOperation?,
          Simulation.CallKind.ofEVMOperation?,
          Simulation.CreateKind.ofEVMOperation?, hPrim]

theorem raw_jump_stack_short_executes_at
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hShort : state.stack.length < 1)
    (hDecode : Compact.decodeAt bytes pc .jump)
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult bytes 1 state)
      [] (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
  have hPop := stack_pop_none_of_length_lt_one hShort
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

theorem raw_jumpi_stack_short_executes_at
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hShort : state.stack.length < 2)
    (hDecode : Compact.decodeAt bytes pc .jumpi)
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult bytes 1 state)
      [] (.error EvmYul.EVM.ExecutionException.StackUnderflow) := by
  have hPop := stack_pop2_none_of_length_lt_two hShort
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

theorem raw_returndatacopy_invalid_executes_at
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hEnough : 3 ≤ state.stack.length)
    (hBounds :
      state.returnData.size <
        (state.stack[1]?.getD (EvmYul.UInt256.ofNat 0)).toNat +
          (state.stack[2]?.getD (EvmYul.UInt256.ofNat 0)).toNat)
    (hDecode : Compact.decodeAt bytes pc (.prim .returndatacopy))
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult bytes 1 state)
      [] (.error EvmYul.EVM.ExecutionException.InvalidMemoryAccess) := by
  rcases exists_pop3_of_three_le (α := Word) hEnough with
    ⟨rest, μ₀, μ₁, μ₂, hPop⟩
  have hIdx := stack_get?_of_pop3 hPop
  have hBounds' : state.returnData.size < μ₁.toNat + μ₂.toNat := by
    simpa [hIdx.1, hIdx.2] using hBounds
  have hPrim :
      PrimOp.returndatacopy.step state =
        .error EvmYul.EVM.ExecutionException.InvalidMemoryAccess := by
    simp [PrimOp.step, PrimOp.continuingStep?, PrimStep.run,
      hPop, hBounds']
  apply raw_prim_error_executes_at hDecode hPc
  rw [Assembly.InteractionSemantics.PrimOp.openStep_closed
    (Assembly.InteractionSemantics.PrimOp.externalKind_none_of_continuingStep
      (op := PrimOp.returndatacopy) (step := PrimStep.returndatacopy) rfl)
    (by intro h; cases h) (by intro h; cases h)]
  simp [hPrim]

theorem CurrentInstruction.open_stack_short_executes
    {bytes : ByteArray} {gasful openState : EVMState}
    (current : CurrentInstruction bytes gasful openState)
    (hRel : OpenStateRel gasful openState)
    (hShort :
      gasful.stack.length <
        (EvmYul.EVM.δ (decodedOperationAt gasful)).getD 0) :
    ∃ err,
      err ≠ EvmYul.EVM.ExecutionException.OutOfFuel ∧
      Interaction.Executes
        (Compact.InteractionSemantics.openRunNResult bytes 1 openState)
        [] (.error err) := by
  have hOpenShort :
      openState.stack.length <
        (EvmYul.EVM.δ current.decoded.1).getD 0 := by
    rw [← current.decodedOperation]
    simpa [hRel.stack_eq] using hShort
  cases hInstr : current.instr with
  | push width value =>
      have hValid : Compact.FitsWidth width value.toNat := by
        simpa [hInstr, Compact.Instr.Valid] using current.valid
      have hDecoded := current.instr_decoded
      rw [hInstr] at hDecoded
      have hPositive := hValid.1
      have hWidth := hValid.2.1
      interval_cases width <;>
        simp [Compact.Instr.decoded?, Compact.pushOp?] at hDecoded <;>
        rw [← hDecoded] at hOpenShort <;>
        simp [EvmYul.EVM.δ] at hOpenShort
  | jump =>
      have hDecoded := current.instr_decoded
      rw [hInstr] at hDecoded
      simp [Compact.Instr.decoded?] at hDecoded
      rw [← hDecoded] at hOpenShort
      simp [EvmYul.EVM.δ] at hOpenShort
      have hDecode : Compact.decodeAt bytes current.pc .jump := by
        rw [← hInstr]
        exact current.decode
      refine ⟨EvmYul.EVM.ExecutionException.StackUnderflow, ?_⟩
      constructor
      · intro h
        cases h
      · apply raw_jump_stack_short_executes_at
          (hDecode := hDecode) (hPc := current.open_pc)
        simp [hOpenShort]
  | jumpi =>
      have hDecoded := current.instr_decoded
      rw [hInstr] at hDecoded
      simp [Compact.Instr.decoded?] at hDecoded
      rw [← hDecoded] at hOpenShort
      simp [EvmYul.EVM.δ] at hOpenShort
      have hDecode : Compact.decodeAt bytes current.pc .jumpi := by
        rw [← hInstr]
        exact current.decode
      refine ⟨EvmYul.EVM.ExecutionException.StackUnderflow, ?_⟩
      constructor
      · intro h
        cases h
      · exact raw_jumpi_stack_short_executes_at
          hOpenShort hDecode current.open_pc
  | jumpdest =>
      have hDecoded := current.instr_decoded
      rw [hInstr] at hDecoded
      simp [Compact.Instr.decoded?] at hDecoded
      rw [← hDecoded] at hOpenShort
      simp [EvmYul.EVM.δ] at hOpenShort
  | prim op =>
      have hDecoded := current.instr_decoded
      rw [hInstr] at hDecoded
      simp [Compact.Instr.decoded?] at hDecoded
      rw [← hDecoded] at hOpenShort
      have hDecode : Compact.decodeAt bytes current.pc (.prim op) := by
        rw [← hInstr]
        exact current.decode
      cases hStep : op.continuingStep? with
      | none =>
          exact raw_noncontinuing_prim_stack_short_executes_at
            hStep hOpenShort hDecode current.open_pc
      | some step =>
          exact raw_continuing_prim_stack_short_executes_at
            hStep hOpenShort hDecode current.open_pc

theorem runRefinesOpen_stackUnderflow_rel
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {gasful openState : EVMState}
    (current : CurrentInstruction bytes gasful openState)
    (hRel : OpenStateRel gasful openState)
    (hGas : XGasChecksPass gasful)
    (hOpcodeValid : EvmYul.EVM.δ (decodedOperationAt gasful) ≠ none)
    (hShort :
      gasful.stack.length <
        (EvmYul.EVM.δ (decodedOperationAt gasful)).getD 0) :
    ∃ transcript,
      RunRefinesOpen
        (EvmYul.EVM.X (fuel + 1) validJumps gasful)
        (Compact.InteractionSemantics.openRunNResult
          bytes (fuel + 1) openState)
        transcript := by
  obtain ⟨openErr, hOpenRuntime, hOne⟩ :=
    current.open_stack_short_executes hRel hShort
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_error_add_executes
      (extra := fuel) hOne
  refine ⟨[], ?_⟩
  apply RunRefinesOpen.exceptionalFrame
    (gasErr := EvmYul.EVM.ExecutionException.StackUnderflow)
    (openErr := openErr)
  · intro h
    cases h
  · exact hOpenRuntime
  · exact x_stack_underflow_after_gas_opcode_check
      (fuel := fuel) (validJumps := validJumps)
      hGas hOpcodeValid hShort
  · simpa [Nat.add_comm] using hExec

theorem runRefinesOpen_invalid_returndatacopy_rel
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {gasful openState : EVMState}
    (current : CurrentInstruction bytes gasful openState)
    (hRel : OpenStateRel gasful openState)
    (hPrefix : XJumpChecksPass validJumps gasful)
    (hInvalid : invalidReturnDataCopyAt gasful) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps gasful)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) openState)
      [] := by
  have hOp := hInvalid.1
  have hNotShort : ¬ gasful.stack.length < 3 := by
    simpa [hOp, EvmYul.EVM.δ] using hPrefix.stack.stackEnough
  have hEnough : 3 ≤ openState.stack.length := by
    have : 3 ≤ gasful.stack.length := by omega
    simpa [hRel.stack_eq] using this
  have hBounds :
      openState.returnData.size <
        (openState.stack[1]?.getD (EvmYul.UInt256.ofNat 0)).toNat +
          (openState.stack[2]?.getD (EvmYul.UInt256.ofNat 0)).toNat := by
    have hReturn := hRel.machineDataRel.returnData
    simpa [hRel.stack_eq, hReturn] using hInvalid.2
  have hInstr := current.instr_eq_returndatacopy hOp
  have hDecode :
      Compact.decodeAt bytes current.pc (.prim .returndatacopy) := by
    rw [← hInstr]
    exact current.decode
  rw [x_invalid_returndatacopy_after_jump_checks
    (fuel := fuel) (validJumps := validJumps)
    hPrefix hInvalid]
  have hOne := raw_returndatacopy_invalid_executes_at
    hEnough hBounds hDecode current.open_pc
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

/-- Remaining local obligation after gas, opcode validity, and stack arity all
pass. In particular CALL/CREATE operand underflow has already failed before an
external request, and static/underflow check-order differences have already
been collapsed only at the exceptional-frame outcome boundary. -/
def PostStackRefinement
    (bytes : ByteArray) (validJumps : Array Word) (initial : EVMState) : Prop :=
  ∀ (fuel : Nat) (gasful openState : EVMState),
    FrameReachable validJumps initial gasful →
    OpenStateRel gasful openState →
    XOpcodeStackChecksPass gasful →
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

def PostJumpRefinement
    (bytes : ByteArray) (validJumps : Array Word) (initial : EVMState) : Prop :=
  ∀ (fuel : Nat) (gasful openState : EVMState),
    FrameReachable validJumps initial gasful →
    OpenStateRel gasful openState →
    XJumpChecksPass validJumps gasful →
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

def PostMemoryAccessRefinement
    (bytes : ByteArray) (validJumps : Array Word) (initial : EVMState) : Prop :=
  ∀ (fuel : Nat) (gasful openState : EVMState),
    FrameReachable validJumps initial gasful →
    OpenStateRel gasful openState →
    XMemoryAccessChecksPass validJumps gasful →
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

def PostStackLimitRefinement
    (bytes : ByteArray) (validJumps : Array Word) (initial : EVMState) : Prop :=
  ∀ (fuel : Nat) (gasful openState : EVMState),
    FrameReachable validJumps initial gasful →
    OpenStateRel gasful openState →
    XStackLimitChecksPass validJumps gasful →
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

theorem postJumpRefinement_of_postMemoryAccess
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (hPost : PostMemoryAccessRefinement bytes validJumps initial) :
    PostJumpRefinement bytes validJumps initial := by
  intro fuel gasful openState hReach hRel hPrefix current hCont
  by_cases hInvalid : invalidReturnDataCopyAt gasful
  · exact ⟨[], runRefinesOpen_invalid_returndatacopy_rel
      current hRel hPrefix hInvalid⟩
  · exact hPost fuel gasful openState hReach hRel
      ⟨hPrefix, hInvalid⟩ current hCont

theorem postMemoryAccessRefinement_of_postStackLimit
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (hPost : PostStackLimitRefinement bytes validJumps initial) :
    PostMemoryAccessRefinement bytes validJumps initial := by
  intro fuel gasful openState hReach hRel hPrefix current hCont
  by_cases hOverflow : stackOverflowAt gasful
  · exact ⟨[], runRefinesOpen_stackOverflow_after_memory_access_checks
      hPrefix hOverflow⟩
  · exact hPost fuel gasful openState hReach hRel
      ⟨hPrefix, hOverflow⟩ current hCont

theorem postStackRefinement_of_postJump
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (hPost : PostJumpRefinement bytes validJumps initial) :
    PostStackRefinement bytes validJumps initial := by
  intro fuel gasful openState hReach hRel hPrefix current hCont
  by_cases hBadJump : badJumpAt validJumps gasful
  · exact ⟨[], runRefinesOpen_bad_jump_destination_after_stack_check
      hPrefix hBadJump⟩
  by_cases hBadJumpi : badJumpiAt validJumps gasful
  · exact ⟨[], runRefinesOpen_bad_jumpi_destination_after_stack_check
      hPrefix hBadJumpi⟩
  · exact hPost fuel gasful openState hReach hRel
      ⟨hPrefix, hBadJump, hBadJumpi⟩ current hCont

theorem postOpcodeRefinement_of_postStack
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (hPost : PostStackRefinement bytes validJumps initial) :
    PostOpcodeRefinement bytes validJumps initial := by
  intro fuel gasful openState hReach hRel hGas hOpcodeValid current hCont
  by_cases hShort :
      gasful.stack.length <
        (EvmYul.EVM.δ (decodedOperationAt gasful)).getD 0
  · exact runRefinesOpen_stackUnderflow_rel
      current hRel hGas hOpcodeValid hShort
  · exact hPost fuel gasful openState hReach hRel
      ⟨hGas, hOpcodeValid, hShort⟩ current hCont

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

/-- Recursive frame bridge with fuel exhaustion, OOG, invalid opcode, and
stack-underflow behavior discharged. The remaining local premise starts after
the concrete `XOpcodeStackChecksPass` prefix. -/
theorem runRefinesOpen_recursive_of_postStack
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (hCode : FrameCodeInvariant bytes validJumps initial)
    (hPost : PostStackRefinement bytes validJumps initial)
    (fuel : Nat) {gasful openState : EVMState}
    (hReach : FrameReachable validJumps initial gasful)
    (hRel : OpenStateRel gasful openState) :
    ∃ transcript,
      RunRefinesOpen
        (EvmYul.EVM.X fuel validJumps gasful)
        (Compact.InteractionSemantics.openRunNResult bytes fuel openState)
        transcript := by
  exact runRefinesOpen_recursive_of_postOpcode hCode
    (postOpcodeRefinement_of_postStack hPost)
    fuel hReach hRel

/-- Recursive frame bridge after all gas/opcode/stack/jump-destination checks.
Bad destinations remain explicit concrete-only exceptional prefixes. -/
theorem runRefinesOpen_recursive_of_postJump
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (hCode : FrameCodeInvariant bytes validJumps initial)
    (hPost : PostJumpRefinement bytes validJumps initial)
    (fuel : Nat) {gasful openState : EVMState}
    (hReach : FrameReachable validJumps initial gasful)
    (hRel : OpenStateRel gasful openState) :
    ∃ transcript,
      RunRefinesOpen
        (EvmYul.EVM.X fuel validJumps gasful)
        (Compact.InteractionSemantics.openRunNResult bytes fuel openState)
        transcript := by
  exact runRefinesOpen_recursive_of_postStack hCode
    (postStackRefinement_of_postJump hPost)
    fuel hReach hRel

/-- Recursive frame bridge through memory-access and stack-limit validation.
Invalid return-data copies agree exactly; the target-only 1024-stack check is
represented as an open transcript prefix. -/
theorem runRefinesOpen_recursive_of_postStackLimit
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (hCode : FrameCodeInvariant bytes validJumps initial)
    (hPost : PostStackLimitRefinement bytes validJumps initial)
    (fuel : Nat) {gasful openState : EVMState}
    (hReach : FrameReachable validJumps initial gasful)
    (hRel : OpenStateRel gasful openState) :
    ∃ transcript,
      RunRefinesOpen
        (EvmYul.EVM.X fuel validJumps gasful)
        (Compact.InteractionSemantics.openRunNResult bytes fuel openState)
        transcript := by
  exact runRefinesOpen_recursive_of_postJump hCode
    (postJumpRefinement_of_postMemoryAccess
      (postMemoryAccessRefinement_of_postStackLimit hPost))
    fuel hReach hRel

end EvmCompiler.Assembly.GasfulBridge
