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

theorem operation_eq_create_or_create2_of_isCreate
    {op : EvmYul.Operation .EVM}
    (hCreate : EvmYul.Operation.isCreate op = true) :
    op = EvmYul.Operation.CREATE ∨ op = EvmYul.Operation.CREATE2 := by
  cases op with
  | StopArith op => cases op <;> simp [EvmYul.Operation.isCreate] at hCreate
  | CompBit op => cases op <;> simp [EvmYul.Operation.isCreate] at hCreate
  | Keccak op => cases op; simp [EvmYul.Operation.isCreate] at hCreate
  | Env op => cases op <;> simp [EvmYul.Operation.isCreate] at hCreate
  | Block op => cases op <;> simp [EvmYul.Operation.isCreate] at hCreate
  | StackMemFlow op => cases op <;> simp [EvmYul.Operation.isCreate] at hCreate
  | Push op => cases op <;> simp [EvmYul.Operation.isCreate] at hCreate
  | Dup op => cases op <;> simp [EvmYul.Operation.isCreate] at hCreate
  | Exchange op => cases op <;> simp [EvmYul.Operation.isCreate] at hCreate
  | Log op => cases op <;> simp [EvmYul.Operation.isCreate] at hCreate
  | System op =>
      cases op <;> simp [EvmYul.Operation.isCreate] at hCreate ⊢

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

theorem CurrentInstruction.decode_prim
    {bytes : ByteArray} {gasful openState : EVMState}
    (current : CurrentInstruction bytes gasful openState)
    {op : PrimOp} (hOp : decodedOperationAt gasful = op.toEVM) :
    Compact.decodeAt bytes current.pc (.prim op) := by
  rw [← current.instr_eq_prim hOp]
  exact current.decode

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

theorem raw_continuing_prim_static_executes_at
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    {op : PrimOp} {step : PrimStep}
    (hStep : op.continuingStep? = some step)
    (hSensitive : continuingPrimStaticSensitive op)
    (hPerm : state.executionEnv.perm = false)
    (hDecode : Compact.decodeAt bytes pc (.prim op))
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult bytes 1 state)
      [] (.error EvmYul.EVM.ExecutionException.StaticModeViolation) := by
  have hPrim := continuingPrim_step_staticModeViolation_of_static
    hStep hSensitive hPerm
  apply raw_prim_error_executes_at hDecode hPc
  rw [Assembly.InteractionSemantics.PrimOp.openStep_closed
    (Assembly.InteractionSemantics.PrimOp.externalKind_none_of_continuingStep
      hStep)
    (continuingStep_not_gas hStep)
    (continuingPrimStaticSensitive_not_msize hSensitive)]
  simp [hPrim]

theorem raw_create_static_executes_at
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (kind : Simulation.CreateKind)
    {rest : EvmYul.Stack Word} {operands : Simulation.CreateOperands}
    (hOperands : kind.evmOperands? state.stack = some (rest, operands))
    (hPerm : state.executionEnv.perm = false)
    (hDecode :
      Compact.decodeAt bytes pc (.prim (createPrimOp kind)))
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult bytes 1 state)
      [] (.error EvmYul.EVM.ExecutionException.StaticModeViolation) := by
  apply raw_prim_error_executes_at hDecode hPc
  cases kind <;>
    simp [createPrimOp, Assembly.InteractionSemantics.PrimOp.openStep,
      Assembly.InteractionSemantics.PrimOp.createStep,
      PrimOp.toEVM, Simulation.ExternalKind.ofEVMOperation?,
      Simulation.CallKind.ofEVMOperation?,
      Simulation.CreateKind.ofEVMOperation?,
      Simulation.ExternalFrame.ofShared, hOperands, hPerm]

theorem raw_call_static_executes_at
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    {rest : EvmYul.Stack Word} {operands : Simulation.CallOperands}
    (hOperands :
      Simulation.CallKind.evmOperands? .call state.stack =
        some (rest, operands))
    (hPerm : state.executionEnv.perm = false)
    (hValue : operands.valueArg ≠ EvmYul.UInt256.ofNat 0)
    (hDecode : Compact.decodeAt bytes pc (.prim .call))
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult bytes 1 state)
      [] (.error EvmYul.EVM.ExecutionException.StaticModeViolation) := by
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
  have hAllowed :
      Simulation.CallKind.allowedIn .call
        (Simulation.ExternalFrame.ofShared state.toSharedState)
        operands = false := by
    simp [Simulation.CallKind.allowedIn,
      Simulation.ExternalFrame.ofShared, hPerm, hValueBeq]
  apply raw_prim_error_executes_at hDecode hPc
  simp [Assembly.InteractionSemantics.PrimOp.openStep,
    Assembly.InteractionSemantics.PrimOp.callStep,
    PrimOp.toEVM, Simulation.ExternalKind.ofEVMOperation?,
    Simulation.CallKind.ofEVMOperation?, hOperands, hAllowed]

theorem raw_selfdestruct_static_executes_at
    {bytes : ByteArray} {pc : Nat} {state : EVMState}
    (hPerm : state.executionEnv.perm = false)
    (hDecode : Compact.decodeAt bytes pc (.prim .selfdestruct))
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult bytes 1 state)
      [] (.error EvmYul.EVM.ExecutionException.StaticModeViolation) := by
  apply raw_prim_error_executes_at hDecode hPc
  simp [Assembly.InteractionSemantics.PrimOp.openStep,
    PrimOp.toEVM, Simulation.ExternalKind.ofEVMOperation?,
    Simulation.CallKind.ofEVMOperation?,
    Simulation.CreateKind.ofEVMOperation?,
    PrimOp.step_selfdestruct_of_static _ hPerm]

theorem CurrentInstruction.open_static_violation_executes
    {bytes : ByteArray} {validJumps : Array Word}
    {gasful openState : EVMState}
    (current : CurrentInstruction bytes gasful openState)
    (hRel : OpenStateRel gasful openState)
    (hPrefix : XStackLimitChecksPass validJumps gasful)
    (hStatic : staticModeViolationAt gasful) :
    Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult bytes 1 openState)
      [] (.error EvmYul.EVM.ExecutionException.StaticModeViolation) := by
  have hPerm : openState.executionEnv.perm = false := by
    simpa [hRel.executionEnv_eq] using hStatic.1
  rcases hStatic.2 with hCreate | hCreate2 | hSstore | hSelfdestruct |
    hLog0 | hLog1 | hLog2 | hLog3 | hLog4 | hTstore | hCall
  · obtain ⟨rest, operands, hOperands⟩ :=
      create_operands_of_stackEnough hPrefix hCreate
    have hOperandsOpen :
        Simulation.CreateKind.evmOperands? .create openState.stack =
          some (rest, operands) := by
      simpa [← hRel.stack_eq] using hOperands
    apply raw_create_static_executes_at .create hOperandsOpen hPerm
    · simpa [createPrimOp] using current.decode_prim
        (by simpa [PrimOp.toEVM] using hCreate)
    · exact current.open_pc
  · obtain ⟨rest, operands, hOperands⟩ :=
      create2_operands_of_stackEnough hPrefix hCreate2
    have hOperandsOpen :
        Simulation.CreateKind.evmOperands? .create2 openState.stack =
          some (rest, operands) := by
      simpa [← hRel.stack_eq] using hOperands
    apply raw_create_static_executes_at .create2 hOperandsOpen hPerm
    · simpa [createPrimOp] using current.decode_prim
        (by simpa [PrimOp.toEVM] using hCreate2)
    · exact current.open_pc
  · apply raw_continuing_prim_static_executes_at
      (op := PrimOp.sstore) (step := PrimStep.binaryState _)
      rfl trivial hPerm
    · exact current.decode_prim
        (by simpa [PrimOp.toEVM] using hSstore)
    · exact current.open_pc
  · apply raw_selfdestruct_static_executes_at hPerm
    · exact current.decode_prim
        (by simpa [PrimOp.toEVM] using hSelfdestruct)
    · exact current.open_pc
  · apply raw_continuing_prim_static_executes_at
      (op := PrimOp.log0) (step := PrimStep.log0)
      rfl trivial hPerm
    · exact current.decode_prim
        (by simpa [PrimOp.toEVM] using hLog0)
    · exact current.open_pc
  · apply raw_continuing_prim_static_executes_at
      (op := PrimOp.log1) (step := PrimStep.log1)
      rfl trivial hPerm
    · exact current.decode_prim
        (by simpa [PrimOp.toEVM] using hLog1)
    · exact current.open_pc
  · apply raw_continuing_prim_static_executes_at
      (op := PrimOp.log2) (step := PrimStep.log2)
      rfl trivial hPerm
    · exact current.decode_prim
        (by simpa [PrimOp.toEVM] using hLog2)
    · exact current.open_pc
  · apply raw_continuing_prim_static_executes_at
      (op := PrimOp.log3) (step := PrimStep.log3)
      rfl trivial hPerm
    · exact current.decode_prim
        (by simpa [PrimOp.toEVM] using hLog3)
    · exact current.open_pc
  · apply raw_continuing_prim_static_executes_at
      (op := PrimOp.log4) (step := PrimStep.log4)
      rfl trivial hPerm
    · exact current.decode_prim
        (by simpa [PrimOp.toEVM] using hLog4)
    · exact current.open_pc
  · apply raw_continuing_prim_static_executes_at
      (op := PrimOp.tstore) (step := PrimStep.binaryState _)
      rfl trivial hPerm
    · exact current.decode_prim
        (by simpa [PrimOp.toEVM] using hTstore)
    · exact current.open_pc
  · obtain ⟨rest, operands, hOperands⟩ :=
      call_operands_of_stackEnough hPrefix hCall.1
    have hOperandsOpen :
        Simulation.CallKind.evmOperands? .call openState.stack =
          some (rest, operands) := by
      simpa [← hRel.stack_eq] using hOperands
    have hValue := call_valueArg_ne_zero_of_operands hOperands hCall.2
    apply raw_call_static_executes_at hOperandsOpen hPerm hValue
    · exact current.decode_prim
        (by simpa [PrimOp.toEVM] using hCall.1)
    · exact current.open_pc

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

theorem executionException_beq_outOfFuel_iff
    (err : EvmYul.EVM.ExecutionException) :
    (err == EvmYul.EVM.ExecutionException.OutOfFuel) = true ↔
      err = EvmYul.EVM.ExecutionException.OutOfFuel := by
  cases err <;> constructor <;> intro h <;> first | rfl | cases h

/-- Child-frame execution inside imported `EVM.Θ` collapses every runtime
exception to a failed response and propagates only structural fuel exhaustion. -/
theorem theta_error_eq_outOfFuel
    {fuel : Nat}
    {blobVersionedHashes : List ByteArray}
    {createdAccounts : Batteries.RBSet EvmYul.AccountAddress compare}
    {genesisBlockHeader : EvmYul.BlockHeader}
    {blocks : EvmYul.ProcessedBlocks}
    {accountMap sigma0 : EvmYul.AccountMap .EVM}
    {chainContext : EvmYul.EVM.ChildFrameChainContext}
    {substate : EvmYul.Substate}
    {source origin recipient : EvmYul.AccountAddress}
    {code : EvmYul.ToExecute .EVM}
    {gas gasPrice value apparentValue : Word}
    {input : ByteArray} {depth : Nat}
    {header : EvmYul.BlockHeader} {permission : Bool}
    {err : EVMException}
    (hTheta :
      EvmYul.EVM.Θ fuel blobVersionedHashes createdAccounts
        genesisBlockHeader blocks accountMap sigma0 chainContext substate
        source origin recipient code gas gasPrice value apparentValue input
        depth header permission = .error err) :
    err = .OutOfFuel := by
  cases fuel with
  | zero => simpa [EvmYul.EVM.Θ] using hTheta.symm
  | succ fuel =>
      simp only [EvmYul.EVM.Θ] at hTheta
      cases code with
      | Precompiled precompile => simp at hTheta
      | Code account =>
          simp at hTheta
          generalize hXi :
            EvmYul.EVM.Ξ fuel createdAccounts genesisBlockHeader blocks
              (EvmYul.EVM.thetaCallTransfer accountMap source recipient value)
              sigma0 chainContext gas substate
              (EvmYul.EVM.thetaCallExecutionEnv blobVersionedHashes source
                origin recipient (.Code account) gasPrice apparentValue input
                depth header permission) = xiResult at hTheta
          cases xiResult with
          | error childErr =>
              cases hBeq :
                  (childErr == EvmYul.EVM.ExecutionException.OutOfFuel) with
              | false => simp [hBeq] at hTheta
              | true =>
                  have hChild :
                      childErr = EvmYul.EVM.ExecutionException.OutOfFuel :=
                    (executionException_beq_outOfFuel_iff childErr).mp hBeq
                  subst childErr
                  simpa [hBeq] using hTheta.symm
          | ok result =>
              cases result <;> simp at hTheta

/-- Imported `EVM.call` returns a concrete parent response for child runtime
failure; only proof-fuel exhaustion can escape the CALL boundary as an error. -/
theorem evm_call_error_eq_outOfFuel
    {fuel gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {gas source recipient target value apparentValue inputOffset inputSize
      outputOffset outputSize : Word}
    {permission : Bool} {state : EVMState} {err : EVMException}
    (hCall :
      EvmYul.EVM.call fuel gasCost blobVersionedHashes gas source recipient
        target value apparentValue inputOffset inputSize outputOffset outputSize
        permission state = .error err) :
    err = .OutOfFuel := by
  cases fuel with
  | zero => simpa [EvmYul.EVM.call] using hCall.symm
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
                value gas state.accountMap state.toMachineState state.substate))
            (EvmYul.UInt256.ofNat state.executionEnv.gasPrice)
            value apparentValue
            (state.memory.readWithPadding inputOffset.toNat inputSize.toNat)
            (state.executionEnv.depth + 1) state.executionEnv.header
            permission = thetaResult at hCall
        cases thetaResult with
        | error childErr =>
            have hChild : childErr = .OutOfFuel :=
              theta_error_eq_outOfFuel hTheta
            subst childErr
            simpa using hCall.symm
        | ok result => simp at hCall
      · simp at hCall

theorem concreteCall_error_eq_outOfFuel
    {kind : CallKind} {fuel gasCost : Nat}
    {state : EVMState} {operands : CallOperands} {err : EVMException}
    (hCall : concreteCall kind fuel gasCost state operands = .error err) :
    err = .OutOfFuel := by
  cases kind <;>
    exact evm_call_error_eq_outOfFuel (by simpa [concreteCall] using hCall)

theorem evm_step_call_error_eq_outOfFuel_at
    {kind : CallKind} {fuel : Nat} {state : EVMState}
    {rest : EvmYul.Stack Word} {operands : CallOperands}
    {arg : Option (Word × Nat)} {err : EVMException}
    (hOperands : kind.evmOperands? state.stack = some (rest, operands))
    (hStep :
      EvmYul.EVM.step fuel (dynamicGasCostAt state)
        (some (kind.toEVMOperation, arg)) (afterMemoryChargeAt state) =
          .error err) :
    err = .OutOfFuel := by
  have hStack := CallKind.stack_eq_args_append_of_evmOperands hOperands
  have hStackMemory :
      (afterMemoryChargeAt state).stack = kind.args operands ++ rest := by
    simpa [afterMemoryChargeAt, chargeGas] using hStack
  rw [evm_step_call_eq_concreteCallStep kind fuel (dynamicGasCostAt state)
    (afterMemoryChargeAt state) rest operands arg hStackMemory] at hStep
  cases fuel with
  | zero => simpa [concreteCallStep] using hStep.symm
  | succ childFuel =>
      simp only [concreteCallStep] at hStep
      generalize hCall :
        concreteCall kind childFuel (dynamicGasCostAt state)
          (callInputState (afterMemoryChargeAt state)) operands = callResult
          at hStep
      cases callResult with
      | error childErr =>
          simp at hStep
          subst err
          exact concreteCall_error_eq_outOfFuel hCall
      | ok result => simp at hStep

theorem evm_step_create_positive_error_eq_outOfGas_at
    {kind : CreateKind} {fuel : Nat} {state : EVMState}
    {rest : EvmYul.Stack Word} {operands : CreateOperands}
    {arg : Option (Word × Nat)} {err : EVMException}
    (hOperands : kind.evmOperands? state.stack = some (rest, operands))
    (hStep :
      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
        (some (kind.toEVMOperation, arg)) (afterMemoryChargeAt state) =
          .error err) :
    err = .OutOfGass := by
  have hStack := CreateKind.stack_eq_args_append_of_evmOperands hOperands
  have hStackMemory :
      (afterMemoryChargeAt state).stack = kind.args operands ++ rest := by
    simpa [afterMemoryChargeAt, chargeGas] using hStack
  rw [evm_step_create_eq_concreteCreateStep kind (fuel + 1)
    (dynamicGasCostAt state) (afterMemoryChargeAt state) rest operands arg
    hStackMemory] at hStep
  simp only [concreteCreateStep] at hStep
  split at hStep
  · simpa using hStep.symm
  · simp at hStep

theorem call_operands_of_stackEnough_kind
    {validJumps : Array Word} {state : EVMState} (kind : CallKind)
    (hPrefix : XStackLimitChecksPass validJumps state)
    (hOp : decodedOperationAt state = kind.toEVMOperation) :
    ∃ rest operands,
      kind.evmOperands? state.stack = some (rest, operands) := by
  have hNotShort : ¬ state.stack.length < kind.inputArity := by
    cases kind <;>
      simpa [hOp, EvmYul.EVM.δ, CallKind.inputArity,
        CallKind.toEVMOperation] using
          hPrefix.memoryAccess.jumps.stack.stackEnough
  have hEnough : kind.inputArity ≤ state.stack.length := by omega
  cases kind with
  | call | callcode =>
      obtain ⟨rest, gas, address, value, inputOffset, inputSize,
          outputOffset, outputSize, hPop⟩ :=
        exists_pop7_of_seven_le (α := Word)
          (by simpa [CallKind.inputArity] using hEnough)
      refine ⟨rest,
        { requestedGas := gas
          address := address
          valueArg := value
          inputOffset := inputOffset
          inputSize := inputSize
          outputOffset := outputOffset
          outputSize := outputSize }, ?_⟩
      simp [CallKind.evmOperands?, hPop]
  | delegatecall | staticcall =>
      obtain ⟨rest, gas, address, inputOffset, inputSize,
          outputOffset, outputSize, hPop⟩ :=
        PrimStep.Stack.exists_pop6_of_six_le
          (by simpa [CallKind.inputArity] using hEnough)
      refine ⟨rest,
        { requestedGas := gas
          address := address
          valueArg := EvmYul.UInt256.ofNat 0
          inputOffset := inputOffset
          inputSize := inputSize
          outputOffset := outputOffset
          outputSize := outputSize }, ?_⟩
      simp [CallKind.evmOperands?, hPop]

theorem create_operands_of_stackEnough_kind
    {validJumps : Array Word} {state : EVMState} (kind : CreateKind)
    (hPrefix : XStackLimitChecksPass validJumps state)
    (hOp : decodedOperationAt state = kind.toEVMOperation) :
    ∃ rest operands,
      kind.evmOperands? state.stack = some (rest, operands) := by
  cases kind with
  | create =>
      exact create_operands_of_stackEnough
        (validJumps := validJumps) (state := state) hPrefix hOp
  | create2 =>
      exact create2_operands_of_stackEnough
        (validJumps := validJumps) (state := state) hPrefix hOp

theorem call_allowed_of_static_checks
    {validJumps : Array Word} {state : EVMState}
    {rest : EvmYul.Stack Word} {operands : CallOperands}
    (kind : CallKind)
    (hStatic : XStaticChecksPass validJumps state)
    (hOp : decodedOperationAt state = kind.toEVMOperation)
    (hOperands : kind.evmOperands? state.stack = some (rest, operands)) :
    kind.allowedIn
      (ExternalFrame.ofShared (afterDynamicChargeAt state).toSharedState)
      operands = true := by
  cases kind with
  | call =>
      cases hPerm : state.executionEnv.perm with
      | true =>
          simp [CallKind.allowedIn, ExternalFrame.ofShared,
            afterDynamicChargeAt, afterMemoryChargeAt, chargeGas, hPerm]
      | false =>
          have hStack :=
            CallKind.stack_eq_args_append_of_evmOperands hOperands
          have hAt : state.stack[2]? = some operands.valueArg := by
            simpa [CallKind.args] using
              congrArg (fun stack : EvmYul.Stack Word => stack[2]?) hStack
          have hStackZero :
              state.stack[2]? = some (EvmYul.UInt256.ofNat 0) := by
            by_contra hNe
            apply hStatic.staticOk
            exact ⟨hPerm, by
              simp [hOp, hNe, CallKind.toEVMOperation]⟩
          have hValue : operands.valueArg = EvmYul.UInt256.ofNat 0 := by
            simpa [hAt] using hStackZero
          simp [CallKind.allowedIn, ExternalFrame.ofShared,
            afterDynamicChargeAt, afterMemoryChargeAt, chargeGas,
            hPerm, hValue, EvmYul.instBEqUInt256,
            EvmYul.instBEqUInt256.beq, EvmYul.UInt256.ofNat, Id.run]
  | callcode | delegatecall | staticcall =>
      simp [CallKind.allowedIn]

theorem create_permission_of_static_checks
    {validJumps : Array Word} {state : EVMState} (kind : CreateKind)
    (hStatic : XStaticChecksPass validJumps state)
    (hOp : decodedOperationAt state = kind.toEVMOperation) :
    (ExternalFrame.ofShared
      (afterDynamicChargeAt state).toSharedState).permission = true := by
  cases hPerm : state.executionEnv.perm with
  | true =>
      simp [ExternalFrame.ofShared, afterDynamicChargeAt,
        afterMemoryChargeAt, chargeGas, hPerm]
  | false =>
      exfalso
      apply hStatic.staticOk
      exact ⟨hPerm, by
        cases kind <;> simp [hOp, CreateKind.toEVMOperation]⟩

attribute [local simp] PrimStep.idRun_eq

def PrimStepPermissionPass (step : PrimStep) (state : EVMState) : Prop :=
  match step with
  | .binaryState _ | .log0 | .log1 | .log2 | .log3 | .log4 =>
      state.executionEnv.perm = true
  | _ => True

theorem primStep_run_exists_of_checks
    {step : PrimStep} {state : EVMState}
    (hPerm : PrimStepPermissionPass step state)
    (hReturnData :
      ¬ (step = .returndatacopy ∧
        state.returnData.size <
          (state.stack[1]?.getD (EvmYul.UInt256.ofNat 0)).toNat +
            (state.stack[2]?.getD (EvmYul.UInt256.ofNat 0)).toNat))
    (hNotInvalid : step ≠ .invalid)
    (hBound : step.inputArity ≤ state.stack.length) :
    ∃ next, step.run state = .ok next := by
  unfold PrimStepPermissionPass at hPerm
  cases step with
  | bin f =>
      obtain ⟨rest, a, b, hPop⟩ :=
        PrimStep.Stack.exists_pop2_of_two_le
          (by simpa [PrimStep.inputArity] using hBound)
      simp [PrimStep.run, EvmYul.EVM.execBinOp, hPop]
  | un f =>
      obtain ⟨rest, a, hPop⟩ :=
        PrimStep.Stack.exists_pop_of_one_le
          (by simpa [PrimStep.inputArity] using hBound)
      simp [PrimStep.run, EvmYul.EVM.execUnOp, hPop]
  | tri f =>
      obtain ⟨rest, a, b, c, hPop⟩ :=
        PrimStep.Stack.exists_pop3_of_three_le
          (by simpa [PrimStep.inputArity] using hBound)
      simp [PrimStep.run, EvmYul.EVM.execTriOp, hPop]
  | executionEnv f =>
      simp [PrimStep.run, EvmYul.EVM.executionEnvOp]
  | unaryExecutionEnv f =>
      obtain ⟨rest, a, hPop⟩ :=
        PrimStep.Stack.exists_pop_of_one_le
          (by simpa [PrimStep.inputArity] using hBound)
      simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp, hPop]
  | machineState f =>
      simp [PrimStep.run, EvmYul.EVM.machineStateOp]
  | binaryMachineState f =>
      obtain ⟨rest, a, b, hPop⟩ :=
        PrimStep.Stack.exists_pop2_of_two_le
          (by simpa [PrimStep.inputArity] using hBound)
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp, hPop]
  | binaryMachineStateWithResult f =>
      obtain ⟨rest, a, b, hPop⟩ :=
        PrimStep.Stack.exists_pop2_of_two_le
          (by simpa [PrimStep.inputArity] using hBound)
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp', hPop]
  | ternaryMachineState f =>
      obtain ⟨rest, a, b, c, hPop⟩ :=
        PrimStep.Stack.exists_pop3_of_three_le
          (by simpa [PrimStep.inputArity] using hBound)
      simp [PrimStep.run, EvmYul.EVM.ternaryMachineStateOp, hPop]
  | state f =>
      simp [PrimStep.run, EvmYul.EVM.stateOp]
  | unaryState f =>
      obtain ⟨rest, a, hPop⟩ :=
        PrimStep.Stack.exists_pop_of_one_le
          (by simpa [PrimStep.inputArity] using hBound)
      simp [PrimStep.run, EvmYul.EVM.unaryStateOp, hPop]
  | binaryState f =>
      obtain ⟨rest, a, b, hPop⟩ :=
        PrimStep.Stack.exists_pop2_of_two_le
          (by simpa [PrimStep.inputArity] using hBound)
      simp [PrimStep.run, EvmYul.EVM.binaryStateOp, hPerm, hPop]
  | ternaryCopy f =>
      obtain ⟨rest, a, b, c, hPop⟩ :=
        PrimStep.Stack.exists_pop3_of_three_le
          (by simpa [PrimStep.inputArity] using hBound)
      simp [PrimStep.run, EvmYul.EVM.ternaryCopyOp, hPop]
  | quaternaryCopy f =>
      obtain ⟨rest, a, b, c, d, hPop⟩ :=
        PrimStep.Stack.exists_pop4_of_four_le
          (by simpa [PrimStep.inputArity] using hBound)
      simp [PrimStep.run, EvmYul.EVM.quaternaryCopyOp, hPop]
  | pop =>
      obtain ⟨rest, a, hPop⟩ :=
        PrimStep.Stack.exists_pop_of_one_le
          (by simpa [PrimStep.inputArity] using hBound)
      simp [PrimStep.run, hPop]
  | mload =>
      obtain ⟨rest, a, hPop⟩ :=
        PrimStep.Stack.exists_pop_of_one_le
          (by simpa [PrimStep.inputArity] using hBound)
      simp [PrimStep.run, hPop]
  | returndatacopy =>
      obtain ⟨rest, a, b, c, hPop⟩ :=
        PrimStep.Stack.exists_pop3_of_three_le
          (by simpa [PrimStep.inputArity] using hBound)
      have hIdx := stack_get?_of_pop3 hPop
      have hBounds : ¬ state.returnData.size < b.toNat + c.toNat := by
        intro hBad
        apply hReturnData
        exact ⟨rfl, by simpa [hIdx.1, hIdx.2] using hBad⟩
      simp [PrimStep.run, hPop, hBounds]
  | dup n =>
      have hTake : (state.stack.take n).length = n := by
        simp [List.length_take, Nat.min_eq_left
          (by simpa [PrimStep.inputArity] using hBound)]
      simp [PrimStep.run, EvmYul.dup, hTake]
  | swap n =>
      have hTake : (state.stack.take (n + 1)).length = n + 1 := by
        simp [List.length_take, Nat.min_eq_left
          (by simpa [PrimStep.inputArity] using hBound)]
      simp [PrimStep.run, EvmYul.swap, hTake]
  | log0 =>
      obtain ⟨rest, a, b, hPop⟩ :=
        PrimStep.Stack.exists_pop2_of_two_le
          (by simpa [PrimStep.inputArity] using hBound)
      simp [PrimStep.run, hPerm, hPop]
  | log1 =>
      obtain ⟨rest, a, b, c, hPop⟩ :=
        PrimStep.Stack.exists_pop3_of_three_le
          (by simpa [PrimStep.inputArity] using hBound)
      simp [PrimStep.run, hPerm, hPop]
  | log2 =>
      obtain ⟨rest, a, b, c, d, hPop⟩ :=
        PrimStep.Stack.exists_pop4_of_four_le
          (by simpa [PrimStep.inputArity] using hBound)
      simp [PrimStep.run, hPerm, hPop]
  | log3 =>
      obtain ⟨rest, a, b, c, d, e, hPop⟩ :=
        PrimStep.Stack.exists_pop5_of_five_le
          (by simpa [PrimStep.inputArity] using hBound)
      simp [PrimStep.run, hPerm, hPop]
  | log4 =>
      obtain ⟨rest, a, b, c, d, e, f, hPop⟩ :=
        PrimStep.Stack.exists_pop6_of_six_le
          (by simpa [PrimStep.inputArity] using hBound)
      simp [PrimStep.run, hPerm, hPop]
  | invalid => exact False.elim (hNotInvalid rfl)

theorem primStep_permission_of_continuing
    {op : PrimOp} {step : PrimStep} {state : EVMState}
    (hStep : op.continuingStep? = some step)
    (hStaticPermits : continuingPrimStaticPermits state op) :
    PrimStepPermissionPass step state := by
  unfold PrimStepPermissionPass
  cases step <;> try trivial
  all_goals
    apply hStaticPermits
    cases op <;>
      simp [PrimOp.continuingStep?, continuingPrimStaticSensitive] at hStep ⊢

theorem op_eq_returndatacopy_of_continuing_step
    {op : PrimOp} {step : PrimStep}
    (hStep : op.continuingStep? = some step)
    (hReturnStep : step = .returndatacopy) :
    op = .returndatacopy := by
  subst step
  cases op <;> simp [PrimOp.continuingStep?] at hStep ⊢

theorem positiveContinuingStep
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (stepFuel : Nat) {gasful openState : EVMState}
    (hReach : FrameReachable validJumps initial gasful)
    (hRel : OpenStateRel gasful openState)
    (hPrefix : XSstoreStipendChecksPass validJumps gasful)
    (hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt gasful) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          gasful.stack[2]?.getD (EvmYul.UInt256.ofNat 0)))
    (current : CurrentInstruction bytes gasful openState)
    {op : PrimOp} {step : PrimStep}
    (hInstr : current.instr = .prim op)
    (hStep : op.continuingStep? = some step)
    (hMsize : op ≠ .msize)
    (hCont :
      ∀ gasfulNext openNext,
        FrameReachable validJumps initial gasfulNext →
        OpenStateRel gasfulNext openNext →
        ∃ transcript,
          RunRefinesOpen
            (EvmYul.EVM.X (stepFuel + 1) validJumps gasfulNext)
            (Compact.InteractionSemantics.openRunNResult
              bytes (stepFuel + 1) openNext)
            transcript) :
    ∃ transcript,
      RunRefinesOpen
        (EvmYul.EVM.X (stepFuel + 1 + 1) validJumps gasful)
        (Compact.InteractionSemantics.openRunNResult
          bytes (stepFuel + 1 + 1) openState)
        transcript := by
  have hPair : current.decoded = (op.toEVM, none) := by
    have h := current.instr_decoded
    rw [hInstr] at h
    simpa [Compact.Instr.decoded?] using h.symm
  have hDecodedPair := current.decodedPair.trans hPair
  have hDecodedOp : decodedOperationAt gasful = op.toEVM := by
    simp [decodedOperationAt, hDecodedPair]
  have hOpcodeValid : EvmYul.EVM.δ op.toEVM ≠ none := by
    simpa [hDecodedOp] using
      hPrefix.static.stackLimit.memoryAccess.jumps.stack.opcodeValid
  have hInvalid : op ≠ .invalid := by
    intro hOp
    subst op
    apply hOpcodeValid
    simp [PrimOp.toEVM, EvmYul.EVM.δ]
  have hStepNotInvalid : step ≠ .invalid := by
    intro hInvalidStep
    subst step
    cases op <;> simp [PrimOp.continuingStep?] at hStep
    exact hInvalid rfl
  have hInput := (PrimOp.continuingStep?_delta_alpha hStep).1
  have hBoundGasful :
      (EvmYul.EVM.δ op.toEVM).getD 0 ≤ gasful.stack.length :=
    Nat.le_of_not_gt (by
      simpa [hDecodedOp] using
        hPrefix.static.stackLimit.memoryAccess.jumps.stack.stackEnough)
  have hBound :
      step.inputArity ≤ (afterEVMInstructionChargeAt gasful).stack.length := by
    simpa [← hInput, afterEVMInstructionChargeAt,
      afterMemoryChargeAt, chargeGas] using hBoundGasful
  have hStaticPermits : continuingPrimStaticPermits gasful op :=
    continuingPrimStaticPermits_of_static_check hPrefix.static hDecodedOp
  have hPerm :
      PrimStepPermissionPass step (afterEVMInstructionChargeAt gasful) := by
    have h := primStep_permission_of_continuing hStep hStaticPermits
    simpa [PrimStepPermissionPass, afterEVMInstructionChargeAt,
      afterMemoryChargeAt, chargeGas]
      using h
  have hReturnData :
      ¬ (step = .returndatacopy ∧
        (afterEVMInstructionChargeAt gasful).returnData.size <
          ((afterEVMInstructionChargeAt gasful).stack[1]?.getD
            (EvmYul.UInt256.ofNat 0)).toNat +
          ((afterEVMInstructionChargeAt gasful).stack[2]?.getD
            (EvmYul.UInt256.ofNat 0)).toNat) := by
    rintro ⟨hReturnStep, hBounds⟩
    have hOpReturn :=
      op_eq_returndatacopy_of_continuing_step hStep hReturnStep
    subst op
    apply hPrefix.static.stackLimit.memoryAccess.returnDataCopyOk
    constructor
    · exact hDecodedOp
    · simpa [afterEVMInstructionChargeAt, afterMemoryChargeAt, chargeGas]
        using hBounds
  obtain ⟨gasfulNext, hPrimRun⟩ :=
    primStep_run_exists_of_checks hPerm hReturnData hStepNotInvalid hBound
  have hPrimGasful :
      op.step (afterEVMInstructionChargeAt gasful) = .ok gasfulNext := by
    rw [PrimOp.step_eq_continuingStep_run hStep]
    exact hPrimRun
  have hGasful :
      EvmYul.EVM.step (stepFuel + 1) (dynamicGasCostAt gasful)
        (some (op.toEVM, none)) (afterMemoryChargeAt gasful) =
          .ok gasfulNext := by
    rw [evm_step_continuing_prim_after_charges
      (fuel := stepFuel) (arg := none) hStep trivial hStaticPermits]
    exact hPrimGasful
  have hCompatible : OpenCompatibleStep step :=
    (frameLocalStep_of_continuingStep
      (frameLocalPrimOp_of_continuingStep hStep hMsize hInvalid) hStep).openCompatible
  obtain ⟨openNext, hOpen, hNextRel⟩ :=
    continuingPrim_open_success_rel_of_compatible
      hStep hCompatible hRel hPrimGasful
  have hDecode : Compact.decodeAt bytes current.pc (.prim op) := by
    rw [← hInstr]
    exact current.decode
  have hFirst := raw_continuing_prim_executes_at
    hStep hMsize hDecode current.open_pc hOpen
  have hStepActual :
      EvmYul.EVM.step (stepFuel + 1) (dynamicGasCostAt gasful)
        (some
          ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt gasful) = .ok gasfulNext := by
    simpa [hDecodedPair] using hGasful
  have hHalt := haltOutputAt_none_of_continuingStep gasfulNext hStep
  have hReachNext : FrameReachable validJumps initial gasfulNext :=
    .next hReach hPrefix hStepActual (by simpa [hDecodedOp] using hHalt)
  obtain ⟨tail, hTail⟩ := hCont gasfulNext openNext hReachNext hNextRel
  refine ⟨tail, ?_⟩
  exact runRefinesOpen_running_step_rel hPrefix hCreateOk hDecodedOp
    hStepActual hHalt hFirst hTail

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

theorem runRefinesOpen_staticModeViolation_rel
    {fuel : Nat} {validJumps : Array Word}
    {bytes : ByteArray} {gasful openState : EVMState}
    (current : CurrentInstruction bytes gasful openState)
    (hRel : OpenStateRel gasful openState)
    (hPrefix : XStackLimitChecksPass validJumps gasful)
    (hStatic : staticModeViolationAt gasful) :
    RunRefinesOpen
      (EvmYul.EVM.X (fuel + 1) validJumps gasful)
      (Compact.InteractionSemantics.openRunNResult
        bytes (fuel + 1) openState)
      [] := by
  rw [x_static_mode_violation_after_stack_limit_checks
    (fuel := fuel) (validJumps := validJumps)
    hPrefix hStatic]
  have hOne := current.open_static_violation_executes
    hRel hPrefix hStatic
  have hExec :=
    Compact.InteractionSemantics.openRunNResult_error_add_executes
      (extra := fuel) hOne
  apply RunRefinesOpen.completed
  · simpa [Nat.add_comm] using hExec
  · exact DoneRel.sameError

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

def PostStaticRefinement
    (bytes : ByteArray) (validJumps : Array Word) (initial : EVMState) : Prop :=
  ∀ (fuel : Nat) (gasful openState : EVMState),
    FrameReachable validJumps initial gasful →
    OpenStateRel gasful openState →
    XStaticChecksPass validJumps gasful →
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

def PostSstoreRefinement
    (bytes : ByteArray) (validJumps : Array Word) (initial : EVMState) : Prop :=
  ∀ (fuel : Nat) (gasful openState : EVMState),
    FrameReachable validJumps initial gasful →
    OpenStateRel gasful openState →
    XSstoreStipendChecksPass validJumps gasful →
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

/-- Final local dispatcher obligation after every `EVM.X` exceptional precheck
has passed. Its implementation only has to relate the actual charged
`EVM.step` result (including CALL/CREATE responses) to the current Compact
instruction and recursive continuation. -/
def PostPrechecksRefinement
    (bytes : ByteArray) (validJumps : Array Word) (initial : EVMState) : Prop :=
  ∀ (fuel : Nat) (gasful openState : EVMState),
    FrameReachable validJumps initial gasful →
    OpenStateRel gasful openState →
    XSstoreStipendChecksPass validJumps gasful →
    (¬ (EvmYul.Operation.isCreate (decodedOperationAt gasful) = true ∧
      (EvmYul.UInt256.ofNat 49152) <
        gasful.stack[2]?.getD (EvmYul.UInt256.ofNat 0))) →
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

def PositiveStepRefinement
    (bytes : ByteArray) (validJumps : Array Word) (initial : EVMState) : Prop :=
  ∀ (stepFuel : Nat) (gasful openState : EVMState),
    FrameReachable validJumps initial gasful →
    OpenStateRel gasful openState →
    XSstoreStipendChecksPass validJumps gasful →
    (¬ (EvmYul.Operation.isCreate (decodedOperationAt gasful) = true ∧
      (EvmYul.UInt256.ofNat 49152) <
        gasful.stack[2]?.getD (EvmYul.UInt256.ofNat 0))) →
    CurrentInstruction bytes gasful openState →
    (∀ gasfulNext openNext,
      FrameReachable validJumps initial gasfulNext →
      OpenStateRel gasfulNext openNext →
      ∃ transcript,
        RunRefinesOpen
          (EvmYul.EVM.X (stepFuel + 1) validJumps gasfulNext)
          (Compact.InteractionSemantics.openRunNResult
            bytes (stepFuel + 1) openNext)
          transcript) →
    ∃ transcript,
      RunRefinesOpen
        (EvmYul.EVM.X (stepFuel + 1 + 1) validJumps gasful)
        (Compact.InteractionSemantics.openRunNResult
          bytes (stepFuel + 1 + 1) openState)
        transcript

def PositivePrimRefinement
    (bytes : ByteArray) (validJumps : Array Word) (initial : EVMState) : Prop :=
  ∀ (stepFuel : Nat) (gasful openState : EVMState),
    FrameReachable validJumps initial gasful →
    OpenStateRel gasful openState →
    XSstoreStipendChecksPass validJumps gasful →
    (¬ (EvmYul.Operation.isCreate (decodedOperationAt gasful) = true ∧
      (EvmYul.UInt256.ofNat 49152) <
        gasful.stack[2]?.getD (EvmYul.UInt256.ofNat 0))) →
    (current : CurrentInstruction bytes gasful openState) →
    (op : PrimOp) →
    current.instr = .prim op →
    (∀ gasfulNext openNext,
      FrameReachable validJumps initial gasfulNext →
      OpenStateRel gasfulNext openNext →
      ∃ transcript,
        RunRefinesOpen
          (EvmYul.EVM.X (stepFuel + 1) validJumps gasfulNext)
          (Compact.InteractionSemantics.openRunNResult
            bytes (stepFuel + 1) openNext)
          transcript) →
    ∃ transcript,
      RunRefinesOpen
        (EvmYul.EVM.X (stepFuel + 1 + 1) validJumps gasful)
        (Compact.InteractionSemantics.openRunNResult
          bytes (stepFuel + 1 + 1) openState)
        transcript

def PositiveOtherPrimRefinement
    (bytes : ByteArray) (validJumps : Array Word) (initial : EVMState) : Prop :=
  ∀ (stepFuel : Nat) (gasful openState : EVMState),
    FrameReachable validJumps initial gasful →
    OpenStateRel gasful openState →
    XSstoreStipendChecksPass validJumps gasful →
    (¬ (EvmYul.Operation.isCreate (decodedOperationAt gasful) = true ∧
      (EvmYul.UInt256.ofNat 49152) <
        gasful.stack[2]?.getD (EvmYul.UInt256.ofNat 0))) →
    (current : CurrentInstruction bytes gasful openState) →
    (op : PrimOp) →
    current.instr = .prim op →
    op ≠ .pc → op ≠ .gas → op ≠ .msize →
    (∀ gasfulNext openNext,
      FrameReachable validJumps initial gasfulNext →
      OpenStateRel gasfulNext openNext →
      ∃ transcript,
        RunRefinesOpen
          (EvmYul.EVM.X (stepFuel + 1) validJumps gasfulNext)
          (Compact.InteractionSemantics.openRunNResult
            bytes (stepFuel + 1) openNext)
          transcript) →
    ∃ transcript,
      RunRefinesOpen
        (EvmYul.EVM.X (stepFuel + 1 + 1) validJumps gasful)
        (Compact.InteractionSemantics.openRunNResult
          bytes (stepFuel + 1 + 1) openState)
        transcript

def PositiveRemainingPrimRefinement
    (bytes : ByteArray) (validJumps : Array Word) (initial : EVMState) : Prop :=
  ∀ (stepFuel : Nat) (gasful openState : EVMState),
    FrameReachable validJumps initial gasful →
    OpenStateRel gasful openState →
    XSstoreStipendChecksPass validJumps gasful →
    (¬ (EvmYul.Operation.isCreate (decodedOperationAt gasful) = true ∧
      (EvmYul.UInt256.ofNat 49152) <
        gasful.stack[2]?.getD (EvmYul.UInt256.ofNat 0))) →
    (current : CurrentInstruction bytes gasful openState) →
    (op : PrimOp) →
    current.instr = .prim op →
    op ≠ .pc → op ≠ .gas → op ≠ .msize →
    op ≠ .stop → op ≠ .return → op ≠ .revert → op ≠ .selfdestruct →
    (∀ gasfulNext openNext,
      FrameReachable validJumps initial gasfulNext →
      OpenStateRel gasfulNext openNext →
      ∃ transcript,
        RunRefinesOpen
          (EvmYul.EVM.X (stepFuel + 1) validJumps gasfulNext)
          (Compact.InteractionSemantics.openRunNResult
            bytes (stepFuel + 1) openNext)
          transcript) →
    ∃ transcript,
      RunRefinesOpen
        (EvmYul.EVM.X (stepFuel + 1 + 1) validJumps gasful)
        (Compact.InteractionSemantics.openRunNResult
          bytes (stepFuel + 1 + 1) openState)
        transcript

def PositiveExternalPrimRefinement
    (bytes : ByteArray) (validJumps : Array Word) (initial : EVMState) : Prop :=
  ∀ (stepFuel : Nat) (gasful openState : EVMState),
    FrameReachable validJumps initial gasful →
    OpenStateRel gasful openState →
    XSstoreStipendChecksPass validJumps gasful →
    (¬ (EvmYul.Operation.isCreate (decodedOperationAt gasful) = true ∧
      (EvmYul.UInt256.ofNat 49152) <
        gasful.stack[2]?.getD (EvmYul.UInt256.ofNat 0))) →
    (current : CurrentInstruction bytes gasful openState) →
    (op : PrimOp) →
    current.instr = .prim op →
    op ≠ .pc → op ≠ .gas → op ≠ .msize →
    op ≠ .stop → op ≠ .return → op ≠ .revert → op ≠ .selfdestruct →
    op.continuingStep? = none →
    (∀ gasfulNext openNext,
      FrameReachable validJumps initial gasfulNext →
      OpenStateRel gasfulNext openNext →
      ∃ transcript,
        RunRefinesOpen
          (EvmYul.EVM.X (stepFuel + 1) validJumps gasfulNext)
          (Compact.InteractionSemantics.openRunNResult
            bytes (stepFuel + 1) openNext)
          transcript) →
    ∃ transcript,
      RunRefinesOpen
        (EvmYul.EVM.X (stepFuel + 1 + 1) validJumps gasful)
        (Compact.InteractionSemantics.openRunNResult
          bytes (stepFuel + 1 + 1) openState)
        transcript

theorem primOp_external_of_no_continuing
    (op : PrimOp)
    (hValid : EvmYul.EVM.δ op.toEVM ≠ none)
    (hPc : op ≠ .pc) (hGas : op ≠ .gas) (hMsize : op ≠ .msize)
    (hStop : op ≠ .stop) (hReturn : op ≠ .return)
    (hRevert : op ≠ .revert) (hSelfdestruct : op ≠ .selfdestruct)
    (hStep : op.continuingStep? = none) :
    (∃ kind, op = callPrimOp kind) ∨
      ∃ kind, op = createPrimOp kind := by
  cases op <;>
    simp_all [PrimOp.continuingStep?, PrimOp.toEVM, EvmYul.EVM.δ,
      callPrimOp, createPrimOp]
  case create => exact Or.inr ⟨.create, rfl⟩
  case call => exact Or.inl ⟨.call, rfl⟩
  case callcode => exact Or.inl ⟨.callcode, rfl⟩
  case delegatecall => exact Or.inl ⟨.delegatecall, rfl⟩
  case create2 => exact Or.inr ⟨.create2, rfl⟩
  case staticcall => exact Or.inl ⟨.staticcall, rfl⟩

theorem positiveCallStep
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (stepFuel : Nat) {gasful openState : EVMState}
    (hReach : FrameReachable validJumps initial gasful)
    (hRel : OpenStateRel gasful openState)
    (hPrefix : XSstoreStipendChecksPass validJumps gasful)
    (hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt gasful) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          gasful.stack[2]?.getD (EvmYul.UInt256.ofNat 0)))
    (current : CurrentInstruction bytes gasful openState)
    (kind : CallKind)
    (hInstr : current.instr = .prim (callPrimOp kind))
    (hCont :
      ∀ gasfulNext openNext,
        FrameReachable validJumps initial gasfulNext →
        OpenStateRel gasfulNext openNext →
        ∃ transcript,
          RunRefinesOpen
            (EvmYul.EVM.X (stepFuel + 1) validJumps gasfulNext)
            (Compact.InteractionSemantics.openRunNResult
              bytes (stepFuel + 1) openNext)
            transcript) :
    ∃ transcript,
      RunRefinesOpen
        (EvmYul.EVM.X (stepFuel + 1 + 1) validJumps gasful)
        (Compact.InteractionSemantics.openRunNResult
          bytes (stepFuel + 1 + 1) openState)
        transcript := by
  classical
  have hPair : current.decoded = (kind.toEVMOperation, none) := by
    have h := current.instr_decoded
    rw [hInstr] at h
    cases kind <;>
      simpa [Compact.Instr.decoded?, callPrimOp, PrimOp.toEVM,
        CallKind.toEVMOperation] using h.symm
  have hDecodedPair := current.decodedPair.trans hPair
  have hDecodedOp : decodedOperationAt gasful = kind.toEVMOperation := by
    simp [decodedOperationAt, hDecodedPair]
  obtain ⟨rest, operands, hOperands⟩ :=
    call_operands_of_stackEnough_kind kind hPrefix.static.stackLimit hDecodedOp
  have hAllowed :=
    call_allowed_of_static_checks kind hPrefix.static hDecodedOp hOperands
  have hDecode :
      Compact.decodeAt bytes current.pc (.prim (callPrimOp kind)) := by
    rw [← hInstr]
    exact current.decode
  generalize hStep :
    EvmYul.EVM.step (stepFuel + 1) (dynamicGasCostAt gasful)
      (some (kind.toEVMOperation, none)) (afterMemoryChargeAt gasful) =
        stepResult
  cases stepResult with
  | error err =>
      have hFuel : err = EvmYul.EVM.ExecutionException.OutOfFuel :=
        evm_step_call_error_eq_outOfFuel_at hOperands hStep
      subst err
      have hStepActual :
          EvmYul.EVM.step (stepFuel + 1) (dynamicGasCostAt gasful)
            (some
              ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
                (EvmYul.Operation.STOP, none)))
            (afterMemoryChargeAt gasful) =
              .error EvmYul.EVM.ExecutionException.OutOfFuel := by
        simpa [hDecodedPair] using hStep
      have hX := x_after_prechecks_of_step_error
        (fuel := stepFuel + 1) (validJumps := validJumps)
        hPrefix hCreateOk hStepActual
      exact ⟨[], RunRefinesOpen.outOfFuel hX
        (Interaction.Follows.nil _)⟩
  | ok gasfulNext =>
      have hStepActual :
          EvmYul.EVM.step (stepFuel + 1) (dynamicGasCostAt gasful)
            (some
              ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
                (EvmYul.Operation.STOP, none)))
            (afterMemoryChargeAt gasful) = .ok gasfulNext := by
        simpa [hDecodedPair] using hStep
      have hHalt :
          haltOutputAt gasfulNext kind.toEVMOperation = none := by
        cases kind <;> rfl
      have hReachNext : FrameReachable validJumps initial gasfulNext :=
        .next hReach hPrefix hStepActual (by simpa [hDecodedOp] using hHalt)
      let openNext (response : CallResponse) :=
        InteractionSemantics.EVMState.finishCall
          openState rest operands.callLocal response
      let tailTranscript (response : CallResponse) : Interaction.Transcript :=
        if hResponse :
            CallResponseStateRel kind (afterMemoryChargeAt gasful) operands
              response gasfulNext (openNext response) then
          Classical.choose
            (hCont gasfulNext (openNext response) hReachNext
              hResponse.openStateRel)
        else
          []
      have hTail :
          ∀ response,
            CallResponseStateRel kind (afterMemoryChargeAt gasful) operands
                response gasfulNext (openNext response) →
              RunRefinesOpen
                (EvmYul.EVM.X (stepFuel + 1) validJumps gasfulNext)
                (Compact.InteractionSemantics.openRunNResult
                  bytes (stepFuel + 1) (openNext response))
                (tailTranscript response) := by
        intro response hResponse
        simp only [tailTranscript, dif_pos hResponse]
        exact Classical.choose_spec
          (hCont gasfulNext (openNext response) hReachNext
            hResponse.openStateRel)
      obtain ⟨response, hRun⟩ :=
        runRefinesOpen_call_external_success_actual_rel kind tailTranscript
          hRel hPrefix hDecodedPair hOperands hAllowed hDecode current.open_pc
          hStep hTail
      exact ⟨callExternalExchange kind openState operands response ::
        tailTranscript response, hRun⟩

theorem positiveCreateStep
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (stepFuel : Nat) {gasful openState : EVMState}
    (hReach : FrameReachable validJumps initial gasful)
    (hRel : OpenStateRel gasful openState)
    (hPrefix : XSstoreStipendChecksPass validJumps gasful)
    (hCreateOk :
      ¬ (EvmYul.Operation.isCreate (decodedOperationAt gasful) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          gasful.stack[2]?.getD (EvmYul.UInt256.ofNat 0)))
    (current : CurrentInstruction bytes gasful openState)
    (kind : CreateKind)
    (hInstr : current.instr = .prim (createPrimOp kind))
    (hCont :
      ∀ gasfulNext openNext,
        FrameReachable validJumps initial gasfulNext →
        OpenStateRel gasfulNext openNext →
        ∃ transcript,
          RunRefinesOpen
            (EvmYul.EVM.X (stepFuel + 1) validJumps gasfulNext)
            (Compact.InteractionSemantics.openRunNResult
              bytes (stepFuel + 1) openNext)
            transcript) :
    ∃ transcript,
      RunRefinesOpen
        (EvmYul.EVM.X (stepFuel + 1 + 1) validJumps gasful)
        (Compact.InteractionSemantics.openRunNResult
          bytes (stepFuel + 1 + 1) openState)
        transcript := by
  classical
  have hPair : current.decoded = (kind.toEVMOperation, none) := by
    have h := current.instr_decoded
    rw [hInstr] at h
    cases kind <;>
      simpa [Compact.Instr.decoded?, createPrimOp, PrimOp.toEVM,
        CreateKind.toEVMOperation] using h.symm
  have hDecodedPair := current.decodedPair.trans hPair
  have hDecodedOp : decodedOperationAt gasful = kind.toEVMOperation := by
    simp [decodedOperationAt, hDecodedPair]
  obtain ⟨rest, operands, hOperands⟩ :=
    create_operands_of_stackEnough_kind kind hPrefix.static.stackLimit
      hDecodedOp
  have hPermission :=
    create_permission_of_static_checks kind hPrefix.static hDecodedOp
  have hDecode :
      Compact.decodeAt bytes current.pc (.prim (createPrimOp kind)) := by
    rw [← hInstr]
    exact current.decode
  generalize hStep :
    EvmYul.EVM.step (stepFuel + 1) (dynamicGasCostAt gasful)
      (some (kind.toEVMOperation, none)) (afterMemoryChargeAt gasful) =
        stepResult
  cases stepResult with
  | error err =>
      have hGas : err = EvmYul.EVM.ExecutionException.OutOfGass :=
        evm_step_create_positive_error_eq_outOfGas_at hOperands hStep
      subst err
      have hStepActual :
          EvmYul.EVM.step (stepFuel + 1) (dynamicGasCostAt gasful)
            (some
              ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
                (EvmYul.Operation.STOP, none)))
            (afterMemoryChargeAt gasful) =
              .error EvmYul.EVM.ExecutionException.OutOfGass := by
        simpa [hDecodedPair] using hStep
      have hX := x_after_prechecks_of_step_error
        (fuel := stepFuel + 1) (validJumps := validJumps)
        hPrefix hCreateOk hStepActual
      exact ⟨[], RunRefinesOpen.outOfGas hX
        (Interaction.Follows.nil _)⟩
  | ok gasfulNext =>
      have hStepActual :
          EvmYul.EVM.step (stepFuel + 1) (dynamicGasCostAt gasful)
            (some
              ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
                (EvmYul.Operation.STOP, none)))
            (afterMemoryChargeAt gasful) = .ok gasfulNext := by
        simpa [hDecodedPair] using hStep
      have hHalt :
          haltOutputAt gasfulNext kind.toEVMOperation = none := by
        cases kind <;> rfl
      have hReachNext : FrameReachable validJumps initial gasfulNext :=
        .next hReach hPrefix hStepActual (by simpa [hDecodedOp] using hHalt)
      let openNext (response : CreateResponse) :=
        InteractionSemantics.EVMState.finishCreate
          openState rest operands.createLocal response
      let tailTranscript (response : CreateResponse) : Interaction.Transcript :=
        if hResponse :
            CreateResponseStateRel kind (afterMemoryChargeAt gasful) operands
              response gasfulNext (openNext response) then
          Classical.choose
            (hCont gasfulNext (openNext response) hReachNext
              hResponse.openStateRel)
        else
          []
      have hTail :
          ∀ response,
            CreateResponseStateRel kind (afterMemoryChargeAt gasful) operands
                response gasfulNext (openNext response) →
              RunRefinesOpen
                (EvmYul.EVM.X (stepFuel + 1) validJumps gasfulNext)
                (Compact.InteractionSemantics.openRunNResult
                  bytes (stepFuel + 1) (openNext response))
                (tailTranscript response) := by
        intro response hResponse
        simp only [tailTranscript, dif_pos hResponse]
        exact Classical.choose_spec
          (hCont gasfulNext (openNext response) hReachNext
            hResponse.openStateRel)
      obtain ⟨response, hRun⟩ :=
        runRefinesOpen_create_external_success_actual_rel kind tailTranscript
          hRel hPrefix hCreateOk hDecodedPair hOperands hPermission hDecode
          current.open_pc hStep hTail
      exact ⟨createExternalExchange kind openState operands response ::
        tailTranscript response, hRun⟩

/-- The positive-fuel external dispatcher is fully determined by the concrete
gasful step. Successful CALL/CREATE steps choose the corresponding open
response; structural CALL fuel exhaustion and CREATE parent OOG are explicit
prefix outcomes. -/
theorem positiveExternalPrimRefinement
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState} :
    PositiveExternalPrimRefinement bytes validJumps initial := by
  intro stepFuel gasful openState hReach hRel hPrefix hCreateOk
    current op hInstr hPc hGas hMsize hStop hReturn hRevert hSelfdestruct
      hStep hCont
  have hPair : current.decoded = (op.toEVM, none) := by
    have h := current.instr_decoded
    rw [hInstr] at h
    simpa [Compact.Instr.decoded?] using h.symm
  have hDecodedPair := current.decodedPair.trans hPair
  have hDecodedOp : decodedOperationAt gasful = op.toEVM := by
    simp [decodedOperationAt, hDecodedPair]
  have hValid : EvmYul.EVM.δ op.toEVM ≠ none := by
    simpa [hDecodedOp] using
      hPrefix.static.stackLimit.memoryAccess.jumps.stack.opcodeValid
  rcases primOp_external_of_no_continuing op hValid hPc hGas hMsize hStop
      hReturn hRevert hSelfdestruct hStep with
    ⟨kind, hKind⟩ | ⟨kind, hKind⟩
  · subst op
    exact positiveCallStep stepFuel hReach hRel hPrefix hCreateOk current
      kind hInstr hCont
  · subst op
    exact positiveCreateStep stepFuel hReach hRel hPrefix hCreateOk current
      kind hInstr hCont

theorem positiveResourceStep
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (kind : ResourceQuery) (stepFuel : Nat)
    {gasful openState : EVMState}
    (hReach : FrameReachable validJumps initial gasful)
    (hRel : OpenStateRel gasful openState)
    (hPrefix : XSstoreStipendChecksPass validJumps gasful)
    (current : CurrentInstruction bytes gasful openState)
    (hInstr : current.instr = .prim (resourcePrimOp kind))
    (hCont :
      ∀ gasfulNext openNext,
        FrameReachable validJumps initial gasfulNext →
        OpenStateRel gasfulNext openNext →
        ∃ transcript,
          RunRefinesOpen
            (EvmYul.EVM.X (stepFuel + 1) validJumps gasfulNext)
            (Compact.InteractionSemantics.openRunNResult
              bytes (stepFuel + 1) openNext)
            transcript) :
    ∃ transcript,
      RunRefinesOpen
        (EvmYul.EVM.X (stepFuel + 1 + 1) validJumps gasful)
        (Compact.InteractionSemantics.openRunNResult
          bytes (stepFuel + 1 + 1) openState)
        transcript := by
  have hPair :
      current.decoded = ((resourcePrimOp kind).toEVM, none) := by
    have h := current.instr_decoded
    rw [hInstr] at h
    simpa [Compact.Instr.decoded?] using h.symm
  have hDecodedPair := current.decodedPair.trans hPair
  have hDecodedOp :
      decodedOperationAt gasful = (resourcePrimOp kind).toEVM := by
    simp [decodedOperationAt, hDecodedPair]
  have hDecode :
      Compact.decodeAt bytes current.pc (.prim (resourcePrimOp kind)) := by
    rw [← hInstr]
    exact current.decode
  let gasfulNext := gasfulResourceNext kind gasful
  let openNext := openResourceNextAt kind
    (InteractionConcreteResources.resourceValue kind
      (afterDynamicChargeAt gasful)) openState
  have hStep :
      EvmYul.EVM.step (stepFuel + 1) (dynamicGasCostAt gasful)
        (some
          ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt gasful) = .ok gasfulNext := by
    simpa [gasfulNext, hDecodedPair] using
      evm_step_resource_eq kind stepFuel gasful none
  have hHalt :
      haltOutputAt gasfulNext (resourcePrimOp kind).toEVM = none := by
    cases kind <;> simp [resourcePrimOp, PrimOp.toEVM, haltOutputAt]
  have hReachNext : FrameReachable validJumps initial gasfulNext :=
    .next hReach hPrefix hStep (by simpa [hDecodedOp] using hHalt)
  have hNextRel : OpenStateRel gasfulNext openNext := by
    exact resourceNext_openStateRel kind hRel
  obtain ⟨tail, hTail⟩ := hCont gasfulNext openNext hReachNext hNextRel
  refine ⟨InteractionConcreteResources.resourceExchange kind
      (InteractionConcreteResources.resourceValue kind
        (afterDynamicChargeAt gasful)) :: tail, ?_⟩
  exact runRefinesOpen_resource_success_rel kind hPrefix hDecodedPair
    hDecode current.open_pc hTail

theorem positivePrimRefinement_of_other
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (hOther : PositiveOtherPrimRefinement bytes validJumps initial) :
    PositivePrimRefinement bytes validJumps initial := by
  intro stepFuel gasful openState hReach hRel hPrefix hCreateOk
    current op hInstr hCont
  by_cases hPcOp : op = .pc
  · subst op
    have hPair : current.decoded = (EvmYul.Operation.PC, none) := by
      have h := current.instr_decoded
      rw [hInstr] at h
      simpa [Compact.Instr.decoded?, PrimOp.toEVM] using h.symm
    have hDecodedPair := current.decodedPair.trans hPair
    have hDecodedOp :
        decodedOperationAt gasful = EvmYul.Operation.PC := by
      simp [decodedOperationAt, hDecodedPair]
    have hDecode : Compact.decodeAt bytes current.pc (.prim .pc) := by
      rw [← hInstr]
      exact current.decode
    let gasfulNext := gasfulPcNext gasful
    let openNext := openPcNextAt openState
    have hStep :
        EvmYul.EVM.step (stepFuel + 1) (dynamicGasCostAt gasful)
          (some
            ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
              (EvmYul.Operation.STOP, none)))
          (afterMemoryChargeAt gasful) = .ok gasfulNext := by
      simpa [gasfulNext, hDecodedPair] using
        evm_step_pc_eq_next stepFuel gasful none
    have hHalt : haltOutputAt gasfulNext EvmYul.Operation.PC = none := by
      simp [haltOutputAt]
    have hReachNext : FrameReachable validJumps initial gasfulNext :=
      .next hReach hPrefix hStep (by simpa [hDecodedOp] using hHalt)
    have hNextRel : OpenStateRel gasfulNext openNext := by
      exact pcNext_openStateRel_rel hRel
    obtain ⟨tail, hTail⟩ := hCont gasfulNext openNext hReachNext hNextRel
    exact ⟨tail, runRefinesOpen_pc_success_rel
      hPrefix hDecodedPair hDecode current.open_pc hTail⟩
  by_cases hGasOp : op = .gas
  · subst op
    exact positiveResourceStep .gas stepFuel hReach hRel hPrefix current
      (by simpa [resourcePrimOp] using hInstr) hCont
  by_cases hMsizeOp : op = .msize
  · subst op
    exact positiveResourceStep .msize stepFuel hReach hRel hPrefix current
      (by simpa [resourcePrimOp] using hInstr) hCont
  · exact hOther stepFuel gasful openState hReach hRel hPrefix hCreateOk
      current op hInstr hPcOp hGasOp hMsizeOp hCont

theorem positiveOtherPrimRefinement_of_remaining
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (hRemaining : PositiveRemainingPrimRefinement bytes validJumps initial) :
    PositiveOtherPrimRefinement bytes validJumps initial := by
  intro stepFuel gasful openState hReach hRel hPrefix hCreateOk
    current op hInstr hPcOp hGasOp hMsizeOp hCont
  by_cases hStopOp : op = .stop
  · subst op
    have hPair : current.decoded = (EvmYul.Operation.STOP, none) := by
      have h := current.instr_decoded
      rw [hInstr] at h
      simpa [Compact.Instr.decoded?, PrimOp.toEVM] using h.symm
    have hDecodedPair := current.decodedPair.trans hPair
    have hDecodedOp : decodedOperationAt gasful = EvmYul.Operation.STOP := by
      simp [decodedOperationAt, hDecodedPair]
    have hDecode : Compact.decodeAt bytes current.pc (.prim .stop) := by
      rw [← hInstr]
      exact current.decode
    have hStep :
        EvmYul.EVM.step (stepFuel + 1) (dynamicGasCostAt gasful)
          (some
            (EvmYul.Operation.STOP,
              ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
                (EvmYul.Operation.STOP, none)).2))
          (afterMemoryChargeAt gasful) =
            .ok (gasfulStopStateAfterCharges gasful) :=
      evm_step_stop_after_charges
    exact ⟨[], runRefinesOpen_stop_success_rel
      hRel hPrefix hDecodedOp hStep hDecode current.open_pc⟩
  by_cases hReturnOp : op = .return
  · subst op
    have hPair : current.decoded = (EvmYul.Operation.RETURN, none) := by
      have h := current.instr_decoded
      rw [hInstr] at h
      simpa [Compact.Instr.decoded?, PrimOp.toEVM] using h.symm
    have hDecodedPair := current.decodedPair.trans hPair
    have hDecodedOp : decodedOperationAt gasful = EvmYul.Operation.RETURN := by
      simp [decodedOperationAt, hDecodedPair]
    have hEnough : ¬ gasful.stack.length < 2 := by
      simpa [hDecodedOp, EvmYul.EVM.δ] using
        hPrefix.static.stackLimit.memoryAccess.jumps.stack.stackEnough
    cases hStack : gasful.stack with
    | nil => simp [hStack] at hEnough
    | cons offset tail =>
        cases hTailStack : tail with
        | nil => simp [hStack, hTailStack] at hEnough
        | cons size rest =>
            have hPop :
                (afterEVMInstructionChargeAt gasful).stack.pop2 =
                  some (rest, offset, size) := by
              have hChargedStack :
                  (afterEVMInstructionChargeAt gasful).stack =
                    offset :: size :: rest := by
                simpa [afterEVMInstructionChargeAt, afterMemoryChargeAt,
                  chargeGas, hTailStack] using hStack
              rw [hChargedStack]
              rfl
            have hStep := evm_step_return_after_charges
              (fuel := stepFuel) hPop
            have hDecode :
                Compact.decodeAt bytes current.pc (.prim .return) := by
              rw [← hInstr]
              exact current.decode
            exact ⟨[], runRefinesOpen_return_success_rel
              hRel hPrefix hDecodedOp hStep hDecode current.open_pc⟩
  by_cases hRevertOp : op = .revert
  · subst op
    have hPair : current.decoded = (EvmYul.Operation.REVERT, none) := by
      have h := current.instr_decoded
      rw [hInstr] at h
      simpa [Compact.Instr.decoded?, PrimOp.toEVM] using h.symm
    have hDecodedPair := current.decodedPair.trans hPair
    have hDecodedOp : decodedOperationAt gasful = EvmYul.Operation.REVERT := by
      simp [decodedOperationAt, hDecodedPair]
    have hEnough : ¬ gasful.stack.length < 2 := by
      simpa [hDecodedOp, EvmYul.EVM.δ] using
        hPrefix.static.stackLimit.memoryAccess.jumps.stack.stackEnough
    cases hStack : gasful.stack with
    | nil => simp [hStack] at hEnough
    | cons offset tail =>
        cases hTailStack : tail with
        | nil => simp [hStack, hTailStack] at hEnough
        | cons size rest =>
            have hPop :
                (afterEVMInstructionChargeAt gasful).stack.pop2 =
                  some (rest, offset, size) := by
              have hChargedStack :
                  (afterEVMInstructionChargeAt gasful).stack =
                    offset :: size :: rest := by
                simpa [afterEVMInstructionChargeAt, afterMemoryChargeAt,
                  chargeGas, hTailStack] using hStack
              rw [hChargedStack]
              rfl
            have hStep := evm_step_revert_after_charges
              (fuel := stepFuel) hPop
            have hDecode :
                Compact.decodeAt bytes current.pc (.prim .revert) := by
              rw [← hInstr]
              exact current.decode
            exact ⟨[], runRefinesOpen_revert_success_rel
              hRel hPrefix hDecodedOp hStep hDecode current.open_pc⟩
  by_cases hSelfdestructOp : op = .selfdestruct
  · subst op
    have hPair :
        current.decoded = (EvmYul.Operation.SELFDESTRUCT, none) := by
      have h := current.instr_decoded
      rw [hInstr] at h
      simpa [Compact.Instr.decoded?, PrimOp.toEVM] using h.symm
    have hDecodedPair := current.decodedPair.trans hPair
    have hDecodedOp :
        decodedOperationAt gasful = EvmYul.Operation.SELFDESTRUCT := by
      simp [decodedOperationAt, hDecodedPair]
    have hEnough : ¬ gasful.stack.length < 1 := by
      simpa [hDecodedOp, EvmYul.EVM.δ] using
        hPrefix.static.stackLimit.memoryAccess.jumps.stack.stackEnough
    cases hStack : gasful.stack with
    | nil =>
        exfalso
        apply hEnough
        simp [hStack]
    | cons recipient rest =>
        have hPerm : gasful.executionEnv.perm = true := by
          cases hPermission : gasful.executionEnv.perm
          · exfalso
            apply hPrefix.static.staticOk
            exact ⟨hPermission, by simp [hDecodedOp]⟩
          · rfl
        have hDecode :
            Compact.decodeAt bytes current.pc (.prim .selfdestruct) := by
          rw [← hInstr]
          exact current.decode
        exact ⟨[], runRefinesOpen_selfdestruct_success_rel
          hRel hPrefix hDecodedPair hPerm hStack hDecode current.open_pc⟩
  · exact hRemaining stepFuel gasful openState hReach hRel hPrefix hCreateOk
      current op hInstr hPcOp hGasOp hMsizeOp hStopOp hReturnOp hRevertOp
        hSelfdestructOp hCont

theorem positiveRemainingPrimRefinement_of_external
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (hExternal : PositiveExternalPrimRefinement bytes validJumps initial) :
    PositiveRemainingPrimRefinement bytes validJumps initial := by
  intro stepFuel gasful openState hReach hRel hPrefix hCreateOk
    current op hInstr hPcOp hGasOp hMsizeOp hStopOp hReturnOp hRevertOp
      hSelfdestructOp hCont
  cases hStep : op.continuingStep? with
  | some step =>
      exact positiveContinuingStep stepFuel hReach hRel hPrefix hCreateOk
        current hInstr hStep hMsizeOp hCont
  | none =>
      exact hExternal stepFuel gasful openState hReach hRel hPrefix hCreateOk
        current op hInstr hPcOp hGasOp hMsizeOp hStopOp hReturnOp hRevertOp
          hSelfdestructOp hStep hCont

theorem positiveStepRefinement_of_positivePrim
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (hPrim : PositivePrimRefinement bytes validJumps initial) :
    PositiveStepRefinement bytes validJumps initial := by
  intro stepFuel gasful openState hReach hRel hPrefix hCreateOk current hCont
  cases hInstr : current.instr with
  | push width value =>
      have hFits : Compact.FitsWidth width value.toNat := by
        simpa [hInstr, Compact.Instr.Valid] using current.valid
      obtain ⟨op, hOp⟩ := Compact.exists_pushOp_of_width
        ⟨hFits.1, hFits.2.1⟩
      have hPair : current.decoded = (op, some (value, width)) := by
        have h := current.instr_decoded
        rw [hInstr] at h
        simpa [Compact.Instr.decoded?, hOp] using h.symm
      have hDecodedPair :
          ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
            (EvmYul.Operation.STOP, none)) =
            (op, some (value, width)) :=
        current.decodedPair.trans hPair
      have hDecodedOp : decodedOperationAt gasful = op := by
        simp [decodedOperationAt, hDecodedPair]
      have hDecode : Compact.decodeAt bytes current.pc (.push width value) := by
        rw [← hInstr]
        exact current.decode
      let gasfulNext := gasfulPushNext width value gasful
      let openNext := openPushNextAt width value openState
      have hStep :
          EvmYul.EVM.step (stepFuel + 1) (dynamicGasCostAt gasful)
            (some
              ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
                (EvmYul.Operation.STOP, none)))
            (afterMemoryChargeAt gasful) = .ok gasfulNext := by
        simpa [gasfulNext, hDecodedPair] using
          evm_step_push_eq_next stepFuel gasful value hFits hOp
      have hHalt : haltOutputAt gasfulNext op = none := by
        exact pushOp_haltOutputAt_none gasfulNext hFits hOp
      have hReachNext : FrameReachable validJumps initial gasfulNext :=
        .next hReach hPrefix hStep (by simpa [hDecodedOp] using hHalt)
      have hNextRel : OpenStateRel gasfulNext openNext := by
        exact pushNext_openStateRel_rel width value hRel
      obtain ⟨tail, hTail⟩ := hCont gasfulNext openNext hReachNext hNextRel
      exact ⟨tail, runRefinesOpen_push_success_rel
        hPrefix hFits hOp hDecodedPair hDecode current.open_pc hTail⟩
  | jump =>
      have hPair : current.decoded = (EvmYul.Operation.JUMP, none) := by
        have h := current.instr_decoded
        rw [hInstr] at h
        simpa [Compact.Instr.decoded?] using h.symm
      have hDecodedPair := current.decodedPair.trans hPair
      have hDecodedOp :
          decodedOperationAt gasful = EvmYul.Operation.JUMP := by
        simp [decodedOperationAt, hDecodedPair]
      have hEnough : ¬ gasful.stack.length < 1 := by
        simpa [decodedOperationAt, hDecodedPair, EvmYul.EVM.δ] using
          hPrefix.static.stackLimit.memoryAccess.jumps.stack.stackEnough
      cases hStack : gasful.stack with
      | nil =>
          exfalso
          apply hEnough
          simp [hStack]
      | cons dest rest =>
          have hOpenStack : openState.stack = dest :: rest := by
            rw [← hRel.stack_eq]
            exact hStack
          have hDecode : Compact.decodeAt bytes current.pc .jump := by
            rw [← hInstr]
            exact current.decode
          let gasfulNext := gasfulJumpNext gasful rest dest
          let openNext := openJumpNextAt openState rest dest
          have hStep :
              EvmYul.EVM.step (stepFuel + 1) (dynamicGasCostAt gasful)
                (some
                  ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
                    (EvmYul.Operation.STOP, none)))
                (afterMemoryChargeAt gasful) = .ok gasfulNext := by
            simpa [gasfulNext, hDecodedPair] using
              evm_step_jump_eq_next stepFuel gasful none rest dest hStack
          have hHalt :
              haltOutputAt gasfulNext EvmYul.Operation.JUMP = none := by
            simp [haltOutputAt]
          have hReachNext : FrameReachable validJumps initial gasfulNext :=
            .next hReach hPrefix hStep (by simpa [hDecodedOp] using hHalt)
          have hNextRel : OpenStateRel gasfulNext openNext := by
            exact jumpNext_openStateRel_rel rest dest hRel
          obtain ⟨tail, hTail⟩ :=
            hCont gasfulNext openNext hReachNext hNextRel
          exact ⟨tail, runRefinesOpen_jump_success_rel
            hPrefix hDecodedPair hStack hOpenStack hDecode
              current.open_pc hTail⟩
  | jumpi =>
      have hPair : current.decoded = (EvmYul.Operation.JUMPI, none) := by
        have h := current.instr_decoded
        rw [hInstr] at h
        simpa [Compact.Instr.decoded?] using h.symm
      have hDecodedPair := current.decodedPair.trans hPair
      have hDecodedOp :
          decodedOperationAt gasful = EvmYul.Operation.JUMPI := by
        simp [decodedOperationAt, hDecodedPair]
      have hEnough : ¬ gasful.stack.length < 2 := by
        simpa [decodedOperationAt, hDecodedPair, EvmYul.EVM.δ] using
          hPrefix.static.stackLimit.memoryAccess.jumps.stack.stackEnough
      cases hStack : gasful.stack with
      | nil => simp [hStack] at hEnough
      | cons dest tail =>
          cases hTailStack : tail with
          | nil => simp [hStack, hTailStack] at hEnough
          | cons cond rest =>
              have hGasfulStack : gasful.stack = dest :: cond :: rest := by
                simpa [hTailStack] using hStack
              have hOpenStack : openState.stack = dest :: cond :: rest := by
                rw [← hRel.stack_eq]
                exact hGasfulStack
              have hDecode : Compact.decodeAt bytes current.pc .jumpi := by
                rw [← hInstr]
                exact current.decode
              let gasfulNext := gasfulJumpiNext gasful rest dest cond
              let openNext := openJumpiNextAt openState rest dest cond
              have hStep :
                  EvmYul.EVM.step (stepFuel + 1) (dynamicGasCostAt gasful)
                    (some
                      ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
                        (EvmYul.Operation.STOP, none)))
                    (afterMemoryChargeAt gasful) = .ok gasfulNext := by
                simpa [gasfulNext, hDecodedPair] using
                  evm_step_jumpi_eq_next stepFuel gasful none rest dest cond
                    hGasfulStack
              have hHalt :
                  haltOutputAt gasfulNext EvmYul.Operation.JUMPI = none := by
                simp [haltOutputAt]
              have hReachNext : FrameReachable validJumps initial gasfulNext :=
                .next hReach hPrefix hStep (by
                  simpa [hDecodedOp] using hHalt)
              have hNextRel : OpenStateRel gasfulNext openNext := by
                exact jumpiNext_openStateRel_rel rest dest cond hRel
              obtain ⟨tailTranscript, hTail⟩ :=
                hCont gasfulNext openNext hReachNext hNextRel
              exact ⟨tailTranscript, runRefinesOpen_jumpi_success_rel
                hPrefix hDecodedPair hGasfulStack hOpenStack hDecode
                  current.open_pc hTail⟩
  | jumpdest =>
      have hPair : current.decoded = (EvmYul.Operation.JUMPDEST, none) := by
        have h := current.instr_decoded
        rw [hInstr] at h
        simpa [Compact.Instr.decoded?] using h.symm
      have hDecodedPair := current.decodedPair.trans hPair
      have hDecodedOp :
          decodedOperationAt gasful = EvmYul.Operation.JUMPDEST := by
        simp [decodedOperationAt, hDecodedPair]
      have hDecode : Compact.decodeAt bytes current.pc .jumpdest := by
        rw [← hInstr]
        exact current.decode
      let gasfulNext := (afterEVMInstructionChargeAt gasful).incrPC
      let openNext := openJumpdestNextAt openState
      have hStep :
          EvmYul.EVM.step (stepFuel + 1) (dynamicGasCostAt gasful)
            (some
              ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
                (EvmYul.Operation.STOP, none)))
            (afterMemoryChargeAt gasful) = .ok gasfulNext := by
        simpa [gasfulNext, hDecodedPair] using
          evm_step_jumpdest_eq_next stepFuel gasful none
      have hHalt :
          haltOutputAt gasfulNext EvmYul.Operation.JUMPDEST = none := by
        simp [haltOutputAt]
      have hReachNext : FrameReachable validJumps initial gasfulNext :=
        .next hReach hPrefix hStep (by simpa [hDecodedOp] using hHalt)
      have hNextRel : OpenStateRel gasfulNext openNext := by
        exact jumpdestNext_openStateRel_rel hRel
      obtain ⟨tail, hTail⟩ := hCont gasfulNext openNext hReachNext hNextRel
      exact ⟨tail, runRefinesOpen_jumpdest_success_rel
        hPrefix hDecodedPair hDecode current.open_pc hTail⟩
  | prim op =>
      exact hPrim stepFuel gasful openState hReach hRel hPrefix hCreateOk
        current op hInstr hCont

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

theorem postStackLimitRefinement_of_postStatic
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (hPost : PostStaticRefinement bytes validJumps initial) :
    PostStackLimitRefinement bytes validJumps initial := by
  intro fuel gasful openState hReach hRel hPrefix current hCont
  by_cases hStatic : staticModeViolationAt gasful
  · exact ⟨[], runRefinesOpen_staticModeViolation_rel
      current hRel hPrefix hStatic⟩
  · exact hPost fuel gasful openState hReach hRel
      ⟨hPrefix, hStatic⟩ current hCont

theorem postStaticRefinement_of_postSstore
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (hPost : PostSstoreRefinement bytes validJumps initial) :
    PostStaticRefinement bytes validJumps initial := by
  intro fuel gasful openState hReach hRel hPrefix current hCont
  by_cases hSstore : sstoreStipendOutOfGasAt gasful
  · exact ⟨[], runRefinesOpen_sstore_stipend_outOfGas hPrefix hSstore⟩
  · exact hPost fuel gasful openState hReach hRel
      ⟨hPrefix, hSstore⟩ current hCont

theorem postSstoreRefinement_of_postPrechecks
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (hPost : PostPrechecksRefinement bytes validJumps initial) :
    PostSstoreRefinement bytes validJumps initial := by
  intro fuel gasful openState hReach hRel hPrefix current hCont
  by_cases hCreate :
      EvmYul.Operation.isCreate (decodedOperationAt gasful) = true ∧
        (EvmYul.UInt256.ofNat 49152) <
          gasful.stack[2]?.getD (EvmYul.UInt256.ofNat 0)
  · have hCreateOp := operation_eq_create_or_create2_of_isCreate hCreate.1
    exact ⟨[], runRefinesOpen_create_initcode_outOfGas
      hPrefix hCreateOp hCreate.2⟩
  · exact hPost fuel gasful openState hReach hRel hPrefix
      hCreate current hCont

theorem postPrechecksRefinement_of_positiveStep
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (hPositive : PositiveStepRefinement bytes validJumps initial) :
    PostPrechecksRefinement bytes validJumps initial := by
  intro fuel gasful openState hReach hRel hPrefix hCreateOk current hCont
  cases fuel with
  | zero =>
      have hStep :
          EvmYul.EVM.step 0 (dynamicGasCostAt gasful)
            (some
              ((EvmYul.EVM.decode gasful.executionEnv.code gasful.pc).getD
                (EvmYul.Operation.STOP, none)))
            (afterMemoryChargeAt gasful) =
              .error EvmYul.EVM.ExecutionException.OutOfFuel := by
        simp [EvmYul.EVM.step]
      have hX := x_after_prechecks_of_step_error
        (fuel := 0) (validJumps := validJumps)
        hPrefix hCreateOk hStep
      exact ⟨[], RunRefinesOpen.outOfFuel hX
        (Interaction.Follows.nil _)⟩
  | succ stepFuel =>
      simpa [Nat.add_assoc] using
        hPositive stepFuel gasful openState hReach hRel hPrefix
          hCreateOk current (by
            intro gasfulNext openNext hReachNext hRelNext
            simpa [Nat.add_assoc] using
              hCont gasfulNext openNext hReachNext hRelNext)

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

/-- Recursive gasful/open frame bridge through every checked exceptional
branch. The sole remaining local premise begins at the actual charged
`EVM.step` result and retains the open CALL/CREATE strategy boundary. -/
theorem runRefinesOpen_recursive_of_postPrechecks
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (hCode : FrameCodeInvariant bytes validJumps initial)
    (hPost : PostPrechecksRefinement bytes validJumps initial)
    (fuel : Nat) {gasful openState : EVMState}
    (hReach : FrameReachable validJumps initial gasful)
    (hRel : OpenStateRel gasful openState) :
    ∃ transcript,
      RunRefinesOpen
        (EvmYul.EVM.X fuel validJumps gasful)
        (Compact.InteractionSemantics.openRunNResult bytes fuel openState)
        transcript := by
  exact runRefinesOpen_recursive_of_postStackLimit hCode
    (postStackLimitRefinement_of_postStatic
      (postStaticRefinement_of_postSstore
        (postSstoreRefinement_of_postPrechecks hPost)))
    fuel hReach hRel

/-- Strongest assembled recursive theorem before instruction-family dispatch:
all exceptional checks and zero `EVM.step` proof fuel are discharged, leaving
only positive charged instruction execution. -/
theorem runRefinesOpen_recursive_of_positiveStep
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (hCode : FrameCodeInvariant bytes validJumps initial)
    (hPositive : PositiveStepRefinement bytes validJumps initial)
    (fuel : Nat) {gasful openState : EVMState}
    (hReach : FrameReachable validJumps initial gasful)
    (hRel : OpenStateRel gasful openState) :
    ∃ transcript,
      RunRefinesOpen
        (EvmYul.EVM.X fuel validJumps gasful)
        (Compact.InteractionSemantics.openRunNResult bytes fuel openState)
        transcript := by
  exact runRefinesOpen_recursive_of_postPrechecks hCode
    (postPrechecksRefinement_of_positiveStep hPositive)
    fuel hReach hRel

/-- Recursive frame bridge with every checked exception, actual GAS/MSIZE
observation, compact control/PUSH step, and terminal instruction discharged.
The remaining premise contains only ordinary continuing primitives and actual
CALL/CREATE-family execution. -/
theorem runRefinesOpen_recursive_of_positiveRemainingPrim
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (hCode : FrameCodeInvariant bytes validJumps initial)
    (hRemaining : PositiveRemainingPrimRefinement bytes validJumps initial)
    (fuel : Nat) {gasful openState : EVMState}
    (hReach : FrameReachable validJumps initial gasful)
    (hRel : OpenStateRel gasful openState) :
    ∃ transcript,
      RunRefinesOpen
        (EvmYul.EVM.X fuel validJumps gasful)
        (Compact.InteractionSemantics.openRunNResult bytes fuel openState)
        transcript := by
  exact runRefinesOpen_recursive_of_positiveStep hCode
    (positiveStepRefinement_of_positivePrim
      (positivePrimRefinement_of_other
        (positiveOtherPrimRefinement_of_remaining hRemaining)))
    fuel hReach hRel

/-- Complete recursive bridge modulo only positive-fuel CALL/CREATE-family
execution. All ordinary instructions, resources, terminals, and exceptional
prechecks are discharged before this explicit external strategy boundary. -/
theorem runRefinesOpen_recursive_of_positiveExternalPrim
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (hCode : FrameCodeInvariant bytes validJumps initial)
    (hExternal : PositiveExternalPrimRefinement bytes validJumps initial)
    (fuel : Nat) {gasful openState : EVMState}
    (hReach : FrameReachable validJumps initial gasful)
    (hRel : OpenStateRel gasful openState) :
    ∃ transcript,
      RunRefinesOpen
        (EvmYul.EVM.X fuel validJumps gasful)
        (Compact.InteractionSemantics.openRunNResult bytes fuel openState)
        transcript := by
  exact runRefinesOpen_recursive_of_positiveRemainingPrim hCode
    (positiveRemainingPrimRefinement_of_external hExternal)
    fuel hReach hRel

/-- Responder-agnostic whole-frame refinement from imported gasful `EVM.X` to
the open compact-bytecode interaction. The existential transcript records
actual GAS/MSIZE observations and concrete CALL/CREATE responses, including
parent charge, EIP-150 forwarding, and returned gas. Target OOG and structural
fuel exhaustion remain explicit `RunRefinesOpen` outcomes. -/
theorem runRefinesOpen_recursive
    {bytes : ByteArray} {validJumps : Array Word} {initial : EVMState}
    (hCode : FrameCodeInvariant bytes validJumps initial)
    (fuel : Nat) {gasful openState : EVMState}
    (hReach : FrameReachable validJumps initial gasful)
    (hRel : OpenStateRel gasful openState) :
    ∃ transcript,
      RunRefinesOpen
        (EvmYul.EVM.X fuel validJumps gasful)
        (Compact.InteractionSemantics.openRunNResult bytes fuel openState)
        transcript := by
  exact runRefinesOpen_recursive_of_positiveExternalPrim hCode
    positiveExternalPrimRefinement fuel hReach hRel

end EvmCompiler.Assembly.GasfulBridge
