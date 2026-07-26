import EvmCompiler.Assembly.StackHeadroomSound
import EvmCompiler.Assembly.JumpTargetSound

/-!
# Raw compact-program stack and jump safety

This module discharges gasful safety from the emitted compact instruction
stream itself.  Unlike the source-layout bridge, it is agnostic to whether a
`JUMP` came from a fixed-label Assembly branch or from a separately certified
physical return dispatcher.
-/

namespace EvmCompiler
namespace Assembly
namespace StackHeadroom

open EvmCompiler.Assembly.GasfulBridge

structure RawPoint (bytes : ByteArray) (table : StackTable)
    (state : EVMState) : Prop where
  code_eq : state.executionEnv.code = bytes
  height : HeightPoint table state

theorem raw_compact_sentinel_decodeAt
    {artifact : Compact.Artifact}
    (hBytes : artifact.bytes = Compact.encode artifact.program)
    (hSentinelFits :
      Compact.Program.codeByteLength artifact.program.code + 1 <
        18446744073709551616)
    (payload : List UInt8) :
    Compact.decodeAt
      (Bytecode.ofList
        (artifact.bytes.toList ++
          (Compact.encodeInstr (.prim .invalid) ++ payload)))
      (Compact.Program.codeByteLength artifact.program.code)
      (.prim .invalid) := by
  have hBytesList :
      artifact.bytes.toList =
        artifact.program.code.flatMap Compact.encodeLocated := by
    rw [hBytes]
    simp [Compact.encode, Bytecode.ofList]
  have hLength :
      artifact.bytes.toList.length =
        Compact.Program.codeByteLength artifact.program.code := by
    rw [hBytesList, Compact.flatMap_encodeLocated_length]
  have hStart :
      artifact.bytes.toList.length + 1 <
        18446744073709551616 := by
    rw [hLength]
    exact hSentinelFits
  have hPc :
      (EvmYul.UInt256.ofNat artifact.bytes.toList.length).toNat =
        artifact.bytes.toList.length := by
    apply Bytecode.uint256_ofNat_toNat_of_decode_window
    omega
  have hDecode :=
    Compact.decodeInstrAtPrefix artifact.bytes.toList payload
      (.prim .invalid) trivial hPc hStart
      (by simpa [Compact.Instr.byteSize] using hStart)
  rw [hLength] at hDecode
  simpa [List.append_assoc] using hDecode

theorem state_pc_eq_of_located_toNat
    {state : EVMState} {located : Compact.Located}
    (hPc : located.pc = state.pc.toNat) :
    state.pc = EvmYul.UInt256.ofNat located.pc := by
  calc
    state.pc = EvmYul.UInt256.ofNat state.pc.toNat :=
      (EvmYul.UInt256.ofNat_toNat state.pc).symm
    _ = EvmYul.UInt256.ofNat located.pc := by rw [hPc]

theorem raw_decode
    {program : Compact.Program} {bytes : ByteArray}
    {state : EVMState} {located : Compact.Located}
    (hDecode : Compact.DecodingCorrect program bytes)
    (hMem : located ∈ program.code)
    (hCode : state.executionEnv.code = bytes)
    (hPc : located.pc = state.pc.toNat) :
    ∃ decoded,
      located.instr.decoded? = some decoded ∧
        EvmYul.EVM.decode state.executionEnv.code state.pc =
          some decoded := by
  obtain ⟨decoded, hInstr, hBytes⟩ := hDecode.decodes located hMem
  refine ⟨decoded, hInstr, ?_⟩
  have hStatePc := state_pc_eq_of_located_toNat hPc
  simpa [hCode, hStatePc] using hBytes

theorem rawPoint_jumpdest_step
    {program : Compact.Program} {bytes : ByteArray} {cert : Cert}
    {state next : EVMState} {located : Compact.Located}
    {astack : AbsStack} {stepFuel : Nat}
    (hDecode : Compact.DecodingCorrect program bytes)
    (hMem : located ∈ program.code)
    (hPc : located.pc = state.pc.toNat)
    (hInstr : located.instr = .jumpdest)
    (hFlow : rawInstrOk? program cert.table located astack = true)
    (hCode : state.executionEnv.code = bytes)
    (hEntry : memStack cert.table state.pc astack = true)
    (hAgrees : Agrees astack state.stack)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    RawPoint bytes cert.table next := by
  obtain ⟨decoded, hDecodedInstr, hDecoded⟩ :=
    raw_decode hDecode hMem hCode hPc
  rw [hInstr] at hDecodedInstr
  simp [Compact.Instr.decoded?] at hDecodedInstr
  subst decoded
  cases stepFuel with
  | zero =>
      simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      rw [hDecoded] at hStep
      simp only [Option.getD_some] at hStep
      rw [evm_step_jumpdest_eq_next fuel state none] at hStep
      have hNext : next = (afterEVMInstructionChargeAt state).incrPC := by
        simpa using hStep.symm
      subst next
      have hStatePc := state_pc_eq_of_located_toNat hPc
      have hNextPc :
          ((afterEVMInstructionChargeAt state).incrPC).pc =
            EvmYul.UInt256.ofNat
              (located.pc + located.instr.byteSize) := by
        simp [EvmYul.EVM.State.incrPC, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, chargeGas, hStatePc, hInstr,
          Compact.Instr.byteSize, uint256_ofNat_add]
      have hNextStack :
          ((afterEVMInstructionChargeAt state).incrPC).stack =
            state.stack := by
        simp [EvmYul.EVM.State.incrPC, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, chargeGas]
      have hNextCode :
          ((afterEVMInstructionChargeAt state).incrPC).executionEnv.code =
            bytes := by
        simpa [EvmYul.EVM.State.incrPC, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, chargeGas] using hCode
      refine ⟨hNextCode, astack, ?_, ?_⟩
      · rw [hNextPc]
        simpa [rawInstrOk?, hInstr] using hFlow
      · rw [hNextStack]
        exact hAgrees

theorem rawPoint_push0_step
    {program : Compact.Program} {bytes : ByteArray} {cert : Cert}
    {state next : EVMState} {located : Compact.Located}
    {astack : AbsStack} {stepFuel : Nat}
    (hDecode : Compact.DecodingCorrect program bytes)
    (hMem : located ∈ program.code)
    (hPc : located.pc = state.pc.toNat)
    (hInstr : located.instr = .push0)
    (hFlow : rawInstrOk? program cert.table located astack = true)
    (hCode : state.executionEnv.code = bytes)
    (hEntry : memStack cert.table state.pc astack = true)
    (hAgrees : Agrees astack state.stack)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    RawPoint bytes cert.table next := by
  obtain ⟨decoded, hDecodedInstr, hDecoded⟩ :=
    raw_decode hDecode hMem hCode hPc
  rw [hInstr] at hDecodedInstr
  simp [Compact.Instr.decoded?] at hDecodedInstr
  subst decoded
  cases stepFuel with
  | zero =>
      simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      rw [hDecoded] at hStep
      simp only [Option.getD_some] at hStep
      rw [evm_step_push0_eq_next fuel state] at hStep
      have hNext :
          next = gasfulPushNext 0 (EvmYul.UInt256.ofNat 0) state := by
        simpa using hStep.symm
      subst next
      have hStatePc := state_pc_eq_of_located_toNat hPc
      have hNextPc :
          (gasfulPushNext 0 (EvmYul.UInt256.ofNat 0) state).pc =
            EvmYul.UInt256.ofNat
              (located.pc + located.instr.byteSize) := by
        simp [gasfulPushNext, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, chargeGas, hStatePc, hInstr,
          Compact.Instr.byteSize, uint256_ofNat_add]
      have hNextStack :
          (gasfulPushNext 0 (EvmYul.UInt256.ofNat 0) state).stack =
            EvmYul.UInt256.ofNat 0 :: state.stack := by
        simp [gasfulPushNext, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push,
          afterEVMInstructionChargeAt, afterMemoryChargeAt, chargeGas]
      have hNextCode :
          (gasfulPushNext 0
              (EvmYul.UInt256.ofNat 0) state).executionEnv.code =
            bytes := by
        simpa [gasfulPushNext,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, chargeGas] using hCode
      refine
        ⟨hNextCode, some (EvmYul.UInt256.ofNat 0) :: astack, ?_, ?_⟩
      · rw [hNextPc]
        simpa [rawInstrOk?, hInstr] using hFlow
      · rw [hNextStack]
        exact agrees_cons rfl hAgrees

theorem rawPoint_push_step
    {program : Compact.Program} {bytes : ByteArray} {cert : Cert}
    {state next : EVMState} {located : Compact.Located}
    {astack : AbsStack} {width : Nat} {value : Word}
    {stepFuel : Nat}
    (hDecode : Compact.DecodingCorrect program bytes)
    (hMem : located ∈ program.code)
    (hPc : located.pc = state.pc.toNat)
    (hInstr : located.instr = .push width value)
    (hFits : Compact.FitsWidth width value.toNat)
    (hFlow : rawInstrOk? program cert.table located astack = true)
    (hCode : state.executionEnv.code = bytes)
    (hEntry : memStack cert.table state.pc astack = true)
    (hAgrees : Agrees astack state.stack)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    RawPoint bytes cert.table next := by
  obtain ⟨op, hOp⟩ := Compact.exists_pushOp_of_width
    ⟨hFits.1, hFits.2.1⟩
  obtain ⟨decoded, hDecodedInstr, hDecoded⟩ :=
    raw_decode hDecode hMem hCode hPc
  rw [hInstr] at hDecodedInstr
  simp [Compact.Instr.decoded?, hOp] at hDecodedInstr
  subst decoded
  cases stepFuel with
  | zero =>
      simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      rw [hDecoded] at hStep
      simp only [Option.getD_some] at hStep
      rw [evm_step_push_eq_next fuel state value hFits hOp] at hStep
      have hNext : next = gasfulPushNext width value state := by
        simpa using hStep.symm
      subst next
      have hStatePc := state_pc_eq_of_located_toNat hPc
      have hNextPc :
          (gasfulPushNext width value state).pc =
            EvmYul.UInt256.ofNat
              (located.pc + located.instr.byteSize) := by
        simp [gasfulPushNext, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, chargeGas, hStatePc, hInstr,
          Compact.Instr.byteSize, uint256_ofNat_add, Nat.add_assoc]
      have hNextStack :
          (gasfulPushNext width value state).stack =
            value :: state.stack := by
        simp [gasfulPushNext, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push,
          afterEVMInstructionChargeAt, afterMemoryChargeAt, chargeGas]
      have hNextCode :
          (gasfulPushNext width value state).executionEnv.code =
            bytes := by
        simpa [gasfulPushNext,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, chargeGas] using hCode
      refine ⟨hNextCode, some value :: astack, ?_, ?_⟩
      · rw [hNextPc]
        simpa [rawInstrOk?, hInstr] using hFlow
      · rw [hNextStack]
        exact agrees_cons rfl hAgrees

theorem rawJumpi_flow
    {program : Compact.Program} {table : StackTable}
    {located : Compact.Located} {dest cond : Word}
    {condAbs : Option Word} {rest : AbsStack}
    (hInstr : located.instr = .jumpi)
    (hFlow :
      rawInstrOk? program table located
          (some dest :: condAbs :: rest) = true)
    (hCond : AgreesVal condAbs cond) :
    (cond ≠ EvmYul.UInt256.ofNat 0 →
        memStack table dest rest = true) ∧
    (cond = EvmYul.UInt256.ofNat 0 →
        memStack table
            (EvmYul.UInt256.ofNat
              (located.pc + located.instr.byteSize)) rest =
          true) := by
  cases condAbs with
  | some value =>
      simp only [rawInstrOk?, hInstr, Bool.and_eq_true] at hFlow
      have hValue : value = cond := agreesVal_some hCond
      subst value
      by_cases hZero : cond = EvmYul.UInt256.ofNat 0
      · have hNext :
            memStack table
                (EvmYul.UInt256.ofNat
                  (located.pc + Compact.Instr.jumpi.byteSize)) rest =
              true := by
          simpa [hZero] using hFlow.2
        exact
          ⟨fun hNe => absurd hZero hNe,
            fun _ => by simpa [hInstr] using hNext⟩
      · have hDest : memStack table dest rest = true := by
          simpa [hZero] using hFlow.2
        exact
          ⟨fun _ => hDest,
            fun hEq => absurd hEq hZero⟩
  | none =>
      simp only [rawInstrOk?, hInstr, Bool.and_eq_true] at hFlow
      exact
        ⟨fun _ => hFlow.2.1,
          fun _ => by simpa [hInstr] using hFlow.2.2⟩

theorem rawPoint_jump_step
    {program : Compact.Program} {bytes : ByteArray} {cert : Cert}
    {state next : EVMState} {located : Compact.Located}
    {astack : AbsStack} {validJumps : Array Word} {stepFuel : Nat}
    (hDecode : Compact.DecodingCorrect program bytes)
    (hMem : located ∈ program.code)
    (hPc : located.pc = state.pc.toNat)
    (hInstr : located.instr = .jump)
    (hFlow : rawInstrOk? program cert.table located astack = true)
    (hCode : state.executionEnv.code = bytes)
    (hEntry : memStack cert.table state.pc astack = true)
    (hAgrees : Agrees astack state.stack)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    RawPoint bytes cert.table next := by
  obtain ⟨decoded, hDecodedInstr, hDecoded⟩ :=
    raw_decode hDecode hMem hCode hPc
  rw [hInstr] at hDecodedInstr
  simp [Compact.Instr.decoded?] at hDecodedInstr
  subst decoded
  cases astack with
  | nil =>
      simp [rawInstrOk?, hInstr] at hFlow
  | cons head restAbs =>
      cases head with
      | none =>
          simp [rawInstrOk?, hInstr] at hFlow
      | some dest =>
          simp only [rawInstrOk?, hInstr, Bool.and_eq_true] at hFlow
          obtain ⟨actualDest, rest, hStack, hDest, hAgreesRest⟩ :=
            agrees_cons_inv hAgrees
          have hDestEq : dest = actualDest := agreesVal_some hDest
          subst actualDest
          cases stepFuel with
          | zero =>
              simp [EvmYul.EVM.step] at hStep
          | succ fuel =>
              rw [hDecoded] at hStep
              simp only [Option.getD_some] at hStep
              rw [evm_step_jump_eq_next fuel state none rest dest hStack]
                at hStep
              have hNext : next = gasfulJumpNext state rest dest := by
                simpa using hStep.symm
              subst next
              have hNextPc :
                  (gasfulJumpNext state rest dest).pc = dest := by
                simp [gasfulJumpNext]
              have hNextStack :
                  (gasfulJumpNext state rest dest).stack = rest := by
                simp [gasfulJumpNext]
              have hNextCode :
                  (gasfulJumpNext state rest dest).executionEnv.code =
                    bytes := by
                simpa [gasfulJumpNext, afterEVMInstructionChargeAt,
                  afterMemoryChargeAt, chargeGas] using hCode
              refine ⟨hNextCode, restAbs, ?_, ?_⟩
              · rw [hNextPc]
                exact hFlow.2
              · rw [hNextStack]
                exact hAgreesRest

theorem rawPoint_jumpi_step
    {program : Compact.Program} {bytes : ByteArray} {cert : Cert}
    {state next : EVMState} {located : Compact.Located}
    {astack : AbsStack} {validJumps : Array Word} {stepFuel : Nat}
    (hDecode : Compact.DecodingCorrect program bytes)
    (hMem : located ∈ program.code)
    (hPc : located.pc = state.pc.toNat)
    (hInstr : located.instr = .jumpi)
    (hFlow : rawInstrOk? program cert.table located astack = true)
    (hCode : state.executionEnv.code = bytes)
    (hEntry : memStack cert.table state.pc astack = true)
    (hAgrees : Agrees astack state.stack)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    RawPoint bytes cert.table next := by
  obtain ⟨decoded, hDecodedInstr, hDecoded⟩ :=
    raw_decode hDecode hMem hCode hPc
  rw [hInstr] at hDecodedInstr
  simp [Compact.Instr.decoded?] at hDecodedInstr
  subst decoded
  cases astack with
  | nil =>
      simp [rawInstrOk?, hInstr] at hFlow
  | cons destAbs tailAbs =>
      cases destAbs with
      | none =>
          simp [rawInstrOk?, hInstr] at hFlow
      | some dest =>
          cases tailAbs with
          | nil =>
              simp [rawInstrOk?, hInstr] at hFlow
          | cons condAbs restAbs =>
              obtain ⟨actualDest, actualTail, hStack, hDest,
                  hAgreesTail⟩ :=
                agrees_cons_inv hAgrees
              obtain ⟨cond, rest, hTail, hCond, hAgreesRest⟩ :=
                agrees_cons_inv hAgreesTail
              subst actualTail
              have hDestEq : dest = actualDest := agreesVal_some hDest
              subst actualDest
              have hStack' : state.stack = dest :: cond :: rest := hStack
              have hPair :
                  ((EvmYul.EVM.decode state.executionEnv.code
                      state.pc).getD
                    (EvmYul.Operation.STOP, none)) =
                    (EvmYul.Operation.JUMPI, none) := by
                simp [hDecoded]
              have hEnough : ¬ state.stack.length < 2 := by
                simpa [decodedOperationAt, hPair, EvmYul.EVM.δ] using
                  hPrefix.static.stackLimit.memoryAccess.jumps.stack.stackEnough
              have hBoth := rawJumpi_flow hInstr hFlow hCond
              cases stepFuel with
              | zero =>
                  simp [EvmYul.EVM.step] at hStep
              | succ fuel =>
                  rw [hDecoded] at hStep
                  simp only [Option.getD_some] at hStep
                  rw [evm_step_jumpi_eq_next fuel state none rest dest cond
                    hStack'] at hStep
                  have hNext :
                      next = gasfulJumpiNext state rest dest cond := by
                    simpa using hStep.symm
                  subst next
                  have hNextStack :
                      (gasfulJumpiNext state rest dest cond).stack =
                        rest := by
                    simp [gasfulJumpiNext]
                  have hNextCode :
                      (gasfulJumpiNext state rest dest cond).executionEnv.code =
                        bytes := by
                    simpa [gasfulJumpiNext,
                      afterEVMInstructionChargeAt, afterMemoryChargeAt,
                      chargeGas] using hCode
                  by_cases hCondZero :
                      cond = EvmYul.UInt256.ofNat 0
                  · have hNextPc :
                        (gasfulJumpiNext state rest dest cond).pc =
                          EvmYul.UInt256.ofNat
                            (located.pc + located.instr.byteSize) := by
                      have hStatePc :=
                        state_pc_eq_of_located_toNat hPc
                      simp [gasfulJumpiNext,
                        word_bne_eq_true_iff, hCondZero, hStatePc,
                        hInstr, Compact.Instr.byteSize,
                        uint256_ofNat_add]
                    refine ⟨hNextCode, restAbs, ?_, ?_⟩
                    · rw [hNextPc]
                      exact hBoth.2 hCondZero
                    · rw [hNextStack]
                      exact hAgreesRest
                  · have hCondNe :
                        cond != EvmYul.UInt256.ofNat 0 := by
                      exact word_bne_eq_true_iff.mpr hCondZero
                    have hNextPc :
                        (gasfulJumpiNext state rest dest cond).pc =
                          dest := by
                      simp [gasfulJumpiNext, hCondNe]
                    refine ⟨hNextCode, restAbs, ?_, ?_⟩
                    · rw [hNextPc]
                      exact hBoth.1 hCondZero
                    · rw [hNextStack]
                      exact hAgreesRest

theorem raw_prim_decode
    {program : Compact.Program} {bytes : ByteArray}
    {state : EVMState} {located : Compact.Located} {op : PrimOp}
    (hDecode : Compact.DecodingCorrect program bytes)
    (hMem : located ∈ program.code)
    (hPc : located.pc = state.pc.toNat)
    (hInstr : located.instr = .prim op)
    (hCode : state.executionEnv.code = bytes) :
    EvmYul.EVM.decode state.executionEnv.code state.pc =
      some (op.toEVM, none) := by
  obtain ⟨decoded, hDecodedInstr, hDecoded⟩ :=
    raw_decode hDecode hMem hCode hPc
  rw [hInstr] at hDecodedInstr
  simp [Compact.Instr.decoded?] at hDecodedInstr
  subst decoded
  exact hDecoded

theorem raw_prim_flow
    {program : Compact.Program} {table : StackTable}
    {located : Compact.Located} {op : PrimOp}
    {astack astack' : AbsStack}
    (hInstr : located.instr = .prim op)
    (hInvalid : op ≠ .invalid)
    {input output : Nat}
    (hArity : op.stackArity? = some (input, output))
    (hFlow : rawInstrOk? program table located astack = true)
    (hAbs : absPrim? op astack = some astack') :
    memStack table
        (EvmYul.UInt256.ofNat
          (located.pc + located.instr.byteSize)) astack' =
      true := by
  simp only [rawInstrOk?, hInstr, if_neg hInvalid, hArity] at hFlow
  rw [hAbs] at hFlow
  simpa [hInstr] using hFlow

theorem rawPoint_prim_continuing_step
    {program : Compact.Program} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {state next : EVMState}
    {located : Compact.Located} {op : PrimOp} {primStep : PrimStep}
    {astack : AbsStack} {stepFuel : Nat}
    (hDecode : Compact.DecodingCorrect program bytes)
    (hMem : located ∈ program.code)
    (hPc : located.pc = state.pc.toNat)
    (hInstr : located.instr = .prim op)
    (hInvalid : op ≠ .invalid)
    (hContinuing : op.continuingStep? = some primStep)
    (hLocal : FrameLocalPrimOp op)
    (hFlow : rawInstrOk? program cert.table located astack = true)
    (hCode : state.executionEnv.code = bytes)
    (hAgrees : Agrees astack state.stack)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    RawPoint bytes cert.table next := by
  have hDecoded :=
    raw_prim_decode hDecode hMem hPc hInstr hCode
  cases stepFuel with
  | zero =>
      simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      have hDecodedOp : decodedOperationAt state = op.toEVM := by
        simp [decodedOperationAt, hDecoded]
      have hStaticPermits : continuingPrimStaticPermits state op :=
        continuingPrimStaticPermits_of_static_check hPrefix.static
          hDecodedOp
      have hGasful :
          EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
              (some (op.toEVM, none)) (afterMemoryChargeAt state) =
            .ok next := by
        simpa [hDecoded] using hStep
      have hPrim :
          op.step (afterEVMInstructionChargeAt state) = .ok next := by
        rw [← hGasful]
        exact
          (evm_step_continuing_prim_after_charges hContinuing trivial
            hStaticPermits).symm
      obtain ⟨input, output, hArity⟩ :=
        stackArity?_isSome_of_continuingStep hContinuing
      cases hAbs : absPrim? op astack with
      | none =>
          have hImpossible :
              rawInstrOk? program cert.table located astack = false := by
            simp [rawInstrOk?, hInstr, hInvalid, hArity, hAbs]
          rw [hImpossible] at hFlow
          contradiction
      | some astack' =>
          rw [PrimOp.step_eq_continuingStep_run hContinuing] at hPrim
          have hLocalStep :=
            frameLocalStep_of_continuingStep hLocal hContinuing
          have hNextCode : next.executionEnv.code = bytes := by
            calc
              next.executionEnv.code =
                  (afterEVMInstructionChargeAt state).executionEnv.code :=
                hLocalStep.run_code hPrim
              _ = state.executionEnv.code := by
                simp [afterEVMInstructionChargeAt, afterMemoryChargeAt,
                  afterDynamicChargeAt, chargeGas]
              _ = bytes := hCode
          have hNextPcRaw := PrimStep.run_pc hPrim
          have hStatePc := state_pc_eq_of_located_toNat hPc
          have hNextPc :
              next.pc =
                EvmYul.UInt256.ofNat
                  (located.pc + located.instr.byteSize) := by
            calc
              next.pc =
                  (afterEVMInstructionChargeAt state).pc +
                    EvmYul.UInt256.ofNat 1 :=
                hNextPcRaw
              _ = state.pc + EvmYul.UInt256.ofNat 1 := by
                simp [afterEVMInstructionChargeAt, afterMemoryChargeAt,
                  afterDynamicChargeAt, chargeGas]
              _ = EvmYul.UInt256.ofNat (located.pc + 1) := by
                rw [hStatePc, uint256_ofNat_add]
              _ =
                  EvmYul.UInt256.ofNat
                    (located.pc + located.instr.byteSize) := by
                simp [hInstr, Compact.Instr.byteSize]
          refine ⟨hNextCode, astack', ?_, ?_⟩
          · rw [hNextPc]
            exact raw_prim_flow hInstr hInvalid hArity hFlow hAbs
          · exact
              agrees_absPrim_step hContinuing hArity hAbs
                (by
                  rw [afterEVMInstructionChargeAt_stack]
                  exact hAgrees)
                (by
                  rw [PrimOp.step_eq_continuingStep_run hContinuing]
                  exact hPrim)

theorem rawPoint_resource_step
    {program : Compact.Program} {bytes : ByteArray} {cert : Cert}
    {state next : EVMState} {located : Compact.Located}
    {astack : AbsStack} {stepFuel : Nat}
    (hDecode : Compact.DecodingCorrect program bytes)
    (hMem : located ∈ program.code)
    (hPc : located.pc = state.pc.toNat)
    (kind : Simulation.ResourceQuery)
    (hInstr : located.instr = .prim (resourcePrimOp kind))
    (hFlow : rawInstrOk? program cert.table located astack = true)
    (hCode : state.executionEnv.code = bytes)
    (hAgrees : Agrees astack state.stack)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    RawPoint bytes cert.table next := by
  have hDecoded :=
    raw_prim_decode hDecode hMem hPc hInstr hCode
  cases stepFuel with
  | zero =>
      simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      have hActual :
          EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
              (some ((resourcePrimOp kind).toEVM, none))
              (afterMemoryChargeAt state) = .ok next := by
        simpa [hDecoded] using hStep
      rw [evm_step_resource_eq] at hActual
      cases hActual
      have hInvalid : resourcePrimOp kind ≠ .invalid := by
        cases kind <;> simp [resourcePrimOp]
      have hArity :
          (resourcePrimOp kind).stackArity? = some (0, 1) := by
        cases kind <;> rfl
      have hAbs :
          absPrim? (resourcePrimOp kind) astack =
            some (none :: astack) := by
        cases kind <;>
          simp [absPrim?, PrimOp.continuingStep?, PrimOp.stackArity?,
            resourcePrimOp, EvmYul.EVM.δ, EvmYul.EVM.α, PrimOp.toEVM,
            List.replicate]
      have hStatePc := state_pc_eq_of_located_toNat hPc
      have hNextPc :
          (gasfulResourceNext kind state).pc =
            EvmYul.UInt256.ofNat
              (located.pc + located.instr.byteSize) := by
        simp [gasfulResourceNext, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, afterDynamicChargeAt, chargeGas,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, hStatePc, hInstr,
          Compact.Instr.byteSize, uint256_ofNat_add]
      have hNextCode :
          (gasfulResourceNext kind state).executionEnv.code = bytes := by
        simpa [gasfulResourceNext, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, afterDynamicChargeAt, chargeGas] using
          hCode
      have hNextLen :
          (gasfulResourceNext kind state).stack.length =
            state.stack.length + 1 := by
        cases kind <;>
          simp [gasfulResourceNext, afterEVMInstructionChargeAt,
            afterMemoryChargeAt, afterDynamicChargeAt, chargeGas,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC, EvmYul.Stack.push]
      have hNextTail :
          (gasfulResourceNext kind state).stack.tail = state.stack := by
        cases kind <;>
          simp [gasfulResourceNext, afterEVMInstructionChargeAt,
            afterMemoryChargeAt, afterDynamicChargeAt, chargeGas,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC, EvmYul.Stack.push]
      cases hNS : (gasfulResourceNext kind state).stack with
      | nil =>
          rw [hNS] at hNextLen
          simp at hNextLen
      | cons value tail =>
          have hTail : tail = state.stack := by
            have hTail' := hNextTail
            rw [hNS] at hTail'
            simpa using hTail'
          subst tail
          refine ⟨hNextCode, none :: astack, ?_, ?_⟩
          · rw [hNextPc]
            exact raw_prim_flow hInstr hInvalid hArity hFlow hAbs
          · rw [hNS]
            exact agrees_cons agreesVal_none hAgrees

theorem rawPoint_pc_step
    {program : Compact.Program} {bytes : ByteArray} {cert : Cert}
    {state next : EVMState} {located : Compact.Located}
    {astack : AbsStack} {stepFuel : Nat}
    (hDecode : Compact.DecodingCorrect program bytes)
    (hMem : located ∈ program.code)
    (hPc : located.pc = state.pc.toNat)
    (hInstr : located.instr = .prim .pc)
    (hFlow : rawInstrOk? program cert.table located astack = true)
    (hCode : state.executionEnv.code = bytes)
    (hAgrees : Agrees astack state.stack)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    RawPoint bytes cert.table next := by
  have hDecoded :=
    raw_prim_decode hDecode hMem hPc hInstr hCode
  cases stepFuel with
  | zero =>
      simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      have hActual :
          EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
              (some (EvmYul.Operation.PC, none))
              (afterMemoryChargeAt state) = .ok next := by
        simpa [hDecoded, PrimOp.toEVM] using hStep
      rw [evm_step_pc_eq_next] at hActual
      cases hActual
      have hInvalid : PrimOp.pc ≠ .invalid := by simp
      have hArity : PrimOp.pc.stackArity? = some (0, 1) := rfl
      have hAbs :
          absPrim? PrimOp.pc astack = some (none :: astack) := by
        simp [absPrim?, PrimOp.continuingStep?, PrimOp.stackArity?,
          EvmYul.EVM.δ, EvmYul.EVM.α, PrimOp.toEVM, List.replicate]
      have hStatePc := state_pc_eq_of_located_toNat hPc
      have hNextPc :
          (gasfulPcNext state).pc =
            EvmYul.UInt256.ofNat
              (located.pc + located.instr.byteSize) := by
        simp [gasfulPcNext, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, afterDynamicChargeAt, chargeGas,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, hStatePc, hInstr,
          Compact.Instr.byteSize, uint256_ofNat_add]
      have hNextCode :
          (gasfulPcNext state).executionEnv.code = bytes := by
        simpa [gasfulPcNext, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, afterDynamicChargeAt, chargeGas] using hCode
      have hNextLen :
          (gasfulPcNext state).stack.length =
            state.stack.length + 1 := by
        simp [gasfulPcNext, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, afterDynamicChargeAt, chargeGas,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push]
      have hNextTail :
          (gasfulPcNext state).stack.tail = state.stack := by
        simp [gasfulPcNext, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, afterDynamicChargeAt, chargeGas,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push]
      cases hNS : (gasfulPcNext state).stack with
      | nil =>
          rw [hNS] at hNextLen
          simp at hNextLen
      | cons value tail =>
          have hTail : tail = state.stack := by
            have hTail' := hNextTail
            rw [hNS] at hTail'
            simpa using hTail'
          subst tail
          refine ⟨hNextCode, none :: astack, ?_, ?_⟩
          · rw [hNextPc]
            exact raw_prim_flow hInstr hInvalid hArity hFlow hAbs
          · rw [hNS]
            exact agrees_cons agreesVal_none hAgrees

theorem rawPoint_call_step
    {program : Compact.Program} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {state next : EVMState}
    {located : Compact.Located} {astack : AbsStack} {stepFuel : Nat}
    (hDecode : Compact.DecodingCorrect program bytes)
    (hMem : located ∈ program.code)
    (hPc : located.pc = state.pc.toNat)
    (kind : Simulation.CallKind)
    (hInstr : located.instr = .prim (callPrimOp kind))
    (hFlow : rawInstrOk? program cert.table located astack = true)
    (hCode : state.executionEnv.code = bytes)
    (hAgrees : Agrees astack state.stack)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    RawPoint bytes cert.table next := by
  have hDecoded :=
    raw_prim_decode hDecode hMem hPc hInstr hCode
  have hOpEq : (callPrimOp kind).toEVM = kind.toEVMOperation := by
    cases kind <;> rfl
  have hDecodedOp : decodedOperationAt state = kind.toEVMOperation := by
    simp [decodedOperationAt, hDecoded, hOpEq]
  obtain ⟨rest, operands, hOperands⟩ :=
    call_operands_of_stackEnough_kind kind hPrefix.static.stackLimit
      hDecodedOp
  cases stepFuel with
  | zero =>
      simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      have hActual :
          EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
              (some (kind.toEVMOperation, none))
              (afterMemoryChargeAt state) = .ok next := by
        simpa [hDecoded, hOpEq] using hStep
      obtain ⟨response, hResponse⟩ :=
        evm_step_call_responseStateRel_at kind hDecodedOp hOperands hActual
      have hStack :=
        CallKind.stack_eq_args_append_of_evmOperands hOperands
      have hLength :
          state.stack.length =
            (Simulation.CallKind.args kind operands).length +
              rest.length := by
        rw [hStack]
        simp
      have hNextLength : next.stack.length = rest.length + 1 := by
        have hStackEq := hResponse.openStateRel.stack_eq
        rw [hStackEq]
        simp [InteractionSemantics.EVMState.finishCall,
          EvmYul.EVM.State.incrPC]
      have hNextTail : next.stack.tail = rest := by
        have hStackEq := hResponse.openStateRel.stack_eq
        rw [hStackEq]
        simp [InteractionSemantics.EVMState.finishCall,
          EvmYul.EVM.State.incrPC]
      have hStatePc := state_pc_eq_of_located_toNat hPc
      have hNextPc :
          next.pc =
            EvmYul.UInt256.ofNat
              (located.pc + located.instr.byteSize) := by
        calc
          next.pc =
              (InteractionSemantics.EVMState.finishCall
                (afterDynamicChargeAt state) rest operands.callLocal
                  response).pc :=
            hResponse.pc_eq
          _ = state.pc + EvmYul.UInt256.ofNat 1 := by
            simp [InteractionSemantics.EVMState.finishCall,
              InteractionSemantics.EVMState.installWorld,
              afterDynamicChargeAt, afterMemoryChargeAt, chargeGas,
              EvmYul.EVM.State.incrPC]
          _ = EvmYul.UInt256.ofNat (located.pc + 1) := by
            rw [hStatePc, uint256_ofNat_add]
          _ =
              EvmYul.UInt256.ofNat
                (located.pc + located.instr.byteSize) := by
            simp [hInstr, Compact.Instr.byteSize]
      have hNextCode : next.executionEnv.code = bytes := by
        calc
          next.executionEnv.code =
              (InteractionSemantics.EVMState.finishCall
                (afterDynamicChargeAt state) rest operands.callLocal
                  response).executionEnv.code :=
            hResponse.openStateRel.code_eq
          _ = state.executionEnv.code := by
            simp [InteractionSemantics.EVMState.finishCall,
              InteractionSemantics.EVMState.installWorld,
              afterDynamicChargeAt, afterMemoryChargeAt, chargeGas,
              EvmYul.EVM.State.incrPC,
              Simulation.OpenWorld.installEVMShared,
              Simulation.OpenWorld.installEVM]
          _ = bytes := hCode
      have hArity := callPrimOp_args_arity kind operands
      have hInvalid : callPrimOp kind ≠ .invalid := by
        cases kind <;> simp [callPrimOp]
      have hNe : callPrimOp kind ≠ .eq := by
        cases kind <;> simp [callPrimOp]
      have hCont : (callPrimOp kind).continuingStep? = none := by
        cases kind <;> rfl
      have hBound :
          (Simulation.CallKind.args kind operands).length ≤
            astack.length := by
        rw [agrees_length hAgrees]
        omega
      have hAbs :
          absPrim? (callPrimOp kind) astack =
            some
              (none ::
                astack.drop
                  (Simulation.CallKind.args kind operands).length) := by
        simp [absPrim?, hNe, hCont, hArity, List.replicate]
        simpa using hBound
      obtain ⟨value, tail, hNextStack⟩ :
          ∃ value tail, next.stack = value :: tail := by
        cases hCase : next.stack with
        | nil =>
            rw [hCase] at hNextLength
            simp at hNextLength
        | cons value tail =>
            exact ⟨value, tail, rfl⟩
      have hTail : tail = rest := by
        have hTail' := hNextTail
        rw [hNextStack] at hTail'
        simpa using hTail'
      subst tail
      refine
        ⟨hNextCode,
          none ::
            astack.drop
              (Simulation.CallKind.args kind operands).length,
          ?_, ?_⟩
      · rw [hNextPc]
        exact raw_prim_flow hInstr hInvalid hArity hFlow hAbs
      · rw [hNextStack]
        refine agrees_cons agreesVal_none ?_
        have hDrop :=
          agrees_drop hAgrees
            (Simulation.CallKind.args kind operands).length
        rw [hStack, List.drop_left] at hDrop
        exact hDrop

theorem rawPoint_create_step
    {program : Compact.Program} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {state next : EVMState}
    {located : Compact.Located} {astack : AbsStack} {stepFuel : Nat}
    (hDecode : Compact.DecodingCorrect program bytes)
    (hMem : located ∈ program.code)
    (hPc : located.pc = state.pc.toNat)
    (kind : Simulation.CreateKind)
    (hInstr : located.instr = .prim (createPrimOp kind))
    (hFlow : rawInstrOk? program cert.table located astack = true)
    (hCode : state.executionEnv.code = bytes)
    (hAgrees : Agrees astack state.stack)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    RawPoint bytes cert.table next := by
  have hDecoded :=
    raw_prim_decode hDecode hMem hPc hInstr hCode
  have hOpEq :
      (createPrimOp kind).toEVM = kind.toEVMOperation := by
    cases kind <;> rfl
  have hDecodedOp : decodedOperationAt state = kind.toEVMOperation := by
    simp [decodedOperationAt, hDecoded, hOpEq]
  obtain ⟨rest, operands, hOperands⟩ :=
    create_operands_of_stackEnough_kind kind hPrefix.static.stackLimit
      hDecodedOp
  cases stepFuel with
  | zero =>
      simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      have hActual :
          EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
              (some (kind.toEVMOperation, none))
              (afterMemoryChargeAt state) = .ok next := by
        simpa [hDecoded, hOpEq] using hStep
      obtain ⟨response, hResponse⟩ :=
        evm_step_create_responseStateRel_at kind hDecodedOp hOperands
          hActual
      have hStack :=
        CreateKind.stack_eq_args_append_of_evmOperands hOperands
      have hLength :
          state.stack.length =
            (Simulation.CreateKind.args kind operands).length +
              rest.length := by
        rw [hStack]
        simp
      have hNextLength : next.stack.length = rest.length + 1 := by
        have hStackEq := hResponse.openStateRel.stack_eq
        rw [hStackEq]
        simp [InteractionSemantics.EVMState.finishCreate,
          EvmYul.EVM.State.incrPC]
      have hNextTail : next.stack.tail = rest := by
        have hStackEq := hResponse.openStateRel.stack_eq
        rw [hStackEq]
        simp [InteractionSemantics.EVMState.finishCreate,
          EvmYul.EVM.State.incrPC]
      have hStatePc := state_pc_eq_of_located_toNat hPc
      have hNextPc :
          next.pc =
            EvmYul.UInt256.ofNat
              (located.pc + located.instr.byteSize) := by
        calc
          next.pc =
              (InteractionSemantics.EVMState.finishCreate
                (afterDynamicChargeAt state) rest operands.createLocal
                  response).pc :=
            hResponse.pc_eq
          _ = state.pc + EvmYul.UInt256.ofNat 1 := by
            simp [InteractionSemantics.EVMState.finishCreate,
              InteractionSemantics.EVMState.installWorld,
              afterDynamicChargeAt, afterMemoryChargeAt, chargeGas,
              EvmYul.EVM.State.incrPC]
          _ = EvmYul.UInt256.ofNat (located.pc + 1) := by
            rw [hStatePc, uint256_ofNat_add]
          _ =
              EvmYul.UInt256.ofNat
                (located.pc + located.instr.byteSize) := by
            simp [hInstr, Compact.Instr.byteSize]
      have hNextCode : next.executionEnv.code = bytes := by
        calc
          next.executionEnv.code =
              (InteractionSemantics.EVMState.finishCreate
                (afterDynamicChargeAt state) rest operands.createLocal
                  response).executionEnv.code :=
            hResponse.openStateRel.code_eq
          _ = state.executionEnv.code := by
            simp [InteractionSemantics.EVMState.finishCreate,
              InteractionSemantics.EVMState.installWorld,
              afterDynamicChargeAt, afterMemoryChargeAt, chargeGas,
              EvmYul.EVM.State.incrPC,
              Simulation.OpenWorld.installEVMShared,
              Simulation.OpenWorld.installEVM]
          _ = bytes := hCode
      have hArity := createPrimOp_args_arity kind operands
      have hInvalid : createPrimOp kind ≠ .invalid := by
        cases kind <;> simp [createPrimOp]
      have hNe : createPrimOp kind ≠ .eq := by
        cases kind <;> simp [createPrimOp]
      have hCont : (createPrimOp kind).continuingStep? = none := by
        cases kind <;> rfl
      have hBound :
          (Simulation.CreateKind.args kind operands).length ≤
            astack.length := by
        rw [agrees_length hAgrees]
        omega
      have hAbs :
          absPrim? (createPrimOp kind) astack =
            some
              (none ::
                astack.drop
                  (Simulation.CreateKind.args kind operands).length) := by
        simp [absPrim?, hNe, hCont, hArity, List.replicate]
        simpa using hBound
      obtain ⟨value, tail, hNextStack⟩ :
          ∃ value tail, next.stack = value :: tail := by
        cases hCase : next.stack with
        | nil =>
            rw [hCase] at hNextLength
            simp at hNextLength
        | cons value tail =>
            exact ⟨value, tail, rfl⟩
      have hTail : tail = rest := by
        have hTail' := hNextTail
        rw [hNextStack] at hTail'
        simpa using hTail'
      subst tail
      refine
        ⟨hNextCode,
          none ::
            astack.drop
              (Simulation.CreateKind.args kind operands).length,
          ?_, ?_⟩
      · rw [hNextPc]
        exact raw_prim_flow hInstr hInvalid hArity hFlow hAbs
      · rw [hNextStack]
        refine agrees_cons agreesVal_none ?_
        have hDrop :=
          agrees_drop hAgrees
            (Simulation.CreateKind.args kind operands).length
        rw [hStack, List.drop_left] at hDrop
        exact hDrop

theorem raw_sentinel_no_success
    {program : Compact.Program} {bytes : ByteArray}
    {state next : EVMState} {stepFuel : Nat}
    (hSentinel :
      Compact.decodeAt bytes
        (Compact.Program.codeByteLength program.code)
        (.prim .invalid))
    (hCode : state.executionEnv.code = bytes)
    (hPc :
      state.pc =
        EvmYul.UInt256.ofNat
          (Compact.Program.codeByteLength program.code))
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    False := by
  obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ := hSentinel
  simp [Compact.Instr.decoded?] at hInstrDecoded
  subst decoded
  have hDecoded :
      EvmYul.EVM.decode state.executionEnv.code state.pc =
        some (EvmYul.Operation.INVALID, none) := by
    simpa [hCode, hPc] using hBytesDecoded
  cases stepFuel with
  | zero =>
      simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      rw [hDecoded] at hStep
      simp only [Option.getD_some] at hStep
      change
        EvmYul.step (τ := .EVM) EvmYul.Operation.INVALID none
            { { afterMemoryChargeAt state with
                  execLength := (afterMemoryChargeAt state).execLength + 1 } with
              gasAvailable :=
                (afterMemoryChargeAt state).gasAvailable -
                  EvmYul.UInt256.ofNat (dynamicGasCostAt state) } =
          Except.ok next at hStep
      change
        (Except.error EvmYul.EVM.ExecutionException.InvalidInstruction :
            Except EVMException EVMState) =
          Except.ok next at hStep
      cases hStep

theorem rawPoint_step
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {current next : EVMState}
    {stepFuel : Nat}
    (hProgram : artifact.program.Valid)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hRaw : rawCheck? artifact cert = true)
    (hSentinel :
      Compact.decodeAt bytes
        (Compact.Program.codeByteLength artifact.program.code)
        (.prim .invalid))
    (hPoint : RawPoint bytes cert.table current)
    (hPrefix : XSstoreStipendChecksPass validJumps current)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt current)
        (some
          ((EvmYul.EVM.decode current.executionEnv.code current.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt current) = .ok next)
    (hContinues :
      haltOutputAt next (decodedOperationAt current) = none) :
    RawPoint bytes cert.table next := by
  rcases hPoint with ⟨hCode, astack, hEntry, hAgrees⟩
  rcases rawCheck?_classify hRaw hEntry with hEnd |
      ⟨located, hMem, hPc, hFlow⟩
  · exact False.elim
      (raw_sentinel_no_success hSentinel hCode hEnd hStep)
  · generalize hInstr : located.instr = instr
    cases instr with
    | push width value =>
        have hLocatedValid :=
          (List.forall_iff_forall_mem.mp hProgram) located hMem
        rw [hInstr] at hLocatedValid
        have hFits : Compact.FitsWidth width value.toNat := by
          simpa [Compact.Instr.Valid] using hLocatedValid
        exact
          rawPoint_push_step hDecode hMem hPc hInstr hFits hFlow hCode
            hEntry hAgrees hStep
    | push0 =>
        exact
          rawPoint_push0_step hDecode hMem hPc hInstr hFlow hCode hEntry
            hAgrees hStep
    | jump =>
        exact
          rawPoint_jump_step hDecode hMem hPc hInstr hFlow hCode hEntry
            hAgrees hPrefix hStep
    | jumpi =>
        exact
          rawPoint_jumpi_step hDecode hMem hPc hInstr hFlow hCode hEntry
            hAgrees hPrefix hStep
    | jumpdest =>
        exact
          rawPoint_jumpdest_step hDecode hMem hPc hInstr hFlow hCode hEntry
            hAgrees hStep
    | prim op =>
        have hDecoded :=
          raw_prim_decode hDecode hMem hPc hInstr hCode
        by_cases hPcOp : op = .pc
        · subst op
          exact
            rawPoint_pc_step hDecode hMem hPc hInstr hFlow hCode hAgrees
              hStep
        · by_cases hGasOp : op = .gas
          · subst op
            exact
              rawPoint_resource_step hDecode hMem hPc .gas
                (by simpa [resourcePrimOp] using hInstr) hFlow hCode
                hAgrees hStep
          · by_cases hMsizeOp : op = .msize
            · subst op
              exact
                rawPoint_resource_step hDecode hMem hPc .msize
                  (by simpa [resourcePrimOp] using hInstr) hFlow hCode
                  hAgrees hStep
            · cases hContinuing : op.continuingStep? with
              | some primStep =>
                  have hDecodedOp :
                      decodedOperationAt current = op.toEVM := by
                    simp [decodedOperationAt, hDecoded]
                  have hOpcodeValid :
                      EvmYul.EVM.δ op.toEVM ≠ none := by
                    have hRawValid :=
                      hPrefix.static.stackLimit.memoryAccess.jumps.stack.opcodeValid_raw
                    simpa [decodedOperationAt, hDecoded] using hRawValid
                  have hInvalid : op ≠ .invalid := by
                    intro hInvalidEq
                    subst op
                    simp [PrimOp.toEVM, EvmYul.EVM.δ] at hOpcodeValid
                  have hLocal : FrameLocalPrimOp op :=
                    frameLocalPrimOp_of_continuingStep hContinuing
                      hMsizeOp hInvalid
                  exact
                    rawPoint_prim_continuing_step hDecode hMem hPc hInstr
                      hInvalid hContinuing hLocal hFlow hCode hAgrees
                      hPrefix hStep
              | none =>
                  by_cases hStopOp : op = .stop
                  · subst op
                    have hDecodedOp :
                        decodedOperationAt current =
                          EvmYul.Operation.STOP := by
                      simp [decodedOperationAt, hDecoded, PrimOp.toEVM]
                    simp [hDecodedOp, haltOutputAt] at hContinues
                  · by_cases hReturnOp : op = .return
                    · subst op
                      have hDecodedOp :
                          decodedOperationAt current =
                            EvmYul.Operation.RETURN := by
                        simp [decodedOperationAt, hDecoded, PrimOp.toEVM]
                      simp [hDecodedOp, haltOutputAt] at hContinues
                    · by_cases hRevertOp : op = .revert
                      · subst op
                        have hDecodedOp :
                            decodedOperationAt current =
                              EvmYul.Operation.REVERT := by
                          simp [decodedOperationAt, hDecoded, PrimOp.toEVM]
                        simp [hDecodedOp, haltOutputAt] at hContinues
                      · by_cases hSelfdestructOp : op = .selfdestruct
                        · subst op
                          have hDecodedOp :
                              decodedOperationAt current =
                                EvmYul.Operation.SELFDESTRUCT := by
                            simp [decodedOperationAt, hDecoded,
                              PrimOp.toEVM]
                          simp [hDecodedOp, haltOutputAt] at hContinues
                        · have hOpcodeValid :
                              EvmYul.EVM.δ op.toEVM ≠ none := by
                            have hRawValid :=
                              hPrefix.static.stackLimit.memoryAccess.jumps.stack.opcodeValid_raw
                            simpa [decodedOperationAt, hDecoded] using
                              hRawValid
                          rcases
                              primOp_external_of_no_continuing op
                                hOpcodeValid hPcOp hGasOp hMsizeOp
                                hStopOp hReturnOp hRevertOp
                                hSelfdestructOp hContinuing with
                            ⟨kind, hCall⟩ | ⟨kind, hCreate⟩
                          · subst op
                            exact
                              rawPoint_call_step hDecode hMem hPc kind
                                hInstr hFlow hCode hAgrees hPrefix hStep
                          · subst op
                            exact
                              rawPoint_create_step hDecode hMem hPc kind
                                hInstr hFlow hCode hAgrees hPrefix hStep

theorem rawPoint_initial
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {initial : EVMState}
    (hRaw : rawCheck? artifact cert = true)
    (hCode : initial.executionEnv.code = bytes)
    (hPc : initial.pc = EvmYul.UInt256.ofNat 0)
    (hStack : initial.stack = []) :
    RawPoint bytes cert.table initial := by
  refine ⟨hCode, [], ?_, ?_⟩
  · rw [hPc]
    exact rawCheck?_anchor hRaw
  · rw [hStack]
    exact List.Forall₂.nil

theorem reach_rawPoint
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {initial : EVMState}
    (hProgram : artifact.program.Valid)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hRaw : rawCheck? artifact cert = true)
    (hSentinel :
      Compact.decodeAt bytes
        (Compact.Program.codeByteLength artifact.program.code)
        (.prim .invalid))
    (hInitial : RawPoint bytes cert.table initial) :
    ∀ state, FrameReachable validJumps initial state →
      RawPoint bytes cert.table state := by
  intro state hReach
  induction hReach with
  | initial =>
      exact hInitial
  | @next current next stepFuel hReach hPrefix hStep hContinues ih =>
      exact
        rawPoint_step hProgram hDecode hRaw hSentinel ih hPrefix hStep
          hContinues

theorem frameLayoutInvariant_of_rawCert
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {initial : EVMState}
    (hProgram : artifact.program.Valid)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hRaw : rawCheck? artifact cert = true)
    (hSentinel :
      Compact.decodeAt bytes
        (Compact.Program.codeByteLength artifact.program.code)
        (.prim .invalid))
    (hInitial : RawPoint bytes cert.table initial) :
    FrameLayoutInvariant artifact.program bytes validJumps initial := by
  intro state hReach
  have hPoint :=
    reach_rawPoint hProgram hDecode hRaw hSentinel hInitial state hReach
  rcases hPoint with ⟨hCode, astack, hEntry, hAgrees⟩
  refine ⟨hCode, ?_⟩
  rcases rawCheck?_classify hRaw hEntry with hEnd |
      ⟨located, hMem, hPc, hFlow⟩
  · exact Or.inr hEnd
  · exact
      Or.inl
        ⟨located, hMem, state_pc_eq_of_located_toNat hPc⟩

theorem raw_decoded_alpha_le_delta_succ
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {state : EVMState}
    (hProgram : artifact.program.Valid)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hRaw : rawCheck? artifact cert = true)
    (hSentinel :
      Compact.decodeAt bytes
        (Compact.Program.codeByteLength artifact.program.code)
        (.prim .invalid))
    (hPoint : RawPoint bytes cert.table state) :
    (EvmYul.EVM.α (decodedOperationAt state)).getD 0 ≤
        (EvmYul.EVM.δ (decodedOperationAt state)).getD 0 + 1 ∧
      (EvmYul.EVM.δ (decodedOperationAt state)).getD 0 ≤ 20 := by
  rcases hPoint with ⟨hCode, astack, hEntry, hAgrees⟩
  rcases rawCheck?_classify hRaw hEntry with hEnd |
      ⟨located, hMem, hPc, hFlow⟩
  · obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ := hSentinel
    simp [Compact.Instr.decoded?] at hInstrDecoded
    subst decoded
    have hDecoded :
        EvmYul.EVM.decode state.executionEnv.code state.pc =
          some (EvmYul.Operation.INVALID, none) := by
      simpa [hCode, hEnd] using hBytesDecoded
    have hGoal :=
      prim_alpha_le_delta_succ PrimOp.invalid
    simpa [decodedOperationAt, hDecoded, PrimOp.toEVM] using hGoal
  · generalize hInstr : located.instr = instr
    cases instr with
    | push width value =>
        have hLocatedValid :=
          (List.forall_iff_forall_mem.mp hProgram) located hMem
        rw [hInstr] at hLocatedValid
        have hFits : Compact.FitsWidth width value.toNat := by
          simpa [Compact.Instr.Valid] using hLocatedValid
        obtain ⟨op, hOp⟩ :=
          Compact.exists_pushOp_of_width ⟨hFits.1, hFits.2.1⟩
        obtain ⟨decoded, hInstrDecoded, hDecoded⟩ :=
          raw_decode hDecode hMem hCode hPc
        rw [hInstr] at hInstrDecoded
        simp [Compact.Instr.decoded?, hOp] at hInstrDecoded
        subst decoded
        have hGoal := pushOp_alpha_le_delta_succ hFits hOp
        simpa [decodedOperationAt, hDecoded] using hGoal
    | push0 =>
        obtain ⟨decoded, hInstrDecoded, hDecoded⟩ :=
          raw_decode hDecode hMem hCode hPc
        rw [hInstr] at hInstrDecoded
        simp [Compact.Instr.decoded?] at hInstrDecoded
        subst decoded
        have hGoal :
            (EvmYul.EVM.α EvmYul.Operation.PUSH0).getD 0 ≤
                (EvmYul.EVM.δ EvmYul.Operation.PUSH0).getD 0 + 1 ∧
              (EvmYul.EVM.δ EvmYul.Operation.PUSH0).getD 0 ≤ 20 :=
          ⟨by decide, by decide⟩
        simpa [decodedOperationAt, hDecoded] using hGoal
    | jump =>
        obtain ⟨decoded, hInstrDecoded, hDecoded⟩ :=
          raw_decode hDecode hMem hCode hPc
        rw [hInstr] at hInstrDecoded
        simp [Compact.Instr.decoded?] at hInstrDecoded
        subst decoded
        have hGoal :
            (EvmYul.EVM.α EvmYul.Operation.JUMP).getD 0 ≤
                (EvmYul.EVM.δ EvmYul.Operation.JUMP).getD 0 + 1 ∧
              (EvmYul.EVM.δ EvmYul.Operation.JUMP).getD 0 ≤ 20 :=
          ⟨by decide, by decide⟩
        simpa [decodedOperationAt, hDecoded] using hGoal
    | jumpi =>
        obtain ⟨decoded, hInstrDecoded, hDecoded⟩ :=
          raw_decode hDecode hMem hCode hPc
        rw [hInstr] at hInstrDecoded
        simp [Compact.Instr.decoded?] at hInstrDecoded
        subst decoded
        have hGoal :
            (EvmYul.EVM.α EvmYul.Operation.JUMPI).getD 0 ≤
                (EvmYul.EVM.δ EvmYul.Operation.JUMPI).getD 0 + 1 ∧
              (EvmYul.EVM.δ EvmYul.Operation.JUMPI).getD 0 ≤ 20 :=
          ⟨by decide, by decide⟩
        simpa [decodedOperationAt, hDecoded] using hGoal
    | jumpdest =>
        obtain ⟨decoded, hInstrDecoded, hDecoded⟩ :=
          raw_decode hDecode hMem hCode hPc
        rw [hInstr] at hInstrDecoded
        simp [Compact.Instr.decoded?] at hInstrDecoded
        subst decoded
        have hGoal :
            (EvmYul.EVM.α EvmYul.Operation.JUMPDEST).getD 0 ≤
                (EvmYul.EVM.δ EvmYul.Operation.JUMPDEST).getD 0 + 1 ∧
              (EvmYul.EVM.δ EvmYul.Operation.JUMPDEST).getD 0 ≤ 20 :=
          ⟨by decide, by decide⟩
        simpa [decodedOperationAt, hDecoded] using hGoal
    | prim op =>
        have hDecoded :=
          raw_prim_decode hDecode hMem hPc hInstr hCode
        have hGoal := prim_alpha_le_delta_succ op
        simpa [decodedOperationAt, hDecoded] using hGoal

theorem raw_noOverflow_of_point
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {state : EVMState}
    (hProgram : artifact.program.Valid)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hRaw : rawCheck? artifact cert = true)
    (hSentinel :
      Compact.decodeAt bytes
        (Compact.Program.codeByteLength artifact.program.code)
        (.prim .invalid))
    (hPoint : RawPoint bytes cert.table state) :
    ¬ stackOverflowAt state := by
  intro hOverflow
  unfold stackOverflowAt at hOverflow
  rcases hPoint with ⟨hCode, astack, hEntry, hAgrees⟩
  have hLength : state.stack.length ≤ stackCap := by
    rw [← agrees_length hAgrees]
    exact
      memStack_length_le_cap (rawCheck?_bounded hRaw) hEntry
  have hPoint' : RawPoint bytes cert.table state :=
    ⟨hCode, astack, hEntry, hAgrees⟩
  obtain ⟨hNet, hDelta⟩ :=
    raw_decoded_alpha_le_delta_succ hProgram hDecode hRaw hSentinel
      hPoint'
  unfold stackCap at hLength
  omega

theorem reach_raw_noOverflow
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {initial : EVMState}
    (hProgram : artifact.program.Valid)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hRaw : rawCheck? artifact cert = true)
    (hSentinel :
      Compact.decodeAt bytes
        (Compact.Program.codeByteLength artifact.program.code)
        (.prim .invalid))
    (hInitial : RawPoint bytes cert.table initial) :
    ∀ state, FrameReachable validJumps initial state →
      ¬ stackOverflowAt state := by
  intro state hReach
  exact
    raw_noOverflow_of_point hProgram hDecode hRaw hSentinel
      (reach_rawPoint hProgram hDecode hRaw hSentinel hInitial state
        hReach)

theorem raw_step_error_ne_safety_at
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {state : EVMState} {stepFuel : Nat}
    {err forbidden : EVMException}
    (hForbidden :
      forbidden = EvmYul.EVM.ExecutionException.StackOverflow ∨
        forbidden =
          EvmYul.EVM.ExecutionException.BadJumpDestination)
    (hProgram : artifact.program.Valid)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hRaw : rawCheck? artifact cert = true)
    (hSentinel :
      Compact.decodeAt bytes
        (Compact.Program.codeByteLength artifact.program.code)
        (.prim .invalid))
    (hPoint : RawPoint bytes cert.table state)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .error err) :
    err ≠ forbidden := by
  intro hErr
  subst err
  rcases hPoint with ⟨hCode, astack, hEntry, hAgrees⟩
  cases stepFuel with
  | zero =>
      simp [EvmYul.EVM.step] at hStep
      rcases hForbidden with hForbidden | hForbidden
      · rw [hForbidden] at hStep
        cases hStep
      · rw [hForbidden] at hStep
        cases hStep
  | succ fuel =>
    rcases rawCheck?_classify hRaw hEntry with hEnd |
        ⟨located, hMem, hPc, hFlow⟩
    · obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ := hSentinel
      simp [Compact.Instr.decoded?] at hInstrDecoded
      subst decoded
      have hDecoded :
          EvmYul.EVM.decode state.executionEnv.code state.pc =
            some (EvmYul.Operation.INVALID, none) := by
        simpa [hCode, hEnd] using hBytesDecoded
      rw [hDecoded] at hStep
      simp only [Option.getD_some] at hStep
      change
        EvmYul.step (τ := .EVM) EvmYul.Operation.INVALID none
            { { afterMemoryChargeAt state with
                  execLength :=
                    (afterMemoryChargeAt state).execLength + 1 } with
              gasAvailable :=
                (afterMemoryChargeAt state).gasAvailable -
                  EvmYul.UInt256.ofNat (dynamicGasCostAt state) } =
          Except.error forbidden at hStep
      change
        (Except.error EvmYul.EVM.ExecutionException.InvalidInstruction :
            Except EVMException EVMState) =
          Except.error forbidden at hStep
      rcases hForbidden with hForbidden | hForbidden
      · rw [hForbidden] at hStep
        cases hStep
      · rw [hForbidden] at hStep
        cases hStep
    · generalize hInstr : located.instr = instr
      cases instr with
      | push width value =>
          have hLocatedValid :=
            (List.forall_iff_forall_mem.mp hProgram) located hMem
          rw [hInstr] at hLocatedValid
          have hFits : Compact.FitsWidth width value.toNat := by
            simpa [Compact.Instr.Valid] using hLocatedValid
          obtain ⟨op, hOp⟩ :=
            Compact.exists_pushOp_of_width ⟨hFits.1, hFits.2.1⟩
          obtain ⟨decoded, hInstrDecoded, hDecoded⟩ :=
            raw_decode hDecode hMem hCode hPc
          rw [hInstr] at hInstrDecoded
          simp [Compact.Instr.decoded?, hOp] at hInstrDecoded
          subst decoded
          rw [hDecoded] at hStep
          simp only [Option.getD_some] at hStep
          rw [evm_step_push_eq_next fuel state value hFits hOp] at hStep
          cases hStep
      | push0 =>
          obtain ⟨decoded, hInstrDecoded, hDecoded⟩ :=
            raw_decode hDecode hMem hCode hPc
          rw [hInstr] at hInstrDecoded
          simp [Compact.Instr.decoded?] at hInstrDecoded
          subst decoded
          rw [hDecoded] at hStep
          simp only [Option.getD_some] at hStep
          rw [evm_step_push0_eq_next fuel state] at hStep
          cases hStep
      | jumpdest =>
          obtain ⟨decoded, hInstrDecoded, hDecoded⟩ :=
            raw_decode hDecode hMem hCode hPc
          rw [hInstr] at hInstrDecoded
          simp [Compact.Instr.decoded?] at hInstrDecoded
          subst decoded
          rw [hDecoded] at hStep
          simp only [Option.getD_some] at hStep
          rw [evm_step_jumpdest_eq_next fuel state none] at hStep
          cases hStep
      | jump =>
          obtain ⟨decoded, hInstrDecoded, hDecoded⟩ :=
            raw_decode hDecode hMem hCode hPc
          rw [hInstr] at hInstrDecoded
          simp [Compact.Instr.decoded?] at hInstrDecoded
          subst decoded
          cases astack with
          | nil =>
              simp [rawInstrOk?, hInstr] at hFlow
          | cons head restAbs =>
              cases head with
              | none =>
                  simp [rawInstrOk?, hInstr] at hFlow
              | some dest =>
                  obtain ⟨actualDest, rest, hStack, hDest,
                      hAgreesRest⟩ :=
                    agrees_cons_inv hAgrees
                  have hDestEq : dest = actualDest :=
                    agreesVal_some hDest
                  subst actualDest
                  rw [hDecoded] at hStep
                  simp only [Option.getD_some] at hStep
                  rw [evm_step_jump_eq_next fuel state none rest dest
                    hStack] at hStep
                  cases hStep
      | jumpi =>
          obtain ⟨decoded, hInstrDecoded, hDecoded⟩ :=
            raw_decode hDecode hMem hCode hPc
          rw [hInstr] at hInstrDecoded
          simp [Compact.Instr.decoded?] at hInstrDecoded
          subst decoded
          cases astack with
          | nil =>
              simp [rawInstrOk?, hInstr] at hFlow
          | cons destAbs tailAbs =>
              cases destAbs with
              | none =>
                  simp [rawInstrOk?, hInstr] at hFlow
              | some dest =>
                  cases tailAbs with
                  | nil =>
                      simp [rawInstrOk?, hInstr] at hFlow
                  | cons condAbs restAbs =>
                      obtain ⟨actualDest, actualTail, hStack, hDest,
                          hAgreesTail⟩ :=
                        agrees_cons_inv hAgrees
                      obtain ⟨cond, rest, hTail, hCond,
                          hAgreesRest⟩ :=
                        agrees_cons_inv hAgreesTail
                      subst actualTail
                      have hDestEq : dest = actualDest :=
                        agreesVal_some hDest
                      subst actualDest
                      have hStack' :
                          state.stack = dest :: cond :: rest :=
                        hStack
                      rw [hDecoded] at hStep
                      simp only [Option.getD_some] at hStep
                      rw [evm_step_jumpi_eq_next fuel state none rest dest
                        cond hStack'] at hStep
                      cases hStep
      | prim op =>
          have hDecoded :=
            raw_prim_decode hDecode hMem hPc hInstr hCode
          cases hContinuing : op.continuingStep? with
          | some primStep =>
              have hDecodedOp :
                  decodedOperationAt state = op.toEVM := by
                simp [decodedOperationAt, hDecoded]
              have hStaticPermits :
                  continuingPrimStaticPermits state op :=
                continuingPrimStaticPermits_of_static_check
                  hPrefix.static hDecodedOp
              have hGasful :
                  EvmYul.EVM.step (fuel + 1)
                      (dynamicGasCostAt state)
                      (some (op.toEVM, none))
                    (afterMemoryChargeAt state) =
                    .error
                      forbidden := by
                simpa [hDecoded] using hStep
              have hPrim :
                  op.step (afterEVMInstructionChargeAt state) =
                    .error
                      forbidden := by
                rw [← hGasful]
                exact
                  (evm_step_continuing_prim_after_charges hContinuing
                    trivial hStaticPermits).symm
              rw [PrimOp.step_eq_continuingStep_run hContinuing] at hPrim
              rcases hForbidden with hForbidden | hForbidden
              · rw [hForbidden] at hPrim
                exact primStep_run_error_ne_stackOverflow hPrim rfl
              · rw [hForbidden] at hPrim
                exact
                  primStep_run_error_ne_badJumpDestination hPrim rfl
          | none =>
              by_cases hPcOp : op = .pc
              · subst op
                have hActual :
                    EvmYul.EVM.step (fuel + 1)
                        (dynamicGasCostAt state)
                        (some (EvmYul.Operation.PC, none))
                        (afterMemoryChargeAt state) =
                      .error
                        forbidden := by
                  simpa [hDecoded, PrimOp.toEVM] using hStep
                rw [evm_step_pc_eq_next] at hActual
                cases hActual
              · by_cases hGasOp : op = .gas
                · subst op
                  have hActual :
                      EvmYul.EVM.step (fuel + 1)
                          (dynamicGasCostAt state)
                          (some ((resourcePrimOp .gas).toEVM, none))
                          (afterMemoryChargeAt state) =
                        .error
                          forbidden := by
                    simpa [hDecoded, resourcePrimOp, PrimOp.toEVM]
                      using hStep
                  rw [evm_step_resource_eq] at hActual
                  cases hActual
                · by_cases hStopOp : op = .stop
                  · subst op
                    have hPair :
                        ((EvmYul.EVM.decode state.executionEnv.code
                            state.pc).getD
                          (EvmYul.Operation.STOP, none)) =
                          (EvmYul.Operation.STOP, none) := by
                      simp [hDecoded, PrimOp.toEVM]
                    rw [hPair] at hStep
                    have hOk :=
                      evm_step_stop_after_charges
                        (fuel := fuel) (state := state)
                    rw [hPair] at hOk
                    rw [hOk] at hStep
                    cases hStep
                  · by_cases hReturnOp : op = .return
                    · subst op
                      have hEnough : ¬ state.stack.length < 2 := by
                        have hEnoughRaw :=
                          hPrefix.static.stackLimit.memoryAccess.jumps.stack.stackEnough
                        simpa [decodedOperationAt, hDecoded,
                          PrimOp.toEVM, EvmYul.EVM.δ] using hEnoughRaw
                      match hStack : state.stack with
                      | [] =>
                          exact hEnough (by simp [hStack])
                      | [top] =>
                          exact hEnough (by simp [hStack])
                      | top :: second :: rest =>
                          have hPop :
                              (afterEVMInstructionChargeAt
                                  state).stack.pop2 =
                                some ⟨rest, top, second⟩ := by
                            rw [afterEVMInstructionChargeAt_stack,
                              hStack]
                            rfl
                          have hPair :
                              ((EvmYul.EVM.decode
                                  state.executionEnv.code
                                  state.pc).getD
                                (EvmYul.Operation.STOP, none)) =
                                (EvmYul.Operation.RETURN, none) := by
                            simp [hDecoded, PrimOp.toEVM]
                          rw [hPair] at hStep
                          have hOk :=
                            evm_step_return_after_charges
                              (fuel := fuel) (state := state) hPop
                          rw [hPair] at hOk
                          rw [hOk] at hStep
                          cases hStep
                    · by_cases hRevertOp : op = .revert
                      · subst op
                        have hEnough : ¬ state.stack.length < 2 := by
                          have hEnoughRaw :=
                            hPrefix.static.stackLimit.memoryAccess.jumps.stack.stackEnough
                          simpa [decodedOperationAt, hDecoded,
                            PrimOp.toEVM, EvmYul.EVM.δ] using hEnoughRaw
                        match hStack : state.stack with
                        | [] =>
                            exact hEnough (by simp [hStack])
                        | [top] =>
                            exact hEnough (by simp [hStack])
                        | top :: second :: rest =>
                            have hPop :
                                (afterEVMInstructionChargeAt
                                    state).stack.pop2 =
                                  some ⟨rest, top, second⟩ := by
                              rw [afterEVMInstructionChargeAt_stack,
                                hStack]
                              rfl
                            have hPair :
                                ((EvmYul.EVM.decode
                                    state.executionEnv.code
                                    state.pc).getD
                                  (EvmYul.Operation.STOP, none)) =
                                  (EvmYul.Operation.REVERT, none) := by
                              simp [hDecoded, PrimOp.toEVM]
                            rw [hPair] at hStep
                            have hOk :=
                              evm_step_revert_after_charges
                                (fuel := fuel) (state := state) hPop
                            rw [hPair] at hOk
                            rw [hOk] at hStep
                            cases hStep
                      · by_cases hSelfdestructOp : op = .selfdestruct
                        · subst op
                          have hEnough :
                              ¬ state.stack.length < 1 := by
                            have hEnoughRaw :=
                              hPrefix.static.stackLimit.memoryAccess.jumps.stack.stackEnough
                            simpa [decodedOperationAt, hDecoded,
                              PrimOp.toEVM, EvmYul.EVM.δ] using
                                hEnoughRaw
                          match hStack : state.stack with
                          | [] =>
                              exact hEnough (by simp [hStack])
                          | recipient :: rest =>
                              have hPair :
                                  ((EvmYul.EVM.decode
                                      state.executionEnv.code
                                      state.pc).getD
                                    (EvmYul.Operation.STOP, none)) =
                                    (EvmYul.Operation.SELFDESTRUCT,
                                      none) := by
                                simp [hDecoded, PrimOp.toEVM]
                              rw [hPair] at hStep
                              rw [evm_step_selfdestruct_eq_next fuel
                                state recipient rest hStack] at hStep
                              cases hStep
                        · have hMsizeOp : op ≠ .msize := by
                            intro hMsize
                            subst op
                            simp [PrimOp.continuingStep?] at hContinuing
                          have hValid :
                              EvmYul.EVM.δ op.toEVM ≠ none := by
                            have hValidRaw :=
                              hPrefix.static.stackLimit.memoryAccess.jumps.stack.opcodeValid_raw
                            simpa [decodedOperationAt, hDecoded] using
                              hValidRaw
                          rcases
                              primOp_external_of_no_continuing op
                                hValid hPcOp hGasOp hMsizeOp hStopOp
                                hReturnOp hRevertOp hSelfdestructOp
                                hContinuing with
                            ⟨kind, hCall⟩ | ⟨kind, hCreate⟩
                          · subst op
                            have hOpEq :
                                (callPrimOp kind).toEVM =
                                  kind.toEVMOperation := by
                              cases kind <;> rfl
                            have hDecodedOp :
                                decodedOperationAt state =
                                  kind.toEVMOperation := by
                              simp [decodedOperationAt, hDecoded,
                                hOpEq]
                            obtain ⟨rest, operands, hOperands⟩ :=
                              call_operands_of_stackEnough_kind kind
                                hPrefix.static.stackLimit hDecodedOp
                            have hActual :
                                EvmYul.EVM.step (fuel + 1)
                                    (dynamicGasCostAt state)
                                    (some
                                      (kind.toEVMOperation, none))
                                    (afterMemoryChargeAt state) =
                                  .error
                                    forbidden := by
                              simpa [hDecoded, hOpEq] using hStep
                            have hExternalErr :=
                              evm_step_call_error_eq_outOfFuel_at
                                hOperands hActual
                            rcases hForbidden with hForbidden | hForbidden
                            · rw [hForbidden] at hExternalErr
                              cases hExternalErr
                            · rw [hForbidden] at hExternalErr
                              cases hExternalErr
                          · subst op
                            have hOpEq :
                                (createPrimOp kind).toEVM =
                                  kind.toEVMOperation := by
                              cases kind <;> rfl
                            have hDecodedOp :
                                decodedOperationAt state =
                                  kind.toEVMOperation := by
                              simp [decodedOperationAt, hDecoded,
                                hOpEq]
                            obtain ⟨rest, operands, hOperands⟩ :=
                              create_operands_of_stackEnough_kind kind
                                hPrefix.static.stackLimit hDecodedOp
                            have hActual :
                                EvmYul.EVM.step (fuel + 1)
                                    (dynamicGasCostAt state)
                                    (some
                                      (kind.toEVMOperation, none))
                                    (afterMemoryChargeAt state) =
                                  .error
                                    forbidden := by
                              simpa [hDecoded, hOpEq] using hStep
                            have hExternalErr :=
                              evm_step_create_positive_error_eq_outOfGas_at
                                hOperands hActual
                            rcases hForbidden with hForbidden | hForbidden
                            · rw [hForbidden] at hExternalErr
                              cases hExternalErr
                            · rw [hForbidden] at hExternalErr
                              cases hExternalErr

theorem raw_step_error_ne_stackOverflow_at
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {state : EVMState} {stepFuel : Nat}
    {err : EVMException}
    (hProgram : artifact.program.Valid)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hRaw : rawCheck? artifact cert = true)
    (hSentinel :
      Compact.decodeAt bytes
        (Compact.Program.codeByteLength artifact.program.code)
        (.prim .invalid))
    (hPoint : RawPoint bytes cert.table state)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .error err) :
    err ≠ EvmYul.EVM.ExecutionException.StackOverflow :=
  raw_step_error_ne_safety_at (Or.inl rfl) hProgram hDecode hRaw
    hSentinel hPoint hPrefix hStep

theorem raw_step_error_ne_badJumpDestination_at
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {state : EVMState} {stepFuel : Nat}
    {err : EVMException}
    (hProgram : artifact.program.Valid)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hRaw : rawCheck? artifact cert = true)
    (hSentinel :
      Compact.decodeAt bytes
        (Compact.Program.codeByteLength artifact.program.code)
        (.prim .invalid))
    (hPoint : RawPoint bytes cert.table state)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .error err) :
    err ≠ EvmYul.EVM.ExecutionException.BadJumpDestination :=
  raw_step_error_ne_safety_at (Or.inr rfl) hProgram hDecode hRaw
    hSentinel hPoint hPrefix hStep

theorem x_ne_stackOverflow_of_rawCert
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {initial : EVMState}
    (hProgram : artifact.program.Valid)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hRaw : rawCheck? artifact cert = true)
    (hSentinel :
      Compact.decodeAt bytes
        (Compact.Program.codeByteLength artifact.program.code)
        (.prim .invalid))
    (hCode : initial.executionEnv.code = bytes)
    (hPc : initial.pc = EvmYul.UInt256.ofNat 0)
    (hStack : initial.stack = []) :
    ∀ fuel,
      EvmYul.EVM.X fuel validJumps initial ≠
        .error EvmYul.EVM.ExecutionException.StackOverflow := by
  intro fuel
  have hInitial :=
    rawPoint_initial hRaw hCode hPc hStack
  exact
    x_ne_stackOverflow_of_invariants
      (reach_raw_noOverflow hProgram hDecode hRaw hSentinel hInitial)
      (fun state stepFuel err hReach hPrefix hStep =>
        raw_step_error_ne_stackOverflow_at hProgram hDecode hRaw
          hSentinel
          (reach_rawPoint hProgram hDecode hRaw hSentinel hInitial state
            hReach)
          hPrefix hStep)
      fuel initial .initial

def RawJumpdestsListed
    (program : Compact.Program) (validJumps : Array Word) : Prop :=
  ∀ located,
    located ∈ program.code →
      located.instr = .jumpdest →
        validJumps.contains
          (EvmYul.UInt256.ofNat located.pc) = true

theorem rawJumpdestsListed_D_J
    {program : Compact.Program} {bytes : ByteArray}
    (hLayout : Compact.Program.codeLayoutFrom program.code 0)
    (hWindow :
      Compact.Program.codeByteLength program.code <
        18446744073709551616)
    (hDecode : Compact.DecodingCorrect program bytes) :
    RawJumpdestsListed program
      (EvmYul.EVM.D_J bytes (EvmYul.UInt256.ofNat 0)) := by
  intro located hMem hJumpdest
  exact
    Compact.D_J_contains_of_decodingCorrect hLayout hWindow hDecode
      hMem hJumpdest

theorem rawPoint_not_badJump
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {state : EVMState}
    (hProgram : artifact.program.Valid)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hRaw : rawCheck? artifact cert = true)
    (hSentinel :
      Compact.decodeAt bytes
        (Compact.Program.codeByteLength artifact.program.code)
        (.prim .invalid))
    (hPoint : RawPoint bytes cert.table state)
    (hListed : RawJumpdestsListed artifact.program validJumps) :
    ¬ badJumpAt validJumps state ∧
      ¬ badJumpiAt validJumps state := by
  rcases hPoint with ⟨hCode, astack, hEntry, hAgrees⟩
  rcases rawCheck?_classify hRaw hEntry with hEnd |
      ⟨located, hMem, hPc, hFlow⟩
  · obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ := hSentinel
    simp [Compact.Instr.decoded?] at hInstrDecoded
    subst decoded
    have hDecoded :
        EvmYul.EVM.decode state.executionEnv.code state.pc =
          some (EvmYul.Operation.INVALID, none) := by
      simpa [hCode, hEnd] using hBytesDecoded
    constructor
    · intro hBad
      have hOp := hBad.1
      simp [decodedOperationAt, hDecoded] at hOp
    · intro hBad
      have hOp := hBad.1
      simp [decodedOperationAt, hDecoded] at hOp
  · generalize hInstr : located.instr = instr
    cases instr with
    | push width value =>
        have hLocatedValid :=
          (List.forall_iff_forall_mem.mp hProgram) located hMem
        rw [hInstr] at hLocatedValid
        have hFits : Compact.FitsWidth width value.toNat := by
          simpa [Compact.Instr.Valid] using hLocatedValid
        obtain ⟨op, hOp⟩ :=
          Compact.exists_pushOp_of_width ⟨hFits.1, hFits.2.1⟩
        have hArgWidth :=
          (Compact.pushOp?_properties ⟨hFits.1, hFits.2.1⟩ hOp).2
        obtain ⟨decoded, hInstrDecoded, hDecoded⟩ :=
          raw_decode hDecode hMem hCode hPc
        rw [hInstr] at hInstrDecoded
        simp [Compact.Instr.decoded?, hOp] at hInstrDecoded
        subst decoded
        constructor
        · intro hBad
          have hOpEq := hBad.1
          simp [decodedOperationAt, hDecoded] at hOpEq
          rw [hOpEq] at hArgWidth
          simp [EvmYul.EVM.argOnNBytesOfInstr] at hArgWidth
          have hPos := hFits.1
          omega
        · intro hBad
          have hOpEq := hBad.1
          simp [decodedOperationAt, hDecoded] at hOpEq
          rw [hOpEq] at hArgWidth
          simp [EvmYul.EVM.argOnNBytesOfInstr] at hArgWidth
          have hPos := hFits.1
          omega
    | push0 =>
        obtain ⟨decoded, hInstrDecoded, hDecoded⟩ :=
          raw_decode hDecode hMem hCode hPc
        rw [hInstr] at hInstrDecoded
        simp [Compact.Instr.decoded?] at hInstrDecoded
        subst decoded
        constructor
        · intro hBad
          have hOp := hBad.1
          simp [decodedOperationAt, hDecoded] at hOp
        · intro hBad
          have hOp := hBad.1
          simp [decodedOperationAt, hDecoded] at hOp
    | jumpdest =>
        obtain ⟨decoded, hInstrDecoded, hDecoded⟩ :=
          raw_decode hDecode hMem hCode hPc
        rw [hInstr] at hInstrDecoded
        simp [Compact.Instr.decoded?] at hInstrDecoded
        subst decoded
        constructor
        · intro hBad
          have hOp := hBad.1
          simp [decodedOperationAt, hDecoded] at hOp
        · intro hBad
          have hOp := hBad.1
          simp [decodedOperationAt, hDecoded] at hOp
    | prim op =>
        have hDecoded :=
          raw_prim_decode hDecode hMem hPc hInstr hCode
        constructor
        · intro hBad
          have hOp := hBad.1
          simp [decodedOperationAt, hDecoded] at hOp
          exact (primOp_toEVM_ne_jump op).1 hOp
        · intro hBad
          have hOp := hBad.1
          simp [decodedOperationAt, hDecoded] at hOp
          exact (primOp_toEVM_ne_jump op).2 hOp
    | jump =>
        obtain ⟨decoded, hInstrDecoded, hDecoded⟩ :=
          raw_decode hDecode hMem hCode hPc
        rw [hInstr] at hInstrDecoded
        simp [Compact.Instr.decoded?] at hInstrDecoded
        subst decoded
        cases astack with
        | nil =>
            simp [rawInstrOk?, hInstr] at hFlow
        | cons head restAbs =>
            cases head with
            | none =>
                simp [rawInstrOk?, hInstr] at hFlow
            | some dest =>
                simp only [rawInstrOk?, hInstr, Bool.and_eq_true] at hFlow
                obtain ⟨actualDest, rest, hStack, hDest,
                    hAgreesRest⟩ :=
                  agrees_cons_inv hAgrees
                have hDestEq : dest = actualDest :=
                  agreesVal_some hDest
                subst actualDest
                obtain ⟨target, hTargetMem, hTargetPc, hJumpdest⟩ :=
                  jumpdestAt?_sound hFlow.1
                have hContainsAt :=
                  hListed target hTargetMem hJumpdest
                have hDestWord :
                    dest = EvmYul.UInt256.ofNat target.pc := by
                  calc
                    dest = EvmYul.UInt256.ofNat dest.toNat :=
                      (EvmYul.UInt256.ofNat_toNat dest).symm
                    _ = EvmYul.UInt256.ofNat target.pc := by
                      rw [hTargetPc]
                rw [← hDestWord] at hContainsAt
                have hStackHead : state.stack[0]? = some dest := by
                  simp [hStack]
                have hNotInFalse :
                    EvmYul.EVM.X.notIn state.stack[0]? validJumps =
                      false := by
                  simp [hStackHead, EvmYul.EVM.X.notIn,
                    EvmYul.EVM.X.belongs, hContainsAt]
                constructor
                · intro hBad
                  rw [hBad.2] at hNotInFalse
                  cases hNotInFalse
                · intro hBad
                  have hOp := hBad.1
                  simp [decodedOperationAt, hDecoded] at hOp
    | jumpi =>
        obtain ⟨decoded, hInstrDecoded, hDecoded⟩ :=
          raw_decode hDecode hMem hCode hPc
        rw [hInstr] at hInstrDecoded
        simp [Compact.Instr.decoded?] at hInstrDecoded
        subst decoded
        cases astack with
        | nil =>
            simp [rawInstrOk?, hInstr] at hFlow
        | cons destAbs tailAbs =>
            cases destAbs with
            | none =>
                simp [rawInstrOk?, hInstr] at hFlow
            | some dest =>
                cases tailAbs with
                | nil =>
                    simp [rawInstrOk?, hInstr] at hFlow
                | cons condAbs restAbs =>
                    simp only [rawInstrOk?, hInstr,
                      Bool.and_eq_true] at hFlow
                    obtain ⟨actualDest, actualTail, hStack, hDest,
                        hAgreesTail⟩ :=
                      agrees_cons_inv hAgrees
                    obtain ⟨cond, rest, hTail, hCond,
                        hAgreesRest⟩ :=
                      agrees_cons_inv hAgreesTail
                    subst actualTail
                    have hDestEq : dest = actualDest :=
                      agreesVal_some hDest
                    subst actualDest
                    obtain ⟨target, hTargetMem, hTargetPc,
                        hJumpdest⟩ :=
                      jumpdestAt?_sound hFlow.1
                    have hContainsAt :=
                      hListed target hTargetMem hJumpdest
                    have hDestWord :
                        dest = EvmYul.UInt256.ofNat target.pc := by
                      calc
                        dest = EvmYul.UInt256.ofNat dest.toNat :=
                          (EvmYul.UInt256.ofNat_toNat dest).symm
                        _ = EvmYul.UInt256.ofNat target.pc := by
                          rw [hTargetPc]
                    rw [← hDestWord] at hContainsAt
                    have hStackHead :
                        state.stack[0]? = some dest := by
                      simp [hStack]
                    have hNotInFalse :
                        EvmYul.EVM.X.notIn state.stack[0]? validJumps =
                          false := by
                      simp [hStackHead, EvmYul.EVM.X.notIn,
                        EvmYul.EVM.X.belongs, hContainsAt]
                    constructor
                    · intro hBad
                      have hOp := hBad.1
                      simp [decodedOperationAt, hDecoded] at hOp
                    · intro hBad
                      rw [hBad.2.2] at hNotInFalse
                      cases hNotInFalse

theorem x_ne_badJumpDestination_of_rawCert
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {initial : EVMState}
    (hProgram : artifact.program.Valid)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hRaw : rawCheck? artifact cert = true)
    (hSentinel :
      Compact.decodeAt bytes
        (Compact.Program.codeByteLength artifact.program.code)
        (.prim .invalid))
    (hListed : RawJumpdestsListed artifact.program validJumps)
    (hCode : initial.executionEnv.code = bytes)
    (hPc : initial.pc = EvmYul.UInt256.ofNat 0)
    (hStack : initial.stack = []) :
    ∀ fuel,
      EvmYul.EVM.X fuel validJumps initial ≠
        .error
          EvmYul.EVM.ExecutionException.BadJumpDestination := by
  intro fuel
  have hInitial :=
    rawPoint_initial hRaw hCode hPc hStack
  exact
    x_ne_badJumpDestination_of_invariants
      (fun state hReach =>
        rawPoint_not_badJump hProgram hDecode hRaw hSentinel
          (reach_rawPoint hProgram hDecode hRaw hSentinel hInitial state
            hReach)
          hListed)
      (fun state stepFuel err hReach hPrefix hStep =>
        raw_step_error_ne_badJumpDestination_at hProgram hDecode hRaw
          hSentinel
          (reach_rawPoint hProgram hDecode hRaw hSentinel hInitial state
            hReach)
          hPrefix hStep)
      fuel initial .initial

end StackHeadroom
end Assembly
end EvmCompiler
