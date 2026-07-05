import EvmCompiler.Assembly.StackHeadroom
import EvmCompiler.Assembly.GasfulBridgeLayout
import EvmCompiler.Assembly.GasfulBridgeRecursive

/-!
# Soundness of the stack-headroom certificate against the gasful EVM

The validated height table of `EvmCompiler.Assembly.StackHeadroom` is proved
exact along every reachable gasful frame state (`HeightPoint`), by mirroring
the compact control-point step lemmas of the gasful bridge layout module and
adding height bookkeeping.  The headroom cap then makes the interpreter's
`StackOverflow` precheck unreachable.
-/

namespace EvmCompiler
namespace Assembly
namespace StackHeadroom

open EvmCompiler.Assembly.GasfulBridge

/-- The certified per-state fact: the height table pins the exact operand
stack length at the current program counter. -/
def HeightPoint (heights : HeightList) (state : EVMState) : Prop :=
  lookupHeight heights state.pc = some state.stack.length

theorem afterEVMInstructionChargeAt_stack (state : EVMState) :
    (afterEVMInstructionChargeAt state).stack = state.stack := by
  simp [afterEVMInstructionChargeAt, afterMemoryChargeAt, chargeGas]

theorem afterEVMInstructionChargeAt_pc (state : EVMState) :
    (afterEVMInstructionChargeAt state).pc = state.pc := by
  simp [afterEVMInstructionChargeAt, afterMemoryChargeAt, chargeGas]

/-! ## Per-control-point height preservation

Each lemma mirrors the corresponding `artifactFramePoint_*_step` lemma of
`GasfulBridgeLayout`, replaying the exact successor-state identification and
reading the successor height off the validated table. -/

theorem heightPoint_label_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {state next : EVMState} {block : Compact.SourceBlock}
    {label : Label} {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .label label)
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hHeight : HeightPoint cert.heights state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    HeightPoint cert.heights next := by
  obtain ⟨located, hMem, hLocatedPc, hLocatedInstr⟩ :=
    compact_label_entry_mem hCompile hBlock hInstr
  obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
    hDecode.decodes located hMem
  rw [hLocatedInstr] at hInstrDecoded
  simp [Compact.Instr.decoded?] at hInstrDecoded
  subst decoded
  have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
    hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
  have hDecoded :
      EvmYul.EVM.decode state.executionEnv.code state.pc =
        some (EvmYul.Operation.JUMPDEST, none) := by
    simpa [hCode, hStatePc] using hBytesDecoded
  cases stepFuel with
  | zero => simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      have hExact := evm_step_jumpdest_eq_next fuel state none
      rw [hDecoded] at hStep
      simp only [Option.getD_some] at hStep
      rw [hExact] at hStep
      have hNext : next = (afterEVMInstructionChargeAt state).incrPC := by
        simpa using hStep.symm
      subst next
      have hEntry :
          lookupHeight cert.heights (EvmYul.UInt256.ofNat block.compactPc) =
            some state.stack.length := by
        rw [← hPc]; exact hHeight
      have hOk := check?_blockOk hCheck hBlock
      simp only [blockOk?, hEntry, hInstr, beq_iff_eq] at hOk
      have hSucc :
          lookupHeight cert.heights
              (EvmYul.UInt256.ofNat (block.compactPc + 1)) =
            some state.stack.length := hOk
      show lookupHeight cert.heights _ = _
      have hNextPc :
          ((afterEVMInstructionChargeAt state).incrPC).pc =
            EvmYul.UInt256.ofNat (block.compactPc + 1) := by
        simp [EvmYul.EVM.State.incrPC, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, chargeGas, hPc, uint256_ofNat_add]
      have hNextStack :
          ((afterEVMInstructionChargeAt state).incrPC).stack = state.stack := by
        simp [EvmYul.EVM.State.incrPC, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, chargeGas]
      rw [hNextPc, hNextStack]
      exact hSucc

theorem heightPoint_push_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {state next : EVMState} {block : Compact.SourceBlock}
    {value : Word} {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .push value)
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hHeight : HeightPoint cert.heights state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    HeightPoint cert.heights next := by
  obtain ⟨width, located, hWidth, hMem, hLocatedPc, hLocatedInstr⟩ :=
    compact_push_entry_mem hCompile hBlock hInstr
  have hLocatedValid :=
    (List.forall_iff_forall_mem.mp
      (Compact.compile?_valid hCompile).wellFormed.1) located hMem
  rw [hLocatedInstr] at hLocatedValid
  have hFits : Compact.FitsWidth width value.toNat := by
    simpa [Compact.Instr.Valid] using hLocatedValid
  obtain ⟨op, hOp⟩ := Compact.exists_pushOp_of_width
    ⟨hFits.1, hFits.2.1⟩
  obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
    hDecode.decodes located hMem
  rw [hLocatedInstr] at hInstrDecoded
  simp [Compact.Instr.decoded?, hOp] at hInstrDecoded
  subst decoded
  have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
    hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
  have hDecoded : EvmYul.EVM.decode state.executionEnv.code state.pc =
      some (op, some (value, width)) := by
    simpa [hCode, hStatePc] using hBytesDecoded
  cases stepFuel with
  | zero => simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      have hExact := evm_step_push_eq_next fuel state value hFits hOp
      rw [hDecoded] at hStep
      simp only [Option.getD_some] at hStep
      rw [hExact] at hStep
      have hNext : next = gasfulPushNext width value state := by
        simpa using hStep.symm
      subst next
      have hEntry :
          lookupHeight cert.heights (EvmYul.UInt256.ofNat block.compactPc) =
            some state.stack.length := by
        rw [← hPc]; exact hHeight
      have hSize : Compact.sourceInstrSizeAt? artifact.pinnedPushPcs
          artifact.branchWidth block.sourcePc block.sourceInstr =
            some (width + 1) := by
        simp [hInstr, Compact.sourceInstrSizeAt?, hWidth]
      have hOk := check?_blockOk hCheck hBlock
      rw [hInstr] at hSize
      simp only [blockOk?, hEntry, hInstr, hSize, beq_iff_eq] at hOk
      have hSucc :
          lookupHeight cert.heights
              (EvmYul.UInt256.ofNat (block.compactPc + (width + 1))) =
            some (state.stack.length + 1) := hOk
      show lookupHeight cert.heights _ = _
      have hNextPc :
          (gasfulPushNext width value state).pc =
            EvmYul.UInt256.ofNat (block.compactPc + (width + 1)) := by
        simp [gasfulPushNext, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, chargeGas, hPc, uint256_ofNat_add,
          Nat.add_assoc]
      have hNextStack :
          (gasfulPushNext width value state).stack.length =
            state.stack.length + 1 := by
        simp [gasfulPushNext, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push,
          afterEVMInstructionChargeAt, afterMemoryChargeAt, chargeGas]
      rw [hNextPc, hNextStack]
      exact hSucc

theorem heightPoint_branch_push_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {state next : EVMState} {block : Compact.SourceBlock}
    {label : Label} {isJumpi : Bool} {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr =
      if isJumpi then .jumpi label else .jump label)
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hHeight : HeightPoint cert.heights state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    HeightPoint cert.heights next := by
  obtain ⟨dest, located, hLookup, hMem, hLocatedPc, hLocatedInstr⟩ :=
    compact_branch_entry_mem hCompile hBlock hInstr
  have hLocatedValid :=
    (List.forall_iff_forall_mem.mp
      (Compact.compile?_valid hCompile).wellFormed.1) located hMem
  rw [hLocatedInstr] at hLocatedValid
  have hFits : Compact.FitsWidth artifact.branchWidth
      (EvmYul.UInt256.ofNat dest).toNat := by
    simpa [Compact.Instr.Valid] using hLocatedValid
  obtain ⟨op, hOp⟩ := Compact.exists_pushOp_of_width
    ⟨hFits.1, hFits.2.1⟩
  obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
    hDecode.decodes located hMem
  rw [hLocatedInstr] at hInstrDecoded
  simp [Compact.Instr.decoded?, hOp] at hInstrDecoded
  subst decoded
  have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
    hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
  have hDecoded :
      EvmYul.EVM.decode state.executionEnv.code state.pc =
        some (op, some (EvmYul.UInt256.ofNat dest,
          artifact.branchWidth)) := by
    simpa [hCode, hStatePc] using hBytesDecoded
  cases stepFuel with
  | zero => simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      have hExact := evm_step_push_eq_next fuel state
        (EvmYul.UInt256.ofNat dest) hFits hOp
      rw [hDecoded] at hStep
      simp only [Option.getD_some] at hStep
      rw [hExact] at hStep
      have hNext : next = gasfulPushNext artifact.branchWidth
          (EvmYul.UInt256.ofNat dest) state := by
        simpa using hStep.symm
      subst next
      have hEntry :
          lookupHeight cert.heights (EvmYul.UInt256.ofNat block.compactPc) =
            some state.stack.length := by
        rw [← hPc]; exact hHeight
      have hSucc :
          lookupHeight cert.heights
              (EvmYul.UInt256.ofNat
                (block.compactPc + artifact.branchWidth + 1)) =
            some (state.stack.length + 1) := by
        have hOk := check?_blockOk hCheck hBlock
        cases hJumpi : isJumpi
        · rw [hJumpi] at hInstr
          simp only [Bool.false_eq_true, if_false] at hInstr
          simp only [blockOk?, hEntry, hInstr, hLookup, Bool.and_eq_true,
            beq_iff_eq] at hOk
          exact hOk.1
        · rw [hJumpi] at hInstr
          simp only [if_true] at hInstr
          simp only [blockOk?, hEntry, hInstr, hLookup, Bool.and_eq_true,
            beq_iff_eq, decide_eq_true_eq] at hOk
          exact hOk.1.1.2
      show lookupHeight cert.heights _ = _
      have hNextPc :
          (gasfulPushNext artifact.branchWidth
              (EvmYul.UInt256.ofNat dest) state).pc =
            EvmYul.UInt256.ofNat
              (block.compactPc + artifact.branchWidth + 1) := by
        simp [gasfulPushNext, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, chargeGas, hPc, uint256_ofNat_add,
          Nat.add_assoc]
      have hNextStack :
          (gasfulPushNext artifact.branchWidth
              (EvmYul.UInt256.ofNat dest) state).stack.length =
            state.stack.length + 1 := by
        simp [gasfulPushNext, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push,
          afterEVMInstructionChargeAt, afterMemoryChargeAt, chargeGas]
      rw [hNextPc, hNextStack]
      exact hSucc

/-- Height entry relation at a branch midpoint: the block entry exists and
the midpoint entry is exactly one above it. -/
theorem branchMid_heights
    {artifact : Compact.Artifact} {cert : Cert}
    {block : Compact.SourceBlock} {label : Label} {isJumpi : Bool}
    {dest : Nat} {midLen : Nat}
    (hCheck : check? artifact cert = true)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr =
      if isJumpi then .jumpi label else .jump label)
    (hLookup : Compact.lookupLabel? artifact.labels label = some dest)
    (hMid :
      lookupHeight cert.heights
          (EvmYul.UInt256.ofNat
            (block.compactPc + artifact.branchWidth + 1)) =
        some midLen) :
    ∃ h, midLen = h + 1 ∧
      lookupHeight cert.heights (EvmYul.UInt256.ofNat block.compactPc) =
        some h ∧
      (if isJumpi then
          1 ≤ h ∧
          lookupHeight cert.heights (EvmYul.UInt256.ofNat dest) =
              some (h - 1) ∧
            lookupHeight cert.heights
                (EvmYul.UInt256.ofNat
                  (block.compactPc + artifact.branchWidth + 2)) =
              some (h - 1)
        else
          lookupHeight cert.heights (EvmYul.UInt256.ofNat dest) =
            some h) := by
  have hOk := check?_blockOk hCheck hBlock
  cases hJumpi : isJumpi
  · rw [hJumpi] at hInstr
    simp only [Bool.false_eq_true, if_false] at hInstr
    cases hEntry :
        lookupHeight cert.heights (EvmYul.UInt256.ofNat block.compactPc) with
    | none =>
        simp only [blockOk?, hEntry, hInstr, beq_iff_eq] at hOk
        rw [hOk] at hMid
        cases hMid
    | some h =>
        simp only [blockOk?, hEntry, hInstr, hLookup, Bool.and_eq_true,
          beq_iff_eq] at hOk
        refine ⟨h, ?_, rfl, ?_⟩
        · rw [hOk.1] at hMid
          exact (Option.some.inj hMid).symm
        · simp only [Bool.false_eq_true, if_false]
          exact hOk.2
  · rw [hJumpi] at hInstr
    simp only [if_true] at hInstr
    cases hEntry :
        lookupHeight cert.heights (EvmYul.UInt256.ofNat block.compactPc) with
    | none =>
        simp only [blockOk?, hEntry, hInstr, beq_iff_eq] at hOk
        rw [hOk] at hMid
        cases hMid
    | some h =>
        simp only [blockOk?, hEntry, hInstr, hLookup, Bool.and_eq_true,
          beq_iff_eq, decide_eq_true_eq] at hOk
        refine ⟨h, ?_, rfl, ?_⟩
        · rw [hOk.1.1.2] at hMid
          exact (Option.some.inj hMid).symm
        · simp only [if_true]
          exact ⟨hOk.1.1.1, hOk.1.2, hOk.2⟩

theorem heightPoint_branchMid_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {state next : EVMState}
    {block : Compact.SourceBlock} {label : Label} {isJumpi : Bool}
    {dest : Nat} {rest : EvmYul.Stack Word} {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr =
      if isJumpi then .jumpi label else .jump label)
    (hLookup : Compact.lookupLabel? artifact.labels label = some dest)
    (hPc : state.pc = EvmYul.UInt256.ofNat
      (block.compactPc + artifact.branchWidth + 1))
    (hStack : state.stack = EvmYul.UInt256.ofNat dest :: rest)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hHeight : HeightPoint cert.heights state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    HeightPoint cert.heights next := by
  have hMidEntry :
      lookupHeight cert.heights
          (EvmYul.UInt256.ofNat
            (block.compactPc + artifact.branchWidth + 1)) =
        some state.stack.length := by
    rw [← hPc]; exact hHeight
  obtain ⟨h, hMidLen, _hEntry, hRest⟩ :=
    branchMid_heights hCheck hBlock hInstr hLookup hMidEntry
  obtain ⟨located, hMem, hLocatedPc, hLocatedInstr⟩ :=
    compact_branch_midpoint_mem hCompile hBlock hInstr
  obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
    hDecode.decodes located hMem
  cases stepFuel with
  | zero => simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
        hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
      cases hJumpi : isJumpi
      · -- JUMP
        rw [hJumpi] at hLocatedInstr hRest
        simp only [Bool.false_eq_true, if_false] at hLocatedInstr hRest
        rw [hLocatedInstr] at hInstrDecoded
        simp [Compact.Instr.decoded?] at hInstrDecoded
        subst decoded
        have hDecoded :
            EvmYul.EVM.decode state.executionEnv.code state.pc =
              some (EvmYul.Operation.JUMP, none) := by
          simpa [hCode, hStatePc] using hBytesDecoded
        have hExact :=
          evm_step_jump_eq_next fuel state none rest
            (EvmYul.UInt256.ofNat dest) hStack
        rw [hDecoded] at hStep
        simp only [Option.getD_some] at hStep
        rw [hExact] at hStep
        have hNext :
            next = gasfulJumpNext state rest (EvmYul.UInt256.ofNat dest) := by
          simpa using hStep.symm
        subst next
        have hLen : state.stack.length = rest.length + 1 := by
          rw [hStack]; rfl
        show lookupHeight cert.heights _ = _
        have hNextPc :
            (gasfulJumpNext state rest (EvmYul.UInt256.ofNat dest)).pc =
              EvmYul.UInt256.ofNat dest := by
          simp [gasfulJumpNext]
        have hNextStack :
            (gasfulJumpNext state rest (EvmYul.UInt256.ofNat dest)).stack =
              rest := by
          simp [gasfulJumpNext]
        rw [hNextPc, hNextStack]
        have hRestLen : rest.length = h := by omega
        rw [hRestLen]
        exact hRest
      · -- JUMPI
        rw [hJumpi] at hLocatedInstr hRest
        simp only [if_true] at hLocatedInstr hRest
        obtain ⟨hOne, hDest, hFall⟩ := hRest
        rw [hLocatedInstr] at hInstrDecoded
        simp [Compact.Instr.decoded?] at hInstrDecoded
        subst decoded
        have hDecoded :
            EvmYul.EVM.decode state.executionEnv.code state.pc =
              some (EvmYul.Operation.JUMPI, none) := by
          simpa [hCode, hStatePc] using hBytesDecoded
        have hPair :
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)) =
              (EvmYul.Operation.JUMPI, none) := by
          simp [hDecoded]
        have hEnough : ¬ state.stack.length < 2 := by
          simpa [decodedOperationAt, hPair, EvmYul.EVM.δ] using
            hPrefix.static.stackLimit.memoryAccess.jumps.stack.stackEnough
        cases rest with
        | nil =>
            exfalso
            apply hEnough
            simp [hStack]
        | cons cond tail =>
            have hStack' : state.stack =
                EvmYul.UInt256.ofNat dest :: cond :: tail := by
              simpa using hStack
            have hExact :=
              evm_step_jumpi_eq_next fuel state none tail
                (EvmYul.UInt256.ofNat dest) cond hStack'
            rw [hDecoded] at hStep
            simp only [Option.getD_some] at hStep
            rw [hExact] at hStep
            have hNext : next = gasfulJumpiNext state tail
                (EvmYul.UInt256.ofNat dest) cond := by
              simpa using hStep.symm
            subst next
            have hLen : state.stack.length = tail.length + 2 := by
              rw [hStack']; rfl
            have hTailLen : tail.length = h - 1 := by omega
            show lookupHeight cert.heights _ = _
            by_cases hCond : cond != EvmYul.UInt256.ofNat 0
            · have hNextPc :
                  (gasfulJumpiNext state tail
                      (EvmYul.UInt256.ofNat dest) cond).pc =
                    EvmYul.UInt256.ofNat dest := by
                simp [gasfulJumpiNext, hCond]
              have hNextStack :
                  (gasfulJumpiNext state tail
                      (EvmYul.UInt256.ofNat dest) cond).stack = tail := by
                simp [gasfulJumpiNext]
              rw [hNextPc, hNextStack, hTailLen]
              exact hDest
            · have hNextPc :
                  (gasfulJumpiNext state tail
                      (EvmYul.UInt256.ofNat dest) cond).pc =
                    EvmYul.UInt256.ofNat
                      (block.compactPc + artifact.branchWidth + 2) := by
                simp [gasfulJumpiNext, hCond, hPc]
                rw [uint256_ofNat_add]
              have hNextStack :
                  (gasfulJumpiNext state tail
                      (EvmYul.UInt256.ofNat dest) cond).stack = tail := by
                simp [gasfulJumpiNext]
              rw [hNextPc, hNextStack, hTailLen]
              exact hFall

theorem heightPoint_sentinel_no_success
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {state next : EVMState} {stepFuel : Nat}
    (hSentinel : Compact.decodeAt bytes
      (Compact.Program.codeByteLength artifact.program.code)
      (.prim .invalid))
    (hCode : state.executionEnv.code = bytes)
    (hPc : state.pc = EvmYul.UInt256.ofNat
      (Compact.Program.codeByteLength artifact.program.code))
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) : False :=
  artifactFramePoint_sentinel_no_success hSentinel hCode hPc hStep

theorem stackArity?_isSome_of_continuingStep
    {op : PrimOp} {primStep : PrimStep}
    (hContinuing : op.continuingStep? = some primStep) :
    ∃ input output, op.stackArity? = some (input, output) := by
  cases op <;>
    first
      | exact ⟨_, _, rfl⟩
      | simp [PrimOp.continuingStep?] at hContinuing

theorem heightPoint_prim_continuing_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {state next : EVMState}
    {block : Compact.SourceBlock} {op : PrimOp} {primStep : PrimStep}
    {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .prim op)
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hContinuing : op.continuingStep? = some primStep)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hHeight : HeightPoint cert.heights state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    HeightPoint cert.heights next := by
  have hDecoded := artifact_prim_decode hCompile hDecode hCode hBlock
    hInstr hPc
  cases stepFuel with
  | zero => simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      have hDecodedOp : decodedOperationAt state = op.toEVM := by
        simp [decodedOperationAt, hDecoded]
      have hStaticPermits : continuingPrimStaticPermits state op :=
        continuingPrimStaticPermits_of_static_check hPrefix.static hDecodedOp
      have hGasful :
          EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
              (some (op.toEVM, none)) (afterMemoryChargeAt state) =
            .ok next := by
        simpa [hDecoded] using hStep
      have hPrim :
          op.step (afterEVMInstructionChargeAt state) = .ok next := by
        rw [← hGasful]
        exact (evm_step_continuing_prim_after_charges hContinuing trivial
          hStaticPermits).symm
      by_cases hInvalid : op = .invalid
      · subst op
        rw [PrimOp.step_eq_continuingStep_run hContinuing] at hPrim
        have hStepInvalid : primStep = .invalid := by
          simpa [PrimOp.continuingStep?] using hContinuing.symm
        subst primStep
        simp [PrimStep.run] at hPrim
      · obtain ⟨input, output, hArity⟩ :=
          stackArity?_isSome_of_continuingStep hContinuing
        have hNextLen :=
          PrimOp.step_stack_length_of_stackArity hArity hPrim
        have hNextPcRaw := PrimOp.step_pc_of_stackArity hArity hPrim
        rw [afterEVMInstructionChargeAt_stack] at hNextLen
        have hNextPc : next.pc =
            EvmYul.UInt256.ofNat (block.compactPc + 1) := by
          rw [hNextPcRaw, afterEVMInstructionChargeAt_pc, hPc,
            uint256_ofNat_add]
        have hEntry :
            lookupHeight cert.heights
                (EvmYul.UInt256.ofNat block.compactPc) =
              some state.stack.length := by
          rw [← hPc]; exact hHeight
        have hOk := check?_blockOk hCheck hBlock
        simp only [blockOk?, hEntry, hInstr, if_neg hInvalid, hArity,
          Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hOk
        show lookupHeight cert.heights _ = _
        rw [hNextPc, hNextLen]
        exact hOk.2

theorem heightPoint_resource_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {state next : EVMState} {block : Compact.SourceBlock}
    {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (kind : Simulation.ResourceQuery)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .prim (resourcePrimOp kind))
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hHeight : HeightPoint cert.heights state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    HeightPoint cert.heights next := by
  have hDecoded := artifact_prim_decode hCompile hDecode hCode hBlock
    hInstr hPc
  cases stepFuel with
  | zero => simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      have hActual :
          EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
              (some ((resourcePrimOp kind).toEVM, none))
              (afterMemoryChargeAt state) = .ok next := by
        simpa [hDecoded] using hStep
      rw [evm_step_resource_eq] at hActual
      cases hActual
      have hEntry :
          lookupHeight cert.heights (EvmYul.UInt256.ofNat block.compactPc) =
            some state.stack.length := by
        rw [← hPc]; exact hHeight
      have hArity :
          (resourcePrimOp kind).stackArity? = some (0, 1) := by
        cases kind <;> rfl
      have hOk := check?_blockOk hCheck hBlock
      have hInvalid : resourcePrimOp kind ≠ .invalid := by
        cases kind <;> simp [resourcePrimOp]
      simp only [blockOk?, hEntry, hInstr, if_neg hInvalid, hArity,
        Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hOk
      show lookupHeight cert.heights _ = _
      have hNextPc :
          (gasfulResourceNext kind state).pc =
            EvmYul.UInt256.ofNat (block.compactPc + 1) := by
        simp [gasfulResourceNext, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, afterDynamicChargeAt, chargeGas,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, hPc, uint256_ofNat_add]
      have hNextStack :
          (gasfulResourceNext kind state).stack.length =
            state.stack.length + 1 := by
        cases kind <;>
          simp [gasfulResourceNext, afterEVMInstructionChargeAt,
            afterMemoryChargeAt, afterDynamicChargeAt, chargeGas,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC, EvmYul.Stack.push]
      rw [hNextPc, hNextStack]
      simpa using hOk.2

theorem heightPoint_pc_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {state next : EVMState} {block : Compact.SourceBlock}
    {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .prim .pc)
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hHeight : HeightPoint cert.heights state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    HeightPoint cert.heights next := by
  have hDecoded := artifact_prim_decode hCompile hDecode hCode hBlock
    hInstr hPc
  cases stepFuel with
  | zero => simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      have hActual :
          EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
              (some (EvmYul.Operation.PC, none))
              (afterMemoryChargeAt state) = .ok next := by
        simpa [hDecoded, PrimOp.toEVM] using hStep
      rw [evm_step_pc_eq_next] at hActual
      cases hActual
      have hEntry :
          lookupHeight cert.heights (EvmYul.UInt256.ofNat block.compactPc) =
            some state.stack.length := by
        rw [← hPc]; exact hHeight
      have hOk := check?_blockOk hCheck hBlock
      have hInvalid : PrimOp.pc ≠ PrimOp.invalid := by simp
      have hArity : PrimOp.pc.stackArity? = some (0, 1) := rfl
      simp only [blockOk?, hEntry, hInstr, if_neg hInvalid, hArity,
        Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hOk
      show lookupHeight cert.heights _ = _
      have hNextPc :
          (gasfulPcNext state).pc =
            EvmYul.UInt256.ofNat (block.compactPc + 1) := by
        simp [gasfulPcNext, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, afterDynamicChargeAt, chargeGas,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, hPc, uint256_ofNat_add]
      have hNextStack :
          (gasfulPcNext state).stack.length = state.stack.length + 1 := by
        simp [gasfulPcNext, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, afterDynamicChargeAt, chargeGas,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push]
      rw [hNextPc, hNextStack]
      simpa using hOk.2

theorem callPrimOp_args_arity
    (kind : Simulation.CallKind) (operands : Simulation.CallOperands) :
    (callPrimOp kind).stackArity? =
      some ((Simulation.CallKind.args kind operands).length, 1) := by
  cases kind <;> rfl

theorem createPrimOp_args_arity
    (kind : Simulation.CreateKind) (operands : Simulation.CreateOperands) :
    (createPrimOp kind).stackArity? =
      some ((Simulation.CreateKind.args kind operands).length, 1) := by
  cases kind <;> rfl

theorem heightPoint_call_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {state next : EVMState}
    {block : Compact.SourceBlock} {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (kind : Simulation.CallKind)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .prim (callPrimOp kind))
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hHeight : HeightPoint cert.heights state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    HeightPoint cert.heights next := by
  have hDecoded := artifact_prim_decode hCompile hDecode hCode hBlock
    hInstr hPc
  have hOpEq : (callPrimOp kind).toEVM = kind.toEVMOperation := by
    cases kind <;> rfl
  have hDecodedOp : decodedOperationAt state = kind.toEVMOperation := by
    simp [decodedOperationAt, hDecoded, hOpEq]
  obtain ⟨rest, operands, hOperands⟩ :=
    call_operands_of_stackEnough_kind kind hPrefix.static.stackLimit
      hDecodedOp
  cases stepFuel with
  | zero => simp [EvmYul.EVM.step] at hStep
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
      have hLen : state.stack.length =
          (Simulation.CallKind.args kind operands).length + rest.length := by
        rw [hStack]; simp
      have hNextStack : next.stack.length = rest.length + 1 := by
        have hStackEq := hResponse.openStateRel.stack_eq
        rw [hStackEq]
        simp [InteractionSemantics.EVMState.finishCall,
          EvmYul.EVM.State.incrPC]
      have hNextPc : next.pc =
          EvmYul.UInt256.ofNat (block.compactPc + 1) := by
        calc
          next.pc =
              (InteractionSemantics.EVMState.finishCall
                (afterDynamicChargeAt state) rest operands.callLocal
                  response).pc := hResponse.pc_eq
          _ = state.pc + EvmYul.UInt256.ofNat 1 := by
            simp [InteractionSemantics.EVMState.finishCall,
              InteractionSemantics.EVMState.installWorld,
              afterDynamicChargeAt, afterMemoryChargeAt, chargeGas,
              EvmYul.EVM.State.incrPC]
          _ = EvmYul.UInt256.ofNat (block.compactPc + 1) := by
            rw [hPc, uint256_ofNat_add]
      have hEntry :
          lookupHeight cert.heights (EvmYul.UInt256.ofNat block.compactPc) =
            some state.stack.length := by
        rw [← hPc]; exact hHeight
      have hArity := callPrimOp_args_arity kind operands
      have hInvalid : callPrimOp kind ≠ .invalid := by
        cases kind <;> simp [callPrimOp]
      have hOk := check?_blockOk hCheck hBlock
      simp only [blockOk?, hEntry, hInstr, if_neg hInvalid, hArity,
        Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hOk
      show lookupHeight cert.heights _ = _
      rw [hNextPc, hNextStack]
      have hExpected :
          state.stack.length -
              (Simulation.CallKind.args kind operands).length + 1 =
            rest.length + 1 := by
        omega
      rw [← hExpected]
      exact hOk.2

theorem heightPoint_create_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {state next : EVMState}
    {block : Compact.SourceBlock} {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (kind : Simulation.CreateKind)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .prim (createPrimOp kind))
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hHeight : HeightPoint cert.heights state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    HeightPoint cert.heights next := by
  have hDecoded := artifact_prim_decode hCompile hDecode hCode hBlock
    hInstr hPc
  have hOpEq : (createPrimOp kind).toEVM = kind.toEVMOperation := by
    cases kind <;> rfl
  have hDecodedOp : decodedOperationAt state = kind.toEVMOperation := by
    simp [decodedOperationAt, hDecoded, hOpEq]
  obtain ⟨rest, operands, hOperands⟩ :=
    create_operands_of_stackEnough_kind kind hPrefix.static.stackLimit
      hDecodedOp
  cases stepFuel with
  | zero => simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      have hActual :
          EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
              (some (kind.toEVMOperation, none))
              (afterMemoryChargeAt state) = .ok next := by
        simpa [hDecoded, hOpEq] using hStep
      obtain ⟨response, hResponse⟩ :=
        evm_step_create_responseStateRel_at kind hDecodedOp hOperands hActual
      have hStack :=
        CreateKind.stack_eq_args_append_of_evmOperands hOperands
      have hLen : state.stack.length =
          (Simulation.CreateKind.args kind operands).length +
            rest.length := by
        rw [hStack]; simp
      have hNextStack : next.stack.length = rest.length + 1 := by
        have hStackEq := hResponse.openStateRel.stack_eq
        rw [hStackEq]
        simp [InteractionSemantics.EVMState.finishCreate,
          EvmYul.EVM.State.incrPC]
      have hNextPc : next.pc =
          EvmYul.UInt256.ofNat (block.compactPc + 1) := by
        calc
          next.pc =
              (InteractionSemantics.EVMState.finishCreate
                (afterDynamicChargeAt state) rest operands.createLocal
                  response).pc := hResponse.pc_eq
          _ = state.pc + EvmYul.UInt256.ofNat 1 := by
            simp [InteractionSemantics.EVMState.finishCreate,
              InteractionSemantics.EVMState.installWorld,
              afterDynamicChargeAt, afterMemoryChargeAt, chargeGas,
              EvmYul.EVM.State.incrPC]
          _ = EvmYul.UInt256.ofNat (block.compactPc + 1) := by
            rw [hPc, uint256_ofNat_add]
      have hEntry :
          lookupHeight cert.heights (EvmYul.UInt256.ofNat block.compactPc) =
            some state.stack.length := by
        rw [← hPc]; exact hHeight
      have hArity := createPrimOp_args_arity kind operands
      have hInvalid : createPrimOp kind ≠ .invalid := by
        cases kind <;> simp [createPrimOp]
      have hOk := check?_blockOk hCheck hBlock
      simp only [blockOk?, hEntry, hInstr, if_neg hInvalid, hArity,
        Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hOk
      show lookupHeight cert.heights _ = _
      rw [hNextPc, hNextStack]
      have hExpected :
          state.stack.length -
              (Simulation.CreateKind.args kind operands).length + 1 =
            rest.length + 1 := by
        omega
      rw [← hExpected]
      exact hOk.2

/-! ## The height invariant along reachable frame states -/

theorem heightPoint_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {current next : EVMState} {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (hSentinel : Compact.decodeAt bytes
      (Compact.Program.codeByteLength artifact.program.code)
      (.prim .invalid))
    (hPoint : ArtifactFramePoint artifact bytes current)
    (hHeight : HeightPoint cert.heights current)
    (hPrefix : XSstoreStipendChecksPass validJumps current)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt current)
        (some
          ((EvmYul.EVM.decode current.executionEnv.code current.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt current) = .ok next)
    (hContinues : haltOutputAt next (decodedOperationAt current) = none) :
    HeightPoint cert.heights next := by
  rcases hPoint with ⟨hCode, hControl⟩
  cases hControl with
  | boundary block hBlock hPc =>
      generalize hInstr : block.sourceInstr = instr
      cases instr with
      | label label =>
          exact heightPoint_label_step hCompile hDecode hCheck hCode hBlock
            hInstr hPc hHeight hStep
      | push value =>
          exact heightPoint_push_step hCompile hDecode hCheck hCode hBlock
            hInstr hPc hHeight hStep
      | jump label =>
          exact heightPoint_branch_push_step hCompile hDecode hCheck hCode
            hBlock (isJumpi := false) (by simpa using hInstr) hPc hHeight
            hStep
      | jumpi label =>
          exact heightPoint_branch_push_step hCompile hDecode hCheck hCode
            hBlock (isJumpi := true) (by simpa using hInstr) hPc hHeight
            hStep
      | pushLabel target =>
          obtain ⟨_compactSize, _hSize, hEmit⟩ :=
            (Compact.compile?_blocksValid hCompile).block_emit_of_mem hBlock
          rw [hInstr] at hEmit
          simp [Compact.emitSourceBlock?, Compact.emitInstrRev?] at hEmit
      | jumpDynamic =>
          obtain ⟨_compactSize, _hSize, hEmit⟩ :=
            (Compact.compile?_blocksValid hCompile).block_emit_of_mem hBlock
          rw [hInstr] at hEmit
          simp [Compact.emitSourceBlock?, Compact.emitInstrRev?] at hEmit
      | prim op =>
          have hDecoded := artifact_prim_decode hCompile hDecode hCode
            hBlock hInstr hPc
          cases hContinuing : op.continuingStep? with
          | some primStep =>
              exact heightPoint_prim_continuing_step hCompile hDecode hCheck
                hCode hBlock hInstr hPc hContinuing hPrefix hHeight hStep
          | none =>
              by_cases hPcOp : op = .pc
              · subst op
                exact heightPoint_pc_step hCompile hDecode hCheck hCode
                  hBlock hInstr hPc hHeight hStep
              · by_cases hGasOp : op = .gas
                · subst op
                  exact heightPoint_resource_step hCompile hDecode hCheck
                    .gas hCode hBlock
                    (by simpa [resourcePrimOp] using hInstr) hPc hHeight
                    hStep
                · by_cases hStopOp : op = .stop
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
                        · have hMsizeOp : op ≠ .msize := by
                            intro h
                            subst op
                            simp [PrimOp.continuingStep?] at hContinuing
                          have hValid :
                              EvmYul.EVM.δ op.toEVM ≠ none := by
                            have hRaw := hPrefix.static.stackLimit.memoryAccess.jumps.stack.opcodeValid_raw
                            simpa [decodedOperationAt, hDecoded] using hRaw
                          rcases primOp_external_of_no_continuing op hValid
                              hPcOp hGasOp hMsizeOp hStopOp hReturnOp
                              hRevertOp hSelfdestructOp hContinuing with
                            ⟨kind, hCall⟩ | ⟨kind, hCreate⟩
                          · subst op
                            exact heightPoint_call_step hCompile hDecode
                              hCheck kind hCode hBlock hInstr hPc hPrefix
                              hHeight hStep
                          · subst op
                            exact heightPoint_create_step hCompile hDecode
                              hCheck kind hCode hBlock hInstr hPc hPrefix
                              hHeight hStep
  | branchMid block hBlock label isJumpi dest rest hInstr hLookup hPc
      hStack =>
      exact heightPoint_branchMid_step hCompile hDecode hCheck hCode hBlock
        hInstr hLookup hPc hStack hPrefix hHeight hStep
  | sentinel hPc =>
      exact False.elim
        (heightPoint_sentinel_no_success hSentinel hCode hPc hStep)

theorem heightPoint_initial {cert : Cert} {artifact : Compact.Artifact}
    {initial : EVMState}
    (hCheck : check? artifact cert = true)
    (hPc : initial.pc = EvmYul.UInt256.ofNat 0)
    (hStack : initial.stack = []) :
    HeightPoint cert.heights initial := by
  show lookupHeight cert.heights _ = _
  rw [hPc, hStack]
  simpa using check?_anchor hCheck

theorem reach_heightPoint
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {initial : EVMState}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (hSentinel : Compact.decodeAt bytes
      (Compact.Program.codeByteLength artifact.program.code)
      (.prim .invalid))
    (hFrame : ArtifactFrameInvariant artifact bytes validJumps initial)
    (hInitialHeight : HeightPoint cert.heights initial) :
    ∀ state, FrameReachable validJumps initial state →
      HeightPoint cert.heights state := by
  intro state hReach
  induction hReach with
  | initial => exact hInitialHeight
  | @next current next stepFuel hReach hPrefix hStep hContinues ih =>
      exact heightPoint_step hCompile hDecode hCheck hSentinel
        (hFrame current hReach) ih hPrefix hStep hContinues

/-! ## No reachable stack overflow -/

theorem prim_alpha_le_delta_succ (op : PrimOp) :
    (EvmYul.EVM.α op.toEVM).getD 0 ≤ (EvmYul.EVM.δ op.toEVM).getD 0 + 1 ∧
      (EvmYul.EVM.δ op.toEVM).getD 0 ≤ 20 := by
  cases op <;> exact ⟨by decide, by decide⟩

theorem pushOp_alpha_le_delta_succ
    {width : Nat} {op : EVMOp} {value : Word}
    (hFits : Compact.FitsWidth width value.toNat)
    (hOp : Compact.pushOp? width = some op) :
    (EvmYul.EVM.α op).getD 0 ≤ (EvmYul.EVM.δ op).getD 0 + 1 ∧
      (EvmYul.EVM.δ op).getD 0 ≤ 20 := by
  have hPos := hFits.1
  have hLe := hFits.2.1
  interval_cases width <;>
    simp [Compact.pushOp?] at hOp <;> cases hOp <;>
    exact ⟨by decide, by decide⟩

theorem decoded_alpha_le_delta_succ
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {state : EVMState}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hSentinel : Compact.decodeAt bytes
      (Compact.Program.codeByteLength artifact.program.code)
      (.prim .invalid))
    (hPoint : ArtifactFramePoint artifact bytes state) :
    (EvmYul.EVM.α (decodedOperationAt state)).getD 0 ≤
        (EvmYul.EVM.δ (decodedOperationAt state)).getD 0 + 1 ∧
      (EvmYul.EVM.δ (decodedOperationAt state)).getD 0 ≤ 20 := by
  rcases hPoint with ⟨hCode, hControl⟩
  cases hControl with
  | boundary block hBlock hPc =>
      generalize hInstr : block.sourceInstr = instr
      cases instr with
      | label label =>
          obtain ⟨located, hMem, hLocatedPc, hLocatedInstr⟩ :=
            compact_label_entry_mem hCompile hBlock hInstr
          obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
            hDecode.decodes located hMem
          rw [hLocatedInstr] at hInstrDecoded
          simp [Compact.Instr.decoded?] at hInstrDecoded
          subst decoded
          have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
            hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
          have hDecoded :
              EvmYul.EVM.decode state.executionEnv.code state.pc =
                some (EvmYul.Operation.JUMPDEST, none) := by
            simpa [hCode, hStatePc] using hBytesDecoded
          simp [decodedOperationAt, hDecoded]
          exact ⟨by decide, by decide⟩
      | push value =>
          obtain ⟨width, located, hWidth, hMem, hLocatedPc, hLocatedInstr⟩ :=
            compact_push_entry_mem hCompile hBlock hInstr
          have hLocatedValid :=
            (List.forall_iff_forall_mem.mp
              (Compact.compile?_valid hCompile).wellFormed.1) located hMem
          rw [hLocatedInstr] at hLocatedValid
          have hFits : Compact.FitsWidth width value.toNat := by
            simpa [Compact.Instr.Valid] using hLocatedValid
          obtain ⟨op, hOp⟩ := Compact.exists_pushOp_of_width
            ⟨hFits.1, hFits.2.1⟩
          obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
            hDecode.decodes located hMem
          rw [hLocatedInstr] at hInstrDecoded
          simp [Compact.Instr.decoded?, hOp] at hInstrDecoded
          subst decoded
          have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
            hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
          have hDecoded :
              EvmYul.EVM.decode state.executionEnv.code state.pc =
                some (op, some (value, width)) := by
            simpa [hCode, hStatePc] using hBytesDecoded
          have hGoal := pushOp_alpha_le_delta_succ hFits hOp
          simpa [decodedOperationAt, hDecoded] using hGoal
      | jump label =>
          obtain ⟨dest, located, hLookup, hMem, hLocatedPc, hLocatedInstr⟩ :=
            compact_branch_entry_mem hCompile hBlock
              (isJumpi := false) (by simpa using hInstr)
          have hLocatedValid :=
            (List.forall_iff_forall_mem.mp
              (Compact.compile?_valid hCompile).wellFormed.1) located hMem
          rw [hLocatedInstr] at hLocatedValid
          have hFits : Compact.FitsWidth artifact.branchWidth
              (EvmYul.UInt256.ofNat dest).toNat := by
            simpa [Compact.Instr.Valid] using hLocatedValid
          obtain ⟨op, hOp⟩ := Compact.exists_pushOp_of_width
            ⟨hFits.1, hFits.2.1⟩
          obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
            hDecode.decodes located hMem
          rw [hLocatedInstr] at hInstrDecoded
          simp [Compact.Instr.decoded?, hOp] at hInstrDecoded
          subst decoded
          have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
            hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
          have hDecoded :
              EvmYul.EVM.decode state.executionEnv.code state.pc =
                some (op, some (EvmYul.UInt256.ofNat dest,
                  artifact.branchWidth)) := by
            simpa [hCode, hStatePc] using hBytesDecoded
          have hGoal := pushOp_alpha_le_delta_succ hFits hOp
          simpa [decodedOperationAt, hDecoded] using hGoal
      | jumpi label =>
          obtain ⟨dest, located, hLookup, hMem, hLocatedPc, hLocatedInstr⟩ :=
            compact_branch_entry_mem hCompile hBlock
              (isJumpi := true) (by simpa using hInstr)
          have hLocatedValid :=
            (List.forall_iff_forall_mem.mp
              (Compact.compile?_valid hCompile).wellFormed.1) located hMem
          rw [hLocatedInstr] at hLocatedValid
          have hFits : Compact.FitsWidth artifact.branchWidth
              (EvmYul.UInt256.ofNat dest).toNat := by
            simpa [Compact.Instr.Valid] using hLocatedValid
          obtain ⟨op, hOp⟩ := Compact.exists_pushOp_of_width
            ⟨hFits.1, hFits.2.1⟩
          obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
            hDecode.decodes located hMem
          rw [hLocatedInstr] at hInstrDecoded
          simp [Compact.Instr.decoded?, hOp] at hInstrDecoded
          subst decoded
          have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
            hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
          have hDecoded :
              EvmYul.EVM.decode state.executionEnv.code state.pc =
                some (op, some (EvmYul.UInt256.ofNat dest,
                  artifact.branchWidth)) := by
            simpa [hCode, hStatePc] using hBytesDecoded
          have hGoal := pushOp_alpha_le_delta_succ hFits hOp
          simpa [decodedOperationAt, hDecoded] using hGoal
      | pushLabel target =>
          obtain ⟨_compactSize, _hSize, hEmit⟩ :=
            (Compact.compile?_blocksValid hCompile).block_emit_of_mem hBlock
          rw [hInstr] at hEmit
          simp [Compact.emitSourceBlock?, Compact.emitInstrRev?] at hEmit
      | jumpDynamic =>
          obtain ⟨_compactSize, _hSize, hEmit⟩ :=
            (Compact.compile?_blocksValid hCompile).block_emit_of_mem hBlock
          rw [hInstr] at hEmit
          simp [Compact.emitSourceBlock?, Compact.emitInstrRev?] at hEmit
      | prim op =>
          have hDecoded := artifact_prim_decode hCompile hDecode hCode
            hBlock hInstr hPc
          have hGoal := prim_alpha_le_delta_succ op
          simpa [decodedOperationAt, hDecoded] using hGoal
  | branchMid block hBlock label isJumpi dest rest hInstr hLookup hPc
      hStack =>
      obtain ⟨located, hMem, hLocatedPc, hLocatedInstr⟩ :=
        compact_branch_midpoint_mem hCompile hBlock hInstr
      obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
        hDecode.decodes located hMem
      have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
        hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
      cases hJumpi : isJumpi
      · rw [hJumpi] at hLocatedInstr
        simp only [Bool.false_eq_true, if_false] at hLocatedInstr
        rw [hLocatedInstr] at hInstrDecoded
        simp [Compact.Instr.decoded?] at hInstrDecoded
        subst decoded
        have hDecoded :
            EvmYul.EVM.decode state.executionEnv.code state.pc =
              some (EvmYul.Operation.JUMP, none) := by
          simpa [hCode, hStatePc] using hBytesDecoded
        simp [decodedOperationAt, hDecoded]
        exact ⟨by decide, by decide⟩
      · rw [hJumpi] at hLocatedInstr
        simp only [if_true] at hLocatedInstr
        rw [hLocatedInstr] at hInstrDecoded
        simp [Compact.Instr.decoded?] at hInstrDecoded
        subst decoded
        have hDecoded :
            EvmYul.EVM.decode state.executionEnv.code state.pc =
              some (EvmYul.Operation.JUMPI, none) := by
          simpa [hCode, hStatePc] using hBytesDecoded
        simp [decodedOperationAt, hDecoded]
        exact ⟨by decide, by decide⟩
  | sentinel hPc =>
      obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ := hSentinel
      simp [Compact.Instr.decoded?] at hInstrDecoded
      subst decoded
      have hDecoded :
          EvmYul.EVM.decode state.executionEnv.code state.pc =
            some (EvmYul.Operation.INVALID, none) := by
        simpa [hCode, hPc] using hBytesDecoded
      simp [decodedOperationAt, hDecoded]
      exact ⟨by decide, by decide⟩

theorem noOverflow_of_heightPoint
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {state : EVMState}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (hSentinel : Compact.decodeAt bytes
      (Compact.Program.codeByteLength artifact.program.code)
      (.prim .invalid))
    (hPoint : ArtifactFramePoint artifact bytes state)
    (hHeight : HeightPoint cert.heights state) :
    ¬ stackOverflowAt state := by
  intro hOverflow
  unfold stackOverflowAt at hOverflow
  have hLen : state.stack.length ≤ stackCap :=
    lookupHeight_le_cap (check?_bounded hCheck) hHeight
  obtain ⟨hNet, hDelta⟩ :=
    decoded_alpha_le_delta_succ hCompile hDecode hSentinel hPoint
  unfold stackCap at hLen
  omega

/-- Certified programs never trip the interpreter's stack-limit precheck at
any reachable frame state. -/
theorem reach_noOverflow
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {initial : EVMState}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (hSentinel : Compact.decodeAt bytes
      (Compact.Program.codeByteLength artifact.program.code)
      (.prim .invalid))
    (hFrame : ArtifactFrameInvariant artifact bytes validJumps initial)
    (hInitialHeight : HeightPoint cert.heights initial) :
    ∀ state, FrameReachable validJumps initial state →
      ¬ stackOverflowAt state := by
  intro state hReach
  exact noOverflow_of_heightPoint hCompile hDecode hCheck hSentinel
    (hFrame state hReach)
    (reach_heightPoint hCompile hDecode hCheck hSentinel hFrame
      hInitialHeight state hReach)

end StackHeadroom
end Assembly
end EvmCompiler
