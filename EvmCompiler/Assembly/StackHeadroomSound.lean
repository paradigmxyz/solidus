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

/-! ## The gasful interpreter cannot report `StackOverflow` on certified code

`EvmYul.EVM.X` raises `StackOverflow` only from its per-step precheck, which
`reach_noOverflow` rules out at every reachable state.  The remaining error
sources (the step functions themselves and child frames) carry other labels,
established below. -/

theorem primStep_run_error_ne_stackOverflow
    {primStep : PrimStep} {state : EvmYul.EVM.State}
    {err : EVMException}
    (hRun : primStep.run state = .error err) :
    err ≠ EvmYul.EVM.ExecutionException.StackOverflow := by
  intro hEq
  subst hEq
  cases primStep <;>
    simp only [PrimStep.run, EvmYul.EVM.execBinOp, EvmYul.EVM.execUnOp,
      EvmYul.EVM.execTriOp, EvmYul.EVM.executionEnvOp,
      EvmYul.EVM.unaryExecutionEnvOp, EvmYul.EVM.machineStateOp,
      EvmYul.EVM.binaryMachineStateOp, EvmYul.EVM.binaryMachineStateOp',
      EvmYul.EVM.ternaryMachineStateOp, EvmYul.EVM.stateOp,
      EvmYul.EVM.unaryStateOp, EvmYul.EVM.binaryStateOp,
      EvmYul.EVM.ternaryCopyOp, EvmYul.EVM.quaternaryCopyOp,
      EvmYul.dup, EvmYul.swap] at hRun <;>
    (repeat' split at hRun) <;>
    first
      | cases Except.error.inj hRun
      | cases hRun
      | simp_all

/-- On certified code, a failing charged step at any generated control point
never carries the `StackOverflow` label. -/
theorem step_error_ne_stackOverflow_at
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {validJumps : Array Word} {state : EVMState} {stepFuel : Nat}
    {err : EVMException}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hSentinel : Compact.decodeAt bytes
      (Compact.Program.codeByteLength artifact.program.code)
      (.prim .invalid))
    (hPoint : ArtifactFramePoint artifact bytes state)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .error err) :
    err ≠ EvmYul.EVM.ExecutionException.StackOverflow := by
  intro hEq
  subst hEq
  rcases hPoint with ⟨hCode, hControl⟩
  cases stepFuel with
  | zero =>
      simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
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
          rw [hDecoded] at hStep
          simp only [Option.getD_some] at hStep
          rw [evm_step_jumpdest_eq_next fuel state none] at hStep
          cases hStep
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
          rw [hDecoded] at hStep
          simp only [Option.getD_some] at hStep
          rw [evm_step_push_eq_next fuel state value hFits hOp] at hStep
          cases hStep
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
          rw [hDecoded] at hStep
          simp only [Option.getD_some] at hStep
          rw [evm_step_push_eq_next fuel state
            (EvmYul.UInt256.ofNat dest) hFits hOp] at hStep
          cases hStep
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
          rw [hDecoded] at hStep
          simp only [Option.getD_some] at hStep
          rw [evm_step_push_eq_next fuel state
            (EvmYul.UInt256.ofNat dest) hFits hOp] at hStep
          cases hStep
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
              have hDecodedOp : decodedOperationAt state = op.toEVM := by
                simp [decodedOperationAt, hDecoded]
              have hStaticPermits : continuingPrimStaticPermits state op :=
                continuingPrimStaticPermits_of_static_check hPrefix.static
                  hDecodedOp
              have hGasful :
                  EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
                      (some (op.toEVM, none)) (afterMemoryChargeAt state) =
                    .error EvmYul.EVM.ExecutionException.StackOverflow := by
                simpa [hDecoded] using hStep
              have hPrim :
                  op.step (afterEVMInstructionChargeAt state) =
                    .error EvmYul.EVM.ExecutionException.StackOverflow := by
                rw [← hGasful]
                exact (evm_step_continuing_prim_after_charges hContinuing
                  trivial hStaticPermits).symm
              rw [PrimOp.step_eq_continuingStep_run hContinuing] at hPrim
              exact primStep_run_error_ne_stackOverflow hPrim rfl
          | none =>
              by_cases hPcOp : op = .pc
              · subst op
                have hActual :
                    EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
                        (some (EvmYul.Operation.PC, none))
                        (afterMemoryChargeAt state) =
                      .error
                        EvmYul.EVM.ExecutionException.StackOverflow := by
                  simpa [hDecoded, PrimOp.toEVM] using hStep
                rw [evm_step_pc_eq_next] at hActual
                cases hActual
              · by_cases hGasOp : op = .gas
                · subst op
                  have hActual :
                      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
                          (some ((resourcePrimOp .gas).toEVM, none))
                          (afterMemoryChargeAt state) =
                        .error
                          EvmYul.EVM.ExecutionException.StackOverflow := by
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
                        have hRaw := hPrefix.static.stackLimit.memoryAccess.jumps.stack.stackEnough
                        simpa [decodedOperationAt, hDecoded, PrimOp.toEVM,
                          EvmYul.EVM.δ] using hRaw
                      match hStack : state.stack with
                      | [] => exact hEnough (by simp [hStack])
                      | [top] => exact hEnough (by simp [hStack])
                      | top :: second :: rest =>
                          have hPop :
                              (afterEVMInstructionChargeAt
                                  state).stack.pop2 =
                                some ⟨rest, top, second⟩ := by
                            rw [afterEVMInstructionChargeAt_stack, hStack]
                            rfl
                          have hPair :
                              ((EvmYul.EVM.decode state.executionEnv.code
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
                          have hRaw := hPrefix.static.stackLimit.memoryAccess.jumps.stack.stackEnough
                          simpa [decodedOperationAt, hDecoded,
                            PrimOp.toEVM, EvmYul.EVM.δ] using hRaw
                        match hStack : state.stack with
                        | [] => exact hEnough (by simp [hStack])
                        | [top] => exact hEnough (by simp [hStack])
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
                          have hEnough : ¬ state.stack.length < 1 := by
                            have hRaw := hPrefix.static.stackLimit.memoryAccess.jumps.stack.stackEnough
                            simpa [decodedOperationAt, hDecoded,
                              PrimOp.toEVM, EvmYul.EVM.δ] using hRaw
                          match hStack : state.stack with
                          | [] => exact hEnough (by simp [hStack])
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
                              rw [evm_step_selfdestruct_eq_next fuel state
                                recipient rest hStack] at hStep
                              cases hStep
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
                            have hOpEq :
                                (callPrimOp kind).toEVM =
                                  kind.toEVMOperation := by
                              cases kind <;> rfl
                            have hDecodedOp :
                                decodedOperationAt state =
                                  kind.toEVMOperation := by
                              simp [decodedOperationAt, hDecoded, hOpEq]
                            obtain ⟨rest, operands, hOperands⟩ :=
                              call_operands_of_stackEnough_kind kind
                                hPrefix.static.stackLimit hDecodedOp
                            have hActual :
                                EvmYul.EVM.step (fuel + 1)
                                    (dynamicGasCostAt state)
                                    (some (kind.toEVMOperation, none))
                                    (afterMemoryChargeAt state) =
                                  .error
                                    EvmYul.EVM.ExecutionException.StackOverflow := by
                              simpa [hDecoded, hOpEq] using hStep
                            have hErr :=
                              evm_step_call_error_eq_outOfFuel_at
                                hOperands hActual
                            cases hErr
                          · subst op
                            have hOpEq :
                                (createPrimOp kind).toEVM =
                                  kind.toEVMOperation := by
                              cases kind <;> rfl
                            have hDecodedOp :
                                decodedOperationAt state =
                                  kind.toEVMOperation := by
                              simp [decodedOperationAt, hDecoded, hOpEq]
                            obtain ⟨rest, operands, hOperands⟩ :=
                              create_operands_of_stackEnough_kind kind
                                hPrefix.static.stackLimit hDecodedOp
                            have hActual :
                                EvmYul.EVM.step (fuel + 1)
                                    (dynamicGasCostAt state)
                                    (some (kind.toEVMOperation, none))
                                    (afterMemoryChargeAt state) =
                                  .error
                                    EvmYul.EVM.ExecutionException.StackOverflow := by
                              simpa [hDecoded, hOpEq] using hStep
                            have hErr :=
                              evm_step_create_positive_error_eq_outOfGas_at
                                hOperands hActual
                            cases hErr
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
        rw [hDecoded] at hStep
        simp only [Option.getD_some] at hStep
        rw [evm_step_jump_eq_next fuel state none rest
          (EvmYul.UInt256.ofNat dest) hStack] at hStep
        cases hStep
      · rw [hJumpi] at hLocatedInstr
        simp only [if_true] at hLocatedInstr
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
            exact hEnough (by simp [hStack])
        | cons cond tail =>
            have hStack' : state.stack =
                EvmYul.UInt256.ofNat dest :: cond :: tail := by
              simpa using hStack
            rw [hDecoded] at hStep
            simp only [Option.getD_some] at hStep
            rw [evm_step_jumpi_eq_next fuel state none tail
              (EvmYul.UInt256.ofNat dest) cond hStack'] at hStep
            cases hStep
  | sentinel hPc =>
      obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ := hSentinel
      simp [Compact.Instr.decoded?] at hInstrDecoded
      subst decoded
      have hDecoded :
          EvmYul.EVM.decode state.executionEnv.code state.pc =
            some (EvmYul.Operation.INVALID, none) := by
        simpa [hCode, hPc] using hBytesDecoded
      rw [hDecoded] at hStep
      simp only [Option.getD_some] at hStep
      change EvmYul.step (τ := .EVM) EvmYul.Operation.INVALID none
        { { afterMemoryChargeAt state with
              execLength := (afterMemoryChargeAt state).execLength + 1 } with
          gasAvailable := (afterMemoryChargeAt state).gasAvailable -
            EvmYul.UInt256.ofNat (dynamicGasCostAt state) } =
        Except.error EvmYul.EVM.ExecutionException.StackOverflow at hStep
      change (Except.error EvmYul.EVM.ExecutionException.InvalidInstruction :
          Except EVMException EVMState) =
        Except.error EvmYul.EVM.ExecutionException.StackOverflow at hStep
      cases hStep

/-- Fuel induction over `EvmYul.EVM.X`: with the reachable no-overflow
invariant and step-error classification, the frame run never reports
`StackOverflow`. -/
theorem x_ne_stackOverflow_of_invariants
    {validJumps : Array Word} {initial : EVMState}
    (hNoOverflow :
      ∀ s, FrameReachable validJumps initial s → ¬ stackOverflowAt s)
    (hStepErr :
      ∀ (s : EVMState) (stepFuel : Nat) (err : EVMException),
        FrameReachable validJumps initial s →
        XSstoreStipendChecksPass validJumps s →
        EvmYul.EVM.step stepFuel (dynamicGasCostAt s)
            (some
              ((EvmYul.EVM.decode s.executionEnv.code s.pc).getD
                (EvmYul.Operation.STOP, none)))
            (afterMemoryChargeAt s) = .error err →
        err ≠ EvmYul.EVM.ExecutionException.StackOverflow) :
    ∀ (fuel : Nat) (s : EVMState), FrameReachable validJumps initial s →
      EvmYul.EVM.X fuel validJumps s ≠
        .error EvmYul.EVM.ExecutionException.StackOverflow := by
  intro fuel
  induction fuel with
  | zero =>
      intro s _hReach hEq
      simp [EvmYul.EVM.X] at hEq
  | succ f ih =>
      intro s hReach hEq
      by_cases hMem : s.gasAvailable.toNat < memoryExpansionCostAt s
      · rw [x_outOfGas_before_memory_charge hMem] at hEq
        cases Except.error.inj hEq
      by_cases hDyn :
          (afterMemoryChargeAt s).gasAvailable.toNat < dynamicGasCostAt s
      · rw [x_outOfGas_before_dynamic_charge hMem hDyn] at hEq
        cases Except.error.inj hEq
      have hGas : XGasChecksPass s := ⟨hMem, hDyn⟩
      by_cases hOpc : EvmYul.EVM.δ (decodedOperationAt s) = none
      · rw [x_invalid_instruction_after_gas_checks hGas hOpc] at hEq
        cases Except.error.inj hEq
      by_cases hUnder :
          s.stack.length < (EvmYul.EVM.δ (decodedOperationAt s)).getD 0
      · rw [x_stack_underflow_after_gas_opcode_check hGas hOpc hUnder]
          at hEq
        cases Except.error.inj hEq
      have hOpcode : XOpcodeStackChecksPass s := ⟨hGas, hOpc, hUnder⟩
      by_cases hBJ : badJumpAt validJumps s
      · rw [x_bad_jump_destination_after_stack_check hOpcode hBJ] at hEq
        cases Except.error.inj hEq
      by_cases hBJI : badJumpiAt validJumps s
      · rw [x_bad_jumpi_destination_after_stack_check hOpcode hBJI] at hEq
        cases Except.error.inj hEq
      have hJumps : XJumpChecksPass validJumps s := ⟨hOpcode, hBJ, hBJI⟩
      by_cases hRdc : invalidReturnDataCopyAt s
      · rw [x_invalid_returndatacopy_after_jump_checks hJumps hRdc] at hEq
        cases Except.error.inj hEq
      have hMemoryAccess : XMemoryAccessChecksPass validJumps s :=
        ⟨hJumps, hRdc⟩
      have hNoOverflowAt : ¬ stackOverflowAt s := hNoOverflow s hReach
      have hStackLimit : XStackLimitChecksPass validJumps s :=
        ⟨hMemoryAccess, hNoOverflowAt⟩
      by_cases hStatic : staticModeViolationAt s
      · rw [x_static_mode_violation_after_stack_limit_checks hStackLimit
          hStatic] at hEq
        cases Except.error.inj hEq
      have hStaticPass : XStaticChecksPass validJumps s :=
        ⟨hStackLimit, hStatic⟩
      by_cases hSstore : sstoreStipendOutOfGasAt s
      · rw [x_sstore_stipend_outOfGas_after_static_check hStaticPass
          hSstore] at hEq
        cases Except.error.inj hEq
      have hPrefixS : XSstoreStipendChecksPass validJumps s :=
        ⟨hStaticPass, hSstore⟩
      by_cases hCreateBig :
          EvmYul.Operation.isCreate (decodedOperationAt s) = true ∧
            (EvmYul.UInt256.ofNat 49152) <
              s.stack[2]?.getD (EvmYul.UInt256.ofNat 0)
      · have hCreateOp :=
          operation_eq_create_or_create2_of_isCreate hCreateBig.1
        rw [x_create_initcode_outOfGas_after_sstore_check hPrefixS
          hCreateOp hCreateBig.2] at hEq
        cases Except.error.inj hEq
      · have hX :=
          x_after_prechecks_of_step_result (fuel := f)
            (validJumps := validJumps) hPrefixS hCreateBig rfl
        rw [hX] at hEq
        cases hStepRes :
            EvmYul.EVM.step f (dynamicGasCostAt s)
              (some
                ((EvmYul.EVM.decode s.executionEnv.code s.pc).getD
                  (EvmYul.Operation.STOP, none)))
              (afterMemoryChargeAt s) with
        | error err =>
            rw [hStepRes] at hEq
            simp only [xPostStepExceptResult] at hEq
            exact hStepErr s f err hReach hPrefixS hStepRes
              (Except.error.inj hEq)
        | ok nxt =>
            rw [hStepRes] at hEq
            simp only [xPostStepExceptResult] at hEq
            cases hHalt : haltOutputAt nxt (decodedOperationAt s) with
            | none =>
                have hRun :
                    xPostStepResult f validJumps (decodedOperationAt s)
                        nxt =
                      EvmYul.EVM.X f validJumps nxt := by
                  unfold xPostStepResult
                  rw [hHalt]
                rw [hRun] at hEq
                exact ih nxt
                  (FrameReachable.next hReach hPrefixS hStepRes hHalt) hEq
            | some output =>
                have hOk :
                    ∃ result,
                      xPostStepResult f validJumps (decodedOperationAt s)
                          nxt =
                        .ok result := by
                  unfold xPostStepResult
                  simp only [hHalt]
                  split
                  · exact ⟨_, rfl⟩
                  · exact ⟨_, rfl⟩
                obtain ⟨result, hOk⟩ := hOk
                rw [hOk] at hEq
                cases hEq

/-- Crown composition at the compact-artifact level: on certified code
entered at pc `0` with an empty stack, the gasful frame interpreter can
never return `StackOverflow`. -/
theorem x_ne_stackOverflow_of_cert
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
    (hPc : initial.pc = EvmYul.UInt256.ofNat 0)
    (hStack : initial.stack = []) :
    ∀ fuel, EvmYul.EVM.X fuel validJumps initial ≠
      .error EvmYul.EVM.ExecutionException.StackOverflow := by
  intro fuel
  have hInitialHeight := heightPoint_initial hCheck hPc hStack
  exact x_ne_stackOverflow_of_invariants
    (reach_noOverflow hCompile hDecode hCheck hSentinel hFrame
      hInitialHeight)
    (fun s stepFuel err hReach hPrefix hStep =>
      step_error_ne_stackOverflow_at hCompile hDecode hSentinel
        (hFrame s hReach) hPrefix hStep)
    fuel initial .initial

/-! ## Escape-free refinement view -/

/-- `RunRefinesOpen` with the `stackOverflow` escape constructor removed. -/
inductive RunRefinesOpenNoStackOverflow
    (gasful : Except EVMException (EvmYul.EVM.ExecutionResult EVMState))
    (openRun : Simulation.Interaction EVMException StepResult) :
    Simulation.Interaction.Transcript → Prop where
  | completed {transcript openDone} :
      Simulation.Interaction.Executes openRun transcript openDone →
      DoneRel gasful openDone →
      RunRefinesOpenNoStackOverflow gasful openRun transcript
  | exceptionalFrame {transcript gasErr openErr} :
      gasErr ≠ EvmYul.EVM.ExecutionException.OutOfFuel →
      openErr ≠ EvmYul.EVM.ExecutionException.OutOfFuel →
      gasful = .error gasErr →
      Simulation.Interaction.Executes openRun transcript (.error openErr) →
      RunRefinesOpenNoStackOverflow gasful openRun transcript
  | outOfGas {transcript} :
      gasful = .error EvmYul.EVM.ExecutionException.OutOfGass →
      Simulation.Interaction.Follows openRun transcript →
      RunRefinesOpenNoStackOverflow gasful openRun transcript
  | outOfFuel {transcript} :
      gasful = .error EvmYul.EVM.ExecutionException.OutOfFuel →
      Simulation.Interaction.Follows openRun transcript →
      RunRefinesOpenNoStackOverflow gasful openRun transcript
  | badJumpDestination {transcript} :
      gasful = .error EvmYul.EVM.ExecutionException.BadJumpDestination →
      Simulation.Interaction.Follows openRun transcript →
      RunRefinesOpenNoStackOverflow gasful openRun transcript

/-- Any refinement witness whose gasful side is known not to be a
`StackOverflow` error loses the escape constructor. -/
theorem runRefinesOpenNoStackOverflow_of_ne
    {gasful : Except EVMException (EvmYul.EVM.ExecutionResult EVMState)}
    {openRun : Simulation.Interaction EVMException StepResult}
    {transcript : Simulation.Interaction.Transcript}
    (hRefines : GasfulBridge.RunRefinesOpen gasful openRun transcript)
    (hNe :
      gasful ≠ .error EvmYul.EVM.ExecutionException.StackOverflow) :
    RunRefinesOpenNoStackOverflow gasful openRun transcript := by
  cases hRefines with
  | completed hExec hDone => exact .completed hExec hDone
  | exceptionalFrame hGasErr hOpenErr hGas hExec =>
      exact .exceptionalFrame hGasErr hOpenErr hGas hExec
  | outOfGas hGas hFollow => exact .outOfGas hGas hFollow
  | outOfFuel hFuel hFollow => exact .outOfFuel hFuel hFollow
  | badJumpDestination hBad hFollow => exact .badJumpDestination hBad hFollow
  | stackOverflow hOverflow hFollow => exact absurd hOverflow hNe

end StackHeadroom
end Assembly
end EvmCompiler
