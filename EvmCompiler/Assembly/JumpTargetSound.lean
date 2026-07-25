import EvmCompiler.Assembly.JumpdestScan
import EvmCompiler.Assembly.GasfulBridgeLayout

/-!
# The gasful interpreter cannot report `BadJumpDestination` on compiled code

`EvmYul.EVM.X` raises `BadJumpDestination` only from its per-step jump
precheck: a decoded `JUMP`/`JUMPI` whose stack-head target is not in the
`validJumps` table.  The compact compiler emits fixed-label branches only --
every branch is `PUSH <dest>; JUMP[I]` with `dest` drawn from the label
table, and every label lowers to a located `JUMPDEST` at exactly `dest`.
With the jumpdest-scan membership fact of
`EvmCompiler.Assembly.JumpdestScan`, every reachable control point therefore
passes the jump precheck whenever `validJumps` lists all label destinations
-- in particular for the interpreter's own entry table
`EvmYul.EVM.D_J bytes 0`.

The module mirrors the `StackOverflow`-exclusion campaign of
`StackHeadroomSound`, but needs no stack certificate: the control-point
layout invariant alone rules the label out.

* `artifactFramePoint_not_badJump`: no generated control point trips either
  jump precheck.
* `step_error_ne_badJumpDestination_at` / `primStep_run_error_ne_badJumpDestination`:
  failing charged steps never carry the label (child-frame errors collapse
  to `OutOfFuel`/`OutOfGass` at the call boundary).
* `x_ne_badJumpDestination_of_frame`: the frame run never returns the label.
* `RunRefinesOpenNoBadJump` / `runRefinesOpenNoBadJump_of_ne`: the bridge
  outcome view without the `badJumpDestination` escape constructor.
-/

namespace EvmCompiler.Assembly.GasfulBridge

/-! ## Label destinations are emitted jumpdests listed by the scanner -/

/-- A successful compact label-table lookup names an emitted `JUMPDEST` at
exactly the looked-up destination. -/
theorem compact_lookup_destination_jumpdest_mem
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {label : Label} {dest : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hLookup : Compact.lookupLabel? artifact.labels label = some dest) :
    ∃ located, located ∈ artifact.program.code ∧ located.pc = dest ∧
      located.instr = .jumpdest := by
  obtain ⟨sourceDest, hSourceDest⟩ :=
    Compact.compile?_physical_labelPc_of_lookup hCompile hLookup
  have hAt := Assembly.Program.instrAtPc_of_labelPc hSourceDest
  obtain ⟨block, hBlock, _hBlockPc, hInstr⟩ :=
    (Compact.compile?_blocksValid hCompile).block_of_instrAtPc hAt
  have hConsistent :=
    (Compact.compile?_valid hCompile).labelsConsistent block hBlock label hInstr
  rw [hLookup] at hConsistent
  have hDest : block.compactPc = dest :=
    (Option.some.inj hConsistent).symm
  obtain ⟨located, hMem, hPc, hJumpdest⟩ :=
    compact_label_entry_mem hCompile hBlock hInstr
  exact ⟨located, hMem, hPc.trans hDest, hJumpdest⟩

/-- `validJumps` lists every compact label destination. This is the only
jump-table fact the bad-jump exclusion needs; `EvmYul.EVM.D_J` satisfies it
on any byte image that decodes the compiled program. -/
def LabelTargetsListed
    (artifact : Compact.Artifact) (validJumps : Array Word) : Prop :=
  ∀ label dest,
    Compact.lookupLabel? artifact.labels label = some dest →
      validJumps.contains (EvmYul.UInt256.ofNat dest) = true

/-- EVMYulLean's own jumpdest table over any byte image that decodes the
compiled program lists every compact label destination. -/
theorem labelTargetsListed_D_J
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes) :
    LabelTargetsListed artifact
      (EvmYul.EVM.D_J bytes (EvmYul.UInt256.ofNat 0)) := by
  intro label dest hLookup
  obtain ⟨located, hMem, hPc, hJumpdest⟩ :=
    compact_lookup_destination_jumpdest_mem hCompile hLookup
  have hWellFormed := (Compact.compile?_valid hCompile).wellFormed
  have hListed := Compact.D_J_contains_of_decodingCorrect
    hWellFormed.2.1 hWellFormed.2.2.1 hDecode hMem hJumpdest
  rw [hPc] at hListed
  exact hListed

/-! ## Reachable control points pass the jump prechecks -/

/-- `PrimOp` lowering never produces the dynamic-jump opcodes. -/
theorem primOp_toEVM_ne_jump (op : PrimOp) :
    op.toEVM ≠ EvmYul.Operation.JUMP ∧
      op.toEVM ≠ EvmYul.Operation.JUMPI := by
  cases op <;> refine ⟨fun h => ?_, fun h => ?_⟩ <;> cases h

/-- No generated control point trips the interpreter's `JUMP`/`JUMPI`
prechecks when `validJumps` lists every label destination. -/
theorem artifactFramePoint_not_badJump
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {validJumps : Array Word} {state : EVMState}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hSentinel : Compact.decodeAt bytes
      (Compact.Program.codeByteLength artifact.program.code)
      (.prim .invalid))
    (hPoint : ArtifactFramePoint artifact bytes state)
    (hListed : LabelTargetsListed artifact validJumps) :
    ¬ badJumpAt validJumps state ∧ ¬ badJumpiAt validJumps state := by
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
          constructor
          · intro hBad
            have hOp := hBad.1
            simp [decodedOperationAt, hDecoded] at hOp
          · intro hBad
            have hOp := hBad.1
            simp [decodedOperationAt, hDecoded] at hOp
      | push value =>
          obtain ⟨width, located, hWidth, hMem, hLocatedPc, hLocatedInstr⟩ :=
            compact_push_entry_mem hCompile hBlock hInstr
          by_cases hZeroWidth : width = 0
          · subst hZeroWidth
            have hValueZero := Compact.pushWidthAt?_zero_value hWidth
            subst hValueZero
            have hInstr0 : located.instr = .push0 := by
              simpa [Compact.pushInstrOfWidth] using hLocatedInstr
            obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
              hDecode.decodes located hMem
            rw [hInstr0] at hInstrDecoded
            simp [Compact.Instr.decoded?] at hInstrDecoded
            subst decoded
            have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
              hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
            have hDecoded :
                EvmYul.EVM.decode state.executionEnv.code state.pc =
                  some (EvmYul.Operation.PUSH0, none) := by
              simpa [hCode, hStatePc] using hBytesDecoded
            constructor
            · intro hBad
              have hOpEq := hBad.1
              simp [decodedOperationAt, hDecoded] at hOpEq
            · intro hBad
              have hOpEq := hBad.1
              simp [decodedOperationAt, hDecoded] at hOpEq
          simp only [Compact.pushInstrOfWidth, if_neg hZeroWidth]
            at hLocatedInstr
          have hLocatedValid :=
            (List.forall_iff_forall_mem.mp
              (Compact.compile?_valid hCompile).wellFormed.1) located hMem
          rw [hLocatedInstr] at hLocatedValid
          have hFits : Compact.FitsWidth width value.toNat := by
            simpa [Compact.Instr.Valid] using hLocatedValid
          obtain ⟨op, hOp⟩ := Compact.exists_pushOp_of_width
            ⟨hFits.1, hFits.2.1⟩
          have hArgWidth :=
            (Compact.pushOp?_properties ⟨hFits.1, hFits.2.1⟩ hOp).2
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
      | jump label =>
          obtain ⟨dest, located, hLookup, hMem, hLocatedPc, hLocatedInstr⟩ :=
            compact_branch_entry_mem hCompile hBlock
              (isJumpi := false) (by simpa using hInstr)
          have hLocatedValid :=
            (List.forall_iff_forall_mem.mp
              (Compact.compile?_valid hCompile).wellFormed.1) located hMem
          rw [hLocatedInstr] at hLocatedValid
          have hFits : Compact.FitsWidth (artifact.branchWidthAt block)
              (EvmYul.UInt256.ofNat dest).toNat := by
            simpa [Compact.Instr.Valid] using hLocatedValid
          obtain ⟨op, hOp⟩ := Compact.exists_pushOp_of_width
            ⟨hFits.1, hFits.2.1⟩
          have hArgWidth :=
            (Compact.pushOp?_properties ⟨hFits.1, hFits.2.1⟩ hOp).2
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
                  artifact.branchWidthAt block)) := by
            simpa [hCode, hStatePc] using hBytesDecoded
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
      | jumpi label =>
          obtain ⟨dest, located, hLookup, hMem, hLocatedPc, hLocatedInstr⟩ :=
            compact_branch_entry_mem hCompile hBlock
              (isJumpi := true) (by simpa using hInstr)
          have hLocatedValid :=
            (List.forall_iff_forall_mem.mp
              (Compact.compile?_valid hCompile).wellFormed.1) located hMem
          rw [hLocatedInstr] at hLocatedValid
          have hFits : Compact.FitsWidth (artifact.branchWidthAt block)
              (EvmYul.UInt256.ofNat dest).toNat := by
            simpa [Compact.Instr.Valid] using hLocatedValid
          obtain ⟨op, hOp⟩ := Compact.exists_pushOp_of_width
            ⟨hFits.1, hFits.2.1⟩
          have hArgWidth :=
            (Compact.pushOp?_properties ⟨hFits.1, hFits.2.1⟩ hOp).2
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
                  artifact.branchWidthAt block)) := by
            simpa [hCode, hStatePc] using hBytesDecoded
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
          constructor
          · intro hBad
            have hOpEq := hBad.1
            simp [decodedOperationAt, hDecoded] at hOpEq
            exact (primOp_toEVM_ne_jump op).1 hOpEq
          · intro hBad
            have hOpEq := hBad.1
            simp [decodedOperationAt, hDecoded] at hOpEq
            exact (primOp_toEVM_ne_jump op).2 hOpEq
  | branchMid block hBlock label isJumpi dest rest hInstr hLookup hPc
      hStack =>
      obtain ⟨located, hMem, hLocatedPc, hLocatedInstr⟩ :=
        compact_branch_midpoint_mem hCompile hBlock hInstr
      obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
        hDecode.decodes located hMem
      have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
        hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
      have hContains := hListed label dest hLookup
      have hStackHead :
          state.stack[0]? = some (EvmYul.UInt256.ofNat dest) := by
        simp [hStack]
      have hNotInFalse :
          EvmYul.EVM.X.notIn state.stack[0]? validJumps = false := by
        simp [hStackHead, EvmYul.EVM.X.notIn, EvmYul.EVM.X.belongs,
          hContains]
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
        constructor
        · intro hBad
          rw [hBad.2] at hNotInFalse
          cases hNotInFalse
        · intro hBad
          have hOp := hBad.1
          simp [decodedOperationAt, hDecoded] at hOp
      · rw [hJumpi] at hLocatedInstr
        simp only [if_true] at hLocatedInstr
        rw [hLocatedInstr] at hInstrDecoded
        simp [Compact.Instr.decoded?] at hInstrDecoded
        subst decoded
        have hDecoded :
            EvmYul.EVM.decode state.executionEnv.code state.pc =
              some (EvmYul.Operation.JUMPI, none) := by
          simpa [hCode, hStatePc] using hBytesDecoded
        constructor
        · intro hBad
          have hOp := hBad.1
          simp [decodedOperationAt, hDecoded] at hOp
        · intro hBad
          rw [hBad.2.2] at hNotInFalse
          cases hNotInFalse
  | sentinel hPc =>
      obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ := hSentinel
      simp [Compact.Instr.decoded?] at hInstrDecoded
      subst decoded
      have hDecoded :
          EvmYul.EVM.decode state.executionEnv.code state.pc =
            some (EvmYul.Operation.INVALID, none) := by
        simpa [hCode, hPc] using hBytesDecoded
      constructor
      · intro hBad
        have hOp := hBad.1
        simp [decodedOperationAt, hDecoded] at hOp
      · intro hBad
        have hOp := hBad.1
        simp [decodedOperationAt, hDecoded] at hOp

/-! ## Failing charged steps never carry the label -/

theorem afterEVMInstructionChargeAt_stack' (state : EVMState) :
    (afterEVMInstructionChargeAt state).stack = state.stack := by
  simp [afterEVMInstructionChargeAt, afterMemoryChargeAt, chargeGas]

theorem primStep_run_error_ne_badJumpDestination
    {primStep : PrimStep} {state : EvmYul.EVM.State}
    {err : EVMException}
    (hRun : primStep.run state = .error err) :
    err ≠ EvmYul.EVM.ExecutionException.BadJumpDestination := by
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

/-- On compiled code, a failing charged step at any generated control point
never carries the `BadJumpDestination` label. -/
theorem step_error_ne_badJumpDestination_at
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
    err ≠ EvmYul.EVM.ExecutionException.BadJumpDestination := by
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
          by_cases hZeroWidth : width = 0
          · subst hZeroWidth
            have hValueZero := Compact.pushWidthAt?_zero_value hWidth
            subst hValueZero
            have hInstr0 : located.instr = .push0 := by
              simpa [Compact.pushInstrOfWidth] using hLocatedInstr
            obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
              hDecode.decodes located hMem
            rw [hInstr0] at hInstrDecoded
            simp [Compact.Instr.decoded?] at hInstrDecoded
            subst decoded
            have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
              hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
            have hDecoded :
                EvmYul.EVM.decode state.executionEnv.code state.pc =
                  some (EvmYul.Operation.PUSH0, none) := by
              simpa [hCode, hStatePc] using hBytesDecoded
            rw [hDecoded] at hStep
            simp only [Option.getD_some] at hStep
            rw [evm_step_push0_eq_next fuel state] at hStep
            cases hStep
          simp only [Compact.pushInstrOfWidth, if_neg hZeroWidth]
            at hLocatedInstr
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
          have hFits : Compact.FitsWidth (artifact.branchWidthAt block)
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
                  artifact.branchWidthAt block)) := by
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
          have hFits : Compact.FitsWidth (artifact.branchWidthAt block)
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
                  artifact.branchWidthAt block)) := by
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
                    .error EvmYul.EVM.ExecutionException.BadJumpDestination := by
                simpa [hDecoded] using hStep
              have hPrim :
                  op.step (afterEVMInstructionChargeAt state) =
                    .error EvmYul.EVM.ExecutionException.BadJumpDestination := by
                rw [← hGasful]
                exact (evm_step_continuing_prim_after_charges hContinuing
                  trivial hStaticPermits).symm
              rw [PrimOp.step_eq_continuingStep_run hContinuing] at hPrim
              exact primStep_run_error_ne_badJumpDestination hPrim rfl
          | none =>
              by_cases hPcOp : op = .pc
              · subst op
                have hActual :
                    EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
                        (some (EvmYul.Operation.PC, none))
                        (afterMemoryChargeAt state) =
                      .error
                        EvmYul.EVM.ExecutionException.BadJumpDestination := by
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
                          EvmYul.EVM.ExecutionException.BadJumpDestination := by
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
                            rw [afterEVMInstructionChargeAt_stack', hStack]
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
                              rw [afterEVMInstructionChargeAt_stack',
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
                                    EvmYul.EVM.ExecutionException.BadJumpDestination := by
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
                                    EvmYul.EVM.ExecutionException.BadJumpDestination := by
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
        Except.error EvmYul.EVM.ExecutionException.BadJumpDestination at hStep
      change (Except.error EvmYul.EVM.ExecutionException.InvalidInstruction :
          Except EVMException EVMState) =
        Except.error EvmYul.EVM.ExecutionException.BadJumpDestination at hStep
      cases hStep

/-! ## The frame run never returns `BadJumpDestination` -/

/-- Fuel induction over `EvmYul.EVM.X`: with the reachable jump-precheck
invariant and step-error classification, the frame run never reports
`BadJumpDestination`. -/
theorem x_ne_badJumpDestination_of_invariants
    {validJumps : Array Word} {initial : EVMState}
    (hNoBadJump :
      ∀ s, FrameReachable validJumps initial s →
        ¬ badJumpAt validJumps s ∧ ¬ badJumpiAt validJumps s)
    (hStepErr :
      ∀ (s : EVMState) (stepFuel : Nat) (err : EVMException),
        FrameReachable validJumps initial s →
        XSstoreStipendChecksPass validJumps s →
        EvmYul.EVM.step stepFuel (dynamicGasCostAt s)
            (some
              ((EvmYul.EVM.decode s.executionEnv.code s.pc).getD
                (EvmYul.Operation.STOP, none)))
            (afterMemoryChargeAt s) = .error err →
        err ≠ EvmYul.EVM.ExecutionException.BadJumpDestination) :
    ∀ (fuel : Nat) (s : EVMState), FrameReachable validJumps initial s →
      EvmYul.EVM.X fuel validJumps s ≠
        .error EvmYul.EVM.ExecutionException.BadJumpDestination := by
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
      · exact absurd hBJ (hNoBadJump s hReach).1
      by_cases hBJI : badJumpiAt validJumps s
      · exact absurd hBJI (hNoBadJump s hReach).2
      have hJumps : XJumpChecksPass validJumps s := ⟨hOpcode, hBJ, hBJI⟩
      by_cases hRdc : invalidReturnDataCopyAt s
      · rw [x_invalid_returndatacopy_after_jump_checks hJumps hRdc] at hEq
        cases Except.error.inj hEq
      have hMemoryAccess : XMemoryAccessChecksPass validJumps s :=
        ⟨hJumps, hRdc⟩
      by_cases hOverflow : stackOverflowAt s
      · rw [x_stack_overflow_after_memory_access_checks hMemoryAccess
          hOverflow] at hEq
        cases Except.error.inj hEq
      have hStackLimit : XStackLimitChecksPass validJumps s :=
        ⟨hMemoryAccess, hOverflow⟩
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

/-- Crown composition at the compact-artifact level: on compiled code whose
label destinations are all listed in `validJumps`, the gasful frame
interpreter can never return `BadJumpDestination`, from any frame entry
state. -/
theorem x_ne_badJumpDestination_of_frame
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {validJumps : Array Word} {initial : EVMState}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hSentinel : Compact.decodeAt bytes
      (Compact.Program.codeByteLength artifact.program.code)
      (.prim .invalid))
    (hFrame : ArtifactFrameInvariant artifact bytes validJumps initial)
    (hListed : LabelTargetsListed artifact validJumps) :
    ∀ fuel, EvmYul.EVM.X fuel validJumps initial ≠
      .error EvmYul.EVM.ExecutionException.BadJumpDestination := by
  intro fuel
  exact x_ne_badJumpDestination_of_invariants
    (fun s hReach =>
      artifactFramePoint_not_badJump hCompile hDecode hSentinel
        (hFrame s hReach) hListed)
    (fun s stepFuel err hReach hPrefix hStep =>
      step_error_ne_badJumpDestination_at hCompile hDecode hSentinel
        (hFrame s hReach) hPrefix hStep)
    fuel initial .initial

/-! ## Escape-free refinement view -/

/-- `RunRefinesOpen` with the `badJumpDestination` escape constructor
removed. -/
inductive RunRefinesOpenNoBadJump
    (gasful : Except EVMException (EvmYul.EVM.ExecutionResult EVMState))
    (openRun : Simulation.Interaction EVMException StepResult) :
    Simulation.Interaction.Transcript → Prop where
  | completed {transcript openDone} :
      Simulation.Interaction.Executes openRun transcript openDone →
      DoneRel gasful openDone →
      RunRefinesOpenNoBadJump gasful openRun transcript
  | exceptionalFrame {transcript gasErr openErr} :
      gasErr ≠ EvmYul.EVM.ExecutionException.OutOfFuel →
      openErr ≠ EvmYul.EVM.ExecutionException.OutOfFuel →
      gasful = .error gasErr →
      Simulation.Interaction.Executes openRun transcript (.error openErr) →
      RunRefinesOpenNoBadJump gasful openRun transcript
  | outOfGas {transcript} :
      gasful = .error EvmYul.EVM.ExecutionException.OutOfGass →
      Simulation.Interaction.Follows openRun transcript →
      RunRefinesOpenNoBadJump gasful openRun transcript
  | outOfFuel {transcript} :
      gasful = .error EvmYul.EVM.ExecutionException.OutOfFuel →
      Simulation.Interaction.Follows openRun transcript →
      RunRefinesOpenNoBadJump gasful openRun transcript
  | stackOverflow {transcript} :
      gasful = .error EvmYul.EVM.ExecutionException.StackOverflow →
      Simulation.Interaction.Follows openRun transcript →
      RunRefinesOpenNoBadJump gasful openRun transcript

/-- Any refinement witness whose gasful side is known not to be a
`BadJumpDestination` error loses the escape constructor. -/
theorem runRefinesOpenNoBadJump_of_ne
    {gasful : Except EVMException (EvmYul.EVM.ExecutionResult EVMState)}
    {openRun : Simulation.Interaction EVMException StepResult}
    {transcript : Simulation.Interaction.Transcript}
    (hRefines : RunRefinesOpen gasful openRun transcript)
    (hNe :
      gasful ≠ .error EvmYul.EVM.ExecutionException.BadJumpDestination) :
    RunRefinesOpenNoBadJump gasful openRun transcript := by
  cases hRefines with
  | completed hExec hDone => exact .completed hExec hDone
  | exceptionalFrame hGasErr hOpenErr hGas hExec =>
      exact .exceptionalFrame hGasErr hOpenErr hGas hExec
  | outOfGas hGas hFollow => exact .outOfGas hGas hFollow
  | outOfFuel hFuel hFollow => exact .outOfFuel hFuel hFollow
  | badJumpDestination hBad hFollow => exact absurd hBad hNe
  | stackOverflow hOverflow hFollow => exact .stackOverflow hOverflow hFollow

end EvmCompiler.Assembly.GasfulBridge
