import EvmCompiler.Assembly.GasfulBridgeRecursive

namespace EvmCompiler.Assembly.GasfulBridge

theorem uint256_ofNat_add (a b : Nat) :
    EvmYul.UInt256.ofNat a + EvmYul.UInt256.ofNat b =
      EvmYul.UInt256.ofNat (a + b) := by
  change EvmYul.UInt256.add
    (EvmYul.UInt256.ofNat a) (EvmYul.UInt256.ofNat b) =
      EvmYul.UInt256.ofNat (a + b)
  unfold EvmYul.UInt256.add EvmYul.UInt256.ofNat
  congr 1
  apply Fin.ext
  change ((a % EvmYul.UInt256.size + b % EvmYul.UInt256.size) %
      EvmYul.UInt256.size) = (a + b) % EvmYul.UInt256.size
  rw [← Nat.add_mod]

/-- The compact compiler's checked end-of-code byte decodes as the supported
`INVALID` sentinel before any caller-owned payload. -/
theorem compact_compile_sentinel_decodeAt
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (payload : List UInt8) :
    Compact.decodeAt
      (Bytecode.ofList
        (artifact.bytes.toList ++
          (Compact.encodeInstr (.prim .invalid) ++ payload)))
      (Compact.Program.codeByteLength artifact.program.code)
      (.prim .invalid) := by
  have hValid := Compact.compile?_valid hCompile
  have hBytes : artifact.bytes.toList =
      artifact.program.code.flatMap Compact.encodeLocated := by
    rw [hValid.bytes]
    simp [Compact.encode, Bytecode.ofList]
  have hLength : artifact.bytes.toList.length =
      Compact.Program.codeByteLength artifact.program.code := by
    rw [hBytes, Compact.flatMap_encodeLocated_length]
  have hStart :
      artifact.bytes.toList.length + 1 < 18446744073709551616 := by
    rw [hLength]
    exact hValid.sentinelFits
  have hPc :
      (EvmYul.UInt256.ofNat artifact.bytes.toList.length).toNat =
        artifact.bytes.toList.length := by
    apply Bytecode.uint256_ofNat_toNat_of_decode_window
    omega
  have hDecode := Compact.decodeInstrAtPrefix artifact.bytes.toList payload
    (.prim .invalid) trivial hPc hStart (by
      simpa [Compact.Instr.byteSize] using hStart)
  rw [hLength] at hDecode
  simpa [List.append_assoc] using hDecode

/-- Every checked compact source block begins at an instruction recorded in
the emitted compact program. -/
theorem compact_block_entry_mem
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {block : Compact.SourceBlock}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hBlock : block ∈ artifact.blocks) :
    ∃ located, located ∈ artifact.program.code ∧
      located.pc = block.compactPc := by
  have hArtifact := Compact.compile?_valid hCompile
  obtain ⟨compactSize, hSize, hCode⟩ :=
    (Compact.compile?_blocksValid hCompile).block_emit_of_mem hBlock
  rcases block with ⟨sourcePc, compactPc, sourceInstr, code⟩
  cases sourceInstr with
  | label name =>
      simp [Compact.emitSourceBlock?, Compact.emitInstrRev?] at hCode
      subst code
      exact ⟨{ pc := compactPc, instr := .jumpdest },
        hArtifact.mem_program_of_mem_block hBlock (by simp), rfl⟩
  | prim op =>
      simp [Compact.emitSourceBlock?, Compact.emitInstrRev?] at hCode
      subst code
      exact ⟨{ pc := compactPc, instr := .prim op },
        hArtifact.mem_program_of_mem_block hBlock (by simp), rfl⟩
  | push value =>
      cases hWidth :
          Compact.pushWidthAt? artifact.pinnedPushPcs sourcePc value with
      | none =>
          simp [Compact.sourceInstrSizeAt?, hWidth] at hSize
      | some width =>
          simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hWidth]
            at hCode
          subst code
          exact ⟨{ pc := compactPc, instr := .push width value },
            hArtifact.mem_program_of_mem_block hBlock (by simp), rfl⟩
  | pushLabel target =>
      simp [Compact.emitSourceBlock?, Compact.emitInstrRev?] at hCode
  | jump target =>
      cases hDest : Compact.lookupLabel? artifact.labels target with
      | none =>
          simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest]
            at hCode
      | some dest =>
          by_cases hFits :
              Compact.fitsWidth? artifact.branchWidth dest = true
          · simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest,
              hFits] at hCode
            subst code
            exact
              ⟨{ pc := compactPc
                 instr := .push artifact.branchWidth
                   (EvmYul.UInt256.ofNat dest) },
                hArtifact.mem_program_of_mem_block hBlock (by simp), rfl⟩
          · simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest,
              hFits] at hCode
  | jumpi target =>
      cases hDest : Compact.lookupLabel? artifact.labels target with
      | none =>
          simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest]
            at hCode
      | some dest =>
          by_cases hFits :
              Compact.fitsWidth? artifact.branchWidth dest = true
          · simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest,
              hFits] at hCode
            subst code
            exact
              ⟨{ pc := compactPc
                 instr := .push artifact.branchWidth
                   (EvmYul.UInt256.ofNat dest) },
                hArtifact.mem_program_of_mem_block hBlock (by simp), rfl⟩
          · simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest,
              hFits] at hCode
  | jumpDynamic =>
      simp [Compact.emitSourceBlock?, Compact.emitInstrRev?] at hCode

/-- The compact entry PC is a valid layout point; for an empty physical source
it is exactly the checked sentinel. -/
theorem compact_initial_layoutPoint
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact) :
    CompactLayoutPoint artifact.program (EvmYul.UInt256.ofNat 0) := by
  rcases Compact.compile?_initial_boundary hCompile with hBlock | hEnd
  · rcases hBlock with ⟨block, hMem, _hSource, hCompact⟩
    obtain ⟨located, hLocated, hPc⟩ :=
      compact_block_entry_mem hCompile hMem
    left
    exact ⟨located, hLocated, by rw [hPc, hCompact]⟩
  · right
    rw [hEnd.2]

/-- The second instruction of every checked fixed-label branch block is also
an emitted compact-program instruction. -/
theorem compact_branch_midpoint_mem
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {block : Compact.SourceBlock}
    {label : Label} {isJumpi : Bool}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr =
      if isJumpi then .jumpi label else .jump label) :
    ∃ located, located ∈ artifact.program.code ∧
      located.pc = block.compactPc + artifact.branchWidth + 1 ∧
      located.instr = if isJumpi then .jumpi else .jump := by
  have hArtifact := Compact.compile?_valid hCompile
  obtain ⟨compactSize, hSize, hCode⟩ :=
    (Compact.compile?_blocksValid hCompile).block_emit_of_mem hBlock
  rcases block with ⟨sourcePc, compactPc, sourceInstr, code⟩
  cases hJumpi : isJumpi
  · simp [hJumpi] at hInstr ⊢
    subst sourceInstr
    cases hDest : Compact.lookupLabel? artifact.labels label with
    | none =>
        simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest] at hCode
    | some dest =>
        by_cases hFits :
            Compact.fitsWidth? artifact.branchWidth dest = true
        · simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest,
            hFits] at hCode
          subst code
          exact
            ⟨{ pc := compactPc + artifact.branchWidth + 1,
               instr := .jump },
              hArtifact.mem_program_of_mem_block hBlock (by simp), rfl, rfl⟩
        · simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest,
            hFits] at hCode
  · simp [hJumpi] at hInstr ⊢
    subst sourceInstr
    cases hDest : Compact.lookupLabel? artifact.labels label with
    | none =>
        simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest] at hCode
    | some dest =>
        by_cases hFits :
            Compact.fitsWidth? artifact.branchWidth dest = true
        · simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest,
            hFits] at hCode
          subst code
          exact
            ⟨{ pc := compactPc + artifact.branchWidth + 1,
               instr := .jumpi },
              hArtifact.mem_program_of_mem_block hBlock (by simp), rfl, rfl⟩
        · simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest,
            hFits] at hCode

/-- A successful compact label-table lookup names the entry instruction of an
actual emitted source block, never an arbitrary payload `JUMPDEST`. -/
theorem compact_lookup_destination_mem
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {label : Label} {dest : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hLookup : Compact.lookupLabel? artifact.labels label = some dest) :
    ∃ located, located ∈ artifact.program.code ∧ located.pc = dest := by
  have hArtifact := Compact.compile?_valid hCompile
  obtain ⟨sourceDest, hSourceDest⟩ :=
    Compact.compile?_physical_labelPc_of_lookup hCompile hLookup
  have hAt := Assembly.Program.instrAtPc_of_labelPc hSourceDest
  obtain ⟨block, hBlock, _hBlockPc, hInstr⟩ :=
    (Compact.compile?_blocksValid hCompile).block_of_instrAtPc hAt
  have hConsistent :=
    hArtifact.labelsConsistent block hBlock label hInstr
  rw [hLookup] at hConsistent
  have hDest : block.compactPc = dest :=
    (Option.some.inj hConsistent).symm
  obtain ⟨located, hMem, hPc⟩ :=
    compact_block_entry_mem hCompile hBlock
  exact ⟨located, hMem, hPc.trans hDest⟩

/-- Every fixed-label branch block carries a generated destination whose PC is
an emitted compact layout member. -/
theorem compact_branch_destination_mem
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {block : Compact.SourceBlock}
    {label : Label} {isJumpi : Bool}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr =
      if isJumpi then .jumpi label else .jump label) :
    ∃ dest located,
      Compact.lookupLabel? artifact.labels label = some dest ∧
        located ∈ artifact.program.code ∧ located.pc = dest := by
  obtain ⟨_compactSize, _hSize, hCode⟩ :=
    (Compact.compile?_blocksValid hCompile).block_emit_of_mem hBlock
  cases hJumpi : isJumpi
  · simp [hJumpi] at hInstr
    rw [hInstr] at hCode
    cases hDest : Compact.lookupLabel? artifact.labels label with
    | none =>
        simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest] at hCode
    | some dest =>
        obtain ⟨located, hMem, hPc⟩ :=
          compact_lookup_destination_mem hCompile hDest
        exact ⟨dest, located, rfl, hMem, hPc⟩
  · simp [hJumpi] at hInstr
    rw [hInstr] at hCode
    cases hDest : Compact.lookupLabel? artifact.labels label with
    | none =>
        simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest] at hCode
    | some dest =>
        obtain ⟨located, hMem, hPc⟩ :=
          compact_lookup_destination_mem hCompile hDest
        exact ⟨dest, located, rfl, hMem, hPc⟩

/-- The entry instruction of every fixed-label branch block is the generated
destination PUSH, with the label-table destination recorded explicitly. -/
theorem compact_branch_entry_mem
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {block : Compact.SourceBlock}
    {label : Label} {isJumpi : Bool}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr =
      if isJumpi then .jumpi label else .jump label) :
    ∃ dest located,
      Compact.lookupLabel? artifact.labels label = some dest ∧
        located ∈ artifact.program.code ∧
        located.pc = block.compactPc ∧
        located.instr = .push artifact.branchWidth
          (EvmYul.UInt256.ofNat dest) := by
  rcases block with ⟨sourcePc, compactPc, sourceInstr, code⟩
  have hArtifact := Compact.compile?_valid hCompile
  obtain ⟨_compactSize, _hSize, hCode⟩ :=
    (Compact.compile?_blocksValid hCompile).block_emit_of_mem hBlock
  cases hJumpi : isJumpi
  · simp [hJumpi] at hInstr
    rw [hInstr] at hCode
    cases hDest : Compact.lookupLabel? artifact.labels label with
    | none =>
        simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest] at hCode
    | some dest =>
        by_cases hFits :
            Compact.fitsWidth? artifact.branchWidth dest = true
        · simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest,
            hFits] at hCode
          subst code
          let located : Compact.Located :=
            { pc := compactPc
              instr := .push artifact.branchWidth
                (EvmYul.UInt256.ofNat dest) }
          exact ⟨dest, located, rfl,
            hArtifact.mem_program_of_mem_block hBlock (by simp [located]),
            rfl, rfl⟩
        · simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest,
            hFits] at hCode
  · simp [hJumpi] at hInstr
    rw [hInstr] at hCode
    cases hDest : Compact.lookupLabel? artifact.labels label with
    | none =>
        simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest] at hCode
    | some dest =>
        by_cases hFits :
            Compact.fitsWidth? artifact.branchWidth dest = true
        · simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest,
            hFits] at hCode
          subst code
          let located : Compact.Located :=
            { pc := compactPc
              instr := .push artifact.branchWidth
                (EvmYul.UInt256.ofNat dest) }
          exact ⟨dest, located, rfl,
            hArtifact.mem_program_of_mem_block hBlock (by simp [located]),
            rfl, rfl⟩
        · simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest,
            hFits] at hCode
/-- A successful compact label lookup identifies a generated source boundary.
The source PC is existential because only the compact destination is relevant
to gasful control preservation. -/
theorem compact_lookup_destination_boundary
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {label : Label} {dest : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hLookup : Compact.lookupLabel? artifact.labels label = some dest) :
    ∃ sourceDest,
      Compact.BoundaryPair artifact.blocks
        artifact.physicalSource.byteLength
        (Compact.Program.codeByteLength artifact.program.code)
        sourceDest dest := by
  obtain ⟨sourceDest, hSource⟩ :=
    Compact.compile?_physical_labelPc_of_lookup hCompile hLookup
  exact ⟨sourceDest,
    Compact.compile?_label_boundary hCompile hSource hLookup⟩

/-- The fallthrough PC after a generated fixed-label branch is either the
next emitted source block or the trailing checked sentinel. -/
theorem compact_branch_fallthrough_boundary
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {block : Compact.SourceBlock}
    {label : Label} {isJumpi : Bool}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr =
      if isJumpi then .jumpi label else .jump label) :
    ∃ sourceNext,
      Compact.BoundaryPair artifact.blocks
        artifact.physicalSource.byteLength
        (Compact.Program.codeByteLength artifact.program.code)
        sourceNext (block.compactPc + artifact.branchWidth + 2) := by
  obtain ⟨compactSize, hSize, _hCode⟩ :=
    (Compact.compile?_blocksValid hCompile).block_emit_of_mem hBlock
  have hNext :=
    (Compact.compile?_blocksValid hCompile).next_boundary hBlock hSize
  have hArtifact := Compact.compile?_valid hCompile
  rw [hArtifact.blockCode] at hNext
  cases hJumpi : isJumpi
  · simp [hJumpi] at hInstr
    rw [hInstr] at hSize hNext
    simp [Compact.sourceInstrSizeAt?] at hSize
    subst compactSize
    exact ⟨block.sourcePc + (Assembly.Instr.jump label).byteSize, by
      simpa [Nat.add_assoc] using hNext⟩
  · simp [hJumpi] at hInstr
    rw [hInstr] at hSize hNext
    simp [Compact.sourceInstrSizeAt?] at hSize
    subst compactSize
    exact ⟨block.sourcePc + (Assembly.Instr.jumpi label).byteSize, by
      simpa [Nat.add_assoc] using hNext⟩

/-- Instruction-level control points generated by the compact compiler. A
fixed-label branch has one internal point after its generated PUSH; all other
points are source-block entries or the checked invalid sentinel. -/
inductive CompactControlPoint (artifact : Compact.Artifact) : EVMState → Prop
  | boundary {state : EVMState} (block : Compact.SourceBlock)
      (member : block ∈ artifact.blocks)
      (pc : state.pc = EvmYul.UInt256.ofNat block.compactPc) :
      CompactControlPoint artifact state
  | branchMid {state : EVMState} (block : Compact.SourceBlock)
      (member : block ∈ artifact.blocks) (label : Label) (isJumpi : Bool)
      (dest : Nat) (rest : EvmYul.Stack Word)
      (instr : block.sourceInstr =
        if isJumpi then .jumpi label else .jump label)
      (lookup : Compact.lookupLabel? artifact.labels label = some dest)
      (pc : state.pc = EvmYul.UInt256.ofNat
        (block.compactPc + artifact.branchWidth + 1))
      (stack : state.stack = EvmYul.UInt256.ofNat dest :: rest) :
      CompactControlPoint artifact state
  | sentinel {state : EVMState}
      (pc : state.pc = EvmYul.UInt256.ofNat
        (Compact.Program.codeByteLength artifact.program.code)) :
      CompactControlPoint artifact state

theorem compactControlPoint_of_boundary
    {artifact : Compact.Artifact} {state : EVMState}
    {sourcePc compactPc : Nat}
    (hBoundary :
      Compact.BoundaryPair artifact.blocks
        artifact.physicalSource.byteLength
        (Compact.Program.codeByteLength artifact.program.code)
        sourcePc compactPc)
    (hPc : state.pc = EvmYul.UInt256.ofNat compactPc) :
    CompactControlPoint artifact state := by
  rcases hBoundary with hBlock | hEnd
  · rcases hBlock with ⟨block, hMem, _hSourcePc, hCompactPc⟩
    exact .boundary block hMem (by simpa [hCompactPc] using hPc)
  · exact .sentinel (by simpa [hEnd.2] using hPc)

structure ArtifactFramePoint
    (artifact : Compact.Artifact) (bytes : ByteArray)
    (state : EVMState) : Prop where
  code_eq : state.executionEnv.code = bytes
  control : CompactControlPoint artifact state

theorem artifactFramePoint_branch_push_next
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {state : EVMState} {block : Compact.SourceBlock}
    {label : Label} {isJumpi : Bool} {dest : Nat}
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr =
      if isJumpi then .jumpi label else .jump label)
    (hLookup : Compact.lookupLabel? artifact.labels label = some dest)
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc) :
    ArtifactFramePoint artifact bytes
      (gasfulPushNext artifact.branchWidth
        (EvmYul.UInt256.ofNat dest) state) := by
  constructor
  · simpa [gasfulPushNext, afterEVMInstructionChargeAt,
      afterMemoryChargeAt, afterDynamicChargeAt, chargeGas] using hCode
  · apply CompactControlPoint.branchMid block hBlock label isJumpi dest
      state.stack hInstr hLookup
    · simp [gasfulPushNext, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, EvmYul.Stack.push,
        afterEVMInstructionChargeAt, afterMemoryChargeAt,
        chargeGas, hPc, uint256_ofNat_add,
        Nat.add_assoc]
    · simp [gasfulPushNext, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, EvmYul.Stack.push,
        afterEVMInstructionChargeAt, afterMemoryChargeAt,
        chargeGas]

/-- An actual charged gasful step at a fixed-label branch entry executes the
compiler-generated PUSH and reaches its unique branch midpoint. -/
theorem artifactFramePoint_branch_push_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {state next : EVMState} {block : Compact.SourceBlock}
    {label : Label} {isJumpi : Bool} {fuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr =
      if isJumpi then .jumpi label else .jump label)
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hStep :
      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    ArtifactFramePoint artifact bytes next := by
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
  have hExact := evm_step_push_eq_next fuel state
    (EvmYul.UInt256.ofNat dest) hFits hOp
  rw [hDecoded] at hStep
  simp only [Option.getD_some] at hStep
  rw [hExact] at hStep
  have hNext : next = gasfulPushNext artifact.branchWidth
      (EvmYul.UInt256.ofNat dest) state := by
    simpa using hStep.symm
  rw [hNext]
  exact artifactFramePoint_branch_push_next hCode hBlock hInstr hLookup hPc

theorem artifactFramePoint_boundary_branch_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {state next : EVMState} {block : Compact.SourceBlock}
    {label : Label} {isJumpi : Bool} {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr =
      if isJumpi then .jumpi label else .jump label)
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    ArtifactFramePoint artifact bytes next := by
  cases stepFuel with
  | zero => simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      exact artifactFramePoint_branch_push_step hCompile hDecode hCode
        hBlock hInstr hPc hStep

theorem artifactFramePoint_branchMid_jump_next
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {state : EVMState}
    {label : Label} {dest : Nat} {rest : EvmYul.Stack Word}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hCode : state.executionEnv.code = bytes)
    (hLookup : Compact.lookupLabel? artifact.labels label = some dest) :
    ArtifactFramePoint artifact bytes
      (gasfulJumpNext state rest (EvmYul.UInt256.ofNat dest)) := by
  constructor
  · simpa [gasfulJumpNext, afterEVMInstructionChargeAt,
      afterMemoryChargeAt, afterDynamicChargeAt, chargeGas] using hCode
  · obtain ⟨sourceDest, hBoundary⟩ :=
      compact_lookup_destination_boundary hCompile hLookup
    apply compactControlPoint_of_boundary hBoundary
    simp [gasfulJumpNext]

theorem artifactFramePoint_branchMid_jumpi_next
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {state : EVMState} {block : Compact.SourceBlock}
    {label : Label} {dest : Nat} {cond : Word}
    {rest : EvmYul.Stack Word}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .jumpi label)
    (hLookup : Compact.lookupLabel? artifact.labels label = some dest)
    (hPc : state.pc = EvmYul.UInt256.ofNat
      (block.compactPc + artifact.branchWidth + 1)) :
    ArtifactFramePoint artifact bytes
      (gasfulJumpiNext state rest (EvmYul.UInt256.ofNat dest) cond) := by
  constructor
  · simpa [gasfulJumpiNext, afterEVMInstructionChargeAt,
      afterMemoryChargeAt, afterDynamicChargeAt, chargeGas] using hCode
  · by_cases hCond : cond != EvmYul.UInt256.ofNat 0
    · obtain ⟨sourceDest, hBoundary⟩ :=
        compact_lookup_destination_boundary hCompile hLookup
      apply compactControlPoint_of_boundary hBoundary
      simp [gasfulJumpiNext, hCond]
    · obtain ⟨sourceNext, hBoundary⟩ :=
        compact_branch_fallthrough_boundary hCompile hBlock
          (isJumpi := true) (by simpa using hInstr)
      apply compactControlPoint_of_boundary hBoundary
      simp [gasfulJumpiNext, hCond, hPc]
      change EvmYul.UInt256.add
        (EvmYul.UInt256.ofNat
          (block.compactPc + artifact.branchWidth + 1))
        (EvmYul.UInt256.ofNat 1) =
          EvmYul.UInt256.ofNat
            (block.compactPc + artifact.branchWidth + 2)
      unfold EvmYul.UInt256.add EvmYul.UInt256.ofNat
      congr 1
      apply Fin.ext
      change
        (((block.compactPc + artifact.branchWidth + 1) %
            EvmYul.UInt256.size + 1 % EvmYul.UInt256.size) %
          EvmYul.UInt256.size) =
        (block.compactPc + artifact.branchWidth + 2) %
          EvmYul.UInt256.size
      rw [← Nat.add_mod]

/-- An actual charged gasful JUMP from a generated branch midpoint reaches the
compiler label boundary described by `ArtifactFramePoint`. -/
theorem artifactFramePoint_branchMid_jump_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {state next : EVMState} {block : Compact.SourceBlock}
    {label : Label} {dest fuel : Nat} {rest : EvmYul.Stack Word}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .jump label)
    (hLookup : Compact.lookupLabel? artifact.labels label = some dest)
    (hPc : state.pc = EvmYul.UInt256.ofNat
      (block.compactPc + artifact.branchWidth + 1))
    (hStack : state.stack = EvmYul.UInt256.ofNat dest :: rest)
    (hStep :
      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    ArtifactFramePoint artifact bytes next := by
  obtain ⟨located, hMem, hLocatedPc, hLocatedInstr⟩ :=
    compact_branch_midpoint_mem hCompile hBlock
      (isJumpi := false) (by simpa using hInstr)
  obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
    hDecode.decodes located hMem
  rw [hLocatedInstr] at hInstrDecoded
  simp [Compact.Instr.decoded?] at hInstrDecoded
  subst decoded
  have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
    hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
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
  rw [hNext]
  exact artifactFramePoint_branchMid_jump_next hCompile hCode hLookup

/-- An actual charged gasful JUMPI from a generated branch midpoint reaches
either the compiler label boundary or its checked fallthrough boundary. -/
theorem artifactFramePoint_branchMid_jumpi_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {state next : EVMState} {block : Compact.SourceBlock}
    {label : Label} {dest fuel : Nat} {cond : Word}
    {rest : EvmYul.Stack Word}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .jumpi label)
    (hLookup : Compact.lookupLabel? artifact.labels label = some dest)
    (hPc : state.pc = EvmYul.UInt256.ofNat
      (block.compactPc + artifact.branchWidth + 1))
    (hStack : state.stack =
      EvmYul.UInt256.ofNat dest :: cond :: rest)
    (hStep :
      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    ArtifactFramePoint artifact bytes next := by
  obtain ⟨located, hMem, hLocatedPc, hLocatedInstr⟩ :=
    compact_branch_midpoint_mem hCompile hBlock
      (isJumpi := true) (by simpa using hInstr)
  obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
    hDecode.decodes located hMem
  rw [hLocatedInstr] at hInstrDecoded
  simp [Compact.Instr.decoded?] at hInstrDecoded
  subst decoded
  have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
    hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
  have hDecoded :
      EvmYul.EVM.decode state.executionEnv.code state.pc =
        some (EvmYul.Operation.JUMPI, none) := by
    simpa [hCode, hStatePc] using hBytesDecoded
  have hExact :=
    evm_step_jumpi_eq_next fuel state none rest
      (EvmYul.UInt256.ofNat dest) cond hStack
  rw [hDecoded] at hStep
  simp only [Option.getD_some] at hStep
  rw [hExact] at hStep
  have hNext : next = gasfulJumpiNext state rest
      (EvmYul.UInt256.ofNat dest) cond := by
    simpa using hStep.symm
  rw [hNext]
  exact artifactFramePoint_branchMid_jumpi_next hCompile hCode hBlock
    hInstr hLookup hPc

theorem artifactFramePoint_branchMid_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {validJumps : Array Word} {state next : EVMState}
    {block : Compact.SourceBlock} {label : Label} {isJumpi : Bool}
    {dest : Nat} {rest : EvmYul.Stack Word} {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr =
      if isJumpi then .jumpi label else .jump label)
    (hLookup : Compact.lookupLabel? artifact.labels label = some dest)
    (hPc : state.pc = EvmYul.UInt256.ofNat
      (block.compactPc + artifact.branchWidth + 1))
    (hStack : state.stack = EvmYul.UInt256.ofNat dest :: rest)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    ArtifactFramePoint artifact bytes next := by
  cases stepFuel with
  | zero => simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      cases hJumpi : isJumpi
      · simp [hJumpi] at hInstr
        exact artifactFramePoint_branchMid_jump_step hCompile hDecode hCode
          hBlock hInstr hLookup hPc hStack hStep
      · simp [hJumpi] at hInstr
        obtain ⟨located, hMem, hLocatedPc, hLocatedInstr⟩ :=
          compact_branch_midpoint_mem hCompile hBlock
            (isJumpi := true) (by simpa using hInstr)
        obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
          hDecode.decodes located hMem
        rw [hLocatedInstr] at hInstrDecoded
        simp [Compact.Instr.decoded?] at hInstrDecoded
        subst decoded
        have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
          hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
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
            exact artifactFramePoint_branchMid_jumpi_step hCompile hDecode
              hCode hBlock hInstr hLookup hPc hStack' hStep

theorem artifactFramePoint_sentinel_no_success
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
        (afterMemoryChargeAt state) = .ok next) : False := by
  obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ := hSentinel
  simp [Compact.Instr.decoded?] at hInstrDecoded
  subst decoded
  have hDecoded :
      EvmYul.EVM.decode state.executionEnv.code state.pc =
        some (EvmYul.Operation.INVALID, none) := by
    simpa [hCode, hPc] using hBytesDecoded
  cases stepFuel with
  | zero => simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      rw [hDecoded] at hStep
      simp only [Option.getD_some] at hStep
      change EvmYul.step (τ := .EVM) EvmYul.Operation.INVALID none
        { { afterMemoryChargeAt state with
              execLength := (afterMemoryChargeAt state).execLength + 1 } with
          gasAvailable := (afterMemoryChargeAt state).gasAvailable -
            EvmYul.UInt256.ofNat (dynamicGasCostAt state) } =
        Except.ok next at hStep
      change Except.error EvmYul.EVM.ExecutionException.InvalidInstruction =
        Except.ok next at hStep
      cases hStep

def ArtifactFrameStepInvariant
    (artifact : Compact.Artifact) (bytes : ByteArray)
    (validJumps : Array Word) : Prop :=
  ∀ {current next : EVMState} {stepFuel : Nat},
    ArtifactFramePoint artifact bytes current →
    XSstoreStipendChecksPass validJumps current →
    EvmYul.EVM.step stepFuel (dynamicGasCostAt current)
        (some
          ((EvmYul.EVM.decode current.executionEnv.code current.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt current) = .ok next →
    haltOutputAt next (decodedOperationAt current) = none →
    ArtifactFramePoint artifact bytes next

def ArtifactOrdinaryBoundaryStepInvariant
    (artifact : Compact.Artifact) (bytes : ByteArray)
    (validJumps : Array Word) : Prop :=
  ∀ {current next : EVMState} {block : Compact.SourceBlock}
      {stepFuel : Nat},
    current.executionEnv.code = bytes →
    block ∈ artifact.blocks →
    current.pc = EvmYul.UInt256.ofNat block.compactPc →
    (∀ target, block.sourceInstr ≠ .jump target) →
    (∀ target, block.sourceInstr ≠ .jumpi target) →
    XSstoreStipendChecksPass validJumps current →
    EvmYul.EVM.step stepFuel (dynamicGasCostAt current)
        (some
          ((EvmYul.EVM.decode current.executionEnv.code current.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt current) = .ok next →
    haltOutputAt next (decodedOperationAt current) = none →
    ArtifactFramePoint artifact bytes next

/-- Generated branches and the sentinel are discharged internally; only
ordinary source-block boundaries remain in the local preservation premise. -/
theorem artifactFrameStepInvariant_of_ordinaryBoundary
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {validJumps : Array Word}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hSentinel : Compact.decodeAt bytes
      (Compact.Program.codeByteLength artifact.program.code)
      (.prim .invalid))
    (hOrdinary :
      ArtifactOrdinaryBoundaryStepInvariant artifact bytes validJumps) :
    ArtifactFrameStepInvariant artifact bytes validJumps := by
  intro current next stepFuel hPoint hPrefix hStep hContinues
  rcases hPoint with ⟨hCode, hControl⟩
  cases hControl with
  | boundary block hBlock hPc =>
      generalize hInstr : block.sourceInstr = instr
      cases instr with
      | jump label =>
          exact artifactFramePoint_boundary_branch_step hCompile hDecode
            hCode hBlock (isJumpi := false) (by simpa using hInstr)
              hPc hStep
      | jumpi label =>
          exact artifactFramePoint_boundary_branch_step hCompile hDecode
            hCode hBlock (isJumpi := true) (by simpa using hInstr)
              hPc hStep
      | label name | prim op | push value | pushLabel target | jumpDynamic =>
          exact hOrdinary hCode hBlock hPc
            (by intro target; simp [hInstr])
            (by intro target; simp [hInstr])
            hPrefix hStep hContinues
  | branchMid block hBlock label isJumpi dest rest hInstr hLookup hPc hStack =>
      exact artifactFramePoint_branchMid_step hCompile hDecode hCode hBlock
        hInstr hLookup hPc hStack hPrefix hStep
  | sentinel hPc =>
      exact False.elim
        (artifactFramePoint_sentinel_no_success hSentinel hCode hPc hStep)

theorem CompactControlPoint.layoutPoint
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {state : EVMState}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (point : CompactControlPoint artifact state) :
    CompactLayoutPoint artifact.program state.pc := by
  cases point with
  | boundary block hBlock hPc =>
      obtain ⟨located, hMem, hLocatedPc⟩ :=
        compact_block_entry_mem hCompile hBlock
      left
      exact ⟨located, hMem, hPc.trans (congrArg EvmYul.UInt256.ofNat
        hLocatedPc.symm)⟩
  | branchMid block hBlock label isJumpi dest rest hInstr hLookup hPc hStack =>
      obtain ⟨located, hMem, hLocatedPc, _hLocatedInstr⟩ :=
        compact_branch_midpoint_mem hCompile hBlock hInstr
      left
      exact ⟨located, hMem, hPc.trans (congrArg EvmYul.UInt256.ofNat
        hLocatedPc.symm)⟩
  | sentinel hPc => exact Or.inr hPc

theorem ArtifactFramePoint.layout
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {state : EVMState}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (point : ArtifactFramePoint artifact bytes state) :
    state.executionEnv.code = bytes ∧
      CompactLayoutPoint artifact.program state.pc :=
  ⟨point.code_eq, point.control.layoutPoint hCompile⟩

/-- A checked compact frame starts at a generated control point (or at the
sentinel for an empty physical source). -/
theorem artifactFramePoint_initial
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {state : EVMState}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hCode : state.executionEnv.code = bytes)
    (hPc : state.pc = EvmYul.UInt256.ofNat 0) :
    ArtifactFramePoint artifact bytes state := by
  refine ⟨hCode, ?_⟩
  rcases Compact.compile?_initial_boundary hCompile with hBlock | hEnd
  · rcases hBlock with ⟨block, hMem, _hSource, hCompact⟩
    exact .boundary block hMem (by simpa [hCompact] using hPc)
  · exact .sentinel (by simpa [hEnd.2] using hPc)

/-- Reachable gasful parent states stay at control points generated by the
compact compiler. This is the semantic preservation obligation used to remove
the raw layout premise from the public bridge. -/
def ArtifactFrameInvariant
    (artifact : Compact.Artifact) (bytes : ByteArray)
    (validJumps : Array Word) (initial : EVMState) : Prop :=
  ∀ state, FrameReachable validJumps initial state →
    ArtifactFramePoint artifact bytes state

/-- A local successful-step preservation theorem lifts to all parent-frame
states reachable by `FrameReachable`. -/
theorem artifactFrameInvariant_of_step
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {validJumps : Array Word} {initial : EVMState}
    (hInitial : ArtifactFramePoint artifact bytes initial)
    (hPreserve : ArtifactFrameStepInvariant artifact bytes validJumps) :
    ArtifactFrameInvariant artifact bytes validJumps initial := by
  intro state hReach
  induction hReach with
  | initial => exact hInitial
  | next hReach hPrefix hStep hContinues ih =>
      exact hPreserve ih hPrefix hStep hContinues

theorem frameLayoutInvariant_of_artifactFrameInvariant
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {validJumps : Array Word} {initial : EVMState}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hInvariant :
      ArtifactFrameInvariant artifact bytes validJumps initial) :
    FrameLayoutInvariant artifact.program bytes validJumps initial := by
  intro state hReach
  exact (hInvariant state hReach).layout hCompile

end EvmCompiler.Assembly.GasfulBridge
