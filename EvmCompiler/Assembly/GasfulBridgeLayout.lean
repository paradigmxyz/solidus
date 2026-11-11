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

set_option maxHeartbeats 1200000 in
theorem PureStackStep.run_code
    {step : PrimStep} (hPure : PureStackStep step)
    {state final : EVMState}
    (hRun : step.run state = .ok final) :
    final.executionEnv.code = state.executionEnv.code := by
  cases hPure <;>
    simp [PrimStep.run, EvmYul.EVM.execBinOp,
      EvmYul.EVM.execUnOp, EvmYul.EVM.execTriOp,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] at hRun ⊢
  all_goals
    try
      simp [EvmYul.dup, EvmYul.swap,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] at hRun
    repeat' split at hRun
  all_goals try simp_all
  all_goals cases hRun
  all_goals rfl

theorem state_extCodeHash_code (state : EvmYul.State .EVM) (value : Word) :
    (state.extCodeHash value).1.executionEnv.code =
      state.executionEnv.code := by
  by_cases hDead : EvmYul.State.dead state.accountMap
      (EvmYul.AccountAddress.ofUInt256 value) = true <;>
    simp [EvmYul.State.extCodeHash, hDead,
      EvmYul.State.addAccessedAccount]

theorem state_sstore_code
    (state : EvmYul.State .EVM) (key value : Word) :
    (state.sstore key value).executionEnv.code =
      state.executionEnv.code := by
  cases hLookup : state.lookupAccount state.executionEnv.codeOwner
  all_goals unfold EvmYul.State.sstore
  all_goals dsimp only
  all_goals rw [hLookup]
  all_goals rfl

theorem state_tstore_code
    (state : EvmYul.State .EVM) (key value : Word) :
    (state.tstore key value).executionEnv.code =
      state.executionEnv.code := by
  cases hLookup : state.lookupAccount state.executionEnv.codeOwner
  all_goals unfold EvmYul.State.tstore
  all_goals dsimp only
  all_goals rw [hLookup]
  all_goals simp only [Option.option]
  all_goals rfl

set_option maxHeartbeats 1200000 in
theorem FrameLocalStep.run_code
    {step : PrimStep} (hLocal : FrameLocalStep step)
    {state final : EVMState}
    (hRun : step.run state = .ok final) :
    final.executionEnv.code = state.executionEnv.code := by
  cases hLocal
  case pure hPure => exact hPure.run_code hRun
  all_goals
    simp [PrimStep.run, EvmYul.EVM.execBinOp,
      EvmYul.EVM.execUnOp, EvmYul.EVM.execTriOp,
      EvmYul.EVM.executionEnvOp, EvmYul.EVM.unaryExecutionEnvOp,
      EvmYul.EVM.machineStateOp, EvmYul.EVM.binaryMachineStateOp,
      EvmYul.EVM.binaryMachineStateOp',
      EvmYul.EVM.ternaryMachineStateOp, EvmYul.EVM.stateOp,
      EvmYul.EVM.unaryStateOp, EvmYul.EVM.binaryStateOp,
      EvmYul.EVM.ternaryCopyOp, EvmYul.EVM.quaternaryCopyOp,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, EvmYul.dup, EvmYul.swap] at hRun ⊢
  all_goals repeat' split at hRun
  all_goals try simp_all
  all_goals cases hRun
  all_goals try
    simpa using state_extCodeHash_code state.toState _
  all_goals try
    simpa using state_sstore_code state.toState _ _
  all_goals try
    simpa using state_tstore_code state.toState _ _
  all_goals rfl

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
  let block : Compact.SourceBlock :=
    { sourcePc, compactPc, sourceInstr, code }
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
          exact
            ⟨{ pc := compactPc
               instr := Compact.pushInstrOfWidth width value },
              hArtifact.mem_program_of_mem_block hBlock (by simp), rfl⟩
  | pushLabel target =>
      simp [Compact.emitSourceBlock?, Compact.emitInstrRev?] at hCode
  | jump target =>
      obtain ⟨width, hWidth, hWidthAt⟩ :=
        Compact.compile?_lookupBranchWidth_of_jump hCompile hBlock rfl
      change artifact.branchWidthAt block = width at hWidthAt
      cases hDest : Compact.lookupLabel? artifact.labels target with
      | none =>
          simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest]
            at hCode
      | some dest =>
          by_cases hFits : Compact.fitsWidth? width dest = true
          · simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest,
              hWidth, hWidthAt, hFits, block] at hCode
            cases hCode
            exact
              ⟨{ pc := compactPc
                 instr := .push width
                   (EvmYul.UInt256.ofNat dest) },
                hArtifact.mem_program_of_mem_block hBlock (by simp), rfl⟩
          · simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest,
              hWidth, hWidthAt, hFits, block] at hCode
  | jumpi target =>
      obtain ⟨width, hWidth, hWidthAt⟩ :=
        Compact.compile?_lookupBranchWidth_of_jumpi hCompile hBlock rfl
      change artifact.branchWidthAt block = width at hWidthAt
      cases hDest : Compact.lookupLabel? artifact.labels target with
      | none =>
          simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest]
            at hCode
      | some dest =>
          by_cases hFits : Compact.fitsWidth? width dest = true
          · simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest,
              hWidth, hWidthAt, hFits, block] at hCode
            cases hCode
            exact
              ⟨{ pc := compactPc
                 instr := .push width
                   (EvmYul.UInt256.ofNat dest) },
                hArtifact.mem_program_of_mem_block hBlock (by simp), rfl⟩
          · simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest,
              hWidth, hWidthAt, hFits, block] at hCode
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

/-- A primitive source block begins with the corresponding compact primitive. -/
theorem compact_prim_entry_mem
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {block : Compact.SourceBlock}
    {op : PrimOp}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .prim op) :
    ∃ located, located ∈ artifact.program.code ∧
      located.pc = block.compactPc ∧ located.instr = .prim op := by
  have hArtifact := Compact.compile?_valid hCompile
  obtain ⟨_compactSize, _hSize, hCode⟩ :=
    (Compact.compile?_blocksValid hCompile).block_emit_of_mem hBlock
  rcases block with ⟨sourcePc, compactPc, sourceInstr, code⟩
  simp at hInstr
  subst sourceInstr
  simp [Compact.emitSourceBlock?, Compact.emitInstrRev?] at hCode
  subst code
  exact ⟨{ pc := compactPc, instr := .prim op },
    hArtifact.mem_program_of_mem_block hBlock (by simp), rfl, rfl⟩

theorem compact_label_entry_mem
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {block : Compact.SourceBlock}
    {label : Label}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .label label) :
    ∃ located, located ∈ artifact.program.code ∧
      located.pc = block.compactPc ∧ located.instr = .jumpdest := by
  have hArtifact := Compact.compile?_valid hCompile
  obtain ⟨_compactSize, _hSize, hCode⟩ :=
    (Compact.compile?_blocksValid hCompile).block_emit_of_mem hBlock
  rcases block with ⟨sourcePc, compactPc, sourceInstr, code⟩
  simp at hInstr
  subst sourceInstr
  simp [Compact.emitSourceBlock?, Compact.emitInstrRev?] at hCode
  subst code
  exact ⟨{ pc := compactPc, instr := .jumpdest },
    hArtifact.mem_program_of_mem_block hBlock (by simp), rfl, rfl⟩

theorem compact_push_entry_mem
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {block : Compact.SourceBlock}
    {value : Word}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .push value) :
    ∃ width located,
      Compact.pushWidthAt? artifact.pinnedPushPcs block.sourcePc value =
          some width ∧
        located ∈ artifact.program.code ∧
        located.pc = block.compactPc ∧
        located.instr = Compact.pushInstrOfWidth width value := by
  have hArtifact := Compact.compile?_valid hCompile
  obtain ⟨_compactSize, hSize, hCode⟩ :=
    (Compact.compile?_blocksValid hCompile).block_emit_of_mem hBlock
  rcases block with ⟨sourcePc, compactPc, sourceInstr, code⟩
  simp at hInstr
  subst sourceInstr
  cases hWidth : Compact.pushWidthAt?
      artifact.pinnedPushPcs sourcePc value with
  | none => simp [Compact.sourceInstrSizeAt?, hWidth] at hSize
  | some width =>
      simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hWidth] at hCode
      subst code
      exact ⟨width,
        { pc := compactPc, instr := Compact.pushInstrOfWidth width value },
        rfl, hArtifact.mem_program_of_mem_block hBlock (by simp), rfl, rfl⟩

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
      located.pc = block.compactPc + artifact.branchWidthAt block + 1 ∧
      located.instr = if isJumpi then .jumpi else .jump := by
  have hArtifact := Compact.compile?_valid hCompile
  obtain ⟨compactSize, hSize, hCode⟩ :=
    (Compact.compile?_blocksValid hCompile).block_emit_of_mem hBlock
  rcases block with ⟨sourcePc, compactPc, sourceInstr, code⟩
  let block : Compact.SourceBlock :=
    { sourcePc, compactPc, sourceInstr, code }
  cases hJumpi : isJumpi
  · simp [hJumpi] at hInstr ⊢
    subst sourceInstr
    obtain ⟨width, hWidth, hWidthAt⟩ :=
      Compact.compile?_lookupBranchWidth_of_jump hCompile hBlock rfl
    change artifact.branchWidthAt block = width at hWidthAt
    rw [hWidthAt]
    cases hDest : Compact.lookupLabel? artifact.labels label with
    | none =>
        simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest] at hCode
    | some dest =>
        by_cases hFits : Compact.fitsWidth? width dest = true
        · simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest,
            hWidth, hWidthAt, hFits, block] at hCode
          cases hCode
          exact
            ⟨{ pc := compactPc + width + 1,
               instr := .jump },
              hArtifact.mem_program_of_mem_block hBlock (by simp),
              by simp [hWidthAt], rfl⟩
        · simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest,
            hWidth, hWidthAt, hFits, block] at hCode
  · simp [hJumpi] at hInstr ⊢
    subst sourceInstr
    obtain ⟨width, hWidth, hWidthAt⟩ :=
      Compact.compile?_lookupBranchWidth_of_jumpi hCompile hBlock rfl
    change artifact.branchWidthAt block = width at hWidthAt
    rw [hWidthAt]
    cases hDest : Compact.lookupLabel? artifact.labels label with
    | none =>
        simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest] at hCode
    | some dest =>
        by_cases hFits : Compact.fitsWidth? width dest = true
        · simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest,
            hWidth, hWidthAt, hFits, block] at hCode
          cases hCode
          exact
            ⟨{ pc := compactPc + width + 1,
               instr := .jumpi },
              hArtifact.mem_program_of_mem_block hBlock (by simp),
              by simp [hWidthAt], rfl⟩
        · simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest,
            hWidth, hWidthAt, hFits, block] at hCode

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
        located.instr = .push (artifact.branchWidthAt block)
          (EvmYul.UInt256.ofNat dest) := by
  rcases block with ⟨sourcePc, compactPc, sourceInstr, code⟩
  let block : Compact.SourceBlock :=
    { sourcePc, compactPc, sourceInstr, code }
  have hArtifact := Compact.compile?_valid hCompile
  obtain ⟨_compactSize, _hSize, hCode⟩ :=
    (Compact.compile?_blocksValid hCompile).block_emit_of_mem hBlock
  cases hJumpi : isJumpi
  · simp [hJumpi] at hInstr
    obtain ⟨width, hWidth, hWidthAt⟩ :=
      Compact.compile?_lookupBranchWidth_of_jump hCompile hBlock
        (by simpa [block] using hInstr)
    change artifact.branchWidthAt block = width at hWidthAt
    rw [hWidthAt]
    rw [hInstr] at hCode
    cases hDest : Compact.lookupLabel? artifact.labels label with
    | none =>
        simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest] at hCode
    | some dest =>
        by_cases hFits : Compact.fitsWidth? width dest = true
        · simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest,
            hWidth, hWidthAt, hFits, block] at hCode
          cases hCode
          let located : Compact.Located :=
            { pc := compactPc
              instr := .push width
                (EvmYul.UInt256.ofNat dest) }
          exact ⟨dest, located, rfl,
            hArtifact.mem_program_of_mem_block hBlock (by simp [located]),
            rfl, by simp [located, hWidthAt]⟩
        · simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest,
            hWidth, hWidthAt, hFits, block] at hCode
  · simp [hJumpi] at hInstr
    obtain ⟨width, hWidth, hWidthAt⟩ :=
      Compact.compile?_lookupBranchWidth_of_jumpi hCompile hBlock
        (by simpa [block] using hInstr)
    change artifact.branchWidthAt block = width at hWidthAt
    rw [hWidthAt]
    rw [hInstr] at hCode
    cases hDest : Compact.lookupLabel? artifact.labels label with
    | none =>
        simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest] at hCode
    | some dest =>
        by_cases hFits : Compact.fitsWidth? width dest = true
        · simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest,
            hWidth, hWidthAt, hFits, block] at hCode
          cases hCode
          let located : Compact.Located :=
            { pc := compactPc
              instr := .push width
                (EvmYul.UInt256.ofNat dest) }
          exact ⟨dest, located, rfl,
            hArtifact.mem_program_of_mem_block hBlock (by simp [located]),
            rfl, by simp [located, hWidthAt]⟩
        · simp [Compact.emitSourceBlock?, Compact.emitInstrRev?, hDest,
            hWidth, hWidthAt, hFits, block] at hCode
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
        sourceNext (block.compactPc + artifact.branchWidthAt block + 2) := by
  obtain ⟨compactSize, hSize, _hCode⟩ :=
    (Compact.compile?_blocksValid hCompile).block_emit_of_mem hBlock
  have hNext :=
    (Compact.compile?_blocksValid hCompile).next_boundary hBlock hSize
  have hArtifact := Compact.compile?_valid hCompile
  rw [hArtifact.blockCode] at hNext
  cases hJumpi : isJumpi
  · simp [hJumpi] at hInstr
    obtain ⟨width, hWidth, hWidthAt⟩ :=
      Compact.compile?_lookupBranchWidth_of_jump hCompile hBlock hInstr
    rw [hInstr] at hSize hNext
    simp [Compact.sourceInstrSizeAt?, hWidth, hWidthAt] at hSize
    subst compactSize
    exact ⟨block.sourcePc + (Assembly.Instr.jump label).byteSize, by
      simpa [hWidthAt, Nat.add_assoc] using hNext⟩
  · simp [hJumpi] at hInstr
    obtain ⟨width, hWidth, hWidthAt⟩ :=
      Compact.compile?_lookupBranchWidth_of_jumpi hCompile hBlock hInstr
    rw [hInstr] at hSize hNext
    simp [Compact.sourceInstrSizeAt?, hWidth, hWidthAt] at hSize
    subst compactSize
    exact ⟨block.sourcePc + (Assembly.Instr.jumpi label).byteSize, by
      simpa [hWidthAt, Nat.add_assoc] using hNext⟩

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
        (block.compactPc + artifact.branchWidthAt block + 1))
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

theorem artifactFramePoint_of_block_next
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {block : Compact.SourceBlock} {compactSize : Nat}
    {next : EVMState}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hBlock : block ∈ artifact.blocks)
    (hSize : Compact.sourceInstrSizeAt? artifact.pinnedPushPcs
      artifact.branchWidths block.sourcePc block.sourceInstr =
        some compactSize)
    (hCode : next.executionEnv.code = bytes)
    (hPc : next.pc = EvmYul.UInt256.ofNat
      (block.compactPc + compactSize)) :
    ArtifactFramePoint artifact bytes next := by
  have hNext :=
    (Compact.compile?_blocksValid hCompile).next_boundary hBlock hSize
  rw [(Compact.compile?_valid hCompile).blockCode] at hNext
  have hNext' :
      Compact.BoundaryPair artifact.blocks artifact.physicalSource.byteLength
        (Compact.Program.codeByteLength artifact.program.code)
        (block.sourcePc + block.sourceInstr.byteSize)
        (block.compactPc + compactSize) := by
    simpa using hNext
  exact ⟨hCode, compactControlPoint_of_boundary hNext' hPc⟩

theorem artifact_prim_decode
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {state : EVMState} {block : Compact.SourceBlock} {op : PrimOp}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .prim op)
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc) :
    EvmYul.EVM.decode state.executionEnv.code state.pc =
      some (op.toEVM, none) := by
  obtain ⟨located, hMem, hLocatedPc, hLocatedInstr⟩ :=
    compact_prim_entry_mem hCompile hBlock hInstr
  obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
    hDecode.decodes located hMem
  rw [hLocatedInstr] at hInstrDecoded
  simp [Compact.Instr.decoded?] at hInstrDecoded
  subst decoded
  have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
    hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
  simpa [hCode, hStatePc] using hBytesDecoded

theorem artifactFramePoint_resource_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {state next : EVMState} {block : Compact.SourceBlock}
    {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (kind : Simulation.ResourceQuery)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .prim (resourcePrimOp kind))
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    ArtifactFramePoint artifact bytes next := by
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
      have hNextCode :
          (gasfulResourceNext kind state).executionEnv.code = bytes := by
        simpa [gasfulResourceNext, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, afterDynamicChargeAt, chargeGas] using hCode
      have hNextPc :
          (gasfulResourceNext kind state).pc =
            EvmYul.UInt256.ofNat (block.compactPc + 1) := by
        simp [gasfulResourceNext, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, afterDynamicChargeAt, chargeGas,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, hPc, uint256_ofNat_add]
      have hSize : Compact.sourceInstrSizeAt? artifact.pinnedPushPcs
          artifact.branchWidths block.sourcePc block.sourceInstr = some 1 := by
        simp [hInstr, Compact.sourceInstrSizeAt?]
      exact artifactFramePoint_of_block_next hCompile hBlock hSize
        hNextCode hNextPc

theorem artifactFramePoint_pc_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {state next : EVMState} {block : Compact.SourceBlock}
    {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .prim .pc)
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    ArtifactFramePoint artifact bytes next := by
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
      have hNextCode :
          (gasfulPcNext state).executionEnv.code = bytes := by
        simpa [gasfulPcNext, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, afterDynamicChargeAt, chargeGas] using hCode
      have hNextPc :
          (gasfulPcNext state).pc =
            EvmYul.UInt256.ofNat (block.compactPc + 1) := by
        simp [gasfulPcNext, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, afterDynamicChargeAt, chargeGas,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, hPc, uint256_ofNat_add]
      have hSize : Compact.sourceInstrSizeAt? artifact.pinnedPushPcs
          artifact.branchWidths block.sourcePc block.sourceInstr = some 1 := by
        simp [hInstr, Compact.sourceInstrSizeAt?]
      exact artifactFramePoint_of_block_next hCompile hBlock hSize
        hNextCode hNextPc

theorem artifactFramePoint_call_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {validJumps : Array Word} {state next : EVMState}
    {block : Compact.SourceBlock} {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (kind : Simulation.CallKind)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .prim (callPrimOp kind))
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    ArtifactFramePoint artifact bytes next := by
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
      have hSize : Compact.sourceInstrSizeAt? artifact.pinnedPushPcs
          artifact.branchWidths block.sourcePc block.sourceInstr = some 1 := by
        simp [hInstr, Compact.sourceInstrSizeAt?]
      exact artifactFramePoint_of_block_next hCompile hBlock hSize
        hNextCode hNextPc

theorem artifactFramePoint_create_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {validJumps : Array Word} {state next : EVMState}
    {block : Compact.SourceBlock} {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (kind : Simulation.CreateKind)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .prim (createPrimOp kind))
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    ArtifactFramePoint artifact bytes next := by
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
      have hSize : Compact.sourceInstrSizeAt? artifact.pinnedPushPcs
          artifact.branchWidths block.sourcePc block.sourceInstr = some 1 := by
        simp [hInstr, Compact.sourceInstrSizeAt?]
      exact artifactFramePoint_of_block_next hCompile hBlock hSize
        hNextCode hNextPc

theorem artifactFramePoint_prim_continuing_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {validJumps : Array Word} {state next : EVMState}
    {block : Compact.SourceBlock} {op : PrimOp} {primStep : PrimStep}
    {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .prim op)
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hContinuing : op.continuingStep? = some primStep)
    (hLocal : FrameLocalPrimOp op)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    ArtifactFramePoint artifact bytes next := by
  obtain ⟨located, hMem, hLocatedPc, hLocatedInstr⟩ :=
    compact_prim_entry_mem hCompile hBlock hInstr
  obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
    hDecode.decodes located hMem
  rw [hLocatedInstr] at hInstrDecoded
  simp [Compact.Instr.decoded?] at hInstrDecoded
  subst decoded
  have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
    hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
  have hDecoded :
      EvmYul.EVM.decode state.executionEnv.code state.pc =
        some (op.toEVM, none) := by
    simpa [hCode, hStatePc] using hBytesDecoded
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
      rw [PrimOp.step_eq_continuingStep_run hContinuing] at hPrim
      have hLocalStep := frameLocalStep_of_continuingStep hLocal hContinuing
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
      have hNextPc : next.pc = EvmYul.UInt256.ofNat
          (block.compactPc + 1) := by
        calc
          next.pc = (afterEVMInstructionChargeAt state).pc +
              EvmYul.UInt256.ofNat 1 := hNextPcRaw
          _ = state.pc + EvmYul.UInt256.ofNat 1 := by
            simp [afterEVMInstructionChargeAt, afterMemoryChargeAt,
              afterDynamicChargeAt, chargeGas]
          _ = EvmYul.UInt256.ofNat (block.compactPc + 1) := by
            rw [hPc, uint256_ofNat_add]
      have hSize : Compact.sourceInstrSizeAt? artifact.pinnedPushPcs
          artifact.branchWidths block.sourcePc block.sourceInstr = some 1 := by
        simp [hInstr, Compact.sourceInstrSizeAt?]
      exact artifactFramePoint_of_block_next hCompile hBlock hSize
        hNextCode hNextPc

theorem artifactFramePoint_label_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {state next : EVMState} {block : Compact.SourceBlock}
    {label : Label} {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .label label)
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    ArtifactFramePoint artifact bytes next := by
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
      have hSize : Compact.sourceInstrSizeAt? artifact.pinnedPushPcs
          artifact.branchWidths block.sourcePc block.sourceInstr = some 1 := by
        simp [hInstr, Compact.sourceInstrSizeAt?]
      apply artifactFramePoint_of_block_next hCompile hBlock hSize
      · simpa [afterEVMInstructionChargeAt, afterMemoryChargeAt,
          chargeGas] using hCode
      · simp [EvmYul.EVM.State.incrPC, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, chargeGas, hPc, uint256_ofNat_add]

theorem artifactFramePoint_push_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {state next : EVMState} {block : Compact.SourceBlock}
    {value : Word} {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .push value)
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    ArtifactFramePoint artifact bytes next := by
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
    have hDecoded : EvmYul.EVM.decode state.executionEnv.code state.pc =
        some (EvmYul.Operation.PUSH0, none) := by
      simpa [hCode, hStatePc] using hBytesDecoded
    cases stepFuel with
    | zero => simp [EvmYul.EVM.step] at hStep
    | succ fuel =>
        rw [hDecoded] at hStep
        simp only [Option.getD_some] at hStep
        rw [evm_step_push0_eq_next fuel state] at hStep
        have hNext :
            next = gasfulPushNext 0 (EvmYul.UInt256.ofNat 0) state := by
          simpa using hStep.symm
        subst next
        have hSize : Compact.sourceInstrSizeAt? artifact.pinnedPushPcs
            artifact.branchWidths block.sourcePc block.sourceInstr =
              some (0 + 1) := by
          simp [hInstr, Compact.sourceInstrSizeAt?, hWidth]
        apply artifactFramePoint_of_block_next hCompile hBlock hSize
        · simpa [gasfulPushNext, afterEVMInstructionChargeAt,
            afterMemoryChargeAt, chargeGas] using hCode
        · simp [gasfulPushNext, EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC, afterEVMInstructionChargeAt,
            afterMemoryChargeAt, chargeGas, hPc, uint256_ofNat_add,
            Nat.add_assoc]
  simp only [Compact.pushInstrOfWidth, if_neg hZeroWidth] at hLocatedInstr
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
      have hSize : Compact.sourceInstrSizeAt? artifact.pinnedPushPcs
          artifact.branchWidths block.sourcePc block.sourceInstr =
            some (width + 1) := by
        simp [hInstr, Compact.sourceInstrSizeAt?, hWidth]
      apply artifactFramePoint_of_block_next hCompile hBlock hSize
      · simpa [gasfulPushNext, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, chargeGas] using hCode
      · simp [gasfulPushNext, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, chargeGas, hPc, uint256_ofNat_add,
          Nat.add_assoc]

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
      (gasfulPushNext (artifact.branchWidthAt block)
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
  have hExact := evm_step_push_eq_next fuel state
    (EvmYul.UInt256.ofNat dest) hFits hOp
  rw [hDecoded] at hStep
  simp only [Option.getD_some] at hStep
  rw [hExact] at hStep
  have hNext : next = gasfulPushNext (artifact.branchWidthAt block)
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
      (block.compactPc + artifact.branchWidthAt block + 1)) :
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
          (block.compactPc + artifact.branchWidthAt block + 1))
        (EvmYul.UInt256.ofNat 1) =
          EvmYul.UInt256.ofNat
            (block.compactPc + artifact.branchWidthAt block + 2)
      unfold EvmYul.UInt256.add EvmYul.UInt256.ofNat
      congr 1
      apply Fin.ext
      change
        (((block.compactPc + artifact.branchWidthAt block + 1) %
            EvmYul.UInt256.size + 1 % EvmYul.UInt256.size) %
          EvmYul.UInt256.size) =
        (block.compactPc + artifact.branchWidthAt block + 2) %
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
      (block.compactPc + artifact.branchWidthAt block + 1))
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
      (block.compactPc + artifact.branchWidthAt block + 1))
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
      (block.compactPc + artifact.branchWidthAt block + 1))
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

def ArtifactRemainingPrimBoundaryStepInvariant
    (artifact : Compact.Artifact) (bytes : ByteArray)
    (validJumps : Array Word) : Prop :=
  ∀ {current next : EVMState} {block : Compact.SourceBlock}
      {op : PrimOp} {stepFuel : Nat},
    current.executionEnv.code = bytes →
    block ∈ artifact.blocks →
    block.sourceInstr = .prim op →
    current.pc = EvmYul.UInt256.ofNat block.compactPc →
    (∀ primStep, op.continuingStep? = some primStep →
      ¬ FrameLocalPrimOp op) →
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

theorem artifactRemainingPrimBoundaryStepInvariant_of_compile
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {validJumps : Array Word}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes) :
    ArtifactRemainingPrimBoundaryStepInvariant artifact bytes validJumps := by
  intro current next block op stepFuel hCode hBlock hInstr hPc hNotLocal
    hPrefix hStep hContinues
  have hDecoded := artifact_prim_decode hCompile hDecode hCode hBlock
    hInstr hPc
  cases hContinuing : op.continuingStep? with
  | some primStep =>
      by_cases hMsize : op = .msize
      · subst op
        exact artifactFramePoint_resource_step hCompile hDecode .msize
          hCode hBlock (by simpa [resourcePrimOp] using hInstr) hPc hStep
      · by_cases hInvalid : op = .invalid
        · subst op
          cases stepFuel with
          | zero => simp [EvmYul.EVM.step] at hStep
          | succ fuel =>
              rw [hDecoded] at hStep
              simp only [Option.getD_some] at hStep
              change EvmYul.step (τ := .EVM) EvmYul.Operation.INVALID none
                  { { afterMemoryChargeAt current with
                        execLength :=
                          (afterMemoryChargeAt current).execLength + 1 } with
                    gasAvailable :=
                      (afterMemoryChargeAt current).gasAvailable -
                        EvmYul.UInt256.ofNat (dynamicGasCostAt current) } =
                Except.ok next at hStep
              change Except.error
                  EvmYul.EVM.ExecutionException.InvalidInstruction =
                Except.ok next at hStep
              cases hStep
        · exact False.elim
            ((hNotLocal primStep hContinuing)
              (frameLocalPrimOp_of_continuingStep hContinuing hMsize
                hInvalid))
  | none =>
      by_cases hPcOp : op = .pc
      · subst op
        exact artifactFramePoint_pc_step hCompile hDecode hCode hBlock
          hInstr hPc hStep
      · by_cases hGasOp : op = .gas
        · subst op
          exact artifactFramePoint_resource_step hCompile hDecode .gas
            hCode hBlock (by simpa [resourcePrimOp] using hInstr) hPc hStep
        · by_cases hStopOp : op = .stop
          · subst op
            have hDecodedOp :
                decodedOperationAt current = EvmYul.Operation.STOP := by
              simp [decodedOperationAt, hDecoded, PrimOp.toEVM]
            simp [hDecodedOp, haltOutputAt] at hContinues
          · by_cases hReturnOp : op = .return
            · subst op
              have hDecodedOp :
                  decodedOperationAt current = EvmYul.Operation.RETURN := by
                simp [decodedOperationAt, hDecoded, PrimOp.toEVM]
              simp [hDecodedOp, haltOutputAt] at hContinues
            · by_cases hRevertOp : op = .revert
              · subst op
                have hDecodedOp :
                    decodedOperationAt current = EvmYul.Operation.REVERT := by
                  simp [decodedOperationAt, hDecoded, PrimOp.toEVM]
                simp [hDecodedOp, haltOutputAt] at hContinues
              · by_cases hSelfdestructOp : op = .selfdestruct
                · subst op
                  have hDecodedOp : decodedOperationAt current =
                      EvmYul.Operation.SELFDESTRUCT := by
                    simp [decodedOperationAt, hDecoded, PrimOp.toEVM]
                  simp [hDecodedOp, haltOutputAt] at hContinues
                · have hMsizeOp : op ≠ .msize := by
                    intro h
                    subst op
                    simp [PrimOp.continuingStep?] at hContinuing
                  have hValid : EvmYul.EVM.δ op.toEVM ≠ none := by
                    have hRaw := hPrefix.static.stackLimit.memoryAccess.jumps.stack.opcodeValid_raw
                    simpa [decodedOperationAt, hDecoded] using hRaw
                  rcases primOp_external_of_no_continuing op hValid hPcOp
                      hGasOp hMsizeOp hStopOp hReturnOp hRevertOp
                      hSelfdestructOp hContinuing with
                    ⟨kind, hCall⟩ | ⟨kind, hCreate⟩
                  · subst op
                    exact artifactFramePoint_call_step hCompile hDecode kind
                      hCode hBlock hInstr hPc hPrefix hStep
                  · subst op
                    exact artifactFramePoint_create_step hCompile hDecode kind
                      hCode hBlock hInstr hPc hPrefix hStep

theorem artifactOrdinaryBoundaryStepInvariant_of_remainingPrim
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {validJumps : Array Word}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hRemaining :
      ArtifactRemainingPrimBoundaryStepInvariant artifact bytes validJumps) :
    ArtifactOrdinaryBoundaryStepInvariant artifact bytes validJumps := by
  intro current next block stepFuel hCode hBlock hPc hNotJump hNotJumpi
    hPrefix hStep hContinues
  generalize hInstr : block.sourceInstr = instr
  cases instr with
  | label label =>
      exact artifactFramePoint_label_step hCompile hDecode hCode hBlock
        hInstr hPc hStep
  | prim op =>
      cases hContinuing : op.continuingStep? with
      | none =>
          exact hRemaining hCode hBlock hInstr hPc
            (by intro primStep hSome; rw [hContinuing] at hSome; contradiction)
            hPrefix hStep hContinues
      | some primStep =>
          by_cases hLocal : FrameLocalPrimOp op
          · exact artifactFramePoint_prim_continuing_step hCompile hDecode
              hCode hBlock hInstr hPc hContinuing hLocal hPrefix hStep
          · exact hRemaining hCode hBlock hInstr hPc
              (by
                intro otherStep hOther
                rw [hContinuing] at hOther
                cases Option.some.inj hOther
                exact hLocal)
              hPrefix hStep hContinues
  | push value =>
      exact artifactFramePoint_push_step hCompile hDecode hCode hBlock
        hInstr hPc hStep
  | pushLabel target =>
      obtain ⟨_compactSize, _hSize, hEmit⟩ :=
        (Compact.compile?_blocksValid hCompile).block_emit_of_mem hBlock
      rw [hInstr] at hEmit
      simp [Compact.emitSourceBlock?, Compact.emitInstrRev?] at hEmit
  | jump label => exact False.elim (hNotJump label hInstr)
  | jumpi label => exact False.elim (hNotJumpi label hInstr)
  | jumpDynamic =>
      obtain ⟨_compactSize, _hSize, hEmit⟩ :=
        (Compact.compile?_blocksValid hCompile).block_emit_of_mem hBlock
      rw [hInstr] at hEmit
      simp [Compact.emitSourceBlock?, Compact.emitInstrRev?] at hEmit

theorem artifactOrdinaryBoundaryStepInvariant_of_compile
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {validJumps : Array Word}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes) :
    ArtifactOrdinaryBoundaryStepInvariant artifact bytes validJumps := by
  exact artifactOrdinaryBoundaryStepInvariant_of_remainingPrim hCompile
    hDecode
    (artifactRemainingPrimBoundaryStepInvariant_of_compile
      (validJumps := validJumps) hCompile hDecode)

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
