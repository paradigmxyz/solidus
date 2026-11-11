import EvmCompiler.Assembly.MachineBlockDedup
import EvmCompiler.Assembly.Bytecode
import EvmCompiler.Assembly.InteractionPreservation

namespace EvmCompiler
namespace Assembly
namespace MachineBlockDedup

theorem label_mem_flattenMachineBlocks
    {blocks : List MachineBlock} {block : MachineBlock}
    (hBlock : block ∈ blocks) :
    Instr.label block.label ∈ flattenMachineBlocks blocks := by
  unfold flattenMachineBlocks
  exact List.mem_flatMap.mpr ⟨block, hBlock, by simp⟩

theorem code_mem_flattenMachineBlocks
    {blocks : List MachineBlock} {block : MachineBlock}
    {instr : Instr}
    (hBlock : block ∈ blocks) (hInstr : instr ∈ block.code) :
    instr ∈ flattenMachineBlocks blocks := by
  unfold flattenMachineBlocks
  exact List.mem_flatMap.mpr ⟨block, hBlock, by simp [hInstr]⟩

theorem source_label_resolves_of_check
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks) :
    ∃ pc, source.labelPc block.label = some pc := by
  rcases check_parts hCheck with
    ⟨hAccepted, _, _, _, hParse, _, _, _, _, _, _, _, _, _, _⟩
  have hFlatten :
      flattenMachineBlocks cert.originalBlocks = source :=
    flatten_eq_of_parseExact hParse
  have hLabelMem : Instr.label block.label ∈ source := by
    rw [← hFlatten]
    exact label_mem_flattenMachineBlocks hBlock
  exact
    Program.labelPc_exists_of_mem_labels source
      (Program.mem_labels_of_label_mem hLabelMem)

theorem optimized_representative_of_check
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks) :
    ∃ representative,
      representative ∈ cert.optimizedBlocks ∧
      representative.label = resolveAlias cert.aliases block.label ∧
      representative.code =
        block.code.map (rewriteMachineInstr cert.aliases) := by
  rcases check_parts hCheck with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hCorresponds, _, _⟩
  rcases exact_code_correspondence_of_check hCorresponds hBlock with
    ⟨representative, hFind, hCode⟩
  exact
    ⟨representative,
      mem_of_findMachineBlock?_eq_some hFind,
      label_eq_of_findMachineBlock?_eq_some hFind,
      hCode⟩

theorem output_label_resolves_of_check
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks) :
    ∃ pc,
      cert.output.labelPc (resolveAlias cert.aliases block.label) =
        some pc := by
  rcases optimized_representative_of_check hCheck hBlock with
    ⟨representative, hRepresentative, hLabel, _⟩
  have hOutput :
      flattenMachineBlocks cert.optimizedBlocks = cert.output :=
    output_eq_flatten_of_check hCheck
  have hLabelMem :
      Instr.label (resolveAlias cert.aliases block.label) ∈ cert.output := by
    rw [← hOutput, ← hLabel]
    exact label_mem_flattenMachineBlocks hRepresentative
  exact
    Program.labelPc_exists_of_mem_labels cert.output
      (Program.mem_labels_of_label_mem hLabelMem)

theorem labelPc_zero_of_entryFirst
    {entry : Label} {blocks : List MachineBlock}
    (hFirst : entryFirst? entry blocks = true) :
    (flattenMachineBlocks blocks).labelPc entry = some 0 := by
  cases blocks with
  | nil =>
      simp [entryFirst?] at hFirst
  | cons first rest =>
      have hLabel : first.label = entry := by
        simpa [entryFirst?] using hFirst
      subst entry
      simp [flattenMachineBlocks, Program.labelPc, Program.labelPcFrom]

theorem instrAtPc_zero_of_entryFirst
    {entry : Label} {blocks : List MachineBlock}
    (hFirst : entryFirst? entry blocks = true) :
    Program.instrAtPc (flattenMachineBlocks blocks) 0 =
      some (0, .label entry) := by
  cases blocks with
  | nil =>
      simp [entryFirst?] at hFirst
  | cons first rest =>
      have hLabel : first.label = entry := by
        simpa [entryFirst?] using hFirst
      subst entry
      simp [flattenMachineBlocks, Program.instrAtPc,
        Program.instrAtPcFrom]

theorem entry_labelPc_zero_of_check
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true) :
    source.labelPc entry = some 0 ∧
      cert.output.labelPc entry = some 0 := by
  rcases check_parts hCheck with
    ⟨_, _, _, _, hParse, _, _, _, _, _, _, hEntryFirst, _, _, _⟩
  simp only [Bool.and_eq_true] at hEntryFirst
  have hOriginalFirst :
      entryFirst? entry cert.originalBlocks = true :=
    hEntryFirst.1
  have hOptimizedFirst :
      entryFirst? entry cert.optimizedBlocks = true :=
    hEntryFirst.2
  have hSourceFlatten :
      flattenMachineBlocks cert.originalBlocks = source :=
    flatten_eq_of_parseExact hParse
  have hOutputFlatten :
      flattenMachineBlocks cert.optimizedBlocks = cert.output :=
    output_eq_flatten_of_check hCheck
  constructor
  · rw [← hSourceFlatten]
    exact labelPc_zero_of_entryFirst hOriginalFirst
  · rw [← hOutputFlatten]
    exact labelPc_zero_of_entryFirst hOptimizedFirst

def AtOffset (program : Program) (label : Label)
    (offset pc : Nat) : Prop :=
  ∃ base,
    program.labelPc label = some base ∧
      pc = base + offset

def PcRel (source : Program) (cert : Cert)
    (sourcePc optimizedPc : Nat) : Prop :=
  ∃ block,
    block ∈ cert.originalBlocks ∧
      ∃ offset,
        AtOffset source block.label offset sourcePc ∧
          AtOffset cert.output (resolveAlias cert.aliases block.label)
            offset optimizedPc

theorem block_label_pcRel_of_check
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks) :
    ∃ sourcePc optimizedPc,
      source.labelPc block.label = some sourcePc ∧
      cert.output.labelPc (resolveAlias cert.aliases block.label) =
        some optimizedPc ∧
      PcRel source cert sourcePc optimizedPc := by
  rcases source_label_resolves_of_check hCheck hBlock with
    ⟨sourcePc, hSourcePc⟩
  rcases output_label_resolves_of_check hCheck hBlock with
    ⟨optimizedPc, hOptimizedPc⟩
  refine
    ⟨sourcePc, optimizedPc, hSourcePc, hOptimizedPc,
      ⟨block, hBlock, 0,
        ⟨sourcePc, hSourcePc, by simp⟩,
        ⟨optimizedPc, hOptimizedPc, by simp⟩⟩⟩

theorem block_offset_pcRel_of_check
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks)
    (offset : Nat) :
    ∃ sourceBase optimizedBase,
      PcRel source cert (sourceBase + offset) (optimizedBase + offset) := by
  rcases source_label_resolves_of_check hCheck hBlock with
    ⟨sourceBase, hSourcePc⟩
  rcases output_label_resolves_of_check hCheck hBlock with
    ⟨optimizedBase, hOptimizedPc⟩
  exact
    ⟨sourceBase, optimizedBase,
      ⟨block, hBlock, offset,
        ⟨sourceBase, hSourcePc, rfl⟩,
        ⟨optimizedBase, hOptimizedPc, rfl⟩⟩⟩

def LocalInstrAt (block : MachineBlock) (offset : Nat)
    (instr : Instr) : Prop :=
  ∃ before after,
    block.code = before ++ instr :: after ∧
    offset = (Instr.label block.label).byteSize + before.byteLength

@[simp]
theorem rewriteMachineInstr_byteSize (aliases : LabelAliases)
    (instr : Instr) :
    (rewriteMachineInstr aliases instr).byteSize = instr.byteSize := by
  cases instr <;> rfl

theorem byteLength_map_rewriteMachineInstr
    (aliases : LabelAliases) (code : Program) :
    Program.byteLength (code.map (rewriteMachineInstr aliases)) =
      Program.byteLength code := by
  induction code with
  | nil =>
      rfl
  | cons instr rest ih =>
      rw [List.map_cons, Program.byteLength_cons,
        Program.byteLength_cons, rewriteMachineInstr_byteSize, ih]

theorem localInstrAt_rewrite
    {aliases : LabelAliases} {block representative : MachineBlock}
    (hCode :
      representative.code =
        block.code.map (rewriteMachineInstr aliases))
    {offset : Nat} {instr : Instr}
    (hLocal : LocalInstrAt block offset instr) :
    LocalInstrAt representative offset
      (rewriteMachineInstr aliases instr) := by
  rcases hLocal with ⟨before, after, hBody, hOffset⟩
  refine
    ⟨before.map (rewriteMachineInstr aliases),
      after.map (rewriteMachineInstr aliases), ?_, ?_⟩
  · rw [hCode, hBody, List.map_append]
    simp
  · rw [hOffset, byteLength_map_rewriteMachineInstr]
    rfl

theorem flattenMachineBlocks_append
    (left right : List MachineBlock) :
    flattenMachineBlocks (left ++ right) =
      flattenMachineBlocks left ++ flattenMachineBlocks right := by
  simp [flattenMachineBlocks, List.flatMap_append]

theorem instrAtPcFrom_append_at_head
    (preCode : Program) (instr : Instr) (suffix : Program)
    (base : Nat) :
    Program.instrAtPcFrom (preCode ++ instr :: suffix) base
        (base + preCode.byteLength) =
      some (base + preCode.byteLength, instr) := by
  induction preCode generalizing base with
  | nil =>
      simp [Program.instrAtPcFrom]
  | cons head rest ih =>
      rw [Program.byteLength_cons]
      have hNe :
          base + (head.byteSize + Program.byteLength rest) ≠ base := by
        have hPos := Instr.byteSize_pos head
        omega
      simp only [List.cons_append, Program.instrAtPcFrom, if_neg hNe]
      simpa [Nat.add_assoc] using
        ih (base := base + head.byteSize)

theorem instrAtPc_flattenMachineBlocks_of_decomposition
    {blocks beforeBlocks afterBlocks : List MachineBlock}
    {block : MachineBlock} {before after : Program} {instr : Instr}
    (hBlocks : blocks = beforeBlocks ++ block :: afterBlocks)
    (hCode : block.code = before ++ instr :: after) :
    let preCode :=
      flattenMachineBlocks beforeBlocks ++
        [Instr.label block.label] ++ before
    Program.instrAtPc (flattenMachineBlocks blocks) preCode.byteLength =
      some (preCode.byteLength, instr) := by
  dsimp only
  let preCode :=
    flattenMachineBlocks beforeBlocks ++
      [Instr.label block.label] ++ before
  have hFlatten :
      flattenMachineBlocks blocks =
        preCode ++ instr :: (after ++ flattenMachineBlocks afterBlocks) := by
    simp [hBlocks, hCode, preCode, flattenMachineBlocks_append,
      flattenMachineBlocks, List.append_assoc]
  rw [hFlatten]
  simpa [Program.instrAtPc, preCode, List.append_assoc] using
    instrAtPcFrom_append_at_head preCode instr
      (after ++ flattenMachineBlocks afterBlocks) 0

theorem instruction_point_rel_of_check
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks)
    {offset : Nat} {instr : Instr}
    (hLocal : LocalInstrAt block offset instr) :
    ∃ representative sourceBase optimizedBase,
      representative ∈ cert.optimizedBlocks ∧
      representative.label = resolveAlias cert.aliases block.label ∧
      LocalInstrAt representative offset
        (rewriteMachineInstr cert.aliases instr) ∧
      PcRel source cert (sourceBase + offset) (optimizedBase + offset) := by
  rcases optimized_representative_of_check hCheck hBlock with
    ⟨representative, hRepresentative, hLabel, hCode⟩
  rcases block_offset_pcRel_of_check hCheck hBlock offset with
    ⟨sourceBase, optimizedBase, hPcRel⟩
  exact
    ⟨representative, sourceBase, optimizedBase,
      hRepresentative, hLabel,
      localInstrAt_rewrite hCode hLocal, hPcRel⟩

theorem source_instr_mem_of_check
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks)
    {offset : Nat} {instr : Instr}
    (hLocal : LocalInstrAt block offset instr) :
    instr ∈ source := by
  rcases hLocal with ⟨before, after, hCode, _⟩
  have hInstrBlock : instr ∈ block.code := by
    rw [hCode]
    simp
  rcases check_parts hCheck with
    ⟨_, _, _, _, hParse, _, _, _, _, _, _, _, _, _, _⟩
  have hFlatten :
      flattenMachineBlocks cert.originalBlocks = source :=
    flatten_eq_of_parseExact hParse
  rw [← hFlatten]
  exact code_mem_flattenMachineBlocks hBlock hInstrBlock

theorem local_prim_ne_pc_of_check
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks)
    {offset : Nat} {op : PrimOp}
    (hLocal : LocalInstrAt block offset (.prim op)) :
    op ≠ .pc := by
  have hIndependent := (check_parts hCheck).2.2.1
  have hInstrNe :=
    instr_ne_pc_of_positionIndependent hIndependent
      (source_instr_mem_of_check hCheck hBlock hLocal)
  intro hEq
  apply hInstrNe
  simp [hEq]

theorem local_instr_ne_pushLabel_of_check
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks)
    {offset : Nat} {instr : Instr}
    (hLocal : LocalInstrAt block offset instr) :
    ∀ label, instr ≠ .pushLabel label := by
  have hIndependent := (check_parts hCheck).2.2.1
  exact
    instr_ne_pushLabel_of_positionIndependent hIndependent
      (source_instr_mem_of_check hCheck hBlock hLocal)

theorem local_instr_ne_jumpDynamic_of_check
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks)
    {offset : Nat}
    (hLocal : LocalInstrAt block offset .jumpDynamic) :
    False := by
  have hIndependent := (check_parts hCheck).2.2.1
  exact
    instr_ne_jumpDynamic_of_positionIndependent hIndependent
      (source_instr_mem_of_check hCheck hBlock hLocal) rfl

theorem jump_target_block_of_check
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks)
    {offset : Nat} {target : Label} {conditional : Bool}
    (hLocal :
      LocalInstrAt block offset
        (if conditional then .jumpi target else .jump target)) :
    ∃ targetBlock,
      targetBlock ∈ cert.originalBlocks ∧
        targetBlock.label = target := by
  have hInstrMem :=
    source_instr_mem_of_check hCheck hBlock hLocal
  have hTargetMem :
      target ∈
        (if conditional then Instr.jumpi target else Instr.jump target).targets := by
    cases conditional <;> simp [Instr.targets]
  rcases
      Program.target_resolves_of_accepted
        (source_accepted_of_check hCheck) hInstrMem hTargetMem with
    ⟨pc, hTargetPc⟩
  have hLabelMem : target ∈ source.labels := by
    by_contra hNotMem
    have hNone :=
      Program.labelPc_none_of_not_mem_labels source hNotMem
    rw [hTargetPc] at hNone
    contradiction
  exact original_block_of_label_mem_of_check hCheck hLabelMem

theorem instruction_lookup_rel_of_check
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks)
    {offset : Nat} {instr : Instr}
    (hLocal : LocalInstrAt block offset instr) :
    ∃ representative sourcePc optimizedPc,
      representative ∈ cert.optimizedBlocks ∧
      Program.instrAtPc source sourcePc = some (sourcePc, instr) ∧
      Program.instrAtPc cert.output optimizedPc =
        some (optimizedPc, rewriteMachineInstr cert.aliases instr) ∧
      AtOffset source block.label offset sourcePc ∧
      AtOffset cert.output (resolveAlias cert.aliases block.label)
        offset optimizedPc ∧
      PcRel source cert sourcePc optimizedPc := by
  rcases optimized_representative_of_check hCheck hBlock with
    ⟨representative, hRepresentative, hRepresentativeLabel,
      hRepresentativeCode⟩
  have hOptimizedLocal :=
    localInstrAt_rewrite hRepresentativeCode hLocal
  rcases List.mem_iff_append.mp hBlock with
    ⟨sourceBeforeBlocks, sourceAfterBlocks, hSourceBlocks⟩
  rcases List.mem_iff_append.mp hRepresentative with
    ⟨optimizedBeforeBlocks, optimizedAfterBlocks, hOptimizedBlocks⟩
  rcases hLocal with ⟨sourceBefore, sourceAfter, hSourceCode, hOffset⟩
  rcases hOptimizedLocal with
    ⟨optimizedBefore, optimizedAfter, hOptimizedCode, hOptimizedOffset⟩
  let sourcePreCode :=
    flattenMachineBlocks sourceBeforeBlocks ++
      [Instr.label block.label] ++ sourceBefore
  let optimizedPreCode :=
    flattenMachineBlocks optimizedBeforeBlocks ++
      [Instr.label representative.label] ++ optimizedBefore
  have hSourceLookup :
      Program.instrAtPc (flattenMachineBlocks cert.originalBlocks)
          sourcePreCode.byteLength =
        some (sourcePreCode.byteLength, instr) := by
    simpa [sourcePreCode] using
      instrAtPc_flattenMachineBlocks_of_decomposition
        hSourceBlocks hSourceCode
  have hOptimizedLookup :
      Program.instrAtPc (flattenMachineBlocks cert.optimizedBlocks)
          optimizedPreCode.byteLength =
        some
          (optimizedPreCode.byteLength,
            rewriteMachineInstr cert.aliases instr) := by
    simpa [optimizedPreCode] using
      instrAtPc_flattenMachineBlocks_of_decomposition
        hOptimizedBlocks hOptimizedCode
  rcases check_parts hCheck with
    ⟨hSourceAccepted, _, _, _, hParse, _, _, _, _, _, _, _, _, _, _⟩
  have hSourceFlatten :
      flattenMachineBlocks cert.originalBlocks = source :=
    flatten_eq_of_parseExact hParse
  have hOutputFlatten :
      flattenMachineBlocks cert.optimizedBlocks = cert.output :=
    output_eq_flatten_of_check hCheck
  rw [hSourceFlatten] at hSourceLookup
  rw [hOutputFlatten] at hOptimizedLookup
  have hSourceShape :
      source =
        flattenMachineBlocks sourceBeforeBlocks ++
          Instr.label block.label ::
            (block.code ++ flattenMachineBlocks sourceAfterBlocks) := by
    rw [← hSourceFlatten, hSourceBlocks,
      flattenMachineBlocks_append]
    simp [flattenMachineBlocks, List.append_assoc]
  have hOptimizedShape :
      cert.output =
        flattenMachineBlocks optimizedBeforeBlocks ++
          Instr.label representative.label ::
            (representative.code ++
              flattenMachineBlocks optimizedAfterBlocks) := by
    rw [← hOutputFlatten, hOptimizedBlocks,
      flattenMachineBlocks_append]
    simp [flattenMachineBlocks, List.append_assoc]
  have hSourceLabelsNodup : source.labels.Nodup :=
    Program.labels_nodup_of_accepted hSourceAccepted
  have hOutputLabelsNodup : cert.output.labels.Nodup :=
    Program.labels_nodup_of_accepted
      (output_accepted_of_check hCheck)
  have hSourceLabelPc :
      source.labelPc block.label =
        some (flattenMachineBlocks sourceBeforeBlocks).byteLength := by
    rw [hSourceShape]
    apply Program.labelPc_append_label_eq_of_labels_nodup
    simpa [← hSourceShape] using hSourceLabelsNodup
  have hOptimizedLabelPc :
      cert.output.labelPc representative.label =
        some (flattenMachineBlocks optimizedBeforeBlocks).byteLength := by
    rw [hOptimizedShape]
    apply Program.labelPc_append_label_eq_of_labels_nodup
    simpa [← hOptimizedShape] using hOutputLabelsNodup
  have hSourcePcEq :
      sourcePreCode.byteLength =
        (flattenMachineBlocks sourceBeforeBlocks).byteLength + offset := by
    simp [sourcePreCode, Program.byteLength_append,
      Program.byteLength_cons, hOffset, Nat.add_assoc]
  have hOptimizedPcEq :
      optimizedPreCode.byteLength =
        (flattenMachineBlocks optimizedBeforeBlocks).byteLength + offset := by
    simp [optimizedPreCode, Program.byteLength_append,
      Program.byteLength_cons, hOptimizedOffset, Nat.add_assoc]
  have hSourceAt :
      AtOffset source block.label offset sourcePreCode.byteLength :=
    ⟨(flattenMachineBlocks sourceBeforeBlocks).byteLength,
      hSourceLabelPc, hSourcePcEq⟩
  have hOptimizedAt :
      AtOffset cert.output (resolveAlias cert.aliases block.label)
        offset optimizedPreCode.byteLength :=
    ⟨(flattenMachineBlocks optimizedBeforeBlocks).byteLength,
      by simpa [← hRepresentativeLabel] using hOptimizedLabelPc,
      hOptimizedPcEq⟩
  exact
    ⟨representative, sourcePreCode.byteLength,
      optimizedPreCode.byteLength, hRepresentative,
      hSourceLookup, hOptimizedLookup, hSourceAt, hOptimizedAt,
      ⟨block, hBlock, offset, hSourceAt, hOptimizedAt⟩⟩

/--
The label instruction at the head of every source block is paired with the
label instruction at the head of its retained representative. This is the
missing entry/JUMPDEST cursor case complementing
`instruction_lookup_rel_of_check`.
-/
theorem label_lookup_rel_of_check
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks) :
    ∃ representative sourcePc optimizedPc,
      representative ∈ cert.optimizedBlocks ∧
      representative.label = resolveAlias cert.aliases block.label ∧
      Program.instrAtPc source sourcePc =
        some (sourcePc, .label block.label) ∧
      Program.instrAtPc cert.output optimizedPc =
        some (optimizedPc, .label representative.label) ∧
      AtOffset source block.label 0 sourcePc ∧
      AtOffset cert.output (resolveAlias cert.aliases block.label)
        0 optimizedPc ∧
      PcRel source cert sourcePc optimizedPc := by
  rcases optimized_representative_of_check hCheck hBlock with
    ⟨representative, hRepresentative, hRepresentativeLabel, _⟩
  rcases List.mem_iff_append.mp hBlock with
    ⟨sourceBeforeBlocks, sourceAfterBlocks, hSourceBlocks⟩
  rcases List.mem_iff_append.mp hRepresentative with
    ⟨optimizedBeforeBlocks, optimizedAfterBlocks, hOptimizedBlocks⟩
  let sourcePc := (flattenMachineBlocks sourceBeforeBlocks).byteLength
  let optimizedPc :=
    (flattenMachineBlocks optimizedBeforeBlocks).byteLength
  have hSourceLookup :
      Program.instrAtPc (flattenMachineBlocks cert.originalBlocks) sourcePc =
        some (sourcePc, .label block.label) := by
    rw [hSourceBlocks, flattenMachineBlocks_append]
    simpa [flattenMachineBlocks, Program.instrAtPc, sourcePc,
      List.append_assoc] using
      instrAtPcFrom_append_at_head
        (flattenMachineBlocks sourceBeforeBlocks)
        (.label block.label)
        (block.code ++ flattenMachineBlocks sourceAfterBlocks) 0
  have hOptimizedLookup :
      Program.instrAtPc (flattenMachineBlocks cert.optimizedBlocks)
          optimizedPc =
        some (optimizedPc, .label representative.label) := by
    rw [hOptimizedBlocks, flattenMachineBlocks_append]
    simpa [flattenMachineBlocks, Program.instrAtPc, optimizedPc,
      List.append_assoc] using
      instrAtPcFrom_append_at_head
        (flattenMachineBlocks optimizedBeforeBlocks)
        (.label representative.label)
        (representative.code ++
          flattenMachineBlocks optimizedAfterBlocks) 0
  rcases check_parts hCheck with
    ⟨hSourceAccepted, _, _, _, hParse, _, _, _, _, _, _, _, _, _, _⟩
  have hSourceFlatten :
      flattenMachineBlocks cert.originalBlocks = source :=
    flatten_eq_of_parseExact hParse
  have hOutputFlatten :
      flattenMachineBlocks cert.optimizedBlocks = cert.output :=
    output_eq_flatten_of_check hCheck
  rw [hSourceFlatten] at hSourceLookup
  rw [hOutputFlatten] at hOptimizedLookup
  have hSourceShape :
      source =
        flattenMachineBlocks sourceBeforeBlocks ++
          Instr.label block.label ::
            (block.code ++ flattenMachineBlocks sourceAfterBlocks) := by
    rw [← hSourceFlatten, hSourceBlocks, flattenMachineBlocks_append]
    simp [flattenMachineBlocks, List.append_assoc]
  have hOptimizedShape :
      cert.output =
        flattenMachineBlocks optimizedBeforeBlocks ++
          Instr.label representative.label ::
            (representative.code ++
              flattenMachineBlocks optimizedAfterBlocks) := by
    rw [← hOutputFlatten, hOptimizedBlocks, flattenMachineBlocks_append]
    simp [flattenMachineBlocks, List.append_assoc]
  have hSourceLabelPc :
      source.labelPc block.label = some sourcePc := by
    rw [hSourceShape]
    apply Program.labelPc_append_label_eq_of_labels_nodup
    simpa [← hSourceShape] using
      Program.labels_nodup_of_accepted hSourceAccepted
  have hOptimizedLabelPc :
      cert.output.labelPc representative.label = some optimizedPc := by
    rw [hOptimizedShape]
    apply Program.labelPc_append_label_eq_of_labels_nodup
    simpa [← hOptimizedShape] using
      Program.labels_nodup_of_accepted
        (output_accepted_of_check hCheck)
  have hSourceAt : AtOffset source block.label 0 sourcePc :=
    ⟨sourcePc, hSourceLabelPc, by simp⟩
  have hOptimizedAt :
      AtOffset cert.output (resolveAlias cert.aliases block.label)
        0 optimizedPc :=
    ⟨optimizedPc,
      by simpa [← hRepresentativeLabel] using hOptimizedLabelPc,
      by simp⟩
  exact
    ⟨representative, sourcePc, optimizedPc, hRepresentative,
      hRepresentativeLabel, hSourceLookup, hOptimizedLookup,
      hSourceAt, hOptimizedAt,
      ⟨block, hBlock, 0, hSourceAt, hOptimizedAt⟩⟩

/--
A bounded structural cursor. Unlike `PcRel`, every related PC is backed by an
actual instruction lookup and by either a block-head or local-instruction
witness.
-/
inductive CursorRel (source : Program) (cert : Cert) : Nat → Nat → Prop where
  | atLabel {block : MachineBlock} {sourcePc optimizedPc : Nat}
      (block_mem : block ∈ cert.originalBlocks)
      (source_lookup :
        Program.instrAtPc source sourcePc =
          some (sourcePc, .label block.label))
      (optimized_lookup :
        Program.instrAtPc cert.output optimizedPc =
          some
            (optimizedPc,
              .label (resolveAlias cert.aliases block.label)))
      (source_at :
        AtOffset source block.label 0 sourcePc)
      (optimized_at :
        AtOffset cert.output (resolveAlias cert.aliases block.label)
          0 optimizedPc) :
      CursorRel source cert sourcePc optimizedPc
  | atInstr {block : MachineBlock} {offset : Nat} {instr : Instr}
      {sourcePc optimizedPc : Nat}
      (block_mem : block ∈ cert.originalBlocks)
      (local_at : LocalInstrAt block offset instr)
      (source_lookup :
        Program.instrAtPc source sourcePc = some (sourcePc, instr))
      (optimized_lookup :
        Program.instrAtPc cert.output optimizedPc =
          some
            (optimizedPc, rewriteMachineInstr cert.aliases instr))
      (source_at :
        AtOffset source block.label offset sourcePc)
      (optimized_at :
        AtOffset cert.output (resolveAlias cert.aliases block.label)
          offset optimizedPc) :
      CursorRel source cert sourcePc optimizedPc

theorem cursorRel_atLabel_of_check
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks) :
    ∃ sourcePc optimizedPc,
      CursorRel source cert sourcePc optimizedPc := by
  rcases label_lookup_rel_of_check hCheck hBlock with
    ⟨representative, sourcePc, optimizedPc, _, hLabel,
      hSourceLookup, hOptimizedLookup, hSourceAt, hOptimizedAt, _⟩
  refine
    ⟨sourcePc, optimizedPc,
      .atLabel hBlock hSourceLookup ?_ hSourceAt hOptimizedAt⟩
  simpa [← hLabel] using hOptimizedLookup

theorem cursorRel_atInstr_of_check
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks)
    {offset : Nat} {instr : Instr}
    (hLocal : LocalInstrAt block offset instr) :
    ∃ sourcePc optimizedPc,
      CursorRel source cert sourcePc optimizedPc := by
  rcases instruction_lookup_rel_of_check hCheck hBlock hLocal with
    ⟨_, sourcePc, optimizedPc, _, hSourceLookup,
      hOptimizedLookup, hSourceAt, hOptimizedAt, _⟩
  exact
    ⟨sourcePc, optimizedPc,
      .atInstr hBlock hLocal hSourceLookup hOptimizedLookup
        hSourceAt hOptimizedAt⟩

theorem uint256_ofNat_toNat_of_instrAtPc
    {program : Program} (hFits : program.PCFits)
    {pc : Nat} {instr : Instr}
    (hLookup :
      Program.instrAtPc program pc = some (pc, instr)) :
    (EvmYul.UInt256.ofNat pc).toNat = pc := by
  apply Bytecode.uint256_ofNat_toNat_of_lt_size
  have hEnd := Program.instrAtPc_end_le_byteLength hLookup
  have hSize := hFits.byteLength_lt
  have hPositive := Instr.byteSize_pos instr
  omega

theorem localInstrAt_next_or_last
    {block : MachineBlock} {offset : Nat} {instr : Instr}
    (hLocal : LocalInstrAt block offset instr) :
    (∃ next,
      LocalInstrAt block (offset + instr.byteSize) next) ∨
      block.code.getLast? = some instr := by
  rcases hLocal with ⟨before, after, hCode, hOffset⟩
  cases after with
  | nil =>
      right
      simp [hCode]
  | cons next rest =>
      left
      refine ⟨next, before ++ [instr], rest, ?_, ?_⟩
      · simpa [List.append_assoc] using hCode
      · rw [hOffset, Program.byteLength_append]
        simp [Program.byteLength_cons, Nat.add_assoc]

theorem localInstrAt_next_of_not_closesBlock
    {block : MachineBlock} {offset : Nat} {instr : Instr}
    (hClosed : blockClosed? block = true)
    (hLocal : LocalInstrAt block offset instr)
    (hNotClosed : closesBlock instr = false) :
    ∃ next, LocalInstrAt block (offset + instr.byteSize) next := by
  rcases localInstrAt_next_or_last hLocal with hNext | hLast
  · exact hNext
  · simp [blockClosed?, hLast, hNotClosed] at hClosed

theorem firstLocalInstrAt_of_blockClosed
    {block : MachineBlock}
    (hClosed : blockClosed? block = true) :
    ∃ instr, LocalInstrAt block 1 instr := by
  cases hCode : block.code with
  | nil =>
      simp [blockClosed?, hCode] at hClosed
  | cons instr rest =>
      refine ⟨instr, [], rest, hCode, ?_⟩
      simp [Instr.byteSize]

theorem cursorRel_atInstr_of_atOffsets
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks)
    {offset : Nat} {instr : Instr}
    (hLocal : LocalInstrAt block offset instr)
    {sourcePc optimizedPc : Nat}
    (hSourceAt : AtOffset source block.label offset sourcePc)
    (hOptimizedAt :
      AtOffset cert.output (resolveAlias cert.aliases block.label)
        offset optimizedPc) :
    CursorRel source cert sourcePc optimizedPc := by
  rcases instruction_lookup_rel_of_check hCheck hBlock hLocal with
    ⟨_, foundSourcePc, foundOptimizedPc, _, hSourceLookup,
      hOptimizedLookup, hFoundSourceAt, hFoundOptimizedAt, _⟩
  rcases hSourceAt with ⟨sourceBase, hSourceBase, hSourcePc⟩
  rcases hFoundSourceAt with
    ⟨foundSourceBase, hFoundSourceBase, hFoundSourcePc⟩
  have hSourceBaseEq : foundSourceBase = sourceBase := by
    rw [hSourceBase] at hFoundSourceBase
    exact (Option.some.inj hFoundSourceBase).symm
  subst foundSourceBase
  rcases hOptimizedAt with
    ⟨optimizedBase, hOptimizedBase, hOptimizedPc⟩
  rcases hFoundOptimizedAt with
    ⟨foundOptimizedBase, hFoundOptimizedBase, hFoundOptimizedPc⟩
  have hOptimizedBaseEq : foundOptimizedBase = optimizedBase := by
    rw [hOptimizedBase] at hFoundOptimizedBase
    exact (Option.some.inj hFoundOptimizedBase).symm
  subst foundOptimizedBase
  subst sourcePc
  subst optimizedPc
  subst foundSourcePc
  subst foundOptimizedPc
  exact
    .atInstr hBlock hLocal hSourceLookup hOptimizedLookup
      ⟨sourceBase, hSourceBase, rfl⟩
      ⟨optimizedBase, hOptimizedBase, rfl⟩

theorem cursorRel_atLabel_of_labelPcs
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks)
    {sourcePc optimizedPc : Nat}
    (hSourcePc : source.labelPc block.label = some sourcePc)
    (hOptimizedPc :
      cert.output.labelPc (resolveAlias cert.aliases block.label) =
        some optimizedPc) :
    CursorRel source cert sourcePc optimizedPc := by
  rcases label_lookup_rel_of_check hCheck hBlock with
    ⟨representative, foundSourcePc, foundOptimizedPc, _,
      hRepresentativeLabel, hSourceLookup, hOptimizedLookup,
      hFoundSourceAt, hFoundOptimizedAt, _⟩
  rcases hFoundSourceAt with
    ⟨foundSourceBase, hFoundSourceBase, hFoundSourcePc⟩
  have hFoundSourceBase : foundSourceBase = sourcePc := by
    rw [hSourcePc] at hFoundSourceBase
    exact (Option.some.inj hFoundSourceBase).symm
  subst foundSourceBase
  rcases hFoundOptimizedAt with
    ⟨foundOptimizedBase, hFoundOptimizedBase, hFoundOptimizedPc⟩
  have hFoundOptimizedBase : foundOptimizedBase = optimizedPc := by
    rw [hOptimizedPc] at hFoundOptimizedBase
    exact (Option.some.inj hFoundOptimizedBase).symm
  subst foundOptimizedBase
  have hFoundSourcePcEq : foundSourcePc = sourcePc := by omega
  have hFoundOptimizedPcEq : foundOptimizedPc = optimizedPc := by omega
  subst foundSourcePc
  subst foundOptimizedPc
  refine
    .atLabel hBlock hSourceLookup ?_
      ⟨sourcePc, hSourcePc, by simp⟩
      ⟨optimizedPc, hOptimizedPc, by simp⟩
  simpa [← hRepresentativeLabel] using hOptimizedLookup

theorem cursorRel_first_of_label
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks)
    {sourcePc optimizedPc : Nat}
    (hSourceAt : AtOffset source block.label 0 sourcePc)
    (hOptimizedAt :
      AtOffset cert.output (resolveAlias cert.aliases block.label)
        0 optimizedPc) :
    CursorRel source cert (sourcePc + 1) (optimizedPc + 1) := by
  have hClosed := original_block_closed_of_check hCheck hBlock
  rcases firstLocalInstrAt_of_blockClosed hClosed with
    ⟨instr, hLocal⟩
  apply cursorRel_atInstr_of_atOffsets hCheck hBlock hLocal
  · rcases hSourceAt with ⟨base, hBase, hPc⟩
    exact ⟨base, hBase, by omega⟩
  · rcases hOptimizedAt with ⟨base, hBase, hPc⟩
    exact ⟨base, hBase, by omega⟩

theorem cursorRel_next_of_instr
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks)
    {offset : Nat} {instr next : Instr}
    (hNext :
      LocalInstrAt block (offset + instr.byteSize) next)
    {sourcePc optimizedPc : Nat}
    (hSourceAt : AtOffset source block.label offset sourcePc)
    (hOptimizedAt :
      AtOffset cert.output (resolveAlias cert.aliases block.label)
        offset optimizedPc) :
    CursorRel source cert
      (sourcePc + instr.byteSize)
      (optimizedPc + instr.byteSize) := by
  apply cursorRel_atInstr_of_atOffsets hCheck hBlock hNext
  · rcases hSourceAt with ⟨base, hBase, hPc⟩
    exact ⟨base, hBase, by omega⟩
  · rcases hOptimizedAt with ⟨base, hBase, hPc⟩
    exact ⟨base, hBase, by omega⟩

theorem Source.stepResult_eq_stepAtResult_of_lookup
    {program : Program} (hFits : program.PCFits)
    {state : EVMState} {pc : Nat} {instr : Instr}
    (hPc : state.pc = EvmYul.UInt256.ofNat pc)
    (hLookup :
      Program.instrAtPc program pc = some (pc, instr)) :
    Source.stepResult program state =
      Source.stepAtResult program pc instr state := by
  unfold Source.stepResult Source.stepResultWith
  rw [hPc, uint256_ofNat_toNat_of_instrAtPc hFits hLookup, hLookup]

theorem InteractionSemantics.Source.openStepResult_eq_openStepAtResult_of_lookup
    {program : Program} (hFits : program.PCFits)
    {state : EVMState} {pc : Nat} {instr : Instr}
    (hPc : state.pc = EvmYul.UInt256.ofNat pc)
    (hLookup :
      Program.instrAtPc program pc = some (pc, instr)) :
    InteractionSemantics.Source.openStepResult program state =
      InteractionSemantics.Source.openStepAtResult
        program pc instr state := by
  unfold InteractionSemantics.Source.openStepResult
    Source.stepResultWith
  rw [hPc, uint256_ofNat_toNat_of_instrAtPc hFits hLookup, hLookup]

theorem entry_cursorRel_of_check
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true) :
    CursorRel source cert 0 0 := by
  rcases check_parts hCheck with
    ⟨_, _, _, _, hParse, _, _, _, hNormalized, _, _, hEntryFirst,
      _, _, _⟩
  simp only [Bool.and_eq_true] at hEntryFirst
  have hOriginalFirst :
      entryFirst? entry cert.originalBlocks = true :=
    hEntryFirst.1
  have hOptimizedFirst :
      entryFirst? entry cert.optimizedBlocks = true :=
    hEntryFirst.2
  cases hBlocks : cert.originalBlocks with
  | nil =>
      simp [entryFirst?, hBlocks] at hOriginalFirst
  | cons first rest =>
      have hFirstLabel : first.label = entry := by
        simpa [entryFirst?, hBlocks] using hOriginalFirst
      have hFirstMem : first ∈ cert.originalBlocks := by
        simp [hBlocks]
      have hSourceLookup :
          Program.instrAtPc source 0 = some (0, .label entry) := by
        rw [← flatten_eq_of_parseExact hParse]
        exact instrAtPc_zero_of_entryFirst hOriginalFirst
      have hOptimizedLookup :
          Program.instrAtPc cert.output 0 = some (0, .label entry) := by
        rw [← output_eq_flatten_of_check hCheck]
        exact instrAtPc_zero_of_entryFirst hOptimizedFirst
      have hSourceAt : AtOffset source first.label 0 0 := by
        refine ⟨0, ?_, by simp⟩
        simpa [hFirstLabel] using
          (entry_labelPc_zero_of_check hCheck).1
      have hResolve :
          resolveAlias cert.aliases first.label = entry := by
        rw [hFirstLabel]
        exact resolveAlias_entry_of_normalized hNormalized
      have hOptimizedAt :
          AtOffset cert.output
            (resolveAlias cert.aliases first.label) 0 0 := by
        refine ⟨0, ?_, by simp⟩
        simpa [hResolve] using
          (entry_labelPc_zero_of_check hCheck).2
      apply CursorRel.atLabel hFirstMem
      · simpa [hFirstLabel] using hSourceLookup
      · simpa [hResolve] using hOptimizedLookup
      · exact hSourceAt
      · exact hOptimizedAt

def StateCursorRel (source : Program) (cert : Cert)
    (targetState sourceState : EVMState) : Prop :=
  SameRuntimeData targetState sourceState ∧
    ∃ sourcePc optimizedPc,
      sourceState.pc = EvmYul.UInt256.ofNat sourcePc ∧
        targetState.pc = EvmYul.UInt256.ofNat optimizedPc ∧
          CursorRel source cert sourcePc optimizedPc

def ExceptSameRuntimeData :
    Except EVMException EVMState → Except EVMException EVMState → Prop
  | .error targetError, .error sourceError => targetError = sourceError
  | .ok target, .ok source => SameRuntimeData target source
  | _, _ => False

theorem exceptSameRuntimeData_of_map_eraseRuntimeControl_eq
    {target source : Except EVMException EVMState}
    (h :
      target.map eraseRuntimeControl =
        source.map eraseRuntimeControl) :
    ExceptSameRuntimeData target source := by
  cases target with
  | error targetError =>
      cases source with
      | error sourceError =>
          simpa [Except.map, ExceptSameRuntimeData] using h
      | ok sourceState =>
          simp [Except.map] at h
  | ok targetState =>
      cases source with
      | error sourceError =>
          simp [Except.map] at h
      | ok sourceState =>
          simpa [Except.map, ExceptSameRuntimeData,
            SameRuntimeData] using h

theorem prim_step_exceptSameRuntimeData_of_ne_pc
    {op : PrimOp} {target source : EVMState}
    (hNoPc : op ≠ .pc)
    (hRel : SameRuntimeData target source) :
    ExceptSameRuntimeData (op.step target) (op.step source) := by
  by_cases hInvalid : op = .invalid
  · subst op
    simp [PrimOp.step, PrimOp.continuingStep?, PrimStep.run,
      ExceptSameRuntimeData]
  by_cases hArity : ∃ arity, op.stackArity? = some arity
  · by_cases hNoExternal : op.isExternalCallCreate = false
    · exact
        exceptSameRuntimeData_of_map_eraseRuntimeControl_eq
          (PrimOp.step_map_eraseRuntimeControl
            hArity hNoPc hNoExternal hRel)
    · have hExternal :
          op = .create ∨ op = .call ∨ op = .callcode ∨
            op = .delegatecall ∨ op = .create2 ∨ op = .staticcall := by
        cases op <;>
          simp [PrimOp.isExternalCallCreate] at hNoExternal ⊢
      rcases hExternal with
        hCreate | hCall | hCallcode | hDelegatecall | hCreate2 | hStaticcall
      all_goals
        subst op
        simp [PrimOp.step, PrimOp.continuingStep?, ExceptSameRuntimeData]
  · have hTerminal :
        op = .stop ∨ op = .return ∨ op = .revert ∨
          op = .selfdestruct := by
      cases op <;>
        simp [PrimOp.stackArity?] at hArity ⊢
    rcases hTerminal with hStop | hReturn | hRevert | hSelfdestruct
    · subst op
      exact
        exceptSameRuntimeData_of_map_eraseRuntimeControl_eq
          (PrimOp.terminal_step_map_eraseRuntimeControl .stop hRel)
    · subst op
      exact
        exceptSameRuntimeData_of_map_eraseRuntimeControl_eq
          (PrimOp.terminal_step_map_eraseRuntimeControl .return hRel)
    · subst op
      exact
        exceptSameRuntimeData_of_map_eraseRuntimeControl_eq
          (PrimOp.terminal_step_map_eraseRuntimeControl .revert hRel)
    · subst op
      exact
        exceptSameRuntimeData_of_map_eraseRuntimeControl_eq
          (PrimOp.terminal_step_map_eraseRuntimeControl .selfdestruct hRel)

theorem haltKind_output_eq_of_sameRuntimeData
    {kind : HaltKind} {target source : EVMState}
    (hRel : SameRuntimeData target source) :
    kind.output target = kind.output source := by
  have hShared : target.toSharedState = source.toSharedState :=
    SameRuntimeData.shared_eq hRel
  cases kind <;>
    simp [HaltKind.output, hShared]

theorem prim_step_pc_of_haltKind_none
    {op : PrimOp} {state final : EVMState}
    (hNoHalt : op.haltKind? = none)
    (hRun : op.step state = .ok final) :
    final.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  by_cases hArity : ∃ arity, op.stackArity? = some arity
  · rcases hArity with ⟨arity, hArity⟩
    exact PrimOp.step_pc_of_stackArity hArity hRun
  · have hTerminalOrInvalid :
        op = .stop ∨ op = .return ∨ op = .revert ∨
          op = .selfdestruct ∨ op = .invalid := by
      cases op <;>
        simp [PrimOp.stackArity?] at hArity ⊢
    rcases hTerminalOrInvalid with
      hStop | hReturn | hRevert | hSelfdestruct | hInvalid
    · subst op
      simp [PrimOp.haltKind?] at hNoHalt
    · subst op
      simp [PrimOp.haltKind?] at hNoHalt
    · subst op
      simp [PrimOp.haltKind?] at hNoHalt
    · subst op
      simp [PrimOp.haltKind?] at hNoHalt
    · subst op
      simp [PrimOp.step, PrimOp.continuingStep?, PrimStep.run] at hRun

theorem closesBlock_prim_eq_false_of_haltKind_none_of_step_ok
    {op : PrimOp} {state final : EVMState}
    (hNoHalt : op.haltKind? = none)
    (hRun : op.step state = .ok final) :
    closesBlock (.prim op) = false := by
  cases op <;>
    simp [PrimOp.haltKind?, closesBlock] at hNoHalt ⊢
  case invalid =>
    simp [PrimOp.step, PrimOp.continuingStep?, PrimStep.run] at hRun

theorem runtimeStateRel_of_exceptSameRuntimeData
    {optimized source : Except EVMException EVMState}
    (hRel : ExceptSameRuntimeData optimized source) :
    InteractionPreservation.PrimOp.RuntimeStateRel optimized source := by
  cases optimized with
  | error optimizedError =>
      cases source with
      | error sourceError =>
          exact .error hRel
      | ok sourceState =>
          exact False.elim hRel
  | ok optimizedState =>
      cases source with
      | error sourceError =>
          exact False.elim hRel
      | ok sourceState =>
          exact .ok hRel

theorem stepAt_jump_rel
    {source optimized : Program}
    {sourceTarget optimizedTarget : Label}
    {sourceDest optimizedDest sourcePc optimizedPc : Nat}
    {sourceState optimizedState : EVMState}
    (hSourceDest :
      source.labelPc sourceTarget = some sourceDest)
    (hOptimizedDest :
      optimized.labelPc optimizedTarget = some optimizedDest)
    (hRel : SameRuntimeData optimizedState sourceState) :
    ExceptSameRuntimeData
      (Source.stepAt optimized optimizedPc (.jump optimizedTarget)
        optimizedState)
      (Source.stepAt source sourcePc (.jump sourceTarget) sourceState) := by
  simp [Source.stepAt, hSourceDest, hOptimizedDest, ExceptSameRuntimeData]
  exact
    SameRuntimeData.trans
      (SameRuntimeData.jumpPc optimizedDest optimizedState)
      (SameRuntimeData.trans hRel
        (SameRuntimeData.symm
          (SameRuntimeData.jumpPc sourceDest sourceState)))

theorem openStepAt_jump_rel
    {source optimized : Program}
    {sourceTarget optimizedTarget : Label}
    {sourceDest optimizedDest sourcePc optimizedPc : Nat}
    {sourceState optimizedState : EVMState}
    (hSourceDest :
      source.labelPc sourceTarget = some sourceDest)
    (hOptimizedDest :
      optimized.labelPc optimizedTarget = some optimizedDest)
    (hRel : SameRuntimeData optimizedState sourceState) :
    Simulation.Interaction.Rel
      InteractionPreservation.PrimOp.RuntimeStateRel
      (InteractionSemantics.Source.openStepAt optimized optimizedPc
        (.jump optimizedTarget) optimizedState)
      (InteractionSemantics.Source.openStepAt source sourcePc
        (.jump sourceTarget) sourceState) := by
  apply Simulation.Interaction.Rel.done
  exact
    runtimeStateRel_of_exceptSameRuntimeData
      (stepAt_jump_rel hSourceDest hOptimizedDest hRel)

theorem stepAt_jumpi_rel
    {source optimized : Program}
    {sourceTarget optimizedTarget : Label}
    {sourceDest optimizedDest sourcePc optimizedPc : Nat}
    {sourceState optimizedState : EVMState}
    (hSourceDest :
      source.labelPc sourceTarget = some sourceDest)
    (hOptimizedDest :
      optimized.labelPc optimizedTarget = some optimizedDest)
    (hRel : SameRuntimeData optimizedState sourceState) :
    ExceptSameRuntimeData
      (Source.stepAt optimized optimizedPc (.jumpi optimizedTarget)
        optimizedState)
      (Source.stepAt source sourcePc (.jumpi sourceTarget) sourceState) := by
  have hStackEq : optimizedState.stack = sourceState.stack :=
    SameRuntimeData.stack_eq hRel
  simp only [Source.stepAt, hSourceDest, hOptimizedDest,
    Option.elim_some]
  rw [hStackEq]
  cases hPop : sourceState.stack.pop with
  | none =>
      simp [hPop, ExceptSameRuntimeData]
  | some pair =>
      rcases pair with ⟨stack, cond⟩
      let optimizedNextPc : Word :=
        if cond != EvmYul.UInt256.ofNat 0 then
          EvmYul.UInt256.ofNat optimizedDest
        else
          Source.jumpiFallthroughPc optimizedState
      let sourceNextPc : Word :=
        if cond != EvmYul.UInt256.ofNat 0 then
          EvmYul.UInt256.ofNat sourceDest
        else
          Source.jumpiFallthroughPc sourceState
      have hStackRel :
          SameRuntimeData
            { optimizedState with stack := stack }
            { sourceState with stack := stack } :=
        SameRuntimeData.replaceStack
          (targetStack := stack) (sourceStack := stack) hRel rfl
      have hFinal :
          SameRuntimeData
            { optimizedState with pc := optimizedNextPc, stack := stack }
            { sourceState with pc := sourceNextPc, stack := stack } :=
        SameRuntimeData.with_pc_left optimizedNextPc
          (SameRuntimeData.with_pc_right sourceNextPc hStackRel)
      simpa [hPop, ExceptSameRuntimeData, optimizedNextPc,
        sourceNextPc] using hFinal

theorem openStepAt_jumpi_rel
    {source optimized : Program}
    {sourceTarget optimizedTarget : Label}
    {sourceDest optimizedDest sourcePc optimizedPc : Nat}
    {sourceState optimizedState : EVMState}
    (hSourceDest :
      source.labelPc sourceTarget = some sourceDest)
    (hOptimizedDest :
      optimized.labelPc optimizedTarget = some optimizedDest)
    (hRel : SameRuntimeData optimizedState sourceState) :
    Simulation.Interaction.Rel
      InteractionPreservation.PrimOp.RuntimeStateRel
      (InteractionSemantics.Source.openStepAt optimized optimizedPc
        (.jumpi optimizedTarget) optimizedState)
      (InteractionSemantics.Source.openStepAt source sourcePc
        (.jumpi sourceTarget) sourceState) := by
  apply Simulation.Interaction.Rel.done
  exact
    runtimeStateRel_of_exceptSameRuntimeData
      (stepAt_jumpi_rel hSourceDest hOptimizedDest hRel)

theorem aliased_jump_step_rel_of_check
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {targetBlock : MachineBlock}
    (hTarget : targetBlock ∈ cert.originalBlocks)
    {sourceState optimizedState : EVMState}
    (hStateRel : SameRuntimeData optimizedState sourceState)
    (sourcePc optimizedPc : Nat) :
    ∃ sourceDest optimizedDest,
      source.labelPc targetBlock.label = some sourceDest ∧
      cert.output.labelPc
          (resolveAlias cert.aliases targetBlock.label) =
        some optimizedDest ∧
      ExceptSameRuntimeData
        (Source.stepAt cert.output optimizedPc
          (.jump (resolveAlias cert.aliases targetBlock.label))
          optimizedState)
        (Source.stepAt source sourcePc (.jump targetBlock.label)
          sourceState) := by
  rcases source_label_resolves_of_check hCheck hTarget with
    ⟨sourceDest, hSourceDest⟩
  rcases output_label_resolves_of_check hCheck hTarget with
    ⟨optimizedDest, hOptimizedDest⟩
  exact
    ⟨sourceDest, optimizedDest, hSourceDest, hOptimizedDest,
      stepAt_jump_rel hSourceDest hOptimizedDest hStateRel⟩

theorem aliased_jumpi_step_rel_of_check
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {targetBlock : MachineBlock}
    (hTarget : targetBlock ∈ cert.originalBlocks)
    {sourceState optimizedState : EVMState}
    (hStateRel : SameRuntimeData optimizedState sourceState)
    (sourcePc optimizedPc : Nat) :
    ∃ sourceDest optimizedDest,
      source.labelPc targetBlock.label = some sourceDest ∧
      cert.output.labelPc
          (resolveAlias cert.aliases targetBlock.label) =
        some optimizedDest ∧
      ExceptSameRuntimeData
        (Source.stepAt cert.output optimizedPc
          (.jumpi (resolveAlias cert.aliases targetBlock.label))
          optimizedState)
        (Source.stepAt source sourcePc (.jumpi targetBlock.label)
          sourceState) := by
  rcases source_label_resolves_of_check hCheck hTarget with
    ⟨sourceDest, hSourceDest⟩
  rcases output_label_resolves_of_check hCheck hTarget with
    ⟨optimizedDest, hOptimizedDest⟩
  exact
    ⟨sourceDest, optimizedDest, hSourceDest, hOptimizedDest,
      stepAt_jumpi_rel hSourceDest hOptimizedDest hStateRel⟩

/--
The existing owner-level open primitive congruence discharges every primitive
inside corresponding blocks. The remaining open-run lift is therefore a
control/stack-label problem, not a primitive-semantics problem.
-/
theorem open_primitive_step_rel
    {op : PrimOp} {optimizedState sourceState : EVMState}
    (hNoPc : op ≠ .pc)
    (hRel : SameRuntimeData optimizedState sourceState) :
    Simulation.Interaction.Rel
      InteractionPreservation.PrimOp.RuntimeStateRel
      (InteractionSemantics.PrimOp.openStep op optimizedState)
      (InteractionSemantics.PrimOp.openStep op sourceState) :=
  InteractionPreservation.PrimOp.openStep_runtimeRel_of_ne_pc hNoPc hRel

theorem openStepAt_prim_rel
    {source optimized : Program} {sourcePc optimizedPc : Nat}
    {op : PrimOp} {optimizedState sourceState : EVMState}
    (hNoPc : op ≠ .pc)
    (hRel : SameRuntimeData optimizedState sourceState) :
    Simulation.Interaction.Rel
      InteractionPreservation.PrimOp.RuntimeStateRel
      (InteractionSemantics.Source.openStepAt optimized optimizedPc
        (.prim op) optimizedState)
      (InteractionSemantics.Source.openStepAt source sourcePc
        (.prim op) sourceState) := by
  simpa [InteractionSemantics.Source.openStepAt] using
    open_primitive_step_rel hNoPc hRel

/--
Initialize a source-level Assembly run at a program's own physical entry
address. The default is relevant only for malformed programs; checked rounds
retain the entry in both programs.
-/
def entryState (entry : Label) (program : Program)
    (state : EVMState) : EVMState :=
  { state with
    pc := EvmYul.UInt256.ofNat ((program.labelPc entry).getD 0) }

theorem checked_entryState_eq
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    (state : EVMState) :
    entryState entry cert.output state =
      entryState entry source state := by
  rcases entry_labelPc_zero_of_check hCheck with
    ⟨hSourceEntry, hOutputEntry⟩
  simp [entryState, hSourceEntry, hOutputEntry]

theorem checked_entryState_stateCursorRel
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    (state : EVMState) :
    StateCursorRel source cert
      (entryState entry cert.output state)
      (entryState entry source state) := by
  rcases entry_labelPc_zero_of_check hCheck with
    ⟨hSourceEntry, hOutputEntry⟩
  have hStateEq := checked_entryState_eq hCheck state
  refine
    ⟨hStateEq ▸ SameRuntimeData.refl
        (entryState entry source state),
      0, 0, ?_, ?_, entry_cursorRel_of_check hCheck⟩
  · simp [entryState, hSourceEntry]
  · simp [entryState, hOutputEntry]

def HaltRuntimeRel (target source : Halt) : Prop :=
  target.kind = source.kind ∧
    SameRuntimeData target.state source.state ∧
      target.output = source.output

def StepResultRuntimeRel (target source : StepResult) : Prop :=
  match target, source with
  | .running targetState, .running sourceState =>
      SameRuntimeData targetState sourceState
  | .halted targetHalt, .halted sourceHalt =>
      HaltRuntimeRel targetHalt sourceHalt
  | _, _ => False

def ExceptStepResultRuntimeRel :
    Except EVMException StepResult →
      Except EVMException StepResult → Prop :=
  Simulation.Interaction.ExceptRel (fun target source => target = source)
    StepResultRuntimeRel

theorem HaltRuntimeRel.refl (halt : Halt) :
    HaltRuntimeRel halt halt :=
  ⟨rfl, SameRuntimeData.refl _, rfl⟩

theorem HaltRuntimeRel.trans
    {first second third : Halt}
    (hFirst : HaltRuntimeRel first second)
    (hSecond : HaltRuntimeRel second third) :
    HaltRuntimeRel first third :=
  ⟨hFirst.1.trans hSecond.1,
    SameRuntimeData.trans hFirst.2.1 hSecond.2.1,
    hFirst.2.2.trans hSecond.2.2⟩

theorem StepResultRuntimeRel.refl (result : StepResult) :
    StepResultRuntimeRel result result := by
  cases result with
  | running state =>
      exact SameRuntimeData.refl state
  | halted halt =>
      exact HaltRuntimeRel.refl halt

theorem StepResultRuntimeRel.trans
    {first second third : StepResult}
    (hFirst : StepResultRuntimeRel first second)
    (hSecond : StepResultRuntimeRel second third) :
    StepResultRuntimeRel first third := by
  cases first <;> cases second <;> cases third <;>
    simp only [StepResultRuntimeRel] at hFirst hSecond ⊢
  · exact SameRuntimeData.trans hFirst hSecond
  · exact HaltRuntimeRel.trans hFirst hSecond

theorem ExceptStepResultRuntimeRel.refl
    (result : Except EVMException StepResult) :
    ExceptStepResultRuntimeRel result result := by
  cases result with
  | error error =>
      exact .error rfl
  | ok result =>
      exact .ok (StepResultRuntimeRel.refl result)

theorem ExceptStepResultRuntimeRel.trans
    {first second third : Except EVMException StepResult}
    (hFirst : ExceptStepResultRuntimeRel first second)
    (hSecond : ExceptStepResultRuntimeRel second third) :
    ExceptStepResultRuntimeRel first third := by
  cases hFirst with
  | error hFirstError =>
      cases hSecond with
      | error hSecondError =>
          exact .error (hFirstError.trans hSecondError)
  | ok hFirstResult =>
      cases hSecond with
      | ok hSecondResult =>
          exact .ok
            (StepResultRuntimeRel.trans hFirstResult hSecondResult)

/--
Closed result semantics of two programs started at their respective physical
entry PCs. Running checkpoints compare runtime data but intentionally abstract
from layout-dependent PCs; terminal results additionally agree on halt kind
and output.
-/
def ClosedEntryRunResultRel (entry : Label)
    (source target : Program) : Prop :=
  ∀ fuel state,
    ExceptStepResultRuntimeRel
      (Source.runNResult target fuel (entryState entry target state))
      (Source.runNResult source fuel (entryState entry source state))

/--
Open-world counterpart of `ClosedEntryRunResultRel`. Structural interaction
relatedness requires the same external requests and relates every shared-answer
continuation with the same result relation.
-/
def OpenEntryRunResultRel (entry : Label)
    (source target : Program) : Prop :=
  ∀ fuel state,
    Simulation.Interaction.Rel ExceptStepResultRuntimeRel
      (InteractionSemantics.Source.openRunNResult target fuel
        (entryState entry target state))
      (InteractionSemantics.Source.openRunNResult source fuel
        (entryState entry source state))

def EntryRunResultRel (entry : Label)
    (source target : Program) : Prop :=
  ClosedEntryRunResultRel entry source target ∧
    OpenEntryRunResultRel entry source target

theorem ClosedEntryRunResultRel.refl
    (entry : Label) (program : Program) :
    ClosedEntryRunResultRel entry program program := by
  intro fuel state
  exact ExceptStepResultRuntimeRel.refl _

theorem ClosedEntryRunResultRel.trans
    {entry : Label} {first second third : Program}
    (hFirst : ClosedEntryRunResultRel entry first second)
    (hSecond : ClosedEntryRunResultRel entry second third) :
    ClosedEntryRunResultRel entry first third := by
  intro fuel state
  exact
    ExceptStepResultRuntimeRel.trans
      (hSecond fuel state) (hFirst fuel state)

theorem OpenEntryRunResultRel.refl
    (entry : Label) (program : Program) :
    OpenEntryRunResultRel entry program program := by
  intro fuel state
  exact
    Simulation.Interaction.Rel.refl
      ExceptStepResultRuntimeRel.refl _

theorem OpenEntryRunResultRel.trans
    {entry : Label} {first second third : Program}
    (hFirst : OpenEntryRunResultRel entry first second)
    (hSecond : OpenEntryRunResultRel entry second third) :
    OpenEntryRunResultRel entry first third := by
  intro fuel state
  apply Simulation.Interaction.Rel.mono
    (Simulation.Interaction.Rel.trans
      (hSecond fuel state) (hFirst fuel state))
  intro thirdDone firstDone hDone
  rcases hDone with ⟨secondDone, hThirdSecond, hSecondFirst⟩
  exact
    ExceptStepResultRuntimeRel.trans hThirdSecond hSecondFirst

theorem EntryRunResultRel.refl
    (entry : Label) (program : Program) :
    EntryRunResultRel entry program program :=
  ⟨ClosedEntryRunResultRel.refl entry program,
    OpenEntryRunResultRel.refl entry program⟩

theorem EntryRunResultRel.trans
    {entry : Label} {first second third : Program}
    (hFirst : EntryRunResultRel entry first second)
    (hSecond : EntryRunResultRel entry second third) :
    EntryRunResultRel entry first third :=
  ⟨ClosedEntryRunResultRel.trans hFirst.1 hSecond.1,
    OpenEntryRunResultRel.trans hFirst.2 hSecond.2⟩

/--
Strong one-round result relation used internally while fuel remains. Running
states retain the certificate-specific cursor invariant; halted states expose
only the public runtime observation.
-/
def StepResultRelWith
    (stateRel : EVMState → EVMState → Prop)
    (target source : StepResult) : Prop :=
  match target, source with
  | .running targetState, .running sourceState =>
      stateRel targetState sourceState
  | .halted targetHalt, .halted sourceHalt =>
      HaltRuntimeRel targetHalt sourceHalt
  | _, _ => False

def ExceptStepResultRelWith
    (stateRel : EVMState → EVMState → Prop) :
    Except EVMException StepResult →
      Except EVMException StepResult → Prop :=
  Simulation.Interaction.ExceptRel (fun target source => target = source)
    (StepResultRelWith stateRel)

theorem checked_closed_label_step
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks)
    {sourcePc optimizedPc : Nat}
    {sourceState optimizedState : EVMState}
    (hRuntime : SameRuntimeData optimizedState sourceState)
    (hSourcePc :
      sourceState.pc = EvmYul.UInt256.ofNat sourcePc)
    (hOptimizedPc :
      optimizedState.pc = EvmYul.UInt256.ofNat optimizedPc)
    (hSourceLookup :
      Program.instrAtPc source sourcePc =
        some (sourcePc, .label block.label))
    (hOptimizedLookup :
      Program.instrAtPc cert.output optimizedPc =
        some
          (optimizedPc,
            .label (resolveAlias cert.aliases block.label)))
    (hSourceAt : AtOffset source block.label 0 sourcePc)
    (hOptimizedAt :
      AtOffset cert.output (resolveAlias cert.aliases block.label)
        0 optimizedPc) :
    ExceptStepResultRelWith (StateCursorRel source cert)
      (Source.stepResult cert.output optimizedState)
      (Source.stepResult source sourceState) := by
  rw [Source.stepResult_eq_stepAtResult_of_lookup
      (pc_fits_of_check hCheck).1 hSourcePc hSourceLookup,
    Source.stepResult_eq_stepAtResult_of_lookup
      (pc_fits_of_check hCheck).2 hOptimizedPc hOptimizedLookup]
  apply Simulation.Interaction.ExceptRel.ok
  simp only [Source.stepAtResult, Source.stepAt, Target.stepInstr,
    Target.stepInstrWith, Bind.bind, Except.bind, Instr.haltKind?,
    StepResultRelWith]
  constructor
  · exact
      SameRuntimeData.incrPC_left
        (SameRuntimeData.incrPC_right hRuntime)
  · refine
      ⟨sourcePc + 1, optimizedPc + 1, ?_, ?_,
        cursorRel_first_of_label hCheck hBlock
          hSourceAt hOptimizedAt⟩
    · simp [EvmYul.EVM.State.incrPC, hSourcePc,
        UInt256_ofNat_add]
    · simp [EvmYul.EVM.State.incrPC, hOptimizedPc,
        UInt256_ofNat_add]

theorem checked_closed_push_step
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks)
    {offset : Nat} {value : Word}
    (hLocal : LocalInstrAt block offset (.push value))
    {sourcePc optimizedPc : Nat}
    {sourceState optimizedState : EVMState}
    (hRuntime : SameRuntimeData optimizedState sourceState)
    (hSourcePc :
      sourceState.pc = EvmYul.UInt256.ofNat sourcePc)
    (hOptimizedPc :
      optimizedState.pc = EvmYul.UInt256.ofNat optimizedPc)
    (hSourceLookup :
      Program.instrAtPc source sourcePc =
        some (sourcePc, .push value))
    (hOptimizedLookup :
      Program.instrAtPc cert.output optimizedPc =
        some (optimizedPc, .push value))
    (hSourceAt : AtOffset source block.label offset sourcePc)
    (hOptimizedAt :
      AtOffset cert.output (resolveAlias cert.aliases block.label)
        offset optimizedPc) :
    ExceptStepResultRelWith (StateCursorRel source cert)
      (Source.stepResult cert.output optimizedState)
      (Source.stepResult source sourceState) := by
  have hNext :=
    localInstrAt_next_of_not_closesBlock
      (original_block_closed_of_check hCheck hBlock)
      hLocal (by simp [closesBlock])
  rcases hNext with ⟨next, hNext⟩
  rw [Source.stepResult_eq_stepAtResult_of_lookup
      (pc_fits_of_check hCheck).1 hSourcePc hSourceLookup,
    Source.stepResult_eq_stepAtResult_of_lookup
      (pc_fits_of_check hCheck).2 hOptimizedPc hOptimizedLookup]
  apply Simulation.Interaction.ExceptRel.ok
  simp only [Source.stepAtResult, Source.stepAt, Target.stepInstr,
    Target.stepInstrWith, Target.stepPushWith, Bind.bind, Except.bind,
    Instr.haltKind?, StepResultRelWith]
  constructor
  · apply SameRuntimeData.replaceStackAndIncrPC hRuntime
    simpa using congrArg (fun stack => stack.push value)
      (SameRuntimeData.stack_eq hRuntime)
  · refine
      ⟨sourcePc + (Instr.push value).byteSize,
        optimizedPc + (Instr.push value).byteSize, ?_, ?_,
        cursorRel_next_of_instr hCheck hBlock hNext
          hSourceAt hOptimizedAt⟩
    · simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, hSourcePc,
        UInt256_ofNat_add, Instr.byteSize, Instr.push32Size]
    · simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, hOptimizedPc,
        UInt256_ofNat_add, Instr.byteSize, Instr.push32Size]

theorem checked_closed_prim_step
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks)
    {offset : Nat} {op : PrimOp}
    (hLocal : LocalInstrAt block offset (.prim op))
    {sourcePc optimizedPc : Nat}
    {sourceState optimizedState : EVMState}
    (hRuntime : SameRuntimeData optimizedState sourceState)
    (hSourcePc :
      sourceState.pc = EvmYul.UInt256.ofNat sourcePc)
    (hOptimizedPc :
      optimizedState.pc = EvmYul.UInt256.ofNat optimizedPc)
    (hSourceLookup :
      Program.instrAtPc source sourcePc =
        some (sourcePc, .prim op))
    (hOptimizedLookup :
      Program.instrAtPc cert.output optimizedPc =
        some (optimizedPc, .prim op))
    (hSourceAt : AtOffset source block.label offset sourcePc)
    (hOptimizedAt :
      AtOffset cert.output (resolveAlias cert.aliases block.label)
        offset optimizedPc) :
    ExceptStepResultRelWith (StateCursorRel source cert)
      (Source.stepResult cert.output optimizedState)
      (Source.stepResult source sourceState) := by
  have hNoPc := local_prim_ne_pc_of_check hCheck hBlock hLocal
  have hStepRel :=
    prim_step_exceptSameRuntimeData_of_ne_pc hNoPc hRuntime
  rw [Source.stepResult_eq_stepAtResult_of_lookup
      (pc_fits_of_check hCheck).1 hSourcePc hSourceLookup,
    Source.stepResult_eq_stepAtResult_of_lookup
      (pc_fits_of_check hCheck).2 hOptimizedPc hOptimizedLookup]
  simp only [Source.stepAtResult, Source.stepAt,
    Target.stepInstr_prim]
  cases hOptimizedStep : op.step optimizedState with
  | error optimizedError =>
      cases hSourceStep : op.step sourceState with
      | error sourceError =>
          have hError : optimizedError = sourceError := by
            simpa [hOptimizedStep, hSourceStep,
              ExceptSameRuntimeData] using hStepRel
          exact .error hError
      | ok sourceFinal =>
          simp [hOptimizedStep, hSourceStep,
            ExceptSameRuntimeData] at hStepRel
  | ok optimizedFinal =>
      cases hSourceStep : op.step sourceState with
      | error sourceError =>
          simp [hOptimizedStep, hSourceStep,
            ExceptSameRuntimeData] at hStepRel
      | ok sourceFinal =>
          have hFinalRuntime :
              SameRuntimeData optimizedFinal sourceFinal := by
            simpa [hOptimizedStep, hSourceStep,
              ExceptSameRuntimeData] using hStepRel
          cases hHalt : op.haltKind? with
          | some kind =>
              simp only [hOptimizedStep, hSourceStep, Except.bind,
                Instr.haltKind?, hHalt]
              apply Simulation.Interaction.ExceptRel.ok
              exact
                ⟨rfl, hFinalRuntime,
                  haltKind_output_eq_of_sameRuntimeData hFinalRuntime⟩
          | none =>
              have hNotClosed :
                  closesBlock (.prim op) = false :=
                closesBlock_prim_eq_false_of_haltKind_none_of_step_ok
                  hHalt hSourceStep
              rcases
                  localInstrAt_next_of_not_closesBlock
                    (original_block_closed_of_check hCheck hBlock)
                    hLocal hNotClosed with
                ⟨next, hNext⟩
              have hOptimizedFinalPc :=
                prim_step_pc_of_haltKind_none hHalt hOptimizedStep
              have hSourceFinalPc :=
                prim_step_pc_of_haltKind_none hHalt hSourceStep
              simp only [hOptimizedStep, hSourceStep, Except.bind,
                Instr.haltKind?, hHalt]
              apply Simulation.Interaction.ExceptRel.ok
              refine
                ⟨hFinalRuntime,
                  sourcePc + (Instr.prim op).byteSize,
                  optimizedPc + (Instr.prim op).byteSize,
                  ?_, ?_,
                  cursorRel_next_of_instr hCheck hBlock hNext
                    hSourceAt hOptimizedAt⟩
              · rw [hSourceFinalPc, hSourcePc,
                  UInt256_ofNat_add]
                rfl
              · rw [hOptimizedFinalPc, hOptimizedPc,
                  UInt256_ofNat_add]
                rfl

theorem checked_open_prim_step
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks)
    {offset : Nat} {op : PrimOp}
    (hLocal : LocalInstrAt block offset (.prim op))
    {sourcePc optimizedPc : Nat}
    {sourceState optimizedState : EVMState}
    (hRuntime : SameRuntimeData optimizedState sourceState)
    (hSourcePc :
      sourceState.pc = EvmYul.UInt256.ofNat sourcePc)
    (hOptimizedPc :
      optimizedState.pc = EvmYul.UInt256.ofNat optimizedPc)
    (hSourceLookup :
      Program.instrAtPc source sourcePc =
        some (sourcePc, .prim op))
    (hOptimizedLookup :
      Program.instrAtPc cert.output optimizedPc =
        some (optimizedPc, .prim op))
    (hSourceAt : AtOffset source block.label offset sourcePc)
    (hOptimizedAt :
      AtOffset cert.output (resolveAlias cert.aliases block.label)
        offset optimizedPc) :
    Simulation.Interaction.Rel
      (ExceptStepResultRelWith (StateCursorRel source cert))
      (InteractionSemantics.Source.openStepResult
        cert.output optimizedState)
      (InteractionSemantics.Source.openStepResult
        source sourceState) := by
  rw [
    InteractionSemantics.Source.openStepResult_eq_openStepAtResult_of_lookup
      (pc_fits_of_check hCheck).2 hOptimizedPc hOptimizedLookup,
    InteractionSemantics.Source.openStepResult_eq_openStepAtResult_of_lookup
      (pc_fits_of_check hCheck).1 hSourcePc hSourceLookup]
  unfold InteractionSemantics.Source.openStepAtResult
    InteractionSemantics.Source.openStepAt
  have hNoPc := local_prim_ne_pc_of_check hCheck hBlock hLocal
  by_cases hArity : ∃ arity, op.stackArity? = some arity
  · rcases hArity with ⟨⟨input, output⟩, hArity⟩
    have hKind : op.haltKind? = none := by
      cases op <;>
        simp [PrimOp.stackArity?, PrimOp.haltKind?] at hArity ⊢
    by_cases hInvalid : op = .invalid
    · subst op
      have hTargetInvalid :
          InteractionSemantics.PrimOp.openStep .invalid optimizedState =
            .done (.error
              EvmYul.EVM.ExecutionException.InvalidInstruction) := by
        rw [InteractionSemantics.PrimOp.openStep_closed
          (by rfl) (by simp) (by simp)]
        rfl
      have hSourceInvalid :
          InteractionSemantics.PrimOp.openStep .invalid sourceState =
            .done (.error
              EvmYul.EVM.ExecutionException.InvalidInstruction) := by
        rw [InteractionSemantics.PrimOp.openStep_closed
          (by rfl) (by simp) (by simp)]
        rfl
      simp only [InteractionSemantics.Source.openStepAt,
        Instr.haltKind?, PrimOp.haltKind?]
      rw [hTargetInvalid, hSourceInvalid]
      exact .done (.error rfl)
    have hBase :=
      open_primitive_step_rel (op := op) hNoPc hRuntime
    have hTargetAdvance :=
      InteractionPreservation.PrimOp.openStep_advancesPC
        (state := optimizedState) hArity
    have hSourceAdvance :=
      InteractionPreservation.PrimOp.openStep_advancesPC
        (state := sourceState) hArity
    have hTargetStrong :=
      Simulation.Interaction.Rel.strengthen_left
        hBase hTargetAdvance
    have hBoth :=
      Simulation.Interaction.Rel.strengthen_right
        hTargetStrong hSourceAdvance
    have hEnriched :
        Simulation.Interaction.Rel
          (Simulation.Interaction.ExceptRel
            (fun targetError sourceError : EVMException =>
              targetError = sourceError)
            (fun targetFinal sourceFinal =>
              SameRuntimeData targetFinal sourceFinal ∧
                targetFinal.pc =
                  optimizedState.pc + EvmYul.UInt256.ofNat 1 ∧
                sourceFinal.pc =
                  sourceState.pc + EvmYul.UInt256.ofNat 1))
          (InteractionSemantics.PrimOp.openStep op optimizedState)
          (InteractionSemantics.PrimOp.openStep op sourceState) := by
      apply Simulation.Interaction.Rel.mono hBoth
      intro targetDone sourceDone hDone
      rcases hDone with ⟨⟨hRelated, hTargetPc⟩, hSourcePcDone⟩
      cases hRelated with
      | error hError =>
          exact .error hError
      | ok hFinal =>
          exact .ok ⟨hFinal, hTargetPc, hSourcePcDone⟩
    apply Simulation.Interaction.Rel.bind hEnriched
    intro targetFinal sourceFinal hFinal
    simp only [Instr.haltKind?, hKind]
    apply Simulation.Interaction.Rel.done
    apply Simulation.Interaction.ExceptRel.ok
    change StateCursorRel source cert targetFinal sourceFinal
    refine ⟨hFinal.1, sourcePc + 1, optimizedPc + 1, ?_, ?_, ?_⟩
    · rw [hFinal.2.2, hSourcePc, UInt256_ofNat_add]
    · rw [hFinal.2.1, hOptimizedPc, UInt256_ofNat_add]
    · have hNotClosed : closesBlock (.prim op) = false := by
        cases op <;>
          simp [closesBlock, PrimOp.haltKind?] at hKind hInvalid ⊢
      rcases
          localInstrAt_next_of_not_closesBlock
            (original_block_closed_of_check hCheck hBlock)
            hLocal hNotClosed with
        ⟨next, hNext⟩
      simpa [Instr.byteSize] using
        cursorRel_next_of_instr hCheck hBlock hNext
          hSourceAt hOptimizedAt
  · have hTerminal :
        ∃ kind : HaltKind, op = kind.toPrimOp := by
      have hCases :
          op = .stop ∨ op = .return ∨ op = .revert ∨
            op = .selfdestruct := by
        cases op <;> simp [PrimOp.stackArity?] at hArity ⊢
      rcases hCases with hStop | hReturn | hRevert | hSelfdestruct
      · exact ⟨.stop, hStop⟩
      · exact ⟨.return, hReturn⟩
      · exact ⟨.revert, hRevert⟩
      · exact ⟨.selfdestruct, hSelfdestruct⟩
    rcases hTerminal with ⟨kind, rfl⟩
    have hTerminalRel :=
      open_primitive_step_rel
        (op := kind.toPrimOp)
        (by cases kind <;> simp [HaltKind.toPrimOp])
        hRuntime
    apply Simulation.Interaction.Rel.bind hTerminalRel
    intro targetFinal sourceFinal hFinal
    have hKind :
        kind.toPrimOp.haltKind? = some kind := by
      cases kind <;> rfl
    simp only [Instr.haltKind?, hKind]
    apply Simulation.Interaction.Rel.done
    apply Simulation.Interaction.ExceptRel.ok
    exact
      ⟨rfl, hFinal,
        haltKind_output_eq_of_sameRuntimeData hFinal⟩

theorem checked_open_label_step
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks)
    {sourcePc optimizedPc : Nat}
    {sourceState optimizedState : EVMState}
    (hRuntime : SameRuntimeData optimizedState sourceState)
    (hSourcePc :
      sourceState.pc = EvmYul.UInt256.ofNat sourcePc)
    (hOptimizedPc :
      optimizedState.pc = EvmYul.UInt256.ofNat optimizedPc)
    (hSourceLookup :
      Program.instrAtPc source sourcePc =
        some (sourcePc, .label block.label))
    (hOptimizedLookup :
      Program.instrAtPc cert.output optimizedPc =
        some
          (optimizedPc,
            .label (resolveAlias cert.aliases block.label)))
    (hSourceAt : AtOffset source block.label 0 sourcePc)
    (hOptimizedAt :
      AtOffset cert.output (resolveAlias cert.aliases block.label)
        0 optimizedPc) :
    Simulation.Interaction.Rel
      (ExceptStepResultRelWith (StateCursorRel source cert))
      (InteractionSemantics.Source.openStepResult
        cert.output optimizedState)
      (InteractionSemantics.Source.openStepResult
        source sourceState) := by
  have hClosed :=
    checked_closed_label_step hCheck hBlock hRuntime
      hSourcePc hOptimizedPc hSourceLookup hOptimizedLookup
      hSourceAt hOptimizedAt
  rw [Source.stepResult_eq_stepAtResult_of_lookup
      (pc_fits_of_check hCheck).1 hSourcePc hSourceLookup,
    Source.stepResult_eq_stepAtResult_of_lookup
      (pc_fits_of_check hCheck).2 hOptimizedPc hOptimizedLookup] at hClosed
  rw [
    InteractionSemantics.Source.openStepResult_eq_openStepAtResult_of_lookup
      (pc_fits_of_check hCheck).2 hOptimizedPc hOptimizedLookup,
    InteractionSemantics.Source.openStepResult_eq_openStepAtResult_of_lookup
      (pc_fits_of_check hCheck).1 hSourcePc hSourceLookup]
  exact .done hClosed

theorem checked_closed_local_label_step
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks)
    {offset : Nat} {label : Label}
    (hLocal : LocalInstrAt block offset (.label label))
    {sourcePc optimizedPc : Nat}
    {sourceState optimizedState : EVMState}
    (hRuntime : SameRuntimeData optimizedState sourceState)
    (hSourcePc :
      sourceState.pc = EvmYul.UInt256.ofNat sourcePc)
    (hOptimizedPc :
      optimizedState.pc = EvmYul.UInt256.ofNat optimizedPc)
    (hSourceLookup :
      Program.instrAtPc source sourcePc =
        some (sourcePc, .label label))
    (hOptimizedLookup :
      Program.instrAtPc cert.output optimizedPc =
        some (optimizedPc, .label label))
    (hSourceAt : AtOffset source block.label offset sourcePc)
    (hOptimizedAt :
      AtOffset cert.output (resolveAlias cert.aliases block.label)
        offset optimizedPc) :
    ExceptStepResultRelWith (StateCursorRel source cert)
      (Source.stepResult cert.output optimizedState)
      (Source.stepResult source sourceState) := by
  rcases
      localInstrAt_next_of_not_closesBlock
        (original_block_closed_of_check hCheck hBlock)
        hLocal (by simp [closesBlock]) with
    ⟨next, hNext⟩
  rw [Source.stepResult_eq_stepAtResult_of_lookup
      (pc_fits_of_check hCheck).1 hSourcePc hSourceLookup,
    Source.stepResult_eq_stepAtResult_of_lookup
      (pc_fits_of_check hCheck).2 hOptimizedPc hOptimizedLookup]
  apply Simulation.Interaction.ExceptRel.ok
  simp only [Source.stepAtResult, Source.stepAt, Target.stepInstr,
    Target.stepInstrWith, Bind.bind, Except.bind, Instr.haltKind?,
    StepResultRelWith]
  refine
    ⟨SameRuntimeData.incrPC_left
        (SameRuntimeData.incrPC_right hRuntime),
      sourcePc + 1, optimizedPc + 1, ?_, ?_,
      ?_⟩
  · simp [EvmYul.EVM.State.incrPC, hSourcePc,
      UInt256_ofNat_add]
  · simp [EvmYul.EVM.State.incrPC, hOptimizedPc,
      UInt256_ofNat_add]
  · simpa [Instr.byteSize] using
      cursorRel_next_of_instr hCheck hBlock hNext
        hSourceAt hOptimizedAt

theorem checked_open_local_label_step
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks)
    {offset : Nat} {label : Label}
    (hLocal : LocalInstrAt block offset (.label label))
    {sourcePc optimizedPc : Nat}
    {sourceState optimizedState : EVMState}
    (hRuntime : SameRuntimeData optimizedState sourceState)
    (hSourcePc :
      sourceState.pc = EvmYul.UInt256.ofNat sourcePc)
    (hOptimizedPc :
      optimizedState.pc = EvmYul.UInt256.ofNat optimizedPc)
    (hSourceLookup :
      Program.instrAtPc source sourcePc =
        some (sourcePc, .label label))
    (hOptimizedLookup :
      Program.instrAtPc cert.output optimizedPc =
        some (optimizedPc, .label label))
    (hSourceAt : AtOffset source block.label offset sourcePc)
    (hOptimizedAt :
      AtOffset cert.output (resolveAlias cert.aliases block.label)
        offset optimizedPc) :
    Simulation.Interaction.Rel
      (ExceptStepResultRelWith (StateCursorRel source cert))
      (InteractionSemantics.Source.openStepResult
        cert.output optimizedState)
      (InteractionSemantics.Source.openStepResult
        source sourceState) := by
  have hClosed :=
    checked_closed_local_label_step hCheck hBlock hLocal hRuntime
      hSourcePc hOptimizedPc hSourceLookup hOptimizedLookup
      hSourceAt hOptimizedAt
  rw [Source.stepResult_eq_stepAtResult_of_lookup
      (pc_fits_of_check hCheck).1 hSourcePc hSourceLookup,
    Source.stepResult_eq_stepAtResult_of_lookup
      (pc_fits_of_check hCheck).2 hOptimizedPc hOptimizedLookup] at hClosed
  rw [
    InteractionSemantics.Source.openStepResult_eq_openStepAtResult_of_lookup
      (pc_fits_of_check hCheck).2 hOptimizedPc hOptimizedLookup,
    InteractionSemantics.Source.openStepResult_eq_openStepAtResult_of_lookup
      (pc_fits_of_check hCheck).1 hSourcePc hSourceLookup]
  exact .done hClosed

theorem checked_open_push_step
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks)
    {offset : Nat} {value : Word}
    (hLocal : LocalInstrAt block offset (.push value))
    {sourcePc optimizedPc : Nat}
    {sourceState optimizedState : EVMState}
    (hRuntime : SameRuntimeData optimizedState sourceState)
    (hSourcePc :
      sourceState.pc = EvmYul.UInt256.ofNat sourcePc)
    (hOptimizedPc :
      optimizedState.pc = EvmYul.UInt256.ofNat optimizedPc)
    (hSourceLookup :
      Program.instrAtPc source sourcePc =
        some (sourcePc, .push value))
    (hOptimizedLookup :
      Program.instrAtPc cert.output optimizedPc =
        some (optimizedPc, .push value))
    (hSourceAt : AtOffset source block.label offset sourcePc)
    (hOptimizedAt :
      AtOffset cert.output (resolveAlias cert.aliases block.label)
        offset optimizedPc) :
    Simulation.Interaction.Rel
      (ExceptStepResultRelWith (StateCursorRel source cert))
      (InteractionSemantics.Source.openStepResult
        cert.output optimizedState)
      (InteractionSemantics.Source.openStepResult
        source sourceState) := by
  have hClosed :=
    checked_closed_push_step hCheck hBlock hLocal hRuntime
      hSourcePc hOptimizedPc hSourceLookup hOptimizedLookup
      hSourceAt hOptimizedAt
  rw [Source.stepResult_eq_stepAtResult_of_lookup
      (pc_fits_of_check hCheck).1 hSourcePc hSourceLookup,
    Source.stepResult_eq_stepAtResult_of_lookup
      (pc_fits_of_check hCheck).2 hOptimizedPc hOptimizedLookup] at hClosed
  rw [
    InteractionSemantics.Source.openStepResult_eq_openStepAtResult_of_lookup
      (pc_fits_of_check hCheck).2 hOptimizedPc hOptimizedLookup,
    InteractionSemantics.Source.openStepResult_eq_openStepAtResult_of_lookup
      (pc_fits_of_check hCheck).1 hSourcePc hSourceLookup]
  exact .done hClosed

theorem checked_closed_jump_step
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks)
    {offset : Nat} {target : Label}
    (hLocal : LocalInstrAt block offset (.jump target))
    {sourcePc optimizedPc : Nat}
    {sourceState optimizedState : EVMState}
    (hRuntime : SameRuntimeData optimizedState sourceState)
    (hSourcePc :
      sourceState.pc = EvmYul.UInt256.ofNat sourcePc)
    (hOptimizedPc :
      optimizedState.pc = EvmYul.UInt256.ofNat optimizedPc)
    (hSourceLookup :
      Program.instrAtPc source sourcePc =
        some (sourcePc, .jump target))
    (hOptimizedLookup :
      Program.instrAtPc cert.output optimizedPc =
        some
          (optimizedPc,
            .jump (resolveAlias cert.aliases target))) :
    ExceptStepResultRelWith (StateCursorRel source cert)
      (Source.stepResult cert.output optimizedState)
      (Source.stepResult source sourceState) := by
  rcases
      jump_target_block_of_check
        (conditional := false) hCheck hBlock (by simpa using hLocal) with
    ⟨targetBlock, hTargetBlock, hTargetLabel⟩
  rcases source_label_resolves_of_check hCheck hTargetBlock with
    ⟨sourceDest, hSourceDest⟩
  rcases output_label_resolves_of_check hCheck hTargetBlock with
    ⟨optimizedDest, hOptimizedDest⟩
  have hTargetResolve :
      resolveAlias cert.aliases targetBlock.label =
        resolveAlias cert.aliases target := by
    rw [hTargetLabel]
  have hSourceDestTarget :
      source.labelPc target = some sourceDest := by
    simpa [hTargetLabel] using hSourceDest
  have hOptimizedDestTarget :
      cert.output.labelPc (resolveAlias cert.aliases target) =
        some optimizedDest := by
    simpa [hTargetResolve] using hOptimizedDest
  have hJumpRuntime :
      SameRuntimeData
        (Source.jumpPc optimizedDest optimizedState)
        (Source.jumpPc sourceDest sourceState) := by
    exact
      SameRuntimeData.trans
        (SameRuntimeData.jumpPc optimizedDest optimizedState)
        (SameRuntimeData.trans hRuntime
          (SameRuntimeData.symm
            (SameRuntimeData.jumpPc sourceDest sourceState)))
  rw [Source.stepResult_eq_stepAtResult_of_lookup
      (pc_fits_of_check hCheck).1 hSourcePc hSourceLookup,
    Source.stepResult_eq_stepAtResult_of_lookup
      (pc_fits_of_check hCheck).2 hOptimizedPc hOptimizedLookup]
  simp only [Source.stepAtResult, Source.stepAt, hSourceDestTarget,
    hOptimizedDestTarget, Option.elim_some,
    Instr.haltKind?, Bind.bind, Except.bind]
  apply Simulation.Interaction.ExceptRel.ok
  exact
    ⟨hJumpRuntime, sourceDest, optimizedDest, rfl, rfl,
      cursorRel_atLabel_of_labelPcs hCheck hTargetBlock
        hSourceDest hOptimizedDest⟩

theorem checked_open_jump_step
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks)
    {offset : Nat} {target : Label}
    (hLocal : LocalInstrAt block offset (.jump target))
    {sourcePc optimizedPc : Nat}
    {sourceState optimizedState : EVMState}
    (hRuntime : SameRuntimeData optimizedState sourceState)
    (hSourcePc :
      sourceState.pc = EvmYul.UInt256.ofNat sourcePc)
    (hOptimizedPc :
      optimizedState.pc = EvmYul.UInt256.ofNat optimizedPc)
    (hSourceLookup :
      Program.instrAtPc source sourcePc =
        some (sourcePc, .jump target))
    (hOptimizedLookup :
      Program.instrAtPc cert.output optimizedPc =
        some
          (optimizedPc,
            .jump (resolveAlias cert.aliases target))) :
    Simulation.Interaction.Rel
      (ExceptStepResultRelWith (StateCursorRel source cert))
      (InteractionSemantics.Source.openStepResult
        cert.output optimizedState)
      (InteractionSemantics.Source.openStepResult
        source sourceState) := by
  have hClosed :=
    checked_closed_jump_step hCheck hBlock hLocal hRuntime
      hSourcePc hOptimizedPc hSourceLookup hOptimizedLookup
  rcases
      jump_target_block_of_check
        (conditional := false) hCheck hBlock (by simpa using hLocal) with
    ⟨targetBlock, hTargetBlock, hTargetLabel⟩
  rcases source_label_resolves_of_check hCheck hTargetBlock with
    ⟨sourceDest, hSourceDest⟩
  rcases output_label_resolves_of_check hCheck hTargetBlock with
    ⟨optimizedDest, hOptimizedDest⟩
  have hSourceDestTarget :
      source.labelPc target = some sourceDest := by
    simpa [hTargetLabel] using hSourceDest
  have hOptimizedDestTarget :
      cert.output.labelPc (resolveAlias cert.aliases target) =
        some optimizedDest := by
    simpa [hTargetLabel] using hOptimizedDest
  rw [Source.stepResult_eq_stepAtResult_of_lookup
      (pc_fits_of_check hCheck).1 hSourcePc hSourceLookup,
    Source.stepResult_eq_stepAtResult_of_lookup
      (pc_fits_of_check hCheck).2 hOptimizedPc hOptimizedLookup] at hClosed
  rw [
    InteractionSemantics.Source.openStepResult_eq_openStepAtResult_of_lookup
      (pc_fits_of_check hCheck).2 hOptimizedPc hOptimizedLookup,
    InteractionSemantics.Source.openStepResult_eq_openStepAtResult_of_lookup
      (pc_fits_of_check hCheck).1 hSourcePc hSourceLookup]
  simpa [InteractionSemantics.Source.openStepAtResult,
    InteractionSemantics.Source.openStepAt,
    Simulation.Interaction.bind, Simulation.Interaction.pure,
    Source.stepAtResult, Source.stepAt,
    hSourceDestTarget, hOptimizedDestTarget] using
    (Simulation.Interaction.Rel.done hClosed)

theorem checked_closed_jumpi_step
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks)
    {offset : Nat} {target : Label}
    (hLocal : LocalInstrAt block offset (.jumpi target))
    {sourcePc optimizedPc : Nat}
    {sourceState optimizedState : EVMState}
    (hRuntime : SameRuntimeData optimizedState sourceState)
    (hSourcePc :
      sourceState.pc = EvmYul.UInt256.ofNat sourcePc)
    (hOptimizedPc :
      optimizedState.pc = EvmYul.UInt256.ofNat optimizedPc)
    (hSourceLookup :
      Program.instrAtPc source sourcePc =
        some (sourcePc, .jumpi target))
    (hOptimizedLookup :
      Program.instrAtPc cert.output optimizedPc =
        some
          (optimizedPc,
            .jumpi (resolveAlias cert.aliases target)))
    (hSourceAt : AtOffset source block.label offset sourcePc)
    (hOptimizedAt :
      AtOffset cert.output (resolveAlias cert.aliases block.label)
        offset optimizedPc) :
    ExceptStepResultRelWith (StateCursorRel source cert)
      (Source.stepResult cert.output optimizedState)
      (Source.stepResult source sourceState) := by
  rcases
      jump_target_block_of_check
        (conditional := true) hCheck hBlock (by simpa using hLocal) with
    ⟨targetBlock, hTargetBlock, hTargetLabel⟩
  rcases source_label_resolves_of_check hCheck hTargetBlock with
    ⟨sourceDest, hSourceDest⟩
  rcases output_label_resolves_of_check hCheck hTargetBlock with
    ⟨optimizedDest, hOptimizedDest⟩
  have hSourceDestTarget :
      source.labelPc target = some sourceDest := by
    simpa [hTargetLabel] using hSourceDest
  have hOptimizedDestTarget :
      cert.output.labelPc (resolveAlias cert.aliases target) =
        some optimizedDest := by
    simpa [hTargetLabel] using hOptimizedDest
  have hStackEq : optimizedState.stack = sourceState.stack :=
    SameRuntimeData.stack_eq hRuntime
  have hNext :=
    localInstrAt_next_of_not_closesBlock
      (original_block_closed_of_check hCheck hBlock)
      hLocal (by simp [closesBlock])
  rcases hNext with ⟨next, hNext⟩
  rw [Source.stepResult_eq_stepAtResult_of_lookup
      (pc_fits_of_check hCheck).1 hSourcePc hSourceLookup,
    Source.stepResult_eq_stepAtResult_of_lookup
      (pc_fits_of_check hCheck).2 hOptimizedPc hOptimizedLookup]
  simp only [Source.stepAtResult, Source.stepAt,
    hSourceDestTarget, hOptimizedDestTarget, Option.elim_some]
  rw [hStackEq]
  cases hPop : sourceState.stack.pop with
  | none =>
      exact .error rfl
  | some pair =>
      rcases pair with ⟨stack, cond⟩
      have hStackRuntime :
          SameRuntimeData
            { optimizedState with stack := stack }
            { sourceState with stack := stack } :=
        SameRuntimeData.replaceStack hRuntime rfl
      by_cases hCond : cond != EvmYul.UInt256.ofNat 0
      · have hFinalRuntime :
            SameRuntimeData
              { optimizedState with
                pc := EvmYul.UInt256.ofNat optimizedDest
                stack := stack }
              { sourceState with
                pc := EvmYul.UInt256.ofNat sourceDest
                stack := stack } :=
          SameRuntimeData.with_pc_left
            (EvmYul.UInt256.ofNat optimizedDest)
            (SameRuntimeData.with_pc_right
              (EvmYul.UInt256.ofNat sourceDest) hStackRuntime)
        simp only [hPop, hCond, if_pos, Instr.haltKind?,
          Bind.bind, Except.bind]
        apply Simulation.Interaction.ExceptRel.ok
        exact
          ⟨hFinalRuntime, sourceDest, optimizedDest, rfl, rfl,
            cursorRel_atLabel_of_labelPcs hCheck hTargetBlock
              hSourceDest hOptimizedDest⟩
      · have hFinalRuntime :
            SameRuntimeData
              { optimizedState with
                pc := Source.jumpiFallthroughPc optimizedState
                stack := stack }
              { sourceState with
                pc := Source.jumpiFallthroughPc sourceState
                stack := stack } :=
          SameRuntimeData.with_pc_left
            (Source.jumpiFallthroughPc optimizedState)
            (SameRuntimeData.with_pc_right
              (Source.jumpiFallthroughPc sourceState) hStackRuntime)
        simp only [hPop, hCond, if_neg, Instr.haltKind?,
          Bind.bind, Except.bind]
        apply Simulation.Interaction.ExceptRel.ok
        refine
          ⟨hFinalRuntime,
            sourcePc + (Instr.jumpi target).byteSize,
            optimizedPc + (Instr.jumpi target).byteSize,
            ?_, ?_,
            cursorRel_next_of_instr hCheck hBlock hNext
              hSourceAt hOptimizedAt⟩
        · simp [Source.jumpiFallthroughPc, hSourcePc,
            UInt256_ofNat_add, Instr.byteSize, Instr.jumpSize,
            Instr.push32Size, Nat.add_assoc]
        · simp [Source.jumpiFallthroughPc, hOptimizedPc,
            UInt256_ofNat_add, Instr.byteSize, Instr.jumpSize,
            Instr.push32Size, Nat.add_assoc]

theorem checked_open_jumpi_step
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {block : MachineBlock} (hBlock : block ∈ cert.originalBlocks)
    {offset : Nat} {target : Label}
    (hLocal : LocalInstrAt block offset (.jumpi target))
    {sourcePc optimizedPc : Nat}
    {sourceState optimizedState : EVMState}
    (hRuntime : SameRuntimeData optimizedState sourceState)
    (hSourcePc :
      sourceState.pc = EvmYul.UInt256.ofNat sourcePc)
    (hOptimizedPc :
      optimizedState.pc = EvmYul.UInt256.ofNat optimizedPc)
    (hSourceLookup :
      Program.instrAtPc source sourcePc =
        some (sourcePc, .jumpi target))
    (hOptimizedLookup :
      Program.instrAtPc cert.output optimizedPc =
        some
          (optimizedPc,
            .jumpi (resolveAlias cert.aliases target)))
    (hSourceAt : AtOffset source block.label offset sourcePc)
    (hOptimizedAt :
      AtOffset cert.output (resolveAlias cert.aliases block.label)
        offset optimizedPc) :
    Simulation.Interaction.Rel
      (ExceptStepResultRelWith (StateCursorRel source cert))
      (InteractionSemantics.Source.openStepResult
        cert.output optimizedState)
      (InteractionSemantics.Source.openStepResult
        source sourceState) := by
  have hClosed :=
    checked_closed_jumpi_step hCheck hBlock hLocal hRuntime
      hSourcePc hOptimizedPc hSourceLookup hOptimizedLookup
      hSourceAt hOptimizedAt
  rcases
      jump_target_block_of_check
        (conditional := true) hCheck hBlock (by simpa using hLocal) with
    ⟨targetBlock, hTargetBlock, hTargetLabel⟩
  rcases source_label_resolves_of_check hCheck hTargetBlock with
    ⟨sourceDest, hSourceDest⟩
  rcases output_label_resolves_of_check hCheck hTargetBlock with
    ⟨optimizedDest, hOptimizedDest⟩
  have hSourceDestTarget :
      source.labelPc target = some sourceDest := by
    simpa [hTargetLabel] using hSourceDest
  have hOptimizedDestTarget :
      cert.output.labelPc (resolveAlias cert.aliases target) =
        some optimizedDest := by
    simpa [hTargetLabel] using hOptimizedDest
  rw [Source.stepResult_eq_stepAtResult_of_lookup
      (pc_fits_of_check hCheck).1 hSourcePc hSourceLookup,
    Source.stepResult_eq_stepAtResult_of_lookup
      (pc_fits_of_check hCheck).2 hOptimizedPc hOptimizedLookup] at hClosed
  rw [
    InteractionSemantics.Source.openStepResult_eq_openStepAtResult_of_lookup
      (pc_fits_of_check hCheck).2 hOptimizedPc hOptimizedLookup,
    InteractionSemantics.Source.openStepResult_eq_openStepAtResult_of_lookup
      (pc_fits_of_check hCheck).1 hSourcePc hSourceLookup]
  have hStackEq : optimizedState.stack = sourceState.stack :=
    SameRuntimeData.stack_eq hRuntime
  cases hPop : sourceState.stack.pop with
  | none =>
      simpa [InteractionSemantics.Source.openStepAtResult,
        InteractionSemantics.Source.openStepAt,
        Simulation.Interaction.bind, Simulation.Interaction.pure,
        Source.stepAtResult, Source.stepAt,
        hSourceDestTarget, hOptimizedDestTarget,
        hStackEq, hPop] using
        (Simulation.Interaction.Rel.done hClosed)
  | some pair =>
      simpa [InteractionSemantics.Source.openStepAtResult,
        InteractionSemantics.Source.openStepAt,
        Simulation.Interaction.bind, Simulation.Interaction.pure,
        Source.stepAtResult, Source.stepAt,
        hSourceDestTarget, hOptimizedDestTarget,
        hStackEq, hPop] using
        (Simulation.Interaction.Rel.done hClosed)

theorem checked_closed_step
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {optimizedState sourceState : EVMState}
    (hState :
      StateCursorRel source cert optimizedState sourceState) :
    ExceptStepResultRelWith (StateCursorRel source cert)
      (Source.stepResult cert.output optimizedState)
      (Source.stepResult source sourceState) := by
  rcases hState with
    ⟨hRuntime, sourcePc, optimizedPc,
      hSourcePc, hOptimizedPc, hCursor⟩
  cases hCursor with
  | atLabel hBlock hSourceLookup hOptimizedLookup
      hSourceAt hOptimizedAt =>
      exact
        checked_closed_label_step hCheck hBlock hRuntime
          hSourcePc hOptimizedPc hSourceLookup hOptimizedLookup
          hSourceAt hOptimizedAt
  | @atInstr block offset instr _ _ hBlock hLocal
      hSourceLookup hOptimizedLookup hSourceAt hOptimizedAt =>
      cases instr with
      | prim op =>
          exact
            checked_closed_prim_step hCheck hBlock hLocal hRuntime
              hSourcePc hOptimizedPc hSourceLookup
              (by simpa [rewriteMachineInstr] using hOptimizedLookup)
              hSourceAt hOptimizedAt
      | push value =>
          exact
            checked_closed_push_step hCheck hBlock hLocal hRuntime
              hSourcePc hOptimizedPc hSourceLookup
              (by simpa [rewriteMachineInstr] using hOptimizedLookup)
              hSourceAt hOptimizedAt
      | pushLabel label =>
          exact False.elim
            (local_instr_ne_pushLabel_of_check
              hCheck hBlock hLocal label rfl)
      | label label =>
          exact
            checked_closed_local_label_step hCheck hBlock hLocal hRuntime
              hSourcePc hOptimizedPc hSourceLookup
              (by simpa [rewriteMachineInstr] using hOptimizedLookup)
              hSourceAt hOptimizedAt
      | jump target =>
          exact
            checked_closed_jump_step hCheck hBlock hLocal hRuntime
              hSourcePc hOptimizedPc hSourceLookup
              (by simpa [rewriteMachineInstr] using hOptimizedLookup)
      | jumpi target =>
          exact
            checked_closed_jumpi_step hCheck hBlock hLocal hRuntime
              hSourcePc hOptimizedPc hSourceLookup
              (by simpa [rewriteMachineInstr] using hOptimizedLookup)
              hSourceAt hOptimizedAt
      | jumpDynamic =>
          exact False.elim
            (local_instr_ne_jumpDynamic_of_check hCheck hBlock hLocal)

theorem checked_open_step
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true)
    {optimizedState sourceState : EVMState}
    (hState :
      StateCursorRel source cert optimizedState sourceState) :
    Simulation.Interaction.Rel
      (ExceptStepResultRelWith (StateCursorRel source cert))
      (InteractionSemantics.Source.openStepResult
        cert.output optimizedState)
      (InteractionSemantics.Source.openStepResult
        source sourceState) := by
  rcases hState with
    ⟨hRuntime, sourcePc, optimizedPc,
      hSourcePc, hOptimizedPc, hCursor⟩
  cases hCursor with
  | atLabel hBlock hSourceLookup hOptimizedLookup
      hSourceAt hOptimizedAt =>
      exact
        checked_open_label_step hCheck hBlock hRuntime
          hSourcePc hOptimizedPc hSourceLookup hOptimizedLookup
          hSourceAt hOptimizedAt
  | @atInstr block offset instr _ _ hBlock hLocal
      hSourceLookup hOptimizedLookup hSourceAt hOptimizedAt =>
      cases instr with
      | prim op =>
          exact
            checked_open_prim_step hCheck hBlock hLocal hRuntime
              hSourcePc hOptimizedPc hSourceLookup
              (by simpa [rewriteMachineInstr] using hOptimizedLookup)
              hSourceAt hOptimizedAt
      | push value =>
          exact
            checked_open_push_step hCheck hBlock hLocal hRuntime
              hSourcePc hOptimizedPc hSourceLookup
              (by simpa [rewriteMachineInstr] using hOptimizedLookup)
              hSourceAt hOptimizedAt
      | pushLabel label =>
          exact False.elim
            (local_instr_ne_pushLabel_of_check
              hCheck hBlock hLocal label rfl)
      | label label =>
          exact
            checked_open_local_label_step hCheck hBlock hLocal hRuntime
              hSourcePc hOptimizedPc hSourceLookup
              (by simpa [rewriteMachineInstr] using hOptimizedLookup)
              hSourceAt hOptimizedAt
      | jump target =>
          exact
            checked_open_jump_step hCheck hBlock hLocal hRuntime
              hSourcePc hOptimizedPc hSourceLookup
              (by simpa [rewriteMachineInstr] using hOptimizedLookup)
      | jumpi target =>
          exact
            checked_open_jumpi_step hCheck hBlock hLocal hRuntime
              hSourcePc hOptimizedPc hSourceLookup
              (by simpa [rewriteMachineInstr] using hOptimizedLookup)
              hSourceAt hOptimizedAt
      | jumpDynamic =>
          exact False.elim
            (local_instr_ne_jumpDynamic_of_check hCheck hBlock hLocal)

/--
Public interface between the local cursor proof and whole-run preservation.
The cursor relation is deliberately certificate-specific and need not be
transitive across rounds.
-/
structure RoundStepSimulation (entry : Label)
    (source target : Program) where
  stateRel : EVMState → EVMState → Prop
  initial :
    ∀ state,
      stateRel (entryState entry target state)
        (entryState entry source state)
  runtime :
    ∀ {targetState sourceState},
      stateRel targetState sourceState →
        SameRuntimeData targetState sourceState
  closedStep :
    ∀ {targetState sourceState},
      stateRel targetState sourceState →
        ExceptStepResultRelWith stateRel
          (Source.stepResult target targetState)
          (Source.stepResult source sourceState)
  openStep :
    ∀ {targetState sourceState},
      stateRel targetState sourceState →
        Simulation.Interaction.Rel
          (ExceptStepResultRelWith stateRel)
          (InteractionSemantics.Source.openStepResult target targetState)
          (InteractionSemantics.Source.openStepResult source sourceState)

def checkedRoundStepSimulation
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true) :
    RoundStepSimulation entry source cert.output where
  stateRel := StateCursorRel source cert
  initial := checked_entryState_stateCursorRel hCheck
  runtime := fun hState => hState.1
  closedStep := checked_closed_step hCheck
  openStep := checked_open_step hCheck

theorem closedRunNResult_rel_of_roundStepSimulation
    {entry : Label} {source target : Program}
    (simulation : RoundStepSimulation entry source target)
    {targetState sourceState : EVMState}
    (hState : simulation.stateRel targetState sourceState)
    (fuel : Nat) :
    ExceptStepResultRuntimeRel
      (Source.runNResult target fuel targetState)
      (Source.runNResult source fuel sourceState) := by
  induction fuel generalizing targetState sourceState with
  | zero =>
      exact .ok (simulation.runtime hState)
  | succ fuel ih =>
      have hStep := simulation.closedStep hState
      cases hTarget :
          Source.stepResult target targetState with
      | error targetError =>
          cases hSource :
              Source.stepResult source sourceState with
          | error sourceError =>
              rw [hTarget, hSource] at hStep
              cases hStep with
              | error hError =>
                  simpa [Source.runNResult, Control.runNResultWith,
                    hTarget, hSource] using
                    (Simulation.Interaction.ExceptRel.error hError :
                      ExceptStepResultRuntimeRel
                        (.error targetError) (.error sourceError))
          | ok sourceResult =>
              rw [hTarget, hSource] at hStep
              cases hStep
      | ok targetResult =>
          cases hSource :
              Source.stepResult source sourceState with
          | error sourceError =>
              rw [hTarget, hSource] at hStep
              cases hStep
          | ok sourceResult =>
              rw [hTarget, hSource] at hStep
              cases hStep with
              | ok hResult =>
                  cases targetResult with
                  | running targetNext =>
                      cases sourceResult with
                      | running sourceNext =>
                          simpa [Source.runNResult,
                            Control.runNResultWith, hTarget, hSource] using
                            ih hResult
                      | halted sourceHalt =>
                          exact False.elim hResult
                  | halted targetHalt =>
                      cases sourceResult with
                      | running sourceNext =>
                          exact False.elim hResult
                      | halted sourceHalt =>
                          simpa [Source.runNResult,
                            Control.runNResultWith, hTarget, hSource] using
                            (Simulation.Interaction.ExceptRel.ok hResult :
                              ExceptStepResultRuntimeRel
                                (.ok (.halted targetHalt))
                                (.ok (.halted sourceHalt)))

theorem openRunNResult_rel_of_roundStepSimulation
    {entry : Label} {source target : Program}
    (simulation : RoundStepSimulation entry source target)
    {targetState sourceState : EVMState}
    (hState : simulation.stateRel targetState sourceState)
    (fuel : Nat) :
    Simulation.Interaction.Rel ExceptStepResultRuntimeRel
      (InteractionSemantics.Source.openRunNResult target fuel targetState)
      (InteractionSemantics.Source.openRunNResult source fuel sourceState) := by
  induction fuel generalizing targetState sourceState with
  | zero =>
      exact
        .done (.ok (simulation.runtime hState))
  | succ fuel ih =>
      rw [InteractionSemantics.Source.openRunNResult_succ,
        InteractionSemantics.Source.openRunNResult_succ]
      apply Simulation.Interaction.Rel.bind (simulation.openStep hState)
      intro targetResult sourceResult hResult
      cases targetResult with
      | running targetNext =>
          cases sourceResult with
          | running sourceNext =>
              exact ih hResult
          | halted sourceHalt =>
              exact False.elim hResult
      | halted targetHalt =>
          cases sourceResult with
          | running sourceNext =>
              exact False.elim hResult
          | halted sourceHalt =>
              exact .done (.ok hResult)

/--
Whole closed/open one-round theorem obtained from the local cursor simulation.
This is the intended proof boundary: the remaining optimizer-specific work is
to construct `RoundStepSimulation` from `check`.
-/
theorem RoundStepSimulation.entryRunResultRel
    {entry : Label} {source target : Program}
    (simulation : RoundStepSimulation entry source target) :
    EntryRunResultRel entry source target := by
  constructor
  · intro fuel state
    exact
      closedRunNResult_rel_of_roundStepSimulation simulation
        (simulation.initial state) fuel
  · intro fuel state
    exact
      openRunNResult_rel_of_roundStepSimulation simulation
        (simulation.initial state) fuel

/--
The sole semantic obligation needed from the one-round cursor simulation.
Once this theorem is supplied for checked rounds, fixed-point composition is
entirely generic and does not need a trace-wide PC relation.
-/
def CheckedRoundResultSemantics (entry : Label) : Prop :=
  ∀ {source : Program} {cert : Cert},
    check entry source cert = true →
      EntryRunResultRel entry source cert.output

def CheckedRoundStepSemantics (entry : Label) :=
  ∀ {source : Program} {cert : Cert},
    check entry source cert = true →
      RoundStepSimulation entry source cert.output

def checkedRoundStepSemantics (entry : Label) :
    CheckedRoundStepSemantics entry := by
  intro source cert hCheck
  exact checkedRoundStepSimulation hCheck

theorem checkedRoundResultSemantics_of_stepSemantics
    {entry : Label}
    (hStep : CheckedRoundStepSemantics entry) :
    CheckedRoundResultSemantics entry := by
  intro source cert hCheck
  exact (hStep hCheck).entryRunResultRel

theorem CertifiedTrace.entryRunResultRel
    {entry : Label}
    (hRound : CheckedRoundResultSemantics entry)
    {source output : Program}
    (trace : CertifiedTrace entry source output) :
    EntryRunResultRel entry source output := by
  exact
    trace.lift
      (EntryRunResultRel.refl entry)
      EntryRunResultRel.trans
      hRound

/--
Public fixed-point semantic composition theorem. It covers both closed and
open-world `runNResult` executions and is insensitive to the number of
successful deduplication rounds.
-/
theorem fixedPointOptimize_entryRunResultRel
    {entry : Label} {source : Program}
    (hRound : CheckedRoundResultSemantics entry) :
    EntryRunResultRel entry source
      (fixedPointOptimize entry source) := by
  cases hCertify : certifyFixedPoint? entry source with
  | none =>
      simpa [fixedPointOptimize, hCertify] using
        EntryRunResultRel.refl entry source
  | some certified =>
      have hTrace := fixedPointCertified_trace certified
      simpa [fixedPointOptimize, hCertify] using
        hTrace.entryRunResultRel hRound

theorem fixedPointOptimize_entryRunResultRel_of_stepSemantics
    {entry : Label} {source : Program}
    (hStep : CheckedRoundStepSemantics entry) :
    EntryRunResultRel entry source
      (fixedPointOptimize entry source) :=
  fixedPointOptimize_entryRunResultRel
    (checkedRoundResultSemantics_of_stepSemantics hStep)

theorem fixedPointOptimize_entryRunResultRel_unconditional
    {entry : Label} {source : Program} :
    EntryRunResultRel entry source
      (fixedPointOptimize entry source) :=
  fixedPointOptimize_entryRunResultRel_of_stepSemantics
    (checkedRoundStepSemantics entry)

end MachineBlockDedup
end Assembly
end EvmCompiler
