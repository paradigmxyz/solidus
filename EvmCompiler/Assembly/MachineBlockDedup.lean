import EvmCompiler.Assembly.Accepted

namespace EvmCompiler
namespace Assembly
namespace MachineBlockDedup

abbrev LabelAliases := List (Label × Label)

structure MachineBlock where
  label : Label
  code : Program
  deriving DecidableEq, Repr

def finishMachineBlock (block : MachineBlock) : MachineBlock :=
  { block with code := block.code.reverse }

/--
Parse the labeled suffix of an assembly stream into maximal machine blocks.
Instructions before the first label are deliberately ignored; `parseExact?`
below makes the certified path reject such a lossy parse.
-/
def machineBlocksRev :
    Program → Option MachineBlock → List MachineBlock → List MachineBlock
  | [], none, blocks => blocks.reverse
  | [], some block, blocks =>
      (finishMachineBlock block :: blocks).reverse
  | .label label :: rest, none, blocks =>
      machineBlocksRev rest (some { label := label, code := [] }) blocks
  | .label label :: rest, some block, blocks =>
      machineBlocksRev rest (some { label := label, code := [] })
        (finishMachineBlock block :: blocks)
  | _instr :: rest, none, blocks =>
      machineBlocksRev rest none blocks
  | instr :: rest, some block, blocks =>
      machineBlocksRev rest
        (some { block with code := instr :: block.code }) blocks

def machineBlocks (source : Program) : List MachineBlock :=
  machineBlocksRev source none []

def flattenMachineBlocks (blocks : List MachineBlock) : Program :=
  blocks.flatMap fun block => .label block.label :: block.code

def parseExact? (source : Program) (blocks : List MachineBlock) : Bool :=
  decide (flattenMachineBlocks blocks = source)

theorem flatten_eq_of_parseExact {source : Program}
    {blocks : List MachineBlock}
    (hCheck : parseExact? source blocks = true) :
    flattenMachineBlocks blocks = source := by
  simpa [parseExact?] using hCheck

def resolveAlias (aliases : LabelAliases) (label : Label) : Label :=
  (aliases.find? fun entry => entry.1 == label).map Prod.snd |>.getD label

def rewriteMachineInstr (aliases : LabelAliases) : Instr → Instr
  | .pushLabel target => .pushLabel (resolveAlias aliases target)
  | .jump target => .jump (resolveAlias aliases target)
  | .jumpi target => .jumpi (resolveAlias aliases target)
  | instr => instr

def rewriteMachineBlock (aliases : LabelAliases)
    (block : MachineBlock) : MachineBlock :=
  { block with code := block.code.map (rewriteMachineInstr aliases) }

def findMachineBlock? (blocks : List MachineBlock)
    (label : Label) : Option MachineBlock :=
  blocks.find? fun candidate => candidate.label == label

theorem mem_of_findMachineBlock?_eq_some
    {blocks : List MachineBlock} {label : Label} {block : MachineBlock}
    (hFind : findMachineBlock? blocks label = some block) :
    block ∈ blocks := by
  exact List.mem_of_find?_eq_some hFind

theorem label_eq_of_findMachineBlock?_eq_some
    {blocks : List MachineBlock} {label : Label} {block : MachineBlock}
    (hFind : findMachineBlock? blocks label = some block) :
    block.label = label := by
  have hPredicate := List.find?_some hFind
  simpa using hPredicate

def findSameMachine? (blocks : List MachineBlock)
    (block : MachineBlock) : Option MachineBlock :=
  blocks.find? fun candidate => decide (candidate.code = block.code)

def retainedLabels (blocks : List MachineBlock) : List Label :=
  blocks.map MachineBlock.label

def aliasKeys (aliases : LabelAliases) : List Label :=
  aliases.map Prod.fst

def closesBlock : Instr → Bool
  | .jump _ => true
  | .prim .stop | .prim .return | .prim .revert | .prim .invalid
  | .prim .selfdestruct => true
  | _ => false

def blockClosed? (block : MachineBlock) : Bool :=
  match block.code.getLast? with
  | none => false
  | some instr => closesBlock instr

def allBlocksClosed? (blocks : List MachineBlock) : Bool :=
  blocks.all blockClosed?

/--
Collect exact-code aliases without changing implicit fallthrough. A duplicate
is removed only when its immediate source predecessor and the duplicate itself
cannot fall through. The entry is always kept.
-/
def collectSafeMachineAliases (entry : Label) :
    List MachineBlock → List MachineBlock → LabelAliases → Bool →
      List MachineBlock × LabelAliases
  | [], kept, aliases, _ => (kept.reverse, aliases)
  | block :: rest, kept, aliases, predecessorClosed =>
      let mayAlias :=
        block.label != entry &&
          predecessorClosed &&
          blockClosed? block
      if mayAlias then
        match findSameMachine? kept block with
        | some canonical =>
            collectSafeMachineAliases entry rest kept
              ((block.label, canonical.label) :: aliases)
              (blockClosed? block)
        | none =>
            collectSafeMachineAliases entry rest (block :: kept) aliases
              (blockClosed? block)
      else
        collectSafeMachineAliases entry rest (block :: kept) aliases
          (blockClosed? block)

/-- Greedy physical fallthrough layout.  Certification below independently
checks that every label still denotes its exact rewritten machine block. -/
def layoutSuccessor? (block : MachineBlock) : Option Label :=
  match block.code.getLast? with
  | some (.jump target) => some target
  | _ => none

def growMachineLayout (blocks : List MachineBlock) :
    Nat → Label → List Label → List MachineBlock × List Label
  | 0, _, placed => ([], placed)
  | fuel + 1, start, placed =>
      if placed.contains start then ([], placed)
      else
        match findMachineBlock? blocks start with
        | none => ([], placed)
        | some block =>
            let placed := start :: placed
            match layoutSuccessor? block with
            | none => ([block], placed)
            | some target =>
                let (tail, placed) := growMachineLayout blocks fuel target placed
                (block :: tail, placed)

def layoutMachineBlocks (entry : Label)
    (blocks : List MachineBlock) : List MachineBlock :=
  let successors := blocks.filterMap layoutSuccessor?
  let heads := (blocks.filter fun block =>
    !successors.contains block.label).map MachineBlock.label
  let seeds := entry :: (heads ++ blocks.map MachineBlock.label)
  (seeds.foldl (fun state seed =>
    let grown := growMachineLayout blocks blocks.length seed state.2
    (state.1 ++ grown.1, grown.2)) ([], [])).1

def collectMachineAliases (entry : Label)
    (blocks : List MachineBlock) (kept : List MachineBlock)
    (aliases : LabelAliases) : List MachineBlock × LabelAliases :=
  let collected := collectSafeMachineAliases entry blocks kept aliases false
  (layoutMachineBlocks entry collected.1, collected.2)

def aliasesClosed? (original : List MachineBlock)
    (aliases : LabelAliases) : Bool :=
  aliases.all fun pair =>
    match findMachineBlock? original pair.1 with
    | none => false
    | some block => blockClosed? block

/--
Removing the block following a retained fallthrough block would silently
change that predecessor's successor. An already-removed predecessor is
unreachable through its old address, so only retained predecessors need close.
-/
def fallthroughSafe? (original : List MachineBlock)
    (aliases : LabelAliases) : Bool :=
  match original with
  | [] | [_] => true
  | previous :: next :: rest =>
      let previousRemoved := (aliasKeys aliases).contains previous.label
      let nextRemoved := (aliasKeys aliases).contains next.label
      (!nextRemoved || previousRemoved || blockClosed? previous) &&
        fallthroughSafe? (next :: rest) aliases

def positionIndependent? (source : Program) : Bool :=
  source.all fun instr =>
    match instr with
    | .prim .pc => false
    | .pushLabel _ => false
    | .jumpDynamic => false
    | _ => true

theorem instr_ne_pc_of_positionIndependent
    {source : Program} {instr : Instr}
    (hIndependent : positionIndependent? source = true)
    (hInstr : instr ∈ source) :
    instr ≠ .prim .pc := by
  have hOne := (List.all_eq_true.mp hIndependent) instr hInstr
  intro hEq
  subst instr
  simp at hOne

theorem instr_ne_pushLabel_of_positionIndependent
    {source : Program} {instr : Instr}
    (hIndependent : positionIndependent? source = true)
    (hInstr : instr ∈ source) :
    ∀ label, instr ≠ .pushLabel label := by
  have hOne := (List.all_eq_true.mp hIndependent) instr hInstr
  intro label hEq
  subst instr
  simp at hOne

theorem instr_ne_jumpDynamic_of_positionIndependent
    {source : Program} {instr : Instr}
    (hIndependent : positionIndependent? source = true)
    (hInstr : instr ∈ source) :
    instr ≠ .jumpDynamic := by
  have hOne := (List.all_eq_true.mp hIndependent) instr hInstr
  intro hEq
  subst instr
  simp at hOne

theorem alias_source_closed_of_check
    {original : List MachineBlock} {aliases : LabelAliases}
    {source target : Label}
    (hClosed : aliasesClosed? original aliases = true)
    (hAlias : (source, target) ∈ aliases) :
    ∃ block,
      findMachineBlock? original source = some block ∧
        blockClosed? block = true := by
  unfold aliasesClosed? at hClosed
  have hOne :=
    (List.all_eq_true.mp hClosed) (source, target) hAlias
  cases hFind : findMachineBlock? original source with
  | none =>
      simp [hFind] at hOne
  | some block =>
      have hBlockClosed : blockClosed? block = true := by
        simpa [hFind] using hOne
      exact ⟨block, rfl, hBlockClosed⟩

/--
Aliases are normalized in one hop: keys are unique, the entry is never a key,
every key names a removed block, and every target names a retained block.
-/
def aliasesNormalized? (entry : Label) (kept : List MachineBlock)
    (aliases : LabelAliases) : Bool :=
  LabelList.unique? (aliasKeys aliases) &&
    aliases.all fun pair =>
      pair.1 != entry &&
        !(retainedLabels kept).contains pair.1 &&
        (retainedLabels kept).contains pair.2

theorem alias_target_retained_of_normalized
    {entry : Label} {kept : List MachineBlock}
    {aliases : LabelAliases} {source target : Label}
    (hNormalized : aliasesNormalized? entry kept aliases = true)
    (hAlias : (source, target) ∈ aliases) :
    target ∈ retainedLabels kept := by
  have hAll :
      aliases.all (fun pair =>
        pair.1 != entry &&
          !(retainedLabels kept).contains pair.1 &&
          (retainedLabels kept).contains pair.2) = true := by
    simp only [aliasesNormalized?, Bool.and_eq_true] at hNormalized
    exact hNormalized.2
  have hEntry := (List.all_eq_true.mp hAll) (source, target) hAlias
  simp [Bool.and_eq_true] at hEntry
  exact hEntry.2

theorem alias_source_ne_entry_of_normalized
    {entry : Label} {kept : List MachineBlock}
    {aliases : LabelAliases} {source target : Label}
    (hNormalized : aliasesNormalized? entry kept aliases = true)
    (hAlias : (source, target) ∈ aliases) :
    source ≠ entry := by
  have hAll :
      aliases.all (fun pair =>
        pair.1 != entry &&
          !(retainedLabels kept).contains pair.1 &&
          (retainedLabels kept).contains pair.2) = true := by
    simp only [aliasesNormalized?, Bool.and_eq_true] at hNormalized
    exact hNormalized.2
  have hEntry := (List.all_eq_true.mp hAll) (source, target) hAlias
  simp [Bool.and_eq_true] at hEntry
  exact hEntry.1.1

theorem resolveAlias_entry_of_normalized
    {entry : Label} {kept : List MachineBlock}
    {aliases : LabelAliases}
    (hNormalized : aliasesNormalized? entry kept aliases = true) :
    resolveAlias aliases entry = entry := by
  unfold resolveAlias
  cases hFind : aliases.find? (fun pair => pair.1 == entry) with
  | none =>
      simp [hFind]
  | some pair =>
      have hMem : pair ∈ aliases :=
        List.mem_of_find?_eq_some hFind
      have hPredicate := List.find?_some hFind
      rcases pair with ⟨source, target⟩
      have hSource : source = entry := by
        simpa using hPredicate
      subst source
      exact
        False.elim
          ((alias_source_ne_entry_of_normalized hNormalized hMem) rfl)

def entryFirst? (entry : Label) (blocks : List MachineBlock) : Bool :=
  match blocks with
  | [] => false
  | first :: _ => first.label == entry

theorem exists_entry_block_of_entryFirst
    {entry : Label} {blocks : List MachineBlock}
    (hFirst : entryFirst? entry blocks = true) :
    ∃ block, findMachineBlock? blocks entry = some block := by
  cases blocks with
  | nil =>
      simp [entryFirst?] at hFirst
  | cons first rest =>
      have hLabel : first.label = entry := by
        simpa [entryFirst?] using hFirst
      exact ⟨first, by simp [findMachineBlock?, hLabel]⟩

def blockCorresponds? (aliases : LabelAliases)
    (optimized : List MachineBlock) (original : MachineBlock) : Bool :=
  match findMachineBlock? optimized (resolveAlias aliases original.label) with
  | none => false
  | some representative =>
      decide
        (representative.code =
          original.code.map (rewriteMachineInstr aliases))

def exactCodeCorrespondence? (aliases : LabelAliases)
    (original optimized : List MachineBlock) : Bool :=
  original.all (blockCorresponds? aliases optimized)

theorem exact_code_correspondence_of_check
    {aliases : LabelAliases} {original optimized : List MachineBlock}
    (hCheck : exactCodeCorrespondence? aliases original optimized = true)
    {block : MachineBlock} (hBlock : block ∈ original) :
    ∃ representative,
      findMachineBlock? optimized (resolveAlias aliases block.label) =
          some representative ∧
        representative.code =
          block.code.map (rewriteMachineInstr aliases) := by
  have hOne :=
    (List.all_eq_true.mp hCheck) block hBlock
  unfold blockCorresponds? at hOne
  cases hFind :
      findMachineBlock? optimized (resolveAlias aliases block.label) with
  | none =>
      simp [hFind] at hOne
  | some representative =>
      refine ⟨representative, rfl, ?_⟩
      simpa [hFind] using hOne

structure Cert where
  originalBlocks : List MachineBlock
  keptBlocks : List MachineBlock
  aliases : LabelAliases
  output : Program
  deriving DecidableEq, Repr

def Cert.optimizedBlocks (cert : Cert) : List MachineBlock :=
  cert.keptBlocks.map (rewriteMachineBlock cert.aliases)

def collectionExact? (entry : Label) (cert : Cert) : Bool :=
  decide
    (collectMachineAliases entry cert.originalBlocks [] [] =
      (cert.keptBlocks, cert.aliases))

def outputExact? (cert : Cert) : Bool :=
  decide (flattenMachineBlocks cert.optimizedBlocks = cert.output)

def pcFits? (source output : Program) : Bool :=
  decide (source.PCFits ∧ output.PCFits)

def labelsExact? (source : Program) (blocks : List MachineBlock) : Bool :=
  decide (retainedLabels blocks = source.labels)

/--
The fail-closed certificate checker. Besides replaying the deterministic
collection, it independently checks every semantic-shape invariant needed by
run congruence and re-runs the ordinary Assembly accepted checker on the
emitted stream. `positionIndependent?` rejects `PC`, `pushLabel`, and dynamic
jumps: deleting a block changes later numeric addresses, including numeric
label values already on the stack. Requiring every source machine block to
close makes sequential cross-block execution impossible; callers outside this
compiler invariant simply retain the original program when certification
fails.
-/
def check (entry : Label) (source : Program) (cert : Cert) : Bool :=
  source.accepted && (
    pcFits? source cert.output && (
      positionIndependent? source && (
        decide (cert.originalBlocks = machineBlocks source) && (
          parseExact? source cert.originalBlocks && (
            labelsExact? source cert.originalBlocks && (
              allBlocksClosed? cert.originalBlocks && (
                collectionExact? entry cert && (
                  aliasesNormalized? entry cert.keptBlocks cert.aliases && (
                    aliasesClosed? cert.originalBlocks cert.aliases && (
                      fallthroughSafe? cert.originalBlocks cert.aliases && (
                        (entryFirst? entry cert.originalBlocks &&
                          entryFirst? entry cert.optimizedBlocks) && (
                          exactCodeCorrespondence? cert.aliases
                            cert.originalBlocks cert.optimizedBlocks && (
                              outputExact? cert &&
                                cert.output.accepted)))))))))))))

theorem check_parts {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true) :
    source.accepted = true ∧
      pcFits? source cert.output = true ∧
        positionIndependent? source = true ∧
        cert.originalBlocks = machineBlocks source ∧
        parseExact? source cert.originalBlocks = true ∧
        labelsExact? source cert.originalBlocks = true ∧
        allBlocksClosed? cert.originalBlocks = true ∧
        collectionExact? entry cert = true ∧
        aliasesNormalized? entry cert.keptBlocks cert.aliases = true ∧
        aliasesClosed? cert.originalBlocks cert.aliases = true ∧
        fallthroughSafe? cert.originalBlocks cert.aliases = true ∧
        (entryFirst? entry cert.originalBlocks &&
          entryFirst? entry cert.optimizedBlocks) = true ∧
        exactCodeCorrespondence? cert.aliases cert.originalBlocks
            cert.optimizedBlocks = true ∧
        outputExact? cert = true ∧
        cert.output.accepted = true := by
  simpa [check, Bool.and_eq_true] using hCheck

theorem original_block_of_label_mem_of_check
    {entry : Label} {source : Program} {cert : Cert}
    {label : Label}
    (hCheck : check entry source cert = true)
    (hLabel : label ∈ source.labels) :
    ∃ block,
      block ∈ cert.originalBlocks ∧ block.label = label := by
  rcases check_parts hCheck with
    ⟨_, _, _, _, _, hLabelsExact, _, _, _, _, _, _, _, _, _⟩
  have hLabels :
      retainedLabels cert.originalBlocks = source.labels := by
    simpa [labelsExact?] using hLabelsExact
  have hRetained : label ∈ retainedLabels cert.originalBlocks := by
    rw [hLabels]
    exact hLabel
  rcases List.mem_map.mp hRetained with
    ⟨block, hBlock, hBlockLabel⟩
  exact ⟨block, hBlock, hBlockLabel⟩

theorem original_block_closed_of_check
    {entry : Label} {source : Program} {cert : Cert}
    {block : MachineBlock}
    (hCheck : check entry source cert = true)
    (hBlock : block ∈ cert.originalBlocks) :
    blockClosed? block = true := by
  rcases check_parts hCheck with
    ⟨_, _, _, _, _, _, hAllClosed, _, _, _, _, _, _, _, _⟩
  exact (List.all_eq_true.mp hAllClosed) block hBlock

theorem pc_fits_of_check
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true) :
    source.PCFits ∧ cert.output.PCFits := by
  have hFits := (check_parts hCheck).2.1
  simpa [pcFits?] using hFits

theorem source_accepted_of_check
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true) :
    source.accepted = true :=
  (check_parts hCheck).1

theorem output_accepted_of_check
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true) :
    cert.output.accepted = true := by
  rcases check_parts hCheck with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hOutput⟩
  exact hOutput

theorem output_Accepted_of_check
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true) :
    Assembly.Accepted cert.output where
  checked := output_accepted_of_check hCheck

theorem output_eq_flatten_of_check
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true) :
    flattenMachineBlocks cert.optimizedBlocks = cert.output := by
  rcases check_parts hCheck with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hOutput, _⟩
  exact flatten_eq_of_parseExact hOutput

theorem entry_retained_of_check
    {entry : Label} {source : Program} {cert : Cert}
    (hCheck : check entry source cert = true) :
    ∃ block,
      findMachineBlock? cert.optimizedBlocks entry = some block := by
  rcases check_parts hCheck with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hEntry, _, _, _⟩
  simp only [Bool.and_eq_true] at hEntry
  have hOptimizedFirst : entryFirst? entry cert.optimizedBlocks = true :=
    hEntry.2
  exact exists_entry_block_of_entryFirst hOptimizedFirst

def candidate (entry : Label) (source : Program) : Cert :=
  let original := machineBlocks source
  let collected := collectMachineAliases entry original [] []
  let cert : Cert :=
    { originalBlocks := original
      keptBlocks := collected.1
      aliases := collected.2
      output := [] }
  { cert with output := flattenMachineBlocks cert.optimizedBlocks }

abbrev Certified (entry : Label) (source : Program) :=
  { cert : Cert // check entry source cert = true }

def certify? (entry : Label) (source : Program) :
    Option (Certified entry source) :=
  let cert := candidate entry source
  if h : check entry source cert = true then
    some ⟨cert, h⟩
  else
    none

theorem certified_output_accepted
    {entry : Label} {source : Program} (certified : Certified entry source) :
    certified.val.output.accepted = true := by
  exact output_accepted_of_check certified.property

structure FixedPointCert where
  rounds : List Cert
  output : Program
  deriving DecidableEq, Repr

def hasAliases (aliases : LabelAliases) : Bool :=
  !aliases.isEmpty

def traceCheck (entry : Label) :
    Program → List Cert → Program → Bool
  | current, [], output =>
      let terminal := candidate entry current
      decide (current = output) && (
        check entry current terminal && terminal.aliases.isEmpty)
  | current, round :: rest, output =>
      check entry current round && (
        decide (current ≠ round.output) &&
          traceCheck entry round.output rest output)

inductive CertifiedTrace (entry : Label) : Program → Program → Prop where
  | refl (program : Program) :
      CertifiedTrace entry program program
  | step {source output : Program} {round : Cert}
      (checked : check entry source round = true)
      (progress : decide (source ≠ round.output) = true)
      (tail : CertifiedTrace entry round.output output) :
      CertifiedTrace entry source output

theorem certifiedTrace_of_traceCheck
    {entry : Label} {source output : Program} {rounds : List Cert}
    (hCheck : traceCheck entry source rounds output = true) :
    CertifiedTrace entry source output := by
  induction rounds generalizing source with
  | nil =>
      simp only [traceCheck, Bool.and_eq_true] at hCheck
      have hEq : source = output := by
        simpa using hCheck.1
      subst output
      exact .refl source
  | cons round rest ih =>
      simp only [traceCheck, Bool.and_eq_true] at hCheck
      exact
        .step hCheck.1 hCheck.2.1
          (ih hCheck.2.2)

theorem CertifiedTrace.lift
    {entry : Label} {relation : Program → Program → Prop}
    (refl : ∀ program, relation program program)
    (trans :
      ∀ {first second third},
        relation first second →
        relation second third →
        relation first third)
    (round :
      ∀ {source : Program} {cert : Cert},
        check entry source cert = true →
        relation source cert.output)
    {source output : Program}
    (trace : CertifiedTrace entry source output) :
    relation source output := by
  induction trace with
  | refl program =>
      exact refl program
  | step checked _ tail ih =>
      exact trans (round checked) ih

theorem CertifiedTrace.output_accepted
    {entry : Label} {source output : Program}
    (trace : CertifiedTrace entry source output)
    (hAccepted : source.accepted = true) :
    output.accepted = true := by
  induction trace with
  | refl program =>
      exact hAccepted
  | step checked _ tail ih =>
      exact ih (output_accepted_of_check checked)

def fixedPointFuel (entry : Label) :
    Nat → Program → List Cert × Program
  | 0, current => ([], current)
  | fuel + 1, current =>
      let round := candidate entry current
      if check entry current round && decide (current ≠ round.output) then
        let tail := fixedPointFuel entry fuel round.output
        (round :: tail.1, tail.2)
      else
        ([], current)

def fixedPointCandidate (entry : Label) (source : Program) :
    FixedPointCert :=
  let result := fixedPointFuel entry (source.length + 1) source
  { rounds := result.1, output := result.2 }

def fixedPointCheck (entry : Label) (source : Program)
    (cert : FixedPointCert) : Bool :=
  traceCheck entry source cert.rounds cert.output

abbrev FixedPointCertified (entry : Label) (source : Program) :=
  { cert : FixedPointCert // fixedPointCheck entry source cert = true }

def certifyFixedPoint? (entry : Label) (source : Program) :
    Option (FixedPointCertified entry source) :=
  let cert := fixedPointCandidate entry source
  if h : fixedPointCheck entry source cert = true then
    some ⟨cert, h⟩
  else
    none

theorem fixedPointCertified_trace
    {entry : Label} {source : Program}
    (certified : FixedPointCertified entry source) :
    CertifiedTrace entry source certified.val.output := by
  exact certifiedTrace_of_traceCheck certified.property

def optimize (entry : Label) (source : Program) : Program :=
  match certify? entry source with
  | some certified => certified.val.output
  | none => source

theorem optimize_accepted
    {entry : Label} {source : Program}
    (hAccepted : source.accepted = true) :
    (optimize entry source).accepted = true := by
  cases hCertify : certify? entry source with
  | none =>
      simpa [optimize, hCertify] using hAccepted
  | some certified =>
      simpa [optimize, hCertify] using
        certified_output_accepted certified

def compile? (entry : Label) (source : Program) :
    Option TargetProgram :=
  Assembly.compile? (optimize entry source)

def fixedPointOptimize (entry : Label) (source : Program) : Program :=
  match certifyFixedPoint? entry source with
  | some certified => certified.val.output
  | none => source

theorem fixedPointOptimize_accepted
    {entry : Label} {source : Program}
    (hAccepted : source.accepted = true) :
    (fixedPointOptimize entry source).accepted = true := by
  cases hCertify : certifyFixedPoint? entry source with
  | none =>
      simpa [fixedPointOptimize, hCertify] using hAccepted
  | some certified =>
      have hTrace := fixedPointCertified_trace certified
      simpa [fixedPointOptimize, hCertify] using
        hTrace.output_accepted hAccepted

def compileFixedPoint? (entry : Label) (source : Program) :
    Option TargetProgram :=
  Assembly.compile? (fixedPointOptimize entry source)

end MachineBlockDedup
end Assembly
end EvmCompiler
