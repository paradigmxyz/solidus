import EvmCompiler.Compiler.StackArtifact
import EvmCompiler.TypedCfg.ReturnAddressLower
import EvmCompiler.TypedCfg.PeepholeSeamCancelEffRuntime
import EvmCompiler.Structured.PeepholeSeamCombinedEff
import EvmCompiler.TypedCfg.ShuffleCanonChainCombined
import EvmCompiler.Assembly.Compact

namespace EvmCompiler
namespace TypedCfg
namespace ReturnAddressProbe

/-!
Executable projection probe for the dormant symbolic-return-address path.

This module is deliberately not imported by the production compiler.  It
reuses the checked return-address lowering and computes the compact physical
layout that path would receive.  The proof-bearing production splice remains a
separate obligation.
-/

namespace Block

abbrev lowerBodyFrom? := ReturnAddressLower.Block.lowerBodyFrom?

abbrev lower? := ReturnAddressLower.Block.lower?

theorem lower?_starts_with_label
    {program : TypedCfg.Program} {block : TypedCfg.Block}
    {target : Assembly.Program}
    (hLower : lower? program block = some target) :
    ∃ tail, target = .label block.label :: tail := by
  change ReturnAddressLower.Block.lower? program block = some target at hLower
  unfold ReturnAddressLower.Block.lower? at hLower
  cases hBody : lowerBodyFrom? program block.body block.input with
  | none => simp [hBody] at hLower
  | some result =>
      rcases result with ⟨body, output⟩
      by_cases hOutput : output = block.output
      · subst output
        cases hTerm :
            ReturnAddressLower.Terminator.lowerAt? block.output block.term with
        | none => simp [hBody, hTerm] at hLower
        | some term =>
            simp [hBody, hTerm] at hLower
            subst target
            exact ⟨body ++ term, rfl⟩
      · simp [hBody, hOutput] at hLower

end Block

namespace Program

abbrev lowerBlocks? := ReturnAddressLower.Program.lowerBlocks?

abbrev lower? := ReturnAddressLower.Program.lower?

theorem lowerBlocks?_starts_with_label
    {program : TypedCfg.Program} {block : TypedCfg.Block}
    {rest : List TypedCfg.Block} {target : Assembly.Program}
    (hLower : lowerBlocks? program (block :: rest) = some target) :
    ∃ tail, target = .label block.label :: tail := by
  unfold ReturnAddressLower.Program.lowerBlocks? at hLower
  cases hHead : Block.lower? program block with
  | none => simp [hHead] at hLower
  | some head =>
      cases hTail : lowerBlocks? program rest with
      | none => simp [hHead, hTail] at hLower
      | some tail =>
          simp [hHead, hTail] at hLower
          subst target
          rcases Block.lower?_starts_with_label hHead with
            ⟨headTail, rfl⟩
          exact ⟨headTail ++ tail, by simp⟩

theorem lower?_starts_with_entry_label
    {program : TypedCfg.Program} {target : Assembly.Program}
    (hLower : lower? program = some target) :
    ∃ tail, target = .label program.entry :: tail := by
  change ReturnAddressLower.Program.lower? program = some target at hLower
  unfold ReturnAddressLower.Program.lower? at hLower
  cases hOrder : program.blocksInLoweringOrder? with
  | none => simp [hOrder] at hLower
  | some blocks =>
      simp [hOrder] at hLower
      unfold TypedCfg.Program.blocksInLoweringOrder? at hOrder
      cases hExtract :
          TypedCfg.Program.extractBlock? program.blocks program.entry with
      | none => simp [hExtract] at hOrder
      | some result =>
          rcases result with ⟨entry, remaining⟩
          simp [hExtract] at hOrder
          subst blocks
          have hEntry : entry.label = program.entry :=
            TypedCfg.Program.extractBlock?_label hExtract
          rcases lowerBlocks?_starts_with_label hLower with
            ⟨tail, hTarget⟩
          rw [hEntry] at hTarget
          exact ⟨tail, hTarget⟩

theorem lower?_entry_labelPc_zero
    {program : TypedCfg.Program} {target : Assembly.Program}
    (hLower : lower? program = some target) :
    target.labelPc program.entry = some 0 := by
  rcases lower?_starts_with_entry_label hLower with ⟨tail, rfl⟩
  simp [Assembly.Program.labelPc, Assembly.Program.labelPcFrom]

structure BlockFragment (program : TypedCfg.Program)
    (target : Assembly.Program) (block : TypedCfg.Block) where
  pre : Assembly.Program
  code : Assembly.Program
  post : Assembly.Program
  lower : Block.lower? program block = some code
  target_eq : target = pre ++ code ++ post

theorem lowerBlocks?_fragment_of_mem
    {program : TypedCfg.Program} {blocks : List TypedCfg.Block}
    {target : Assembly.Program} {block : TypedCfg.Block}
    (hLower : lowerBlocks? program blocks = some target)
    (hMem : block ∈ blocks) :
    Nonempty (BlockFragment program target block) := by
  induction blocks generalizing target with
  | nil => simp at hMem
  | cons head rest ih =>
      unfold ReturnAddressLower.Program.lowerBlocks? at hLower
      cases hHead : Block.lower? program head with
      | none => simp [hHead] at hLower
      | some headCode =>
          cases hTail : lowerBlocks? program rest with
          | none => simp [hHead, hTail] at hLower
          | some tailCode =>
              simp [hHead, hTail] at hLower
              subst target
              simp only [List.mem_cons] at hMem
              cases hMem with
              | inl hEq =>
                  subst block
                  exact
                    ⟨{ pre := []
                       code := headCode
                       post := tailCode
                       lower := hHead
                       target_eq := by simp }⟩
              | inr hRest =>
                  rcases ih hTail hRest with ⟨fragment⟩
                  exact
                    ⟨{ pre := headCode ++ fragment.pre
                       code := fragment.code
                       post := fragment.post
                       lower := fragment.lower
                       target_eq := by
                         calc
                           headCode ++ tailCode =
                               headCode ++
                                 (fragment.pre ++ fragment.code ++
                                   fragment.post) :=
                             congrArg (headCode ++ ·)
                               fragment.target_eq
                           _ =
                               (headCode ++ fragment.pre) ++
                                 fragment.code ++ fragment.post := by
                             simp [List.append_assoc] }⟩

theorem lower?_fragment_of_findBlock?
    {program : TypedCfg.Program} {target : Assembly.Program}
    {label : Assembly.Label} {block : TypedCfg.Block}
    (hLower : lower? program = some target)
    (hFind : program.findBlock? label = some block) :
    Nonempty (BlockFragment program target block) := by
  change ReturnAddressLower.Program.lower? program = some target at hLower
  unfold ReturnAddressLower.Program.lower? at hLower
  cases hOrder : program.blocksInLoweringOrder? with
  | none => simp [hOrder] at hLower
  | some blocks =>
      simp [hOrder] at hLower
      have hMemSource : block ∈ program.blocks :=
        List.mem_of_find?_eq_some hFind
      have hPerm := TypedCfg.Program.blocksInLoweringOrder?_perm hOrder
      have hMemOrdered : block ∈ blocks :=
        hPerm.mem_iff.mp hMemSource
      exact lowerBlocks?_fragment_of_mem hLower hMemOrdered

end Program

namespace Compact

open Assembly

abbrev LabelTable := Assembly.Compact.LabelTable
abbrev Located := Assembly.Compact.Located
abbrev SourceBlock := Assembly.Compact.SourceBlock
abbrev Program := Assembly.Compact.Program
abbrev PreparationBlock := Assembly.Compact.PreparationBlock

def codeAtPcFrom? : Assembly.Program → Nat → Nat →
    Assembly.Program → Bool
  | program, pc, query, code =>
      if pc = query then
        decide (code <+: program)
      else
        match program with
        | [] => false
        | instr :: rest =>
            if pc < query then
              codeAtPcFrom? rest (pc + instr.byteSize) query code
            else
              false
termination_by program => program.length

def codeAtPc? (program : Assembly.Program) (query : Nat)
    (code : Assembly.Program) : Bool :=
  codeAtPcFrom? program 0 query code

theorem codeAtPcFrom?_sound
    {program code : Assembly.Program} {pc query : Nat}
    (hCheck : codeAtPcFrom? program pc query code = true) :
    ∃ pre post,
      program = pre ++ code ++ post ∧
        query = pc + pre.byteLength := by
  induction program generalizing pc with
  | nil =>
      unfold codeAtPcFrom? at hCheck
      by_cases hPc : pc = query
      · subst query
        simp at hCheck
        subst code
        exact ⟨[], [], by simp, by simp⟩
      · simp [hPc] at hCheck
  | cons instr rest ih =>
      unfold codeAtPcFrom? at hCheck
      by_cases hPc : pc = query
      · subst query
        simp at hCheck
        rcases hCheck with ⟨post, hProgram⟩
        exact ⟨[], post, by simpa using hProgram.symm, by simp⟩
      · simp [hPc] at hCheck
        by_cases hLt : pc < query
        · simp [hLt] at hCheck
          obtain ⟨pre, post, hRest, hQuery⟩ :=
            ih hCheck
          exact
            ⟨instr :: pre, post,
              by simp [hRest, List.append_assoc],
              by
                rw [hQuery]
                simp [Assembly.Program.byteLength_cons,
                  Nat.add_assoc]⟩
        · simp [hLt] at hCheck

theorem codeAtPc?_sound
    {program code : Assembly.Program} {query : Nat}
    (hCheck : codeAtPc? program query code = true) :
    ∃ pre post,
      program = pre ++ code ++ post ∧
        query = pre.byteLength := by
  obtain ⟨pre, post, hProgram, hQuery⟩ :=
    codeAtPcFrom?_sound hCheck
  exact ⟨pre, post, hProgram, by simpa using hQuery⟩

def preparationBlockSafeIndexed?
    (index : Assembly.Compact.PreparationLookupIndex)
    (sourceEnd preparedEnd : Nat) (block : PreparationBlock) : Bool :=
  match block.action, block.sourceInstr with
  | .skip, .label _ => true
  | .skip, .jump target =>
      match index.sourceLabels.get? target with
      | some sourceDest =>
          Assembly.Compact.preparationTargetPcIndexed?
              index.boundaries sourceEnd preparedEnd sourceDest ==
            some block.preparedPc
      | none => false
  | .skip, _ => false
  | .keep, .jump target
  | .keep, .jumpi target
  | .keep, .pushLabel target =>
      match index.sourceLabels.get? target,
          index.preparedLabels.get? target with
      | some sourceDest, some preparedDest =>
          Assembly.Compact.preparationTargetPcIndexed?
              index.boundaries sourceEnd preparedEnd sourceDest ==
            some preparedDest
      | _, _ => false
  | .keep, .jumpDynamic => true
  | .keep, .prim .pc => false
  | .keep, _ => true

def preparationSafeIndexed? (source prepared : Assembly.Program)
    (blocks : List PreparationBlock) : Bool :=
  let index :=
    Assembly.Compact.buildPreparationLookupIndex source prepared blocks
  blocks.all
    (preparationBlockSafeIndexed? index
      source.byteLength prepared.byteLength)

def preparationBlockSafe? (source prepared : Assembly.Program)
    (blocks : List PreparationBlock) (block : PreparationBlock) : Bool :=
  match block.action, block.sourceInstr with
  | .skip, .label _ => true
  | .skip, .jump target =>
      match source.labelPc target with
      | some sourceDest =>
          Assembly.Compact.preparationTargetPc? blocks
              source.byteLength prepared.byteLength sourceDest ==
            some block.preparedPc
      | none => false
  | .skip, _ => false
  | .keep, .jump target
  | .keep, .jumpi target
  | .keep, .pushLabel target =>
      match source.labelPc target, prepared.labelPc target with
      | some sourceDest, some preparedDest =>
          Assembly.Compact.preparationTargetPc? blocks
              source.byteLength prepared.byteLength sourceDest ==
            some preparedDest
      | _, _ => false
  | .keep, .jumpDynamic => true
  | .keep, .prim .pc => false
  | .keep, _ => true

def preparationSafe? (source prepared : Assembly.Program)
    (blocks : List PreparationBlock) : Bool :=
  blocks.all (preparationBlockSafe? source prepared blocks)

def PreparationBlockSafe (source prepared : Assembly.Program)
    (blocks : List PreparationBlock) (block : PreparationBlock) : Prop :=
  match block.action, block.sourceInstr with
  | .skip, .label _ => True
  | .skip, .jump target =>
      ∃ sourceDest,
        source.labelPc target = some sourceDest ∧
          Assembly.Compact.preparationTargetPc? blocks
              source.byteLength prepared.byteLength sourceDest =
            some block.preparedPc
  | .skip, _ => False
  | .keep, .jump target
  | .keep, .jumpi target
  | .keep, .pushLabel target =>
      ∃ sourceDest preparedDest,
        source.labelPc target = some sourceDest ∧
          prepared.labelPc target = some preparedDest ∧
            Assembly.Compact.preparationTargetPc? blocks
                source.byteLength prepared.byteLength sourceDest =
              some preparedDest
  | .keep, .jumpDynamic => True
  | .keep, .prim .pc => False
  | .keep, _ => True

def PreparationSafe (source prepared : Assembly.Program)
    (blocks : List PreparationBlock) : Prop :=
  ∀ block, block ∈ blocks →
    PreparationBlockSafe source prepared blocks block

theorem preparationBlockSafeIndexed_eq
    (source prepared : Assembly.Program)
    (blocks : List PreparationBlock) (block : PreparationBlock) :
    preparationBlockSafeIndexed?
        (Assembly.Compact.buildPreparationLookupIndex
          source prepared blocks)
        source.byteLength prepared.byteLength block =
      preparationBlockSafe? source prepared blocks block := by
  rcases block with ⟨sourcePc, preparedPc, sourceInstr, action⟩
  cases action <;> cases sourceInstr <;>
    simp [preparationBlockSafeIndexed?, preparationBlockSafe?,
      Assembly.Compact.buildPreparationLookupIndex,
      Assembly.Compact.buildLabelPcIndex_get?,
      Assembly.Compact.preparationTargetPcIndexed_eq]
  all_goals try (rename_i op; cases op <;> rfl)
  all_goals
    simp only [← Std.HashMap.get?_eq_getElem?,
      Assembly.Compact.buildLabelPcIndex_get?]

theorem preparationSafeIndexed_eq
    (source prepared : Assembly.Program)
    (blocks : List PreparationBlock) :
    preparationSafeIndexed? source prepared blocks =
      preparationSafe? source prepared blocks := by
  unfold preparationSafeIndexed? preparationSafe?
  apply congrArg (fun predicate => blocks.all predicate)
  funext block
  exact preparationBlockSafeIndexed_eq source prepared blocks block

theorem preparationBlockSafe_of_check
    {source prepared : Assembly.Program}
    {blocks : List PreparationBlock} {block : PreparationBlock}
    (hCheck :
      preparationBlockSafe? source prepared blocks block = true) :
    PreparationBlockSafe source prepared blocks block := by
  rcases block with ⟨sourcePc, preparedPc, sourceInstr, action⟩
  cases action <;> cases sourceInstr <;>
    simp [preparationBlockSafe?, PreparationBlockSafe] at hCheck ⊢
  all_goals
    split at hCheck <;> simp_all

theorem preparationSafe_of_check
    {source prepared : Assembly.Program}
    {blocks : List PreparationBlock}
    (hCheck : preparationSafe? source prepared blocks = true) :
    PreparationSafe source prepared blocks := by
  intro block hMem
  exact preparationBlockSafe_of_check
    ((List.all_eq_true.mp hCheck) block hMem)

def sourceInstrSizeAt? (pinnedPushPcs : List Nat)
    (branchWidth sourcePc : Nat) : Assembly.Instr → Option Nat
  | .label _ | .prim _ | .jumpDynamic => some 1
  | .push value => do
      let width ← Assembly.Compact.pushWidthAt?
        pinnedPushPcs sourcePc value
      some (width + 1)
  | .pushLabel _ => some (branchWidth + 1)
  | .jump _ | .jumpi _ => some (branchWidth + 2)

def layoutRev? (pinnedPushPcs : List Nat) (branchWidth : Nat) :
    Assembly.Program → Nat → Nat → LabelTable →
      Option (LabelTable × Nat)
  | [], _sourcePc, compactPc, labels =>
      some (labels.reverse, compactPc)
  | instr :: rest, sourcePc, compactPc, labels => do
      let size ← sourceInstrSizeAt?
        pinnedPushPcs branchWidth sourcePc instr
      let labels :=
        match instr with
        | .label name => (name, compactPc) :: labels
        | _ => labels
      layoutRev? pinnedPushPcs branchWidth rest
        (sourcePc + instr.byteSize) (compactPc + size) labels

def layout? (pinnedPushPcs : List Nat)
    (source : Assembly.Program) (branchWidth : Nat) :
    Option (LabelTable × Nat) :=
  layoutRev? pinnedPushPcs branchWidth source 0 0 []

theorem layoutRev?_names
    {pinnedPushPcs : List Nat}
    {branchWidth sourcePc compactPc endPc : Nat}
    {source : Assembly.Program} {acc table : LabelTable}
    (hLayout :
      layoutRev? pinnedPushPcs branchWidth source
          sourcePc compactPc acc =
        some (table, endPc)) :
    table.map Prod.fst =
      acc.reverse.map Prod.fst ++ source.labels := by
  induction source generalizing
      sourcePc compactPc acc table endPc with
  | nil =>
      simp [layoutRev?] at hLayout
      rcases hLayout with ⟨rfl, rfl⟩
      simp [Assembly.Program.labels]
  | cons instr rest ih =>
      cases hSize :
          sourceInstrSizeAt?
            pinnedPushPcs branchWidth sourcePc instr with
      | none =>
          simp [layoutRev?, hSize] at hLayout
      | some size =>
          cases instr with
          | label name =>
              have hTail :
                  layoutRev? pinnedPushPcs branchWidth rest
                      (sourcePc +
                        (Assembly.Instr.label name).byteSize)
                      (compactPc + size)
                      ((name, compactPc) :: acc) =
                    some (table, endPc) := by
                simpa [layoutRev?, hSize] using hLayout
              have hRest := ih hTail
              simpa [Assembly.Program.labels, List.reverse_cons,
                List.map_append, List.append_assoc] using hRest
          | prim op
          | push op
          | pushLabel op
          | jump op
          | jumpi op =>
              have hTail := hLayout
              simp [layoutRev?, hSize] at hTail
              have hRest := ih hTail
              simpa [Assembly.Program.labels] using hRest
          | jumpDynamic =>
              have hTail := hLayout
              simp [layoutRev?, hSize] at hTail
              have hRest := ih hTail
              simpa [Assembly.Program.labels] using hRest

def branchWidthFits? (pinnedPushPcs : List Nat)
    (source : Assembly.Program) (branchWidth : Nat) : Bool :=
  match layout? pinnedPushPcs source branchWidth with
  | none => false
  | some (_, codeLength) =>
      Assembly.Compact.fitsWidth? branchWidth codeLength

def branchWidthFor? (pinnedPushPcs : List Nat)
    (source : Assembly.Program) : Option Nat :=
  Assembly.Compact.candidateWidths.find? fun width =>
    branchWidthFits? pinnedPushPcs source width

def emitInstrRev? (pinnedPushPcs : List Nat)
    (branchWidth sourcePc compactPc : Nat) (table : LabelTable)
    (instr : Assembly.Instr)
    (acc : List Assembly.Compact.Located) :
    Option (List Assembly.Compact.Located) :=
  match instr with
  | .label _ =>
      some ({ pc := compactPc, instr := .jumpdest } :: acc)
  | .prim op =>
      some ({ pc := compactPc, instr := .prim op } :: acc)
  | .push value => do
      let width ← Assembly.Compact.pushWidthAt?
        pinnedPushPcs sourcePc value
      some
        ({ pc := compactPc
           instr := Assembly.Compact.pushInstrOfWidth width value } :: acc)
  | .pushLabel target => do
      let dest ← Assembly.Compact.lookupLabel? table target
      if Assembly.Compact.fitsWidth? branchWidth dest then
        some
          ({ pc := compactPc
             instr := .push branchWidth
               (EvmYul.UInt256.ofNat dest) } :: acc)
      else
        none
  | .jump target => do
      let dest ← Assembly.Compact.lookupLabel? table target
      if Assembly.Compact.fitsWidth? branchWidth dest then
        some
          ({ pc := compactPc + branchWidth + 1, instr := .jump } ::
            { pc := compactPc
              instr := .push branchWidth
                (EvmYul.UInt256.ofNat dest) } :: acc)
      else
        none
  | .jumpi target => do
      let dest ← Assembly.Compact.lookupLabel? table target
      if Assembly.Compact.fitsWidth? branchWidth dest then
        some
          ({ pc := compactPc + branchWidth + 1, instr := .jumpi } ::
            { pc := compactPc
              instr := .push branchWidth
                (EvmYul.UInt256.ofNat dest) } :: acc)
      else
        none
  | .jumpDynamic =>
      some ({ pc := compactPc, instr := .jump } :: acc)

def emitRev? (pinnedPushPcs : List Nat) (branchWidth : Nat)
    (table : LabelTable) :
    Assembly.Program → Nat → Nat →
      List Assembly.Compact.Located →
        Option (List Assembly.Compact.Located)
  | [], _sourcePc, _compactPc, acc => some acc.reverse
  | instr :: rest, sourcePc, compactPc, acc => do
      let size ← sourceInstrSizeAt?
        pinnedPushPcs branchWidth sourcePc instr
      let acc ← emitInstrRev? pinnedPushPcs branchWidth
        sourcePc compactPc table instr acc
      emitRev? pinnedPushPcs branchWidth table rest
        (sourcePc + instr.byteSize) (compactPc + size) acc

def emit? (pinnedPushPcs : List Nat) (source : Assembly.Program)
    (branchWidth : Nat) (table : LabelTable) :
    Option Assembly.Compact.Program := do
  let code ← emitRev? pinnedPushPcs branchWidth table source 0 0 []
  some { code := code }

def emitSourceBlock? (pinnedPushPcs : List Nat)
    (branchWidth sourcePc compactPc : Nat) (table : LabelTable)
    (instr : Assembly.Instr) :
    Option (List Assembly.Compact.Located) := do
  let reversed ← emitInstrRev? pinnedPushPcs branchWidth
    sourcePc compactPc table instr []
  some reversed.reverse

def emitBlocksFromRev? (pinnedPushPcs : List Nat)
    (branchWidth : Nat) (table : LabelTable) :
    Assembly.Program → Nat → Nat → List Assembly.Compact.SourceBlock →
      Option (List Assembly.Compact.SourceBlock)
  | [], _sourcePc, _compactPc, acc => some acc.reverse
  | instr :: rest, sourcePc, compactPc, acc => do
      let compactSize ←
        sourceInstrSizeAt? pinnedPushPcs branchWidth sourcePc instr
      let code ← emitSourceBlock? pinnedPushPcs branchWidth
        sourcePc compactPc table instr
      emitBlocksFromRev? pinnedPushPcs branchWidth table rest
        (sourcePc + instr.byteSize) (compactPc + compactSize)
        ({ sourcePc := sourcePc
           compactPc := compactPc
           sourceInstr := instr
           code := code } :: acc)

def emitBlocksFrom? (pinnedPushPcs : List Nat) (branchWidth : Nat)
    (table : LabelTable) :
    Assembly.Program → Nat → Nat →
      Option (List Assembly.Compact.SourceBlock)
  | [], _sourcePc, _compactPc => some []
  | instr :: rest, sourcePc, compactPc => do
      let compactSize ←
        sourceInstrSizeAt? pinnedPushPcs branchWidth sourcePc instr
      let code ← emitSourceBlock? pinnedPushPcs branchWidth
        sourcePc compactPc table instr
      let blocks ← emitBlocksFrom? pinnedPushPcs branchWidth table rest
        (sourcePc + instr.byteSize) (compactPc + compactSize)
      some
        ({ sourcePc := sourcePc
           compactPc := compactPc
           sourceInstr := instr
           code := code } :: blocks)

def emitBlocks? (pinnedPushPcs : List Nat) (source : Assembly.Program)
    (branchWidth : Nat) (table : LabelTable) :
    Option (List Assembly.Compact.SourceBlock) :=
  emitBlocksFrom? pinnedPushPcs branchWidth table source 0 0

inductive BlocksValidFrom (pinnedPushPcs : List Nat)
    (branchWidth : Nat) (table : LabelTable) :
    Assembly.Program → Nat → Nat → List SourceBlock → Prop
  | nil (sourcePc compactPc : Nat) :
      BlocksValidFrom pinnedPushPcs branchWidth table [] sourcePc compactPc []
  | cons (instr : Assembly.Instr) (rest : Assembly.Program)
      (sourcePc compactPc compactSize : Nat)
      (code : List Located) (blocks : List SourceBlock)
      (hSize :
        sourceInstrSizeAt? pinnedPushPcs branchWidth sourcePc instr =
          some compactSize)
      (hCode :
        emitSourceBlock? pinnedPushPcs branchWidth sourcePc compactPc table
            instr =
          some code)
      (hRest :
        BlocksValidFrom pinnedPushPcs branchWidth table rest
          (sourcePc + instr.byteSize) (compactPc + compactSize) blocks) :
      BlocksValidFrom pinnedPushPcs branchWidth table (instr :: rest)
        sourcePc compactPc
        ({ sourcePc := sourcePc
           compactPc := compactPc
           sourceInstr := instr
           code := code } :: blocks)

theorem emitBlocksFrom?_valid
    {pinnedPushPcs : List Nat} {branchWidth : Nat} {table : LabelTable} :
    ∀ {source : Assembly.Program} {sourcePc compactPc : Nat}
      {blocks : List SourceBlock},
      emitBlocksFrom? pinnedPushPcs branchWidth table source
          sourcePc compactPc =
        some blocks →
      BlocksValidFrom pinnedPushPcs branchWidth table source
        sourcePc compactPc blocks := by
  intro source
  induction source with
  | nil =>
      intro sourcePc compactPc blocks hEmit
      simp [emitBlocksFrom?] at hEmit
      subst blocks
      exact .nil sourcePc compactPc
  | cons instr rest ih =>
      intro sourcePc compactPc blocks hEmit
      unfold emitBlocksFrom? at hEmit
      cases hSize :
          sourceInstrSizeAt? pinnedPushPcs branchWidth sourcePc instr with
      | none => simp [hSize] at hEmit
      | some compactSize =>
          simp [hSize] at hEmit
          cases hCode :
              emitSourceBlock? pinnedPushPcs branchWidth
                sourcePc compactPc table instr with
          | none => simp [hCode] at hEmit
          | some code =>
              simp [hCode] at hEmit
              cases hRest :
                  emitBlocksFrom? pinnedPushPcs branchWidth table rest
                    (sourcePc + instr.byteSize)
                    (compactPc + compactSize) with
              | none => simp [hRest] at hEmit
              | some restBlocks =>
                  simp [hRest] at hEmit
                  subst blocks
                  exact .cons instr rest sourcePc compactPc compactSize
                    code restBlocks hSize hCode (ih hRest)

theorem emitBlocks?_valid
    {pinnedPushPcs : List Nat} {source : Assembly.Program}
    {branchWidth : Nat} {table : LabelTable}
    {blocks : List SourceBlock}
    (hEmit :
      emitBlocks? pinnedPushPcs source branchWidth table = some blocks) :
    BlocksValidFrom pinnedPushPcs branchWidth table source 0 0 blocks :=
  emitBlocksFrom?_valid hEmit

theorem emitSourceBlock?_codeByteLength
    {pinnedPushPcs : List Nat}
    {branchWidth sourcePc compactPc compactSize : Nat}
    {table : LabelTable} {instr : Assembly.Instr}
    {code : List Located}
    (hSize :
      sourceInstrSizeAt? pinnedPushPcs branchWidth sourcePc instr =
        some compactSize)
    (hCode :
      emitSourceBlock? pinnedPushPcs branchWidth sourcePc compactPc table
          instr =
        some code) :
    Assembly.Compact.Program.codeByteLength code = compactSize := by
  cases instr with
  | label name | prim name | jumpDynamic =>
      simp [sourceInstrSizeAt?, emitSourceBlock?, emitInstrRev?]
        at hSize hCode
      subst compactSize
      subst code
      rfl
  | push value =>
      cases hWidth :
          Assembly.Compact.pushWidthAt? pinnedPushPcs sourcePc value with
      | none => simp [sourceInstrSizeAt?, hWidth] at hSize
      | some width =>
          simp [sourceInstrSizeAt?, hWidth, emitSourceBlock?, emitInstrRev?]
            at hSize hCode
          subst compactSize
          subst code
          simp [Assembly.Compact.Program.codeByteLength,
            Assembly.Compact.pushInstrOfWidth_byteSize]
  | pushLabel target =>
      cases hDest : Assembly.Compact.lookupLabel? table target with
      | none => simp [emitSourceBlock?, emitInstrRev?, hDest] at hCode
      | some dest =>
          by_cases hFits :
              Assembly.Compact.fitsWidth? branchWidth dest = true
          · simp [sourceInstrSizeAt?, emitSourceBlock?, emitInstrRev?,
              hDest, hFits] at hSize hCode
            subst compactSize
            subst code
            simp [Assembly.Compact.Program.codeByteLength,
              Assembly.Compact.Instr.byteSize]
          · simp [emitSourceBlock?, emitInstrRev?, hDest, hFits] at hCode
  | jump target | jumpi target =>
      cases hDest : Assembly.Compact.lookupLabel? table target with
      | none => simp [emitSourceBlock?, emitInstrRev?, hDest] at hCode
      | some dest =>
          by_cases hFits :
              Assembly.Compact.fitsWidth? branchWidth dest = true
          · simp [sourceInstrSizeAt?, emitSourceBlock?, emitInstrRev?,
              hDest, hFits] at hSize hCode
            subst compactSize
            subst code
            simp [Assembly.Compact.Program.codeByteLength,
              Assembly.Compact.Instr.byteSize, Nat.add_assoc]
          · simp [emitSourceBlock?, emitInstrRev?, hDest, hFits] at hCode

theorem BlocksValidFrom.next_boundary
    {pinnedPushPcs : List Nat} {branchWidth : Nat}
    {table : LabelTable} {source : Assembly.Program}
    {sourcePc compactPc : Nat} {blocks : List SourceBlock}
    (hValid :
      BlocksValidFrom pinnedPushPcs branchWidth table source
        sourcePc compactPc blocks) :
    ∀ {block : SourceBlock}, block ∈ blocks →
      ∀ {compactSize : Nat},
        sourceInstrSizeAt? pinnedPushPcs branchWidth block.sourcePc
            block.sourceInstr =
          some compactSize →
        Assembly.Compact.BoundaryPair blocks
          (sourcePc + source.byteLength)
          (compactPc +
            Assembly.Compact.Program.codeByteLength
              (Assembly.Compact.blocksCode blocks))
          (block.sourcePc + block.sourceInstr.byteSize)
          (block.compactPc + compactSize) := by
  intro block hMem compactSize hSize
  induction hValid generalizing block compactSize with
  | nil => simp at hMem
  | @cons instr rest sourcePc compactPc headSize code blocks
      hHeadSize hCode hRest ih =>
      simp at hMem
      cases hMem with
      | inl hHead =>
          subst block
          have hSizeEq : compactSize = headSize := by
            rw [hHeadSize] at hSize
            exact (Option.some.inj hSize).symm
          subst compactSize
          cases hRest with
          | nil =>
              right
              constructor
              · simp [Assembly.Program.byteLength,
                  Assembly.Instr.byteSize_pos]
              · have hCodeLength :=
                    emitSourceBlock?_codeByteLength hHeadSize hCode
                simp [Assembly.Compact.blocksCode,
                  Assembly.Compact.Program.codeByteLength,
                  hCodeLength]
          | @cons next rest' _ _ nextSize nextCode
              nextBlocks hNextSize hNextCode hNextRest =>
              left
              exact
                ⟨{ sourcePc := sourcePc + instr.byteSize
                   compactPc := compactPc + headSize
                   sourceInstr := next
                   code := nextCode }, by simp⟩
      | inr hTail =>
          have hTailBoundary := ih hTail hSize
          have hHeadCodeLength :=
            emitSourceBlock?_codeByteLength hHeadSize hCode
          rcases hTailBoundary with hNext | hEnd
          · left
            rcases hNext with
              ⟨next, hNextMem, hSource, hCompact⟩
            exact
              ⟨next, by simp [hNextMem], hSource, hCompact⟩
          · right
            rcases hEnd with ⟨hSourceEnd, hCompactEnd⟩
            constructor
            · simpa [Assembly.Program.byteLength_cons,
                Nat.add_assoc] using hSourceEnd
            · simpa [Assembly.Compact.blocksCode,
                Assembly.Compact.Program.codeByteLength_append,
                hHeadCodeLength, Nat.add_assoc] using hCompactEnd

theorem BlocksValidFrom.initial_boundary
    {pinnedPushPcs : List Nat} {branchWidth : Nat}
    {table : LabelTable} {source : Assembly.Program}
    {blocks : List SourceBlock}
    (hValid :
      BlocksValidFrom pinnedPushPcs branchWidth table source 0 0 blocks) :
    Assembly.Compact.BoundaryPair blocks source.byteLength
      (Assembly.Compact.Program.codeByteLength
        (Assembly.Compact.blocksCode blocks))
      0 0 := by
  cases hValid with
  | nil => exact Or.inr ⟨rfl, rfl⟩
  | @cons instr rest sourcePc compactPc compactSize code blocks
      hSize hCode hRest =>
      exact
        Or.inl
          ⟨{ sourcePc := 0
             compactPc := 0
             sourceInstr := instr
             code := code }, by simp⟩

theorem BlocksValidFrom.block_emit_of_mem
    {pinnedPushPcs : List Nat} {branchWidth : Nat}
    {table : LabelTable} {source : Assembly.Program}
    {sourcePc compactPc : Nat} {blocks : List SourceBlock}
    (hValid :
      BlocksValidFrom pinnedPushPcs branchWidth table source
        sourcePc compactPc blocks) :
    ∀ {block : SourceBlock}, block ∈ blocks →
      ∃ compactSize,
        sourceInstrSizeAt? pinnedPushPcs branchWidth block.sourcePc
            block.sourceInstr =
          some compactSize ∧
        emitSourceBlock? pinnedPushPcs branchWidth block.sourcePc
            block.compactPc table block.sourceInstr =
          some block.code := by
  intro block hMem
  induction hValid with
  | nil => simp at hMem
  | @cons instr rest sourcePc compactPc compactSize code blocks
      hSize hCode hRest ih =>
      simp at hMem
      cases hMem with
      | inl hHead =>
          subst block
          exact ⟨compactSize, hSize, hCode⟩
      | inr hTail =>
          exact ih hTail

theorem BlocksValidFrom.decompose_of_block_mem
    {pinnedPushPcs : List Nat} {branchWidth : Nat}
    {table : LabelTable} {source : Assembly.Program}
    {sourcePc compactPc : Nat} {blocks : List SourceBlock}
    (hValid :
      BlocksValidFrom pinnedPushPcs branchWidth table source
        sourcePc compactPc blocks) :
    ∀ {block : SourceBlock}, block ∈ blocks →
      ∃ pre post,
        source = pre ++ block.sourceInstr :: post ∧
          block.sourcePc = sourcePc + pre.byteLength := by
  intro block hMem
  induction hValid with
  | nil => simp at hMem
  | @cons instr rest sourcePc compactPc compactSize code blocks
      hSize hCode hRest ih =>
      simp at hMem
      cases hMem with
      | inl hHead =>
          subst block
          exact ⟨[], rest, rfl, by simp⟩
      | inr hTail =>
          obtain ⟨pre, post, hRest, hPc⟩ := ih hTail
          subst rest
          refine ⟨instr :: pre, post, by simp, ?_⟩
          simpa [Assembly.Program.byteLength_cons,
            Nat.add_assoc] using hPc

theorem BlocksValidFrom.suffix_of_block_mem
    {pinnedPushPcs : List Nat} {branchWidth : Nat}
    {table : LabelTable} {source : Assembly.Program}
    {sourcePc compactPc : Nat} {blocks : List SourceBlock}
    (hValid :
      BlocksValidFrom pinnedPushPcs branchWidth table source
        sourcePc compactPc blocks) :
    ∀ {block : SourceBlock}, block ∈ blocks →
      ∃ rest restBlocks,
        BlocksValidFrom pinnedPushPcs branchWidth table
          (block.sourceInstr :: rest)
          block.sourcePc block.compactPc
          (block :: restBlocks) := by
  intro block hMem
  induction hValid with
  | nil =>
      simp at hMem
  | @cons instr rest sourcePc compactPc compactSize code blocks
      hSize hCode hRest ih =>
      simp at hMem
      cases hMem with
      | inl hHead =>
          subst block
          exact
            ⟨rest, blocks,
              .cons instr rest sourcePc compactPc compactSize
                code blocks hSize hCode hRest⟩
      | inr hTail =>
          exact ih hTail

structure Artifact where
  source : Assembly.Program
  pinnedPushPcs : List Nat
  physicalSource : Assembly.Program
  branchWidth : Nat
  labels : LabelTable
  codeLength : Nat
  preparation : List PreparationBlock
  blocks : List Assembly.Compact.SourceBlock
  program : Assembly.Compact.Program
  bytes : ByteArray

def Artifact.asCompact (artifact : Artifact) :
    Assembly.Compact.Artifact :=
  { pinnedPushPcs := artifact.pinnedPushPcs
    physicalSource := artifact.physicalSource
    branchWidth := artifact.branchWidth
    labels := artifact.labels
    codeLength := artifact.codeLength
    preparation := artifact.preparation
    blocks := artifact.blocks
    program := artifact.program
    bytes := artifact.bytes }

def compile? (source : Assembly.Program)
    (pinnedPushPcs : List Nat := []) : Option Artifact := do
  let _ ← if decide source.PCFits then some () else none
  let physicalSource := Assembly.Compact.prepare source
  let preparation ←
    Assembly.Compact.alignPreparation? source physicalSource
  let _ ←
    if preparationSafeIndexed? source physicalSource preparation then
      some ()
    else
      none
  let branchWidth ← branchWidthFor? pinnedPushPcs physicalSource
  let (labels, codeLength) ←
    layout? pinnedPushPcs physicalSource branchWidth
  let program ← emit? pinnedPushPcs physicalSource branchWidth labels
  let blocks ←
    emitBlocks? pinnedPushPcs physicalSource branchWidth labels
  if Assembly.Compact.blocksCodeMatches? blocks program.code then
    if Assembly.Compact.labelsConsistent? blocks labels then
      if program.wellFormed? then
        if Assembly.Compact.Program.codeByteLength program.code + 1 <
            18446744073709551616 then
          some
            { source
              pinnedPushPcs
              physicalSource
              branchWidth
              labels
              codeLength
              preparation
              blocks
              program
              bytes := Assembly.Compact.encode program }
        else
          none
      else
        none
    else
      none
  else
    none

structure Artifact.ValidFor (artifact : Artifact)
    (source : Assembly.Program) : Prop where
  sourcePCFits : source.PCFits
  physicalSource :
    artifact.physicalSource = Assembly.Compact.prepare source
  preparationAligned :
    Assembly.Compact.alignPreparation? source artifact.physicalSource =
      some artifact.preparation
  preparationSafeIndexed :
    preparationSafeIndexed? source artifact.physicalSource
        artifact.preparation =
      true
  selectedBranchWidth :
    branchWidthFor? artifact.pinnedPushPcs artifact.physicalSource =
      some artifact.branchWidth
  layout :
    layout? artifact.pinnedPushPcs artifact.physicalSource
        artifact.branchWidth =
      some (artifact.labels, artifact.codeLength)
  emitted :
    emit? artifact.pinnedPushPcs artifact.physicalSource
        artifact.branchWidth artifact.labels =
      some artifact.program
  blocks :
    emitBlocks? artifact.pinnedPushPcs artifact.physicalSource
        artifact.branchWidth artifact.labels =
      some artifact.blocks
  blockCode :
    Assembly.Compact.blocksCode artifact.blocks = artifact.program.code
  labelsConsistent :
    Assembly.Compact.LabelsConsistent artifact.blocks artifact.labels
  wellFormed :
    artifact.program.Valid ∧
      Assembly.Compact.Program.codeLayoutFrom artifact.program.code 0 ∧
        Assembly.Compact.Program.codeByteLength artifact.program.code <
            18446744073709551616 ∧
          artifact.program.PCIndependent
  bytes : artifact.bytes = Assembly.Compact.encode artifact.program
  sentinelFits :
    Assembly.Compact.Program.codeByteLength artifact.program.code + 1 <
      18446744073709551616

theorem compile?_valid {source : Assembly.Program}
    {pinnedPushPcs : List Nat} {artifact : Artifact}
    (hCompile : compile? source pinnedPushPcs = some artifact) :
    artifact.ValidFor source := by
  unfold compile? at hCompile
  have hSourceFits : source.PCFits := by
    by_contra hNotFits
    simp [hNotFits] at hCompile
  simp [hSourceFits] at hCompile
  generalize hPhysical :
      Assembly.Compact.prepare source = physicalSource at hCompile
  cases hPreparation :
      Assembly.Compact.alignPreparation? source physicalSource with
  | none => simp [hPreparation] at hCompile
  | some preparation =>
      simp [hPreparation] at hCompile
      by_cases hPreparationSafe :
          preparationSafeIndexed? source physicalSource preparation = true
      · simp [hPreparationSafe] at hCompile
        cases hWidth : branchWidthFor? pinnedPushPcs physicalSource with
        | none => simp [hWidth] at hCompile
        | some branchWidth =>
            simp [hWidth] at hCompile
            cases hLayout : layout? pinnedPushPcs physicalSource branchWidth with
            | none => simp [hLayout] at hCompile
            | some layoutResult =>
                cases layoutResult with
                | mk labels codeLength =>
                    simp [hLayout] at hCompile
                    cases hEmit :
                        emit? pinnedPushPcs physicalSource branchWidth labels with
                    | none => simp [hEmit] at hCompile
                    | some program =>
                        simp [hEmit] at hCompile
                        cases hBlocks :
                            emitBlocks? pinnedPushPcs physicalSource
                              branchWidth labels with
                        | none => simp [hBlocks] at hCompile
                        | some blocks =>
                            simp [hBlocks] at hCompile
                            by_cases hCode :
                                Assembly.Compact.blocksCodeMatches?
                                    blocks program.code = true
                            · simp [hCode] at hCompile
                              by_cases hLabels :
                                  Assembly.Compact.labelsConsistent?
                                      blocks labels = true
                              · simp [hLabels] at hCompile
                                by_cases hWellFormed :
                                    program.wellFormed? = true
                                · simp [hWellFormed] at hCompile
                                  by_cases hSentinel :
                                      Assembly.Compact.Program.codeByteLength
                                          program.code + 1 <
                                        18446744073709551616
                                  · simp [hSentinel] at hCompile
                                    cases hCompile
                                    exact
                                      { sourcePCFits := hSourceFits
                                        physicalSource := hPhysical.symm
                                        preparationAligned := hPreparation
                                        preparationSafeIndexed :=
                                          hPreparationSafe
                                        selectedBranchWidth := hWidth
                                        layout := hLayout
                                        emitted := hEmit
                                        blocks := hBlocks
                                        blockCode :=
                                          Assembly.Compact.blocksCodeMatches_of_check
                                            hCode
                                        labelsConsistent :=
                                          Assembly.Compact.labelsConsistent_of_check
                                            hLabels
                                        wellFormed :=
                                          Assembly.Compact.Program.wellFormed_of_check
                                            hWellFormed
                                        bytes := rfl
                                        sentinelFits := hSentinel }
                                  · simp [hSentinel] at hCompile
                                · simp [hWellFormed] at hCompile
                              · simp [hLabels] at hCompile
                            · simp [hCode] at hCompile
      · simp [hPreparationSafe] at hCompile

theorem Artifact.ValidFor.physicalSourcePCFits
    {artifact : Artifact} {source : Assembly.Program}
    (hValid : artifact.ValidFor source) :
    artifact.physicalSource.PCFits := by
  apply Assembly.Program.PCFits.of_byteLength_le hValid.sourcePCFits
  exact
    (Assembly.Compact.alignPreparation?_valid
      hValid.preparationAligned).prepared_byteLength_le_source_byteLength

theorem compile?_preparationBlocksValid
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    (hCompile : compile? source pinnedPushPcs = some artifact) :
    Assembly.Compact.PreparationBlocksValidFrom
      source artifact.physicalSource 0 0 artifact.preparation :=
  Assembly.Compact.alignPreparation?_valid
    (compile?_valid hCompile).preparationAligned

theorem compile?_preparationSafe
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    (hCompile : compile? source pinnedPushPcs = some artifact) :
    PreparationSafe source artifact.physicalSource artifact.preparation := by
  apply preparationSafe_of_check
  rw [← preparationSafeIndexed_eq]
  exact (compile?_valid hCompile).preparationSafeIndexed

theorem Artifact.ValidFor.mem_program_of_mem_block
    {artifact : Artifact} {source : Assembly.Program}
    (hValid : artifact.ValidFor source)
    {block : SourceBlock} (hBlock : block ∈ artifact.blocks)
    {located : Located} (hLocated : located ∈ block.code) :
    located ∈ artifact.program.code := by
  rw [← hValid.blockCode]
  unfold Assembly.Compact.blocksCode
  exact List.mem_flatMap.mpr ⟨block, hBlock, hLocated⟩

theorem compile?_decodingCorrect
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    (hCompile : compile? source pinnedPushPcs = some artifact) :
    Assembly.Compact.DecodingCorrect artifact.program artifact.bytes := by
  have hValid := compile?_valid hCompile
  rw [hValid.bytes]
  exact
    Assembly.Compact.decodingCorrectOfWellFormed
      hValid.wellFormed.1 hValid.wellFormed.2.1
      hValid.wellFormed.2.2.1

theorem compile?_decodingCorrect_with_suffix
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    (hCompile : compile? source pinnedPushPcs = some artifact)
    (suffix : List UInt8) :
    Assembly.Compact.DecodingCorrect artifact.program
      (Assembly.Bytecode.ofList (artifact.bytes.toList ++ suffix)) := by
  have hValid := compile?_valid hCompile
  rw [hValid.bytes]
  simpa [Assembly.Compact.encode, Assembly.Bytecode.ofList] using
    Assembly.Compact.decodingCorrectOfWellFormedWithSuffix
      hValid.wellFormed.1 hValid.wellFormed.2.1
      hValid.wellFormed.2.2.1 suffix

theorem compile?_blocksValid
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    (hCompile : compile? source pinnedPushPcs = some artifact) :
    BlocksValidFrom artifact.pinnedPushPcs artifact.branchWidth
      artifact.labels artifact.physicalSource 0 0 artifact.blocks :=
  emitBlocks?_valid (compile?_valid hCompile).blocks

theorem compile?_initial_boundary
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    (hCompile : compile? source pinnedPushPcs = some artifact) :
    Assembly.Compact.BoundaryPair artifact.blocks
      artifact.physicalSource.byteLength
      (Assembly.Compact.Program.codeByteLength artifact.program.code)
      0 0 := by
  have hArtifact := compile?_valid hCompile
  have hBoundary := (compile?_blocksValid hCompile).initial_boundary
  rw [hArtifact.blockCode] at hBoundary
  exact hBoundary

theorem compile?_physical_labelPc_of_lookup
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {label : Assembly.Label}
    {compactPc : Nat}
    (hCompile : compile? source pinnedPushPcs = some artifact)
    (hLookup :
      Assembly.Compact.lookupLabel? artifact.labels label =
        some compactPc) :
    ∃ sourcePc,
      artifact.physicalSource.labelPc label = some sourcePc := by
  have hLayout := (compile?_valid hCompile).layout
  unfold layout? at hLayout
  have hNames := layoutRev?_names hLayout
  have hMem :=
    Assembly.Compact.lookupLabel?_name_mem hLookup
  rw [hNames] at hMem
  simp only [List.reverse_nil, List.map_nil,
    List.nil_append] at hMem
  exact
    Assembly.Program.labelPc_exists_of_mem_labels
      artifact.physicalSource hMem

theorem BlocksValidFrom.block_of_instrAtPcFrom
    {pinnedPushPcs : List Nat} {branchWidth : Nat}
    {table : LabelTable} {source : Assembly.Program}
    {sourcePc compactPc query pc : Nat} {blocks : List SourceBlock}
    {instr : Assembly.Instr}
    (hValid :
      BlocksValidFrom pinnedPushPcs branchWidth table source
        sourcePc compactPc blocks)
    (hAt :
      Assembly.Program.instrAtPcFrom source sourcePc query =
        some (pc, instr)) :
    ∃ block,
      block ∈ blocks ∧ block.sourcePc = pc ∧
        block.sourceInstr = instr := by
  induction hValid with
  | nil => simp [Assembly.Program.instrAtPcFrom] at hAt
  | @cons head rest sourcePc compactPc compactSize code blocks
      hSize hCode hRest ih =>
      unfold Assembly.Program.instrAtPcFrom at hAt
      split at hAt
      · simp at hAt
        rcases hAt with ⟨hPc, hInstr⟩
        subst pc
        subst instr
        exact
          ⟨{ sourcePc := sourcePc
             compactPc := compactPc
             sourceInstr := head
             code := code }, by simp⟩
      · obtain ⟨block, hMem, hBlockPc, hInstr⟩ := ih hAt
        exact ⟨block, by simp [hMem], hBlockPc, hInstr⟩

theorem BlocksValidFrom.block_of_instrAtPc
    {pinnedPushPcs : List Nat} {branchWidth : Nat}
    {table : LabelTable} {source : Assembly.Program}
    {blocks : List SourceBlock} {query pc : Nat}
    {instr : Assembly.Instr}
    (hValid :
      BlocksValidFrom pinnedPushPcs branchWidth table source 0 0 blocks)
    (hAt : source.instrAtPc query = some (pc, instr)) :
    ∃ block,
      block ∈ blocks ∧ block.sourcePc = pc ∧
        block.sourceInstr = instr := by
  exact hValid.block_of_instrAtPcFrom hAt

theorem compile?_block_of_instrAtPc
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {query pc : Nat}
    {instr : Assembly.Instr}
    (hCompile : compile? source pinnedPushPcs = some artifact)
    (hAt :
      artifact.physicalSource.instrAtPc query = some (pc, instr)) :
    ∃ block,
      block ∈ artifact.blocks ∧ block.sourcePc = pc ∧
        block.sourceInstr = instr :=
  (compile?_blocksValid hCompile).block_of_instrAtPc hAt

theorem compile?_label_block
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {label : Assembly.Label}
    {sourcePc compactPc : Nat}
    (hCompile : compile? source pinnedPushPcs = some artifact)
    (hSource :
      artifact.physicalSource.labelPc label = some sourcePc)
    (hCompact :
      Assembly.Compact.lookupLabel? artifact.labels label =
        some compactPc) :
    ∃ block,
      block ∈ artifact.blocks ∧
        block.sourcePc = sourcePc ∧
          block.compactPc = compactPc ∧
            block.sourceInstr = .label label := by
  have hAt := Assembly.Program.instrAtPc_of_labelPc hSource
  obtain ⟨block, hMem, hBlockPc, hInstr⟩ :=
    compile?_block_of_instrAtPc hCompile hAt
  have hConsistent :=
    (compile?_valid hCompile).labelsConsistent
      block hMem label hInstr
  rw [hCompact] at hConsistent
  exact
    ⟨block, hMem, hBlockPc,
      (Option.some.inj hConsistent).symm, hInstr⟩

theorem compile?_label_lookup_of_physical_labelPc
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {label : Assembly.Label}
    {sourcePc : Nat}
    (hCompile : compile? source pinnedPushPcs = some artifact)
    (hSource :
      artifact.physicalSource.labelPc label = some sourcePc) :
    ∃ compactPc,
      Assembly.Compact.lookupLabel? artifact.labels label =
        some compactPc := by
  have hAt := Assembly.Program.instrAtPc_of_labelPc hSource
  obtain ⟨block, hMem, _hBlockPc, hInstr⟩ :=
    compile?_block_of_instrAtPc hCompile hAt
  exact
    ⟨block.compactPc,
      (compile?_valid hCompile).labelsConsistent
        block hMem label hInstr⟩

theorem compile?_label_boundary
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {label : Assembly.Label}
    {sourceDest compactDest : Nat}
    (hCompile : compile? source pinnedPushPcs = some artifact)
    (hSource :
      artifact.physicalSource.labelPc label = some sourceDest)
    (hCompact :
      Assembly.Compact.lookupLabel? artifact.labels label =
        some compactDest) :
    Assembly.Compact.BoundaryPair artifact.blocks
      artifact.physicalSource.byteLength
      (Assembly.Compact.Program.codeByteLength artifact.program.code)
      sourceDest compactDest := by
  obtain ⟨block, hMem, hBlockSource, hBlockCompact, _hInstr⟩ :=
    compile?_label_block hCompile hSource hCompact
  exact
    Or.inl
      ⟨block, hMem, hBlockSource, hBlockCompact⟩

theorem compile?_source_openStepResult_eq_block
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {block : SourceBlock}
    {state : Assembly.EVMState}
    (hCompile : compile? source pinnedPushPcs = some artifact)
    (hBlock : block ∈ artifact.blocks)
    (hPc :
      state.pc = EvmYul.UInt256.ofNat block.sourcePc) :
    Assembly.InteractionSemantics.Source.openStepResult
        artifact.physicalSource state =
      Assembly.InteractionSemantics.Source.openStepAtResult
        artifact.physicalSource block.sourcePc block.sourceInstr
        state := by
  have hArtifact := compile?_valid hCompile
  have hBlocks := compile?_blocksValid hCompile
  obtain ⟨pre, post, hSource, hBlockPc⟩ :=
    hBlocks.decompose_of_block_mem hBlock
  have hWholeFits := hArtifact.physicalSourcePCFits
  rw [hSource] at hWholeFits ⊢
  have hPreFits :=
    (Assembly.Program.PCFitsFrom.of_append
      (pre := pre) (code := block.sourceInstr :: post)
      (post := []) (by simpa using hWholeFits)).start
  apply
    Assembly.InteractionPreservation.source_openStepResult_at_boundary
      hPreFits
  simpa [Assembly.Program.pcAfter, hBlockPc] using hPc

end Compact

def optimizedCfg? (cfg : TypedCfg.Program) : Option TypedCfg.Program := do
  let q :=
    TypedCfg.Peephole.seamCancelProgramEff
      (TypedCfg.Peephole.peepholeProgram
        (TypedCfg.Peephole.normalizeProgram cfg))
  let _ ← q.compileCertified?
  let chain := TypedCfg.ShuffleCanon.chainCanonProgram q
  match chain.compileCertified? with
  | none => some q
  | some _ =>
      let reordered := TypedCfg.BlockReorder.reorderProgram chain
      match reordered.compileCertified? with
      | none => some chain
      | some _ => some reordered

theorem optimizedCfg?_entry
    {cfg optimized : TypedCfg.Program}
    (hOptimized : optimizedCfg? cfg = some optimized) :
    optimized.entry = cfg.entry := by
  unfold optimizedCfg? at hOptimized
  let q :=
    TypedCfg.Peephole.seamCancelProgramEff
      (TypedCfg.Peephole.peepholeProgram
        (TypedCfg.Peephole.normalizeProgram cfg))
  cases hQ : q.compileCertified? with
  | none =>
      simp [q, hQ] at hOptimized
  | some qArtifact =>
      let chain := TypedCfg.ShuffleCanon.chainCanonProgram q
      cases hChain : chain.compileCertified? with
      | none =>
          simp [q, chain, hQ, hChain] at hOptimized
          subst optimized
          simp [q]
      | some chainArtifact =>
          let reordered := TypedCfg.BlockReorder.reorderProgram chain
          cases hReordered : reordered.compileCertified? with
          | none =>
              simp [q, chain, reordered, hQ, hChain, hReordered]
                at hOptimized
              subst optimized
              simp [chain, q]
          | some reorderedArtifact =>
              simp [q, chain, reordered, hQ, hChain, hReordered]
                at hOptimized
              subst optimized
              simp [reordered, chain, q]

/-!
The executable optimizer probe makes exactly the same fail-open choice as the
production stack artifact.  This theorem packages the already-proved seam,
chain, and reorder preservation layers behind that executable choice.
-/
theorem optimizedCfg?_entry_openRunNPrefix_rel_of_generated
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg optimized : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext
        source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped)
    (hIndependent : cfg.ProgramCounterIndependent)
    {sourceState : Structured.RunState} {cfgState : EVMState}
    (hStateRel :
      Structured.TypedCfgPreservation.StateRel sourceState [] cfgState)
    (hOptimized : optimizedCfg? cfg = some optimized)
    (fuel : Nat) :
    Simulation.Interaction.Rel
      InteractionCongruence.Block.RuntimeOutcomeRel
      (InteractionSemantics.Program.openRunNPrefix
        cfg fuel cfg.entry cfgState)
      (InteractionSemantics.Program.openRunNPrefix
        optimized fuel optimized.entry cfgState) := by
  let q :=
    TypedCfg.Peephole.seamCancelProgramEff
      (TypedCfg.Peephole.peepholeProgram
        (TypedCfg.Peephole.normalizeProgram cfg))
  have hSeamSeed :
      TypedCfg.Peephole.SeamCombinedStepRelEff
        (source := source) (cfg := cfg)
        context.calls cfg.entry cfgState cfgState :=
    TypedCfg.Peephole.seamCombinedStepRelEff_entry_of_generated
      context hStateRel
  have hSeam :=
    TypedCfg.Peephole.openRunNPrefix_seamCombinedEff_congr_of_source
      context hSourceWF hTyped hIndependent
      fuel cfg.entry cfgState cfgState hSeamSeed
  have hChainSeed :
      TypedCfg.Peephole.ChainCombinedStepRelEff
        (source := source) (cfg := cfg)
        context.calls cfg.entry cfgState cfgState :=
    TypedCfg.Peephole.chainCombinedStepRelEff_entry_of_generated
      context hStateRel
  have hChainRel :=
    TypedCfg.Peephole.openRunNPrefix_chainCombinedEff_congr_of_source
      context hSourceWF hTyped hIndependent
      fuel cfg.entry cfgState cfgState hChainSeed
  unfold optimizedCfg? at hOptimized
  cases hQ : q.compileCertified? with
  | none =>
      simp [q, hQ] at hOptimized
  | some qArtifact =>
      let chain := TypedCfg.ShuffleCanon.chainCanonProgram q
      cases hChain : chain.compileCertified? with
      | none =>
          simp [q, chain, hQ, hChain] at hOptimized
          subst optimized
          simpa [q] using hSeam
      | some chainArtifact =>
          let reordered := TypedCfg.BlockReorder.reorderProgram chain
          cases hReordered : reordered.compileCertified? with
          | none =>
              simp [q, chain, reordered, hQ, hChain, hReordered]
                at hOptimized
              subst optimized
              simpa [chain, q] using hChainRel
          | some reorderedArtifact =>
              simp [q, chain, reordered, hQ, hChain, hReordered]
                at hOptimized
              subst optimized
              have hLabels : chain.LabelsUnique :=
                (TypedCfg.Program.compileCertified?_wellTyped hChain).1
              rw [
                TypedCfg.BlockReorder.openRunNPrefix_reorderProgram
                  chain hLabels]
              simpa [chain, q] using hChainRel

theorem optimizedCfg?_compileCertified_exists
    {cfg optimized : TypedCfg.Program}
    (hOptimized : optimizedCfg? cfg = some optimized) :
    ∃ artifact, optimized.compileCertified? = some artifact := by
  unfold optimizedCfg? at hOptimized
  let q :=
    TypedCfg.Peephole.seamCancelProgramEff
      (TypedCfg.Peephole.peepholeProgram
        (TypedCfg.Peephole.normalizeProgram cfg))
  cases hQ : q.compileCertified? with
  | none =>
      simp [q, hQ] at hOptimized
  | some qArtifact =>
      let chain := TypedCfg.ShuffleCanon.chainCanonProgram q
      cases hChain : chain.compileCertified? with
      | none =>
          simp [q, chain, hQ, hChain] at hOptimized
          subst optimized
          exact ⟨qArtifact, hQ⟩
      | some chainArtifact =>
          let reordered := TypedCfg.BlockReorder.reorderProgram chain
          cases hReordered : reordered.compileCertified? with
          | none =>
              simp [q, chain, reordered, hQ, hChain, hReordered]
                at hOptimized
              subst optimized
              exact ⟨chainArtifact, hChain⟩
          | some reorderedArtifact =>
              simp [q, chain, reordered, hQ, hChain, hReordered]
                at hOptimized
              subst optimized
              exact ⟨reorderedArtifact, hReordered⟩

theorem optimizedCfg?_wellTyped
    {cfg optimized : TypedCfg.Program}
    (hOptimized : optimizedCfg? cfg = some optimized) :
    optimized.WellTyped := by
  obtain ⟨artifact, hCompile⟩ :=
    optimizedCfg?_compileCertified_exists hOptimized
  exact TypedCfg.Program.compileCertified?_wellTyped hCompile

theorem optimizedCfg?_programCounterIndependent
    {cfg optimized : TypedCfg.Program}
    (hIndependent : cfg.ProgramCounterIndependent)
    (hOptimized : optimizedCfg? cfg = some optimized) :
    optimized.ProgramCounterIndependent := by
  unfold optimizedCfg? at hOptimized
  let q :=
    TypedCfg.Peephole.seamCancelProgramEff
      (TypedCfg.Peephole.peepholeProgram
        (TypedCfg.Peephole.normalizeProgram cfg))
  have hQIndependent : q.ProgramCounterIndependent := by
    exact
      TypedCfg.Peephole.seamCancelProgramEff_programCounterIndependent
        (TypedCfg.Peephole.peepholeProgram_programCounterIndependent
          (TypedCfg.Peephole.normalizeProgram_programCounterIndependent
            hIndependent))
  cases hQ : q.compileCertified? with
  | none =>
      simp [q, hQ] at hOptimized
  | some qArtifact =>
      let chain := TypedCfg.ShuffleCanon.chainCanonProgram q
      have hChainIndependent : chain.ProgramCounterIndependent :=
        TypedCfg.ShuffleCanon.chainCanonProgram_programCounterIndependent
          hQIndependent
      cases hChain : chain.compileCertified? with
      | none =>
          simp [q, chain, hQ, hChain] at hOptimized
          subst optimized
          exact hQIndependent
      | some chainArtifact =>
          let reordered := TypedCfg.BlockReorder.reorderProgram chain
          have hReorderedIndependent :
              reordered.ProgramCounterIndependent :=
            TypedCfg.BlockReorder.programCounterIndependent_reorderProgram
              chain hChainIndependent
          cases hReordered : reordered.compileCertified? with
          | none =>
              simp [q, chain, reordered, hQ, hChain, hReordered]
                at hOptimized
              subst optimized
              exact hChainIndependent
          | some reorderedArtifact =>
              simp [q, chain, reordered, hQ, hChain, hReordered]
                at hOptimized
              subst optimized
              exact hReorderedIndependent

structure Artifact where
  cfg : TypedCfg.Program
  assembly : Assembly.Program
  compact : Compact.Artifact

def compileCfg? (cfg : TypedCfg.Program) : Option Artifact := do
  let optimized ← optimizedCfg? cfg
  if ReturnAddressLower.Program.tokensUnique? optimized &&
      ReturnAddressLower.Program.targetsUnique? optimized then
    let assembly ← Program.lower? optimized
    let compact ← Compact.compile? assembly
    some { cfg := optimized, assembly, compact }
  else
    none

def compileFunctions? (source : Functions.Program) : Option Artifact := do
  let stack ← Compiler.StackArtifact.compile? source
  compileCfg? stack.cfg

end ReturnAddressProbe
end TypedCfg
end EvmCompiler
