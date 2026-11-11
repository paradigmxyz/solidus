import EvmCompiler.TypedCfg.VirtualStackTracePreservation

/-!
# Pair-level preservation for virtual-stack canonicalisation

The production pass edits only two adjacent blocks at a time.  This file
extracts the proof-relevant facts carried by each `PairChoice` and by the
independent trace certificate.
-/

namespace EvmCompiler
namespace TypedCfg
namespace VirtualStack

open Assembly (EVMState SameRuntimeData)

structure PairChoice.Valid (program : Program)
    (choice : PairChoice) : Prop where
  leftEligible :
    pairEligible choice.sourceLeft choice.sourceRight = true
  linked :
    chainStep program choice.sourceLeft choice.sourceRight = true
  candidate :
    pairCandidate? [choice.sourceLeft, choice.sourceRight] =
      some [choice.targetLeft, choice.targetRight]
  certified :
    certify? [choice.sourceLeft, choice.sourceRight]
        [choice.targetLeft, choice.targetRight] =
      some choice.certificate
  boundary :
    choice.targetLeft.input = choice.sourceLeft.input ∧
      choice.targetLeft.output = choice.targetRight.input ∧
      choice.targetRight.output = choice.sourceRight.output
  cheaper :
    blocksCost [choice.targetLeft, choice.targetRight] <
      blocksCost [choice.sourceLeft, choice.sourceRight]
  savings :
    choice.savings =
      blocksCost [choice.sourceLeft, choice.sourceRight] -
        blocksCost [choice.targetLeft, choice.targetRight]

theorem PairChoice.Valid.leftHasEvent
    {program : Program} {choice : PairChoice}
    (hValid : choice.Valid program) :
    hasRuntimeEvent choice.sourceLeft = true := by
  simpa [pairEligible] using hValid.leftEligible

theorem pairChoice?_valid
    {program : Program} {left right : Block} {choice : PairChoice}
    (hChoice : pairChoice? program left right = some choice) :
    choice.sourceLeft = left ∧
      choice.sourceRight = right ∧
        choice.Valid program := by
  unfold pairChoice? at hChoice
  cases hEligible : pairEligible left right with
  | false =>
      simp [hEligible] at hChoice
  | true =>
      simp only [hEligible, if_true, pure_bind] at hChoice
      cases hLinked : chainStep program left right with
      | false =>
          simp [hLinked] at hChoice
      | true =>
          simp only [hLinked, if_true, pure_bind] at hChoice
          cases hCandidate :
              pairCandidate? [left, right] with
          | none =>
              simp [hCandidate] at hChoice
          | some candidate =>
              simp only [hCandidate, Bind.bind, Option.bind] at hChoice
              cases candidate with
              | nil =>
                  cases hCertificate :
                      certify? [left, right] [] <;>
                    simp [hCertificate] at hChoice
              | cons targetLeft tail =>
                  cases tail with
                  | nil =>
                      cases hCertificate :
                          certify? [left, right] [targetLeft] <;>
                        simp [hCertificate] at hChoice
                  | cons targetRight rest =>
                      cases rest with
                      | cons third rest =>
                          cases hCertificate :
                              certify? [left, right]
                                (targetLeft :: targetRight :: third :: rest) <;>
                            simp [hCertificate] at hChoice
                      | nil =>
                          generalize hCertificate :
                              certify? [left, right]
                                [targetLeft, targetRight] = certOpt at hChoice
                          cases certOpt with
                          | none =>
                              simp at hChoice
                          | some certificate =>
                              by_cases hBoundary :
                                  targetLeft.input = left.input ∧
                                    targetLeft.output = targetRight.input ∧
                                    targetRight.output = right.output
                              · simp [hBoundary] at hChoice
                                by_cases hCheaper :
                                    blocksCost [targetLeft, targetRight] <
                                      blocksCost [left, right]
                                · simp [hCheaper] at hChoice
                                  subst choice
                                  refine ⟨rfl, rfl, ?_⟩
                                  exact
                                    { leftEligible := hEligible
                                      linked := hLinked
                                      candidate := hCandidate
                                      certified := hCertificate
                                      boundary := hBoundary
                                      cheaper := hCheaper
                                      savings := rfl }
                                · simp [hCheaper] at hChoice
                              · simp [hBoundary] at hChoice

theorem scanEdits_mem
    {program : Program} {fuel : Nat} {ordered : List Block}
    {entry : Label × Edit}
    (hEntry : entry ∈ scanEdits program fuel ordered) :
    ∃ left right rest choice,
      left :: right :: rest <:+ ordered ∧
        pairChoice? program left right = some choice ∧
          entry ∈ choice.edits ∧
            ∀ candidate ∈ choice.edits,
              candidate ∈ scanEdits program fuel ordered := by
  induction fuel generalizing ordered with
  | zero =>
      simp [scanEdits] at hEntry
  | succ fuel ih =>
      cases ordered with
      | nil =>
          simp [scanEdits] at hEntry
      | cons left tail =>
          cases tail with
          | nil =>
              simp [scanEdits] at hEntry
          | cons right rest =>
              rw [scanEdits] at hEntry
              cases hChoice : pairChoice? program left right with
              | none =>
                  rw [hChoice] at hEntry
                  obtain ⟨left', right', rest', choice,
                    hSuffix, hPair, hMem, hAll⟩ := ih hEntry
                  exact
                    ⟨left', right', rest', choice,
                      hSuffix.trans (List.suffix_cons left (right :: rest)),
                      hPair, hMem, by
                        intro candidate hCandidate
                        rw [scanEdits, hChoice]
                        exact hAll candidate hCandidate⟩
              | some choice =>
                  rw [hChoice, List.mem_append] at hEntry
                  cases hEntry with
                  | inl hHere =>
                      exact
                        ⟨left, right, rest, choice,
                          List.suffix_refl _, hChoice, hHere, by
                            intro candidate hCandidate
                            rw [scanEdits, hChoice, List.mem_append]
                            exact Or.inl hCandidate⟩
                  | inr hLater =>
                      obtain ⟨left', right', rest', later,
                        hSuffix, hPair, hMem, hAll⟩ := ih hLater
                      exact
                        ⟨left', right', rest', later,
                          hSuffix.trans
                            ((List.suffix_cons right rest).trans
                              (List.suffix_cons left (right :: rest))),
                          hPair, hMem, by
                            intro candidate hCandidate
                            rw [scanEdits, hChoice, List.mem_append]
                            exact Or.inr (hAll candidate hCandidate)⟩

theorem editTable_lookup_choice
    {program : Program} {label : Label} {edit : Edit}
    (hLookup : (editTable program).lookup label = some edit) :
    ∃ ordered left right rest choice,
      program.blocksInLoweringOrder? = some ordered ∧
        left :: right :: rest <:+ ordered ∧
          pairChoice? program left right = some choice ∧
            (label, edit) ∈ choice.edits ∧
              ∀ candidate ∈ choice.edits,
                candidate ∈ editTable program := by
  have hEntry := ShuffleCanon.lookup_mem hLookup
  unfold editTable at hEntry
  split at hEntry
  · simp at hEntry
  · rename_i ordered hOrdered
    obtain ⟨left, right, rest, choice,
      hSuffix, hChoice, hMem, hAll⟩ := scanEdits_mem hEntry
    exact
      ⟨ordered, left, right, rest, choice,
        hOrdered, hSuffix, hChoice, hMem, by
          intro candidate hCandidate
          unfold editTable
          rw [hOrdered]
          exact hAll candidate hCandidate⟩

theorem chainStep_spec
    {program : Program} {left right : Block}
    (hStep : chainStep program left right = true) :
    left.term = .jump right.label ∧
      Peephole.refCount program right.label = 1 ∧
        right.label ≠ program.entry := by
  unfold chainStep at hStep
  exact of_decide_eq_true hStep

theorem editTable_lookup_left
    {program : Program} {label : Label} {choice : PairChoice}
    (hLookup :
      (editTable program).lookup label = some (.left choice)) :
    label = choice.sourceLeft.label ∧
      choice.Valid program ∧
        choice.sourceLeft ∈ program.blocks ∧
          choice.sourceRight ∈ program.blocks := by
  obtain ⟨ordered, left, right, rest, witness,
    hOrdered, hSuffix, hPair, hMem, hAll⟩ :=
      editTable_lookup_choice hLookup
  simp [PairChoice.edits] at hMem
  rcases hMem with ⟨hLabel, hChoice⟩
  subst witness
  obtain ⟨hSourceLeft, hSourceRight, hValid⟩ :=
    pairChoice?_valid hPair
  have hLeftOrdered : left ∈ ordered :=
    hSuffix.subset (by simp)
  have hRightOrdered : right ∈ ordered :=
    hSuffix.subset (by simp)
  have hLeftBlocks : left ∈ program.blocks :=
    (Program.blocksInLoweringOrder?_perm hOrdered).mem_iff.mpr
      hLeftOrdered
  have hRightBlocks : right ∈ program.blocks :=
    (Program.blocksInLoweringOrder?_perm hOrdered).mem_iff.mpr
      hRightOrdered
  subst hSourceLeft
  subst hSourceRight
  exact ⟨hLabel, hValid, hLeftBlocks, hRightBlocks⟩

theorem editTable_lookup_right
    {program : Program} {label : Label} {choice : PairChoice}
    (hLookup :
      (editTable program).lookup label = some (.right choice)) :
    label = choice.sourceRight.label ∧
      choice.Valid program ∧
        choice.sourceLeft ∈ program.blocks ∧
          choice.sourceRight ∈ program.blocks := by
  obtain ⟨ordered, left, right, rest, witness,
    hOrdered, hSuffix, hPair, hMem, hAll⟩ :=
      editTable_lookup_choice hLookup
  simp [PairChoice.edits] at hMem
  rcases hMem with ⟨hLabel, hChoice⟩
  subst witness
  obtain ⟨hSourceLeft, hSourceRight, hValid⟩ :=
    pairChoice?_valid hPair
  have hLeftOrdered : left ∈ ordered :=
    hSuffix.subset (by simp)
  have hRightOrdered : right ∈ ordered :=
    hSuffix.subset (by simp)
  have hLeftBlocks : left ∈ program.blocks :=
    (Program.blocksInLoweringOrder?_perm hOrdered).mem_iff.mpr
      hLeftOrdered
  have hRightBlocks : right ∈ program.blocks :=
    (Program.blocksInLoweringOrder?_perm hOrdered).mem_iff.mpr
      hRightOrdered
  subst hSourceLeft
  subst hSourceRight
  exact ⟨hLabel, hValid, hLeftBlocks, hRightBlocks⟩

theorem pairChoice_edits_keys
    {program : Program} {left right : Block} {choice : PairChoice}
    (hChoice : pairChoice? program left right = some choice) :
    choice.edits.map Prod.fst = [left.label, right.label] := by
  obtain ⟨hLeft, hRight, hValid⟩ :=
    pairChoice?_valid hChoice
  simp [PairChoice.edits, hLeft, hRight]

theorem scanEdits_keys_sublist
    (program : Program) (fuel : Nat) (ordered : List Block) :
    List.Sublist
      ((scanEdits program fuel ordered).map Prod.fst)
      (ordered.map Block.label) := by
  induction fuel generalizing ordered with
  | zero =>
      simp only [scanEdits, List.map_nil]
      exact List.nil_sublist _
  | succ fuel ih =>
      cases ordered with
      | nil =>
          simp only [scanEdits, List.map_nil]
          exact List.nil_sublist _
      | cons left tail =>
          cases tail with
          | nil =>
              simp only [scanEdits, List.map_nil]
              exact List.nil_sublist _
          | cons right rest =>
              rw [scanEdits]
              cases hChoice : pairChoice? program left right with
              | none =>
                  simpa only [List.map_cons] using
                    ((ih (right :: rest)).trans
                      (List.sublist_cons_self left.label _))
              | some choice =>
                  change
                    List.Sublist
                      ((choice.edits ++
                        scanEdits program fuel rest).map Prod.fst)
                      ((left :: right :: rest).map Block.label)
                  rw [List.map_append,
                    pairChoice_edits_keys hChoice]
                  exact
                    List.Sublist.append
                      (List.Sublist.refl [left.label, right.label])
                      (ih rest)

theorem editTable_keys_nodup
    {program : Program} (hUnique : program.LabelsUnique) :
    ((editTable program).map Prod.fst).Nodup := by
  unfold editTable
  cases hOrdered : program.blocksInLoweringOrder? with
  | none =>
      simp
  | some ordered =>
      have hOrderedNodup :
          (ordered.map Block.label).Nodup := by
        have hPermutation :=
          Program.blocksInLoweringOrder?_perm hOrdered
        have hBlockNodup :
            (program.blocks.map Block.label).Nodup :=
          (Program.blockLabels_nodup_iff program).mpr hUnique
        exact
          (hPermutation.map Block.label).nodup_iff.mp
            hBlockNodup
      exact
        (scanEdits_keys_sublist
          program program.blocks.length ordered).nodup
            hOrderedNodup

theorem lookup_editTable_eq_of_mem
    {program : Program} (hUnique : program.LabelsUnique)
    {label : Label} {edit : Edit}
    (hMem : (label, edit) ∈ editTable program) :
    (editTable program).lookup label = some edit :=
  ShuffleCanon.lookup_eq_of_mem_nodup
    (editTable_keys_nodup hUnique) hMem

/-- The right half of a fired pair always has the matching left-half entry.
The edit table is key-unique, so the membership fact extracted from the same
pair witness can be promoted back to a lookup equation. -/
theorem editTable_lookup_left_of_right
    {program : Program} (hUnique : program.LabelsUnique)
    {label : Label} {choice : PairChoice}
    (hLookup :
      (editTable program).lookup label = some (.right choice)) :
    (editTable program).lookup choice.sourceLeft.label =
      some (.left choice) := by
  obtain ⟨ordered, left, right, rest, witness,
    hOrdered, hSuffix, hPair, hMem, hAll⟩ :=
      editTable_lookup_choice hLookup
  simp [PairChoice.edits] at hMem
  rcases hMem with ⟨hLabel, hChoice⟩
  subst witness
  apply lookup_editTable_eq_of_mem hUnique
  exact hAll
    (choice.sourceLeft.label, .left choice)
    (by simp [PairChoice.edits])

theorem editTable_lookup_right_of_left
    {program : Program} (hUnique : program.LabelsUnique)
    {label : Label} {choice : PairChoice}
    (hLookup :
      (editTable program).lookup label = some (.left choice)) :
    (editTable program).lookup choice.sourceRight.label =
      some (.right choice) := by
  obtain ⟨ordered, left, right, rest, witness,
    hOrdered, hSuffix, hPair, hMem, hAll⟩ :=
      editTable_lookup_choice hLookup
  simp [PairChoice.edits] at hMem
  rcases hMem with ⟨hLabel, hChoice⟩
  subst witness
  apply lookup_editTable_eq_of_mem hUnique
  exact hAll
    (choice.sourceRight.label, .right choice)
    (by simp [PairChoice.edits])

/-- A right-edited block has exactly one incoming CFG edge, from its matching
left-edited block.  This is the topology fact that prevents a pending virtual
stack layout from being observed by an unrelated predecessor. -/
theorem target_right_forces_left
    {program : Program} (hUnique : program.LabelsUnique)
    {block : Block} {label : Label} {choice : PairChoice}
    (hBlock : block ∈ program.blocks)
    (hTarget : label ∈ block.term.targets)
    (hRight :
      (editTable program).lookup label = some (.right choice)) :
    block = choice.sourceLeft ∧
      (editTable program).lookup block.label =
        some (.left choice) := by
  obtain ⟨hLabel, hValid, hLeftBlock, hRightBlock⟩ :=
    editTable_lookup_right hRight
  obtain ⟨hLeftTerm, hRefCount, hNotEntry⟩ :=
    chainStep_spec hValid.linked
  have hLeftTarget :
      label ∈ choice.sourceLeft.term.targets := by
    rw [hLabel, hLeftTerm]
    simp [Terminator.targets]
  have hBlockEq : block = choice.sourceLeft := by
    by_contra hNe
    have hTwo :=
      Peephole.two_le_refCount
        hLeftBlock hLeftTarget hBlock hTarget
        (fun hEq => hNe hEq.symm)
    rw [hLabel] at hTwo
    rw [hRefCount] at hTwo
    omega
  subst block
  exact
    ⟨rfl, editTable_lookup_left_of_right hUnique hRight⟩

theorem block_eq_sourceLeft_of_lookup
    {program : Program} (hUnique : program.LabelsUnique)
    {block : Block} {choice : PairChoice}
    (hBlock : block ∈ program.blocks)
    (hLookup :
      (editTable program).lookup block.label =
        some (.left choice)) :
    block = choice.sourceLeft ∧
      choice.Valid program ∧
      choice.sourceRight ∈ program.blocks := by
  obtain ⟨hLabel, hValid, hLeftBlock, hRightBlock⟩ :=
    editTable_lookup_left hLookup
  have hBlockFind :=
    Program.findBlock?_eq_some_of_mem hUnique hBlock
  have hLeftFind :=
    Program.findBlock?_eq_some_of_mem hUnique hLeftBlock
  rw [hLabel] at hBlockFind
  have hEq : block = choice.sourceLeft :=
    Option.some.inj (hBlockFind.symm.trans hLeftFind)
  exact ⟨hEq, hValid, hRightBlock⟩

theorem block_eq_sourceRight_of_lookup
    {program : Program} (hUnique : program.LabelsUnique)
    {block : Block} {choice : PairChoice}
    (hBlock : block ∈ program.blocks)
    (hLookup :
      (editTable program).lookup block.label =
        some (.right choice)) :
    block = choice.sourceRight ∧
      choice.Valid program ∧
      choice.sourceLeft ∈ program.blocks := by
  obtain ⟨hLabel, hValid, hLeftBlock, hRightBlock⟩ :=
    editTable_lookup_right hLookup
  have hBlockFind :=
    Program.findBlock?_eq_some_of_mem hUnique hBlock
  have hRightFind :=
    Program.findBlock?_eq_some_of_mem hUnique hRightBlock
  rw [hLabel] at hBlockFind
  have hEq : block = choice.sourceRight :=
    Option.some.inj (hBlockFind.symm.trans hRightFind)
  exact ⟨hEq, hValid, hLeftBlock⟩

theorem target_not_right_of_no_left
    {program : Program} (hUnique : program.LabelsUnique)
    {block : Block}
    (hBlock : block ∈ program.blocks)
    (hNoLeft :
      ∀ choice,
        (editTable program).lookup block.label ≠
          some (.left choice))
    {label : Label}
    (hTarget : label ∈ block.term.targets) :
    ∀ choice,
      (editTable program).lookup label ≠
        some (.right choice) := by
  intro choice hRight
  exact
    hNoLeft choice
      (target_right_forces_left
        hUnique hBlock hTarget hRight).2

theorem findBlock?_canonProgram (program : Program) (label : Label) :
    (canonProgramOnce program).findBlock? label =
      (program.findBlock? label).map
        (applyEdit (editTable program)) := by
  simp only [canonProgramOnce, Program.findBlock?]
  induction program.blocks with
  | nil => rfl
  | cons block rest ih =>
      simp only [List.map_cons, List.find?_cons, applyEdit_label]
      by_cases hLabel : (block.label == label) = true
      · simp [hLabel]
      · simp only [hLabel, Bool.false_eq_true, if_false]
        exact ih

theorem certifyPair_trace_sound
    {sourceLeft sourceRight targetLeft targetRight : Block}
    {certificate : Certificate}
    (hCertified :
      certify? [sourceLeft, sourceRight]
          [targetLeft, targetRight] =
        some certificate) :
    ∃ sourceMiddle targetMiddle sourceFinal targetFinal : TraceState,
      sourceLeft.label = targetLeft.label ∧
        sourceLeft.term = targetLeft.term ∧
        traceBody sourceLeft.body
            { stack := List.range sourceLeft.input.length
              nextAtom := sourceLeft.input.length } =
          some sourceMiddle ∧
        traceBody targetLeft.body
            { stack := List.range sourceLeft.input.length
              nextAtom := sourceLeft.input.length } =
          some targetMiddle ∧
        sourceMiddle.events = targetMiddle.events ∧
        sourceMiddle.nextAtom = targetMiddle.nextAtom ∧
        sourceRight.label = targetRight.label ∧
        sourceRight.term = targetRight.term ∧
        traceBody sourceRight.body
            { stack := sourceMiddle.stack
              nextAtom := sourceMiddle.nextAtom } =
          some sourceFinal ∧
        traceBody targetRight.body
            { stack := targetMiddle.stack
              nextAtom := sourceMiddle.nextAtom } =
          some targetFinal ∧
        sourceFinal.events = targetFinal.events ∧
        sourceFinal.nextAtom = targetFinal.nextAtom ∧
        sourceFinal.stack = targetFinal.stack := by
  unfold certify? at hCertified
  simp only [List.head?_cons, Bind.bind, Option.bind,
    List.length_range] at hCertified
  have hDecomp :
      ∃ result,
        certifyBlocks? [sourceLeft, sourceRight]
            [targetLeft, targetRight]
            { source := List.range sourceLeft.input.length
              target := List.range sourceLeft.input.length
              nextAtom := sourceLeft.input.length } =
          some result ∧
        (if result.2.source = result.2.target then
            some { blocks := result.1, final := result.2 }
          else
            none) =
          some certificate := by
    cases hBlocks :
        certifyBlocks? [sourceLeft, sourceRight]
          [targetLeft, targetRight]
          { source := List.range sourceLeft.input.length
            target := List.range sourceLeft.input.length
            nextAtom := sourceLeft.input.length } with
    | none =>
        rw [hBlocks] at hCertified
        simp at hCertified
    | some result =>
        rw [hBlocks] at hCertified
        refine ⟨result, rfl, ?_⟩
        simpa using hCertified
  obtain ⟨result, hBlocks, hFinish⟩ := hDecomp
  rcases result with ⟨traces, final⟩
  by_cases hLeftMeta :
      sourceLeft.label = targetLeft.label ∧
        sourceLeft.term = targetLeft.term
  · rw [certifyBlocks?, if_pos hLeftMeta] at hBlocks
    simp only [pure_bind] at hBlocks
    obtain ⟨sourceMiddle, hSourceMiddle, hBlocks⟩ :=
      Option.bind_eq_some_iff.mp hBlocks
    obtain ⟨targetMiddle, hTargetMiddle, hBlocks⟩ :=
      Option.bind_eq_some_iff.mp hBlocks
    by_cases hMiddleMeta :
        sourceMiddle.events = targetMiddle.events ∧
          sourceMiddle.nextAtom = targetMiddle.nextAtom
    · simp only [hMiddleMeta, if_true, pure_bind] at hBlocks
      obtain ⟨tailResult, hTail, hCombine⟩ :=
        Option.bind_eq_some_iff.mp hBlocks
      by_cases hRightMeta :
          sourceRight.label = targetRight.label ∧
            sourceRight.term = targetRight.term
      · rw [certifyBlocks?, if_pos hRightMeta] at hTail
        simp only [pure_bind] at hTail
        obtain ⟨sourceFinal, hSourceFinal, hTail⟩ :=
          Option.bind_eq_some_iff.mp hTail
        obtain ⟨targetFinal, hTargetFinal, hTail⟩ :=
          Option.bind_eq_some_iff.mp hTail
        by_cases hFinalMeta :
            sourceFinal.events = targetFinal.events ∧
              sourceFinal.nextAtom = targetFinal.nextAtom
        · simp [hFinalMeta, certifyBlocks?] at hTail
          rw [← hTail] at hCombine
          simp only [Option.some.injEq, Prod.mk.injEq] at hCombine
          have hFinalEq :
              final =
                { source := sourceFinal.stack
                  target := targetFinal.stack
                  nextAtom := sourceFinal.nextAtom } :=
            by simpa [hFinalMeta.2] using hCombine.2.symm
          subst final
          have hFinalStack :
              sourceFinal.stack = targetFinal.stack := by
            by_contra hNot
            simp [hNot] at hFinish
          exact
            ⟨sourceMiddle, targetMiddle, sourceFinal, targetFinal,
              hLeftMeta.1, hLeftMeta.2,
              hSourceMiddle, hTargetMiddle,
              hMiddleMeta.1, hMiddleMeta.2,
              hRightMeta.1, hRightMeta.2,
              (by simpa [hMiddleMeta.2] using hSourceFinal),
              (by simpa [hMiddleMeta.2] using hTargetFinal),
              hFinalMeta.1, hFinalMeta.2, hFinalStack⟩
        · simp [hFinalMeta] at hTail
      · rw [certifyBlocks?, if_neg hRightMeta] at hTail
        simp at hTail
    · simp [hMiddleMeta] at hBlocks
  · rw [certifyBlocks?, if_neg hLeftMeta] at hBlocks
    simp at hBlocks

def PairPending (choice : PairChoice)
    (source target : EVMState) : Prop :=
  ∃ sourceMiddle targetMiddle : TraceState,
    ∃ values : ValueTable, ∃ hidden : EvmYul.Stack Word,
      traceBody choice.sourceLeft.body
          { stack := List.range choice.sourceLeft.input.length
            nextAtom := choice.sourceLeft.input.length } =
        some sourceMiddle ∧
      traceBody choice.targetLeft.body
          { stack := List.range choice.sourceLeft.input.length
            nextAtom := choice.sourceLeft.input.length } =
        some targetMiddle ∧
      sourceMiddle.nextAtom = targetMiddle.nextAtom ∧
      values.length = sourceMiddle.nextAtom ∧
      TableStateRel values hidden
        sourceMiddle.stack targetMiddle.stack source target

theorem traceStep_stack_length_of_type
    {instr : Instr} {input output : Shape}
    {before after : TraceState}
    (hType : Instr.type? instr input = some output)
    (hTrace : traceStep instr before = some after)
    (hLength : before.stack.length = input.length) :
    after.stack.length = output.length := by
  cases instr with
  | push value =>
      simp only [traceStep, Option.some.injEq] at hTrace
      subst after
      simp [Instr.type?] at hType
      subst output
      simp [hLength, Shape.length]
  | returnToken value =>
      simp only [traceStep, Option.some.injEq] at hTrace
      subst after
      simp [Instr.type?] at hType
      subst output
      simp [hLength, Shape.length]
  | prim op =>
      unfold traceStep at hTrace
      by_cases hAllowed : primAllowed op = true
      · simp only [hAllowed, if_true, pure_bind] at hTrace
        cases hArity : op.stackArity? with
        | none => simp [hArity] at hTrace
        | some arity =>
            rcases arity with ⟨inputs, outputs⟩
            by_cases hInputs : inputs ≤ before.stack.length
            · simp [hArity, hInputs] at hTrace
              subst after
              have hTypeLength :=
                Instr.length_of_type?_prim hArity hType
              rw [atomRangeFrom_eq_range']
              simp only [List.length_append,
                List.length_range',
                List.length_map, List.length_range,
                List.length_drop]
              omega
            · simp [hArity, hInputs] at hTrace
      · have hFalse : primAllowed op = false :=
          Bool.eq_false_of_not_eq_true hAllowed
        simp [hFalse] at hTrace
  | pop =>
      simp only [traceStep] at hTrace
      cases hStack : before.stack with
      | nil => simp [hStack] at hTrace
      | cons head tail =>
          simp [hStack] at hTrace
          subst after
          have hTypeLength := Instr.length_of_type?_pop hType
          simp [hStack] at hLength
          simp
          omega
  | dup depth =>
      simp only [traceStep] at hTrace
      cases hDup : sourceDup? depth before.stack with
      | none => simp [hDup] at hTrace
      | some stack =>
          simp [hDup] at hTrace
          subst after
          unfold sourceDup? at hDup
          split at hDup
          · rename_i hDepth
            cases hGet : before.stack[depth]? with
            | none => simp [hGet] at hDup
            | some atom =>
                simp [hGet] at hDup
                subst stack
                have hTypeLength := Instr.length_of_type?_dup hType
                simp
                omega
          · simp at hDup
  | swap depth =>
      simp only [traceStep] at hTrace
      cases hSwap : sourceSwap? depth before.stack with
      | none => simp [hSwap] at hTrace
      | some stack =>
          simp [hSwap] at hTrace
          subst after
          unfold sourceSwap? at hSwap
          split at hSwap
          · simp only [Option.some.injEq] at hSwap
            subst stack
            have hTypeLength := Instr.length_of_type?_swap hType
            dsimp
            change (applySwap depth before.stack).length =
              output.length
            simp only [applySwap, ShuffleCanon.length_applySwap]
            rw [hLength]
            exact hTypeLength.2.2.symm
          · simp at hSwap
  | bindLocals offset names =>
      simp only [traceStep, Option.some.injEq] at hTrace
      subst after
      rw [Instr.length_of_type?_bindLocals hType, hLength]
  | bindScratch baseDepth name slot =>
      simp only [traceStep, Option.some.injEq] at hTrace
      subst after
      rw [Instr.length_of_type?_bindScratch hType, hLength]
  | relabel target =>
      simp only [traceStep, Option.some.injEq] at hTrace
      subst after
      rw [Instr.length_of_type?_relabel hType, hLength]
  | unwind target =>
      simp [traceStep] at hTrace

theorem traceBody_stack_length_of_bodyType
    {body : List Instr} {input output : Shape}
    {before after : TraceState}
    (hType : Block.bodyType? body input = some output)
    (hTrace : traceBody body before = some after)
    (hLength : before.stack.length = input.length) :
    after.stack.length = output.length := by
  induction body generalizing input before with
  | nil =>
      simp only [Block.bodyType?, Option.some.injEq] at hType
      simp only [traceBody, Option.some.injEq] at hTrace
      subst output
      subst after
      exact hLength
  | cons instr rest ih =>
      simp only [Block.bodyType?, traceBody] at hType hTrace
      obtain ⟨middleShape, hInstrType, hRestType⟩ :=
        Option.bind_eq_some_iff.mp hType
      obtain ⟨middleTrace, hInstrTrace, hRestTrace⟩ :=
        Option.bind_eq_some_iff.mp hTrace
      exact ih hRestType hRestTrace
        (traceStep_stack_length_of_type
          hInstrType hInstrTrace hLength)

theorem PairPending.targetRight_realizes
    {program : Program} {choice : PairChoice}
    {source target : EVMState}
    (hValid : choice.Valid program)
    (hTargetType :
      Block.bodyType? choice.targetLeft.body
          choice.targetLeft.input =
        some choice.targetLeft.output)
    (hPending : PairPending choice source target) :
    StackRealizes choice.targetRight.input target := by
  obtain ⟨sourceMiddle, targetMiddle, values, hidden,
    hSourceTrace, hTargetTrace, hNext, hValues, hTable⟩ :=
    hPending
  obtain ⟨certSourceMiddle, certTargetMiddle,
    certSourceFinal, certTargetFinal,
    hLeftLabel, hLeftTerm, hCertSourceTrace,
    hCertTargetTrace, hMiddleEvents, hMiddleNext,
    hRightLabel, hRightTerm, hCertSourceFinal,
    hCertTargetFinal, hFinalEvents, hFinalNext,
    hFinalStack⟩ :=
    certifyPair_trace_sound hValid.certified
  have hTargetMiddle : targetMiddle = certTargetMiddle := by
    exact Option.some.inj
      (hTargetTrace.symm.trans hCertTargetTrace)
  subst certTargetMiddle
  have hTraceLength :
      targetMiddle.stack.length =
        choice.targetLeft.output.length :=
    traceBody_stack_length_of_bodyType
      hTargetType hTargetTrace (by
        rw [List.length_range, hValid.boundary.1])
  have hReal := hTable.targetRealizes
  unfold StackRealizes
  unfold StateRealizes at hReal
  rw [hReal, List.length_append, List.length_map,
    ← hValid.boundary.2.1, ← hTraceLength]
  omega

/-- The inter-block invariant: only the right half of a fired pair may observe
the certified pending atom layout.  Every other label is fully synchronized. -/
def PairStepRel (program : Program) (label : Label)
    (source target : EVMState) : Prop :=
  match (editTable program).lookup label with
  | some (.right choice) => PairPending choice source target
  | _ => SameRuntimeData source target

theorem stackRealizes_canonProgramOnce_of_pairStepRel
    {program : Program} {label : Label}
    {source middle : EVMState} {block : Block}
    (hUnique : program.LabelsUnique)
    (hMiddleTyped : (canonProgramOnce program).WellTyped)
    (hSourceRealizes :
      ∀ original,
        program.findBlock? label = some original →
          (∀ choice,
            (editTable program).lookup original.label ≠
              some (.right choice)) →
          StackRealizes original.input source)
    (hStep : PairStepRel program label source middle)
    (hFind :
      (canonProgramOnce program).findBlock? label = some block) :
    StackRealizes block.input middle := by
  rw [findBlock?_canonProgram] at hFind
  cases hSourceFind : program.findBlock? label with
  | none =>
      simp [hSourceFind] at hFind
  | some original =>
      rw [hSourceFind] at hFind
      simp only [Option.map_some, Option.some.injEq] at hFind
      subst block
      have hOriginalLabel : original.label = label := by
        unfold Program.findBlock? at hSourceFind
        have hFound := List.find?_some hSourceFind
        simpa using hFound
      have hOriginalMem : original ∈ program.blocks := by
        unfold Program.findBlock? at hSourceFind
        exact List.mem_of_find?_eq_some hSourceFind
      cases hLookup :
          (editTable program).lookup original.label with
      | none =>
          have hRealSource :=
            hSourceRealizes original hSourceFind (by
              intro choice hRight
              rw [hLookup] at hRight
              contradiction)
          have hSame : SameRuntimeData source middle := by
            simpa only [PairStepRel, ← hOriginalLabel, hLookup]
              using hStep
          unfold StackRealizes at hRealSource ⊢
          simp only [applyEdit, hLookup]
          rw [← SameRuntimeData.stack_eq hSame]
          exact hRealSource
      | some edit =>
          cases edit with
          | left choice =>
              have hRealSource :=
                hSourceRealizes original hSourceFind (by
                  intro other hRight
                  rw [hLookup] at hRight
                  cases hRight)
              obtain ⟨hOriginalEq, hValid, hRightBlock⟩ :=
                block_eq_sourceLeft_of_lookup
                  hUnique hOriginalMem hLookup
              have hSame : SameRuntimeData source middle := by
                simpa only [PairStepRel, ← hOriginalLabel, hLookup]
                  using hStep
              subst original
              unfold StackRealizes at hRealSource ⊢
              simp only [applyEdit, hLookup]
              rw [hValid.boundary.1,
                ← SameRuntimeData.stack_eq hSame]
              exact hRealSource
          | right choice =>
              obtain ⟨hOriginalEq, hValid, hLeftBlock⟩ :=
                block_eq_sourceRight_of_lookup
                  hUnique hOriginalMem hLookup
              have hPending : PairPending choice source middle := by
                simpa only [PairStepRel, ← hOriginalLabel, hLookup]
                  using hStep
              have hLeftLookup :
                  (editTable program).lookup
                      choice.sourceLeft.label =
                    some (.left choice) :=
                editTable_lookup_left_of_right hUnique hLookup
              have hApplied :
                  applyEdit (editTable program)
                      choice.sourceLeft =
                    { choice.sourceLeft with
                      input := choice.targetLeft.input
                      body := choice.targetLeft.body
                      output := choice.targetLeft.output } := by
                unfold applyEdit
                rw [hLeftLookup]
              have hTargetLeftMem :
                  applyEdit (editTable program)
                      choice.sourceLeft ∈
                    (canonProgramOnce program).blocks := by
                rw [canonProgramOnce_blocks, List.mem_map]
                exact ⟨choice.sourceLeft, hLeftBlock, rfl⟩
              have hTargetLeftTyped :=
                Peephole.blockWellTyped_of_mem
                  hMiddleTyped.2.1 hTargetLeftMem
              have hTargetBodyType :
                  Block.bodyType? choice.targetLeft.body
                      choice.targetLeft.input =
                    some choice.targetLeft.output := by
                rw [hApplied] at hTargetLeftTyped
                exact hTargetLeftTyped.1
              subst original
              simp only [applyEdit, hLookup]
              exact hPending.targetRight_realizes
                hValid hTargetBodyType

abbrev PairRuntimeOutcomeRel :
    Except EVMException TypedCfg.Outcome →
      Except EVMException TypedCfg.Outcome → Prop :=
  InteractionCongruence.Block.RuntimeOutcomeRel

/-- A program step either lands synchronously at the next label under the
label-indexed pair invariant, or terminates with an ordinary runtime-related
non-jump outcome. -/
def PairOutcomeRel (program : Program) :
    Except EVMException TypedCfg.Outcome →
      Except EVMException TypedCfg.Outcome → Prop :=
  fun source target =>
    (∃ (next : Label) (sourceState targetState : EVMState),
      source = .ok (.jump next sourceState) ∧
        target = .ok (.jump next targetState) ∧
        PairStepRel program next sourceState targetState)
    ∨ (PairRuntimeOutcomeRel source target ∧
        ∀ (next : Label) (state : EVMState),
          source ≠ .ok (.jump next state))

theorem editTable_entry_ne_right
    {program : Program} {choice : PairChoice} :
    (editTable program).lookup program.entry ≠
      some (.right choice) := by
  intro hRight
  obtain ⟨hLabel, hValid, hLeftBlock, hRightBlock⟩ :=
    editTable_lookup_right hRight
  obtain ⟨hTerm, hRefCount, hNotEntry⟩ :=
    chainStep_spec hValid.linked
  exact hNotEntry hLabel.symm

theorem pairStepRel_entry (program : Program) (state : EVMState) :
    PairStepRel program program.entry state state := by
  unfold PairStepRel
  cases hLookup : (editTable program).lookup program.entry with
  | none =>
      exact SameRuntimeData.refl state
  | some edit =>
      cases edit with
      | left choice =>
          exact SameRuntimeData.refl state
      | right choice =>
          exact absurd hLookup editTable_entry_ne_right

/-- Every edit-table label names an original block. -/
theorem findBlock?_ne_none_of_editTable_lookup
    {program : Program} (hUnique : program.LabelsUnique)
    {label : Label} {edit : Edit}
    (hLookup : (editTable program).lookup label = some edit) :
    program.findBlock? label ≠ none := by
  cases edit with
  | left choice =>
      obtain ⟨hLabel, hValid, hLeftBlock, hRightBlock⟩ :=
        editTable_lookup_left hLookup
      rw [hLabel,
        Program.findBlock?_eq_some_of_mem hUnique hLeftBlock]
      simp
  | right choice =>
      obtain ⟨hLabel, hValid, hLeftBlock, hRightBlock⟩ :=
        editTable_lookup_right hLookup
      rw [hLabel,
        Program.findBlock?_eq_some_of_mem hUnique hRightBlock]
      simp

/-- A pending left-body result jumps into the matching right-half invariant. -/
theorem pairOutcome_jump_pending
    {program : Program} {choice : PairChoice}
    {next : Label} {sourceShape targetShape : Shape}
    {source target : EVMState}
    (hRight :
      (editTable program).lookup next = some (.right choice))
    (hPending : PairPending choice source target) :
    PairOutcomeRel program
      (TypedCfg.Block.runTermChecked sourceShape
        (.jump next) source)
      (TypedCfg.Block.runTermChecked targetShape
        (.jump next) target) := by
  rw [TypedCfg.Block.runTermChecked_jump,
    TypedCfg.Block.runTermChecked_jump,
    TypedCfg.Block.runTerm, TypedCfg.Block.runTerm]
  refine Or.inl ⟨next, source, target, rfl, rfl, ?_⟩
  unfold PairStepRel
  rw [hRight]
  exact hPending

/-- Re-synchronized states stay synchronized through a preserved terminator,
provided that terminator does not enter another pair's right half. -/
theorem pairOutcome_srd_resync
    {program : Program} {block : Block}
    {source target : EVMState}
    (hTargets :
      ∀ (label : Label), label ∈ block.term.targets →
        ∀ choice,
          (editTable program).lookup label ≠
            some (.right choice))
    (hState : SameRuntimeData source target) :
    Simulation.Interaction.Rel (PairOutcomeRel program)
      (match
          TypedCfg.Block.runTermChecked
            block.output block.term source with
        | .ok outcome => pure outcome
        | .error error => throw error)
      (match
          TypedCfg.Block.runTermChecked
            block.output block.term target with
        | .ok outcome => pure outcome
        | .error error => throw error) := by
  have hChecked :=
    InteractionCongruence.Block.runTermChecked_runtimeRel
      (shape := block.output) (term := block.term) hState
  cases hSource :
      TypedCfg.Block.runTermChecked
        block.output block.term source with
  | error sourceError =>
      cases hTarget :
          TypedCfg.Block.runTermChecked
            block.output block.term target with
      | error targetError =>
          rw [hSource, hTarget] at hChecked
          cases hChecked with
          | error hError =>
              subst targetError
              exact Simulation.Interaction.Rel.done
                (Or.inr
                  ⟨Simulation.Interaction.ExceptRel.error
                      (Eq.refl sourceError),
                    by simp⟩)
      | ok targetOutcome =>
          rw [hSource, hTarget] at hChecked
          cases hChecked
  | ok sourceOutcome =>
      cases hTarget :
          TypedCfg.Block.runTermChecked
            block.output block.term target with
      | error targetError =>
          rw [hSource, hTarget] at hChecked
          cases hChecked
      | ok targetOutcome =>
          rw [hSource, hTarget] at hChecked
          refine Simulation.Interaction.Rel.done ?_
          cases hChecked with
          | ok hRuntime =>
              cases hRuntime with
              | jump label hAfter =>
                  have hTargetMem :
                      label ∈ block.term.targets :=
                    Peephole.runTerm_jump_mem_targets
                      (TypedCfg.Block.runTerm_eq_of_runTermChecked_eq_ok
                        hSource)
                  refine
                    Or.inl
                      ⟨label, _, _, rfl, rfl, ?_⟩
                  unfold PairStepRel
                  cases hLookup :
                      (editTable program).lookup label with
                  | none =>
                      exact hAfter
                  | some edit =>
                      cases edit with
                      | left choice =>
                          exact hAfter
                      | right choice =>
                          exact absurd hLookup
                            (hTargets label hTargetMem choice)
              | fallthrough hAfter =>
                  exact Or.inr
                    ⟨Simulation.Interaction.ExceptRel.ok
                        (.fallthrough hAfter),
                      by simp⟩
              | returnDispatch hAfter =>
                  exact Or.inr
                    ⟨Simulation.Interaction.ExceptRel.ok
                        (.returnDispatch hAfter),
                      by simp⟩
              | halt kind hAfter =>
                  exact Or.inr
                    ⟨Simulation.Interaction.ExceptRel.ok
                        (.halt kind hAfter),
                      by simp⟩
              | invalid hAfter =>
                  exact Or.inr
                    ⟨Simulation.Interaction.ExceptRel.ok
                        (.invalid hAfter),
                      by simp⟩

theorem openRunBody_pair_left
    {program : Program} {choice : PairChoice}
    (hValid : choice.Valid program)
    {source target : EVMState}
    (hCount :
      choice.sourceLeft.input.length ≤ source.stack.length)
    (hState : SameRuntimeData source target)
    (hSourceType :
      Block.bodyType? choice.sourceLeft.body
          choice.sourceLeft.input =
        some choice.sourceLeft.output)
    (hTargetType :
      Block.bodyType? choice.targetLeft.body
          choice.targetLeft.input =
        some choice.targetLeft.output) :
    Simulation.Interaction.Rel
      (Simulation.Interaction.ExceptRel
        (fun sourceError targetError : EVMException =>
          sourceError = targetError)
        (fun sourceAfter targetAfter =>
          PairPending choice sourceAfter.1 targetAfter.1 ∧
            sourceAfter.2 = choice.sourceLeft.output ∧
            targetAfter.2 = choice.targetLeft.output))
      (InteractionSemantics.Block.openRunBody
        choice.sourceLeft.body choice.sourceLeft.input source)
      (InteractionSemantics.Block.openRunBody
        choice.targetLeft.body choice.targetLeft.input target) := by
  rw [hValid.boundary.1] at hTargetType ⊢
  obtain ⟨sourceMiddle, targetMiddle, sourceFinal, targetFinal,
    hLeftLabel, hLeftTerm, hSourceTrace, hTargetTrace,
    hEvents, hNext, hRightLabel, hRightTerm,
    hSourceFinalTrace, hTargetFinalTrace,
    hFinalEvents, hFinalNext, hFinalStack⟩ :=
      certifyPair_trace_sound hValid.certified
  obtain ⟨values, hidden, hValuesLength, hTable⟩ :=
    TableStateRel.range_of_sameRuntimeData
      choice.sourceLeft.input.length hCount hState
  have hBody :=
    openRunBody_trace_pair
      choice.sourceLeft.body choice.targetLeft.body
      hSourceTrace hTargetTrace rfl hEvents
      hValuesLength.symm hValuesLength.symm
      (by simpa [hValuesLength] using
        atomsBelow_range choice.sourceLeft.input.length)
      (by simpa [hValuesLength] using
        atomsBelow_range choice.sourceLeft.input.length)
      hTable hSourceType
      hTargetType
  refine Simulation.Interaction.Rel.mono hBody ?_
  intro sourceAfter targetAfter hAfter
  cases hAfter with
  | error hError =>
      exact Simulation.Interaction.ExceptRel.error hError
  | ok hPost =>
      rcases hPost with
        ⟨hBodyPost, hSourceOutput, hTargetOutput⟩
      rcases hBodyPost with
        ⟨afterValues, hAfterLength, hAfterNext, hAfterTable⟩
      apply Simulation.Interaction.ExceptRel.ok
      exact
        ⟨⟨sourceMiddle, targetMiddle, afterValues, hidden,
            hSourceTrace, hTargetTrace, hAfterNext,
            hAfterLength, hAfterTable⟩,
          hSourceOutput, hTargetOutput⟩

theorem openRunBody_pair_right
    {program : Program} {choice : PairChoice}
    (hValid : choice.Valid program)
    {source target : EVMState}
    (hPending : PairPending choice source target)
    (hSourceType :
      Block.bodyType? choice.sourceRight.body
          choice.sourceRight.input =
        some choice.sourceRight.output)
    (hTargetType :
      Block.bodyType? choice.targetRight.body
          choice.targetRight.input =
        some choice.targetRight.output) :
    Simulation.Interaction.Rel
      (Simulation.Interaction.ExceptRel
        (fun sourceError targetError : EVMException =>
          sourceError = targetError)
        (fun sourceAfter targetAfter =>
          SameRuntimeData sourceAfter.1 targetAfter.1 ∧
            sourceAfter.2 = choice.sourceRight.output ∧
            targetAfter.2 = choice.targetRight.output))
      (InteractionSemantics.Block.openRunBody
        choice.sourceRight.body choice.sourceRight.input source)
      (InteractionSemantics.Block.openRunBody
        choice.targetRight.body choice.targetRight.input target) := by
  rcases hPending with
    ⟨sourceMiddle, targetMiddle, values, hidden,
      hSourceMiddle, hTargetMiddle, hMiddleNext,
      hValuesLength, hTable⟩
  obtain ⟨certSourceMiddle, certTargetMiddle,
    sourceFinal, targetFinal,
    hLeftLabel, hLeftTerm,
    hCertSourceMiddle, hCertTargetMiddle,
    hMiddleEvents, hCertMiddleNext,
    hRightLabel, hRightTerm,
    hSourceFinal, hTargetFinal,
    hFinalEvents, hFinalNext, hFinalStack⟩ :=
      certifyPair_trace_sound hValid.certified
  have hSourceMiddleEq :
      sourceMiddle = certSourceMiddle := by
    exact Option.some.inj
      (hSourceMiddle.symm.trans hCertSourceMiddle)
  have hTargetMiddleEq :
      targetMiddle = certTargetMiddle := by
    exact Option.some.inj
      (hTargetMiddle.symm.trans hCertTargetMiddle)
  subst certSourceMiddle
  subst certTargetMiddle
  have hSourceBelow :
      AtomsBelow values.length sourceMiddle.stack := by
    have hBelow :=
      traceBody_atomsBelow hSourceMiddle
        (atomsBelow_range choice.sourceLeft.input.length)
    simpa [hValuesLength] using hBelow
  have hTargetBelow :
      AtomsBelow values.length targetMiddle.stack := by
    have hBelow :=
      traceBody_atomsBelow hTargetMiddle
        (atomsBelow_range choice.sourceLeft.input.length)
    simpa [hValuesLength, hMiddleNext] using hBelow
  have hBody :=
    openRunBody_trace_pair
      choice.sourceRight.body choice.targetRight.body
      hSourceFinal hTargetFinal rfl hFinalEvents
      hValuesLength.symm
      (by simpa [hMiddleNext] using hValuesLength.symm)
      hSourceBelow hTargetBelow hTable
      hSourceType hTargetType
  refine Simulation.Interaction.Rel.mono hBody ?_
  intro sourceAfter targetAfter hAfter
  cases hAfter with
  | error hError =>
      exact Simulation.Interaction.ExceptRel.error hError
  | ok hPost =>
      rcases hPost with
        ⟨hBodyPost, hSourceOutput, hTargetOutput⟩
      rcases hBodyPost with
        ⟨afterValues, hAfterLength, hAfterNext, hAfterTable⟩
      apply Simulation.Interaction.ExceptRel.ok
      refine ⟨?_, hSourceOutput, hTargetOutput⟩
      apply TableStateRel.resync
      simpa [hFinalStack] using hAfterTable

/-- Block-level congruence for the certified pair transform.  The left edit
creates the pending relation, the right edit discharges it, and all untouched
blocks remain in `SameRuntimeData`. -/
theorem openRun_pair_congr
    {program : Program}
    (hUnique : program.LabelsUnique)
    (hSourceTyped : program.WellTyped)
    (hTargetTyped : (canonProgramOnce program).WellTyped)
    {block : Block}
    (hBlock : block ∈ program.blocks)
    (hIndependent : block.ProgramCounterIndependent)
    {source target : EVMState}
    (hStep :
      PairStepRel program block.label source target)
    (hRealizes :
      ∀ choice,
        (editTable program).lookup block.label =
            some (.left choice) →
          StackRealizes block.input source) :
    Simulation.Interaction.Rel (PairOutcomeRel program)
      (InteractionSemantics.Block.openRun block source)
      (InteractionSemantics.Block.openRun
        (applyEdit (editTable program) block) target) := by
  have hSourceBlockTyped : block.WellTyped program :=
    Peephole.blockWellTyped_of_mem
      hSourceTyped.2.1 hBlock
  have hTargetBlockMem :
      applyEdit (editTable program) block ∈
        (canonProgramOnce program).blocks := by
    rw [canonProgramOnce_blocks, List.mem_map]
    exact ⟨block, hBlock, rfl⟩
  have hTargetBlockTyped :
      (applyEdit (editTable program) block).WellTyped
        (canonProgramOnce program) :=
    Peephole.blockWellTyped_of_mem
      hTargetTyped.2.1 hTargetBlockMem
  cases hLookup :
      (editTable program).lookup block.label with
  | none =>
      have hApplied :
          applyEdit (editTable program) block = block := by
        unfold applyEdit
        rw [hLookup]
      rw [hApplied]
      simp only [PairStepRel, hLookup] at hStep
      have hBody :=
        InteractionCongruence.Block.openRunBody_runtimeRel
          hSourceBlockTyped.1 hIndependent hStep
      unfold InteractionSemantics.Block.openRun
        Control.Block.run
      refine Simulation.Interaction.Rel.bind_custom hBody ?_
      intro sourceDone targetDone hDone
      cases hDone with
      | error hError =>
          apply Simulation.Interaction.Rel.done
          apply Or.inr
          constructor
          · exact Simulation.Interaction.ExceptRel.error hError
          · simp
      | ok hAfter =>
          rename_i sourcePair targetPair
          obtain
            ⟨hStateAfter, hSourceOutput, hTargetOutput⟩ :=
              hAfter
          simp only [hSourceOutput, hTargetOutput,
            ↓reduceIte]
          exact
            pairOutcome_srd_resync
              (fun label hTarget choice =>
                target_not_right_of_no_left
                  hUnique hBlock
                  (by
                    intro candidate hLeft
                    rw [hLookup] at hLeft
                    contradiction)
                  hTarget choice)
              hStateAfter
  | some edit =>
      cases edit with
      | left choice =>
          obtain ⟨hBlockEq, hValid, hRightBlock⟩ :=
            block_eq_sourceLeft_of_lookup
              hUnique hBlock hLookup
          subst block
          have hApplied :
              applyEdit (editTable program)
                  choice.sourceLeft =
                { choice.sourceLeft with
                  input := choice.targetLeft.input
                  body := choice.targetLeft.body
                  output := choice.targetLeft.output } := by
            unfold applyEdit
            rw [hLookup]
          have hTargetBodyType :
              Block.bodyType? choice.targetLeft.body
                  choice.targetLeft.input =
                some choice.targetLeft.output := by
            rw [hApplied] at hTargetBlockTyped
            exact hTargetBlockTyped.1
          simp only [PairStepRel, hLookup] at hStep
          have hBody :=
            openRunBody_pair_left hValid
              (hRealizes choice hLookup).le hStep
              hSourceBlockTyped.1 hTargetBodyType
          rw [hApplied]
          unfold InteractionSemantics.Block.openRun
            Control.Block.run
          refine Simulation.Interaction.Rel.bind_custom hBody ?_
          intro sourceDone targetDone hDone
          cases hDone with
          | error hError =>
              exact Simulation.Interaction.Rel.done
                (Or.inr
                  ⟨Simulation.Interaction.ExceptRel.error hError,
                    by simp⟩)
          | ok hAfter =>
              rename_i sourcePair targetPair
              obtain
                ⟨hPending, hSourceOutput, hTargetOutput⟩ :=
                  hAfter
              obtain ⟨hLeftTerm, hRefCount, hNotEntry⟩ :=
                chainStep_spec hValid.linked
              simp only [hSourceOutput, hTargetOutput,
                ↓reduceIte, hLeftTerm]
              exact Simulation.Interaction.Rel.done
                (pairOutcome_jump_pending
                  (editTable_lookup_right_of_left
                    hUnique hLookup)
                  hPending)
      | right choice =>
          obtain ⟨hBlockEq, hValid, hLeftBlock⟩ :=
            block_eq_sourceRight_of_lookup
              hUnique hBlock hLookup
          subst block
          have hApplied :
              applyEdit (editTable program)
                  choice.sourceRight =
                { choice.sourceRight with
                  input := choice.targetRight.input
                  body := choice.targetRight.body
                  output := choice.targetRight.output } := by
            unfold applyEdit
            rw [hLookup]
          have hTargetBodyType :
              Block.bodyType? choice.targetRight.body
                  choice.targetRight.input =
                some choice.targetRight.output := by
            rw [hApplied] at hTargetBlockTyped
            exact hTargetBlockTyped.1
          simp only [PairStepRel, hLookup] at hStep
          have hBody :=
            openRunBody_pair_right hValid hStep
              hSourceBlockTyped.1 hTargetBodyType
          rw [hApplied]
          unfold InteractionSemantics.Block.openRun
            Control.Block.run
          refine Simulation.Interaction.Rel.bind_custom hBody ?_
          intro sourceDone targetDone hDone
          cases hDone with
          | error hError =>
              exact Simulation.Interaction.Rel.done
                (Or.inr
                  ⟨Simulation.Interaction.ExceptRel.error hError,
                    by simp⟩)
          | ok hAfter =>
              rename_i sourcePair targetPair
              obtain
                ⟨hStateAfter, hSourceOutput, hTargetOutput⟩ :=
                  hAfter
              simp only [hSourceOutput, hTargetOutput,
                ↓reduceIte]
              rw [hValid.boundary.2.2]
              exact
                pairOutcome_srd_resync
                  (fun label hTarget candidate =>
                    target_not_right_of_no_left
                      hUnique hBlock
                      (by
                        intro other hLeft
                        rw [hLookup] at hLeft
                        have hImpossible :
                            Edit.right choice =
                              Edit.left other :=
                          Option.some.inj hLeft
                        cases hImpossible)
                      hTarget candidate)
                  hStateAfter

/-- Whole-program one-step congruence, lifting the block theorem through
`findBlock?`.  A missing label cannot be edited, so that branch is the ordinary
synchronized `invalid` outcome. -/
theorem openStep_pair_congr
    {program : Program} {label : Label}
    {source target : EVMState}
    (hUnique : program.LabelsUnique)
    (hSourceTyped : program.WellTyped)
    (hTargetTyped : (canonProgramOnce program).WellTyped)
    (hIndependent : program.ProgramCounterIndependent)
    (hRealizes :
      ∀ block choice,
        program.findBlock? label = some block →
          (editTable program).lookup block.label =
              some (.left choice) →
            StackRealizes block.input source)
    (hStep : PairStepRel program label source target) :
    Simulation.Interaction.Rel (PairOutcomeRel program)
      (InteractionSemantics.Program.openStep
        program label source)
      (InteractionSemantics.Program.openStep
        (canonProgramOnce program) label target) := by
  unfold InteractionSemantics.Program.openStep
    Control.Program.step
  rw [findBlock?_canonProgram]
  cases hFind : program.findBlock? label with
  | none =>
      simp only [hFind, Option.map_none]
      have hState : SameRuntimeData source target := by
        unfold PairStepRel at hStep
        cases hLookup :
            (editTable program).lookup label with
        | none =>
            rw [hLookup] at hStep
            exact hStep
        | some edit =>
            cases edit with
            | left choice =>
                rw [hLookup] at hStep
                exact hStep
            | right choice =>
                exact absurd hFind
                  (findBlock?_ne_none_of_editTable_lookup
                    hUnique hLookup)
      exact Simulation.Interaction.Rel.done
        (Or.inr
          ⟨Simulation.Interaction.ExceptRel.ok
              (InteractionCongruence.Outcome.RuntimeRel.invalid
                hState),
            by simp⟩)
  | some block =>
      simp only [hFind, Option.map_some]
      have hBlock : block ∈ program.blocks := by
        unfold Program.findBlock? at hFind
        exact List.mem_of_find?_eq_some hFind
      have hBlockIndependent :
          block.ProgramCounterIndependent :=
        (List.forall_iff_forall_mem.mp hIndependent)
          block hBlock
      have hLabel : block.label = label := by
        unfold Program.findBlock? at hFind
        have hFound := List.find?_some hFind
        simpa using hFound
      rw [← hLabel] at hStep
      exact
        openRun_pair_congr
          hUnique hSourceTyped hTargetTyped
          hBlock hBlockIndependent hStep
          (fun choice hLookup =>
            hRealizes block choice hFind hLookup)

/-!
## Two certified sweeps

The production program performs a second sweep only when the first result
passes the executable whole-program typing and PC-independence checks.  The
relation below composes the two existing pair certificates without changing
their proof kernel.
-/
def CanonStepRel (program : Program) (label : Label)
    (source target : EVMState) : Prop :=
  let scheduled := canonProgramOnce program
  if secondSweepEligible scheduled then
    ∃ middle,
      PairStepRel program label source middle ∧
        PairStepRel scheduled label middle target
  else
    PairStepRel program label source target

def CanonOutcomeRel (program : Program) :
    Except EVMException TypedCfg.Outcome →
      Except EVMException TypedCfg.Outcome → Prop :=
  fun source target =>
    (∃ (next : Label) (sourceState targetState : EVMState),
      source = .ok (.jump next sourceState) ∧
        target = .ok (.jump next targetState) ∧
        CanonStepRel program next sourceState targetState)
    ∨ (PairRuntimeOutcomeRel source target ∧
        ∀ (next : Label) (state : EVMState),
          source ≠ .ok (.jump next state))

theorem secondSweepEligible_parts
    {program : Program}
    (hEligible : secondSweepEligible program = true) :
    program.WellTyped ∧ program.ProgramCounterIndependent := by
  have hParts :
      program.wellTyped? = true ∧
        program.programCounterIndependent? = true := by
    simpa [secondSweepEligible] using hEligible
  exact
    ⟨Program.wellTyped_of_check hParts.1,
      Program.programCounterIndependent_of_check hParts.2⟩

theorem canonStepRel_entry (program : Program) (state : EVMState) :
    CanonStepRel program program.entry state state := by
  by_cases hEligible :
      secondSweepEligible (canonProgramOnce program) = true
  · simp only [CanonStepRel, hEligible, if_true]
    refine ⟨state, pairStepRel_entry program state, ?_⟩
    simpa using
      pairStepRel_entry (canonProgramOnce program) state
  · have hFalse :
        secondSweepEligible (canonProgramOnce program) = false :=
      Bool.eq_false_of_not_eq_true hEligible
    simp only [CanonStepRel, hFalse, if_false]
    exact pairStepRel_entry program state

theorem pairOutcomeRel_comp
    {program : Program}
    {source middle target :
      Except EVMException TypedCfg.Outcome}
    (hFirst : PairOutcomeRel program source middle)
    (hSecond :
      PairOutcomeRel (canonProgramOnce program) middle target)
    (hEligible :
      secondSweepEligible (canonProgramOnce program) = true) :
    CanonOutcomeRel program source target := by
  rcases hFirst with
    hFirstJump | ⟨hFirstRuntime, hSourceNotJump⟩
  · obtain ⟨next, sourceState, middleState,
        hSource, hMiddle, hFirstStep⟩ :=
      hFirstJump
    rw [hMiddle] at hSecond
    rcases hSecond with
      hSecondJump | ⟨hSecondRuntime, hMiddleNotJump⟩
    · obtain ⟨next₂, middleState₂, targetState,
          hMiddle₂, hTarget, hSecondStep⟩ :=
        hSecondJump
      rw [Except.ok.injEq, Outcome.jump.injEq] at hMiddle₂
      obtain ⟨hNext, hState⟩ := hMiddle₂
      subst next₂
      subst middleState₂
      exact Or.inl
        ⟨next, sourceState, targetState,
          hSource, hTarget, by
            simp only [CanonStepRel, hEligible, if_true]
            exact ⟨middleState, hFirstStep, hSecondStep⟩⟩
    · exact absurd rfl
        (hMiddleNotJump next middleState)
  · rcases hSecond with
      hSecondJump | ⟨hSecondRuntime, hMiddleNotJump⟩
    · obtain ⟨next, middleState, targetState,
          hMiddle, hTarget, hSecondStep⟩ :=
        hSecondJump
      exfalso
      cases hFirstRuntime with
      | error hError =>
          exact absurd hMiddle (by simp)
      | ok hRuntime =>
          cases hRuntime with
          | jump label hState =>
              exact hSourceNotJump label _ rfl
          | fallthrough hState =>
              exact absurd hMiddle (by simp)
          | returnDispatch hState =>
              exact absurd hMiddle (by simp)
          | halt kind hState =>
              exact absurd hMiddle (by simp)
          | invalid hState =>
              exact absurd hMiddle (by simp)
    · refine Or.inr ⟨?_, hSourceNotJump⟩
      cases hFirstRuntime with
      | error hSourceError =>
          cases hSecondRuntime with
          | error hTargetError =>
              exact .error (hSourceError.trans hTargetError)
      | ok hSourceResult =>
          cases hSecondRuntime with
          | ok hTargetResult =>
              exact .ok
                (InteractionCongruence.Outcome.RuntimeRel.trans
                  hSourceResult hTargetResult)

theorem openStep_canonProgram_congr
    {program : Program} {label : Label}
    {source target : EVMState}
    (hUnique : program.LabelsUnique)
    (hSourceTyped : program.WellTyped)
    (hTargetTyped : (canonProgram program).WellTyped)
    (hIndependent : program.ProgramCounterIndependent)
    (hRealizesFirst :
      ∀ block choice,
        program.findBlock? label = some block →
          (editTable program).lookup block.label =
              some (.left choice) →
            StackRealizes block.input source)
    (hRealizesSecond :
      ∀ (hMiddleTyped :
          (canonProgramOnce program).WellTyped)
          middle block choice,
        PairStepRel program label source middle →
          (canonProgramOnce program).findBlock? label = some block →
            (editTable (canonProgramOnce program)).lookup block.label =
                some (.left choice) →
              StackRealizes block.input middle)
    (hStep : CanonStepRel program label source target) :
    Simulation.Interaction.Rel (CanonOutcomeRel program)
      (InteractionSemantics.Program.openStep
        program label source)
      (InteractionSemantics.Program.openStep
        (canonProgram program) label target) := by
  by_cases hEligible :
      secondSweepEligible (canonProgramOnce program) = true
  · obtain ⟨hMiddleTyped, hMiddleIndependent⟩ :=
      secondSweepEligible_parts hEligible
    simp only [CanonStepRel, hEligible, if_true] at hStep
    obtain ⟨middle, hFirstStep, hSecondStep⟩ := hStep
    have hFirst :=
      openStep_pair_congr
        hUnique hSourceTyped hMiddleTyped hIndependent
        hRealizesFirst hFirstStep
    have hTargetTyped' :
        (canonProgramOnce
          (canonProgramOnce program)).WellTyped := by
      rw [← canonProgram_eq_double hEligible]
      exact hTargetTyped
    have hSecond :=
      openStep_pair_congr
        hMiddleTyped.1 hMiddleTyped hTargetTyped'
        hMiddleIndependent
        (fun block choice hFind hLookup =>
          hRealizesSecond hMiddleTyped middle block choice
            hFirstStep hFind hLookup)
        hSecondStep
    have hComposed :=
      Simulation.Interaction.Rel.trans hFirst hSecond
    rw [canonProgram_eq_double hEligible]
    refine Simulation.Interaction.Rel.mono hComposed ?_
    intro sourceOutcome targetOutcome hOutcomes
    obtain ⟨middleOutcome, hFirstOutcome,
      hSecondOutcome⟩ := hOutcomes
    exact pairOutcomeRel_comp
      hFirstOutcome hSecondOutcome hEligible
  · have hFalse :
        secondSweepEligible (canonProgramOnce program) = false :=
      Bool.eq_false_of_not_eq_true hEligible
    simp only [CanonStepRel, hFalse, if_false] at hStep
    have hOne :=
      openStep_pair_congr
        hUnique hSourceTyped
        (by
          rw [← canonProgram_eq_once hFalse]
          exact hTargetTyped)
        hIndependent hRealizesFirst hStep
    rw [canonProgram_eq_once hFalse]
    refine Simulation.Interaction.Rel.mono hOne ?_
    intro sourceOutcome targetOutcome hOutcome
    rcases hOutcome with
      hJump | ⟨hRuntime, hNotJump⟩
    · obtain ⟨next, sourceState, targetState,
          hSource, hTarget, hPair⟩ := hJump
      exact Or.inl
        ⟨next, sourceState, targetState,
          hSource, hTarget, by
            simp only [CanonStepRel, hFalse, if_false]
            exact hPair⟩
    · exact Or.inr ⟨hRuntime, hNotJump⟩

end VirtualStack
end TypedCfg
end EvmCompiler
