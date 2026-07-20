import EvmCompiler.TypedCfg.PeepholeNoopSwapProgram

/-!
# Cross-block fallthrough-seam swap cancellation (session-61, Route A)

Empirical finding (PEEPHOLE_PROGRESS §Session-60): every removable adjacent
`SWAPn;SWAPn` pair on the corpus is born at a **fallthrough block seam** during
byte compaction — the lowered image has `… , swap d , jump G , label G , swap d ,
…` and compaction (`elideFallthroughJumps` + `pruneUnreferencedLabels`) erases the
`jump G ; label G`, abutting the two swaps.  In all measured cases the target
block `G` has a **unique predecessor** (its label is referenced exactly once in
the whole cfg), which makes deleting both swaps unconditionally sound.

This module is the *definition* + *static analysis* + *structural-preservation*
half of the cfg-level, **block-structure-preserving** seam canceller (Route A):
for each block `A` with `A.term = .fallthrough B`, `B` a unique predecessor,
`A.body` ending in `swap d` and `B.body` starting with `swap d`, delete both
swaps and re-type the seam shapes through the `0 ↔ d+1` transposition
(`remapShape d`).  Labels / block-count / terminators are **untouched**, so this
transform slots into the same congruence-family template that the
`normalizeProgram` tower (sessions 57–59) built (the runtime/type/fuel/source
congruences are the follow-on frontier; see §Session-61).

## Soundness of the firing guard

A seam `(A, B)` fires iff:
* `A.term = .fallthrough B.label`,
* `refCount program B.label = 1` (B's label appears exactly once across all
  terminators' `targets`, i.e. B has a **unique predecessor** = this fallthrough),
* `A.body.getLast? = some (.swap d)` and `B.body.head? = some (.swap d)` (same `d`),
* `2 ≤ A.body.length` and `2 ≤ B.body.length`.

The length-≥-2 guard on **both** endpoints makes the head index (`0`) and the tail
index (`length-1`) distinct in every participating block, so a single swap
instruction can never be claimed by two seams at once (a block that is the target
of one seam and the source of another then drops two *distinct* swaps).  Because
`B` has a unique predecessor, the seam predicate evaluated from the source side
(`sourceFire?` on `A`) and from the target side (`targetFire?` on `B`) agree on the
same `(A, B)` pair — no priority resolution is needed.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open TypedCfg (Instr Shape Terminator Block Program Label)

/-- How many times `label` is referenced as a terminator target across the whole
program (counting multiplicity, e.g. `jumpi t t` counts `t` twice). -/
def refCount (program : Program) (label : Label) : Nat :=
  (program.blocks.flatMap (fun block => block.term.targets)).count label

/-- Does block `a` head a firing seam?  Returns the swap depth `d` if `a`
fallthroughs to a unique-predecessor block `b` whose head swap matches `a`'s tail
swap, both bodies having length ≥ 2. -/
def sourceFire? (program : Program) (a : Block) : Option Nat :=
  match a.term with
  | .fallthrough bLabel =>
      if refCount program bLabel = 1 then
        match program.findBlock? bLabel with
        | some b =>
            match a.body.getLast?, b.body.head? with
            | some (.swap d), some (.swap d') =>
                if d = d' ∧ 2 ≤ a.body.length ∧ 2 ≤ b.body.length then
                  some d
                else
                  none
            | _, _ => none
        | none => none
      else
        none
  | _ => none

/-- Does block `b` tail a firing seam?  `b` (a unique-predecessor block) has a
head swap dropped iff its sole predecessor `a` heads a firing seam into it. -/
def targetFire? (program : Program) (b : Block) : Option Nat :=
  if refCount program b.label = 1 then
    match program.blocks.find? (fun a => a.term == Terminator.fallthrough b.label) with
    | some a => sourceFire? program a
    | none => none
  else
    none

/-- The per-block seam edit: drop the tail swap if `block` heads a firing seam
(re-typing `output` through the `0 ↔ d+1` transposition), and drop the head swap
if `block` tails a firing seam (re-typing `input`).  Both firing decisions are
computed against the **original** `program`, so the edits are independent. -/
def seamBlock (program : Program) (block : Block) : Block :=
  let block1 :=
    match sourceFire? program block with
    | some d => { block with output := remapShape d block.output, body := block.body.dropLast }
    | none => block
  match targetFire? program block with
  | some d => { block1 with input := remapShape d block1.input, body := block1.body.tail }
  | none => block1

/-- Whole-program seam cancellation: apply `seamBlock` to every block.  Labels,
block count, entry, and every terminator are preserved. -/
def seamCancelProgram (program : Program) : Program :=
  { program with blocks := program.blocks.map (seamBlock program) }

/-! ## Structural preservation lemmas

The label / terminator of every block, and hence the whole-program label
structure (`findBlock?`, `EmittedLabels`, `LabelsUnique`), are invariant under
`seamBlock` / `seamCancelProgram`.  These mirror the `normalizeProgram` spine. -/

@[simp] theorem seamBlock_label (program : Program) (block : Block) :
    (seamBlock program block).label = block.label := by
  unfold seamBlock
  cases sourceFire? program block <;> cases targetFire? program block <;> rfl

@[simp] theorem seamBlock_term (program : Program) (block : Block) :
    (seamBlock program block).term = block.term := by
  unfold seamBlock
  cases sourceFire? program block <;> cases targetFire? program block <;> rfl

@[simp] theorem seamCancelProgram_entry (program : Program) :
    (seamCancelProgram program).entry = program.entry := rfl

@[simp] theorem seamCancelProgram_blocks (program : Program) :
    (seamCancelProgram program).blocks = program.blocks.map (seamBlock program) := rfl

/-- Block lookup commutes with seam cancellation (labels are preserved). -/
theorem findBlock?_seamCancelProgram (program : Program) (label : Label) :
    (seamCancelProgram program).findBlock? label =
      (program.findBlock? label).map (seamBlock program) := by
  simp only [seamCancelProgram, Program.findBlock?]
  induction program.blocks with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.map_cons, List.find?_cons, seamBlock_label]
      by_cases h : (b.label == label) = true
      · simp [h]
      · simp only [h, Bool.false_eq_true, if_false]; exact ih

/-- Seam cancellation preserves the emitted-label multiset (each block's label
and terminator — hence its `definedLabels` — are untouched). -/
theorem emittedLabels_seamCancelProgram (program : Program) :
    (seamCancelProgram program).EmittedLabels = program.EmittedLabels := by
  unfold Program.EmittedLabels
  rw [seamCancelProgram_blocks, List.flatMap_map]
  apply List.flatMap_congr
  intro b _
  simp only [seamBlock_label, seamBlock_term]

/-- Seam cancellation preserves whole-program `LabelsUnique`. -/
theorem labelsUnique_seamCancelProgram {program : Program}
    (h : program.LabelsUnique) :
    (seamCancelProgram program).LabelsUnique := by
  unfold Program.LabelsUnique at h ⊢
  rw [seamCancelProgram_blocks, List.pairwise_map]
  refine h.imp ?_
  intro a b hab
  simpa only [seamBlock_label] using hab

/-- Seam cancellation preserves `EmittedLabelsUnique`. -/
theorem emittedLabelsUnique_seamCancelProgram {program : Program}
    (h : program.EmittedLabelsUnique) :
    (seamCancelProgram program).EmittedLabelsUnique := by
  unfold Program.EmittedLabelsUnique
  rw [emittedLabels_seamCancelProgram]
  exact h

/-- Seam cancellation preserves the existence of the entry block. -/
theorem entry_findBlock?_seamCancelProgram {program : Program}
    (h : program.findBlock? program.entry ≠ none) :
    (seamCancelProgram program).findBlock? (seamCancelProgram program).entry ≠ none := by
  rw [seamCancelProgram_entry, findBlock?_seamCancelProgram]
  cases hFind : program.findBlock? program.entry with
  | none => exact absurd hFind h
  | some block => simp

/-! ## Body-typing kernels for the seam edits (WellTyped shape half)

Dropping a leading / trailing `swap d` from a well-typed body preserves
`bodyType?` after re-typing the input / output through the `0 ↔ d+1`
transposition `remapShape d` — because `Instr.type? (.swap d)` *is* that
transposition on the running shape.  These are the intra-block kernels the
`WellTyped` (`bodyType?` conjunct) preservation is assembled from. -/

/-- `Instr.type? (.swap d)` computes exactly the `remapShape d` transposition. -/
theorem type?_swap_eq_remapShape {d : Nat} {s s' : Shape}
    (h : Instr.type? (.swap d) s = some s') : s' = remapShape d s := by
  obtain ⟨hslots, htail⟩ := type?_swap_eq h
  cases s'; cases s
  simp only [remapShape] at *
  simp_all

/-- Dropping a trailing `swap d` from a well-typed body: the output is un-swapped
through `remapShape d`. -/
theorem bodyType?_dropTail_swap {d : Nat} {pre : List Instr} {input output : Shape}
    (h : Block.bodyType? (pre ++ [Instr.swap d]) input = some output) :
    Block.bodyType? pre input = some (remapShape d output) := by
  rw [bodyType?_append, Option.bind_eq_some_iff] at h
  obtain ⟨mid, hpre, hswap⟩ := h
  rw [bodyType?_cons, Option.bind_eq_some_iff] at hswap
  obtain ⟨out, hswap', hnil⟩ := hswap
  simp only [Block.bodyType?] at hnil
  have hoo : out = output := Option.some.inj hnil
  subst hoo
  have hEq : out = remapShape d mid := type?_swap_eq_remapShape hswap'
  obtain ⟨_, hlen, _⟩ := Instr.length_of_type?_swap hswap'
  have h0 : 0 < mid.slots.length := by
    have : mid.slots.length = mid.length := rfl
    omega
  have hd1 : d + 1 < mid.slots.length := by
    have : mid.slots.length = mid.length := rfl
    omega
  have hmid : remapShape d out = mid := by
    rw [hEq, remapShape_involutive d mid h0 hd1]
  rw [hmid]; exact hpre

/-- Dropping a leading `swap d` from a well-typed body: the input is un-swapped
through `remapShape d`, the output unchanged. -/
theorem bodyType?_dropHead_swap {d : Nat} {rest : List Instr} {input output : Shape}
    (h : Block.bodyType? (Instr.swap d :: rest) input = some output) :
    Block.bodyType? rest (remapShape d input) = some output := by
  rw [bodyType?_cons, Option.bind_eq_some_iff] at h
  obtain ⟨mid, hswap, hrest⟩ := h
  have : mid = remapShape d input := type?_swap_eq_remapShape hswap
  rw [← this]; exact hrest

/-! ## `compatible` preservation under the seam transposition

The only affected terminator check is the seam predecessor `A`'s
`.fallthrough B`, whose original `A.output.compatible B.input` becomes
`(remapShape d A.output).compatible (remapShape d B.input)`.  Because
`remapShape = swapPos 0 (d+1)` transposes the SAME two in-range positions on both
shapes, `Shape.compatible` is preserved (length + tail are untouched, and
`slotsAgree` is preserved by a pointwise reindexing).  Unlike
`slotsAgree_swapPos_eq` this variant does NOT require equal lengths — only that
`0` and `d+1` are in range on both slot lists. -/

/-- `slotsAgree` (as `true`) is preserved by simultaneously transposing the
`0 ↔ d+1` positions, given both indices are in range on BOTH lists (lengths may
differ). -/
theorem slotsAgree_swapPos_true_of_bounds (d : Nat) (a b : List Slot)
    (h0a : 0 < a.length) (hda : d + 1 < a.length)
    (h0b : 0 < b.length) (hdb : d + 1 < b.length)
    (hAgree : Shape.slotsAgree a b = true) :
    Shape.slotsAgree (swapPos 0 (d + 1) a) (swapPos 0 (d + 1) b) = true := by
  rw [slotsAgree_iff_pointwise] at hAgree ⊢
  intro k
  rw [swapPos_getElem? 0 (d + 1) a k h0a hda,
      swapPos_getElem? 0 (d + 1) b k h0b hdb]
  by_cases hdk : d + 1 = k
  · simpa [hdk] using hAgree 0
  · by_cases hzk : 0 = k
    · simpa [hdk, hzk] using hAgree (d + 1)
    · simpa [hdk, hzk] using hAgree k

/-- `slotsAgree` (as a `Bool`) is invariant under the `0 ↔ d+1` transposition,
given both indices are in range on both lists. -/
theorem slotsAgree_swapPos_eq_of_bounds (d : Nat) (a b : List Slot)
    (h0a : 0 < a.length) (hda : d + 1 < a.length)
    (h0b : 0 < b.length) (hdb : d + 1 < b.length) :
    Shape.slotsAgree (swapPos 0 (d + 1) a) (swapPos 0 (d + 1) b)
      = Shape.slotsAgree a b := by
  by_cases h : Shape.slotsAgree a b = true
  · rw [h]
    exact slotsAgree_swapPos_true_of_bounds d a b h0a hda h0b hdb h
  · simp only [Bool.not_eq_true] at h
    rw [h]
    by_contra hne
    simp only [Bool.not_eq_false] at hne
    have hback := slotsAgree_swapPos_true_of_bounds d
      (swapPos 0 (d + 1) a) (swapPos 0 (d + 1) b)
      (by rw [swapPos_length]; exact h0a) (by rw [swapPos_length]; exact hda)
      (by rw [swapPos_length]; exact h0b) (by rw [swapPos_length]; exact hdb) hne
    rw [swapPos_involutive 0 (d + 1) a h0a hda,
        swapPos_involutive 0 (d + 1) b h0b hdb] at hback
    rw [hback] at h; exact absurd h (by simp)

/-- `Shape.compatible` is invariant under the seam transposition on both shapes,
given `d+1` is in range on both slot lists. -/
theorem compatible_remapShape_eq {d : Nat} {l r : Shape}
    (hl : d + 1 < l.slots.length) (hr : d + 1 < r.slots.length) :
    (remapShape d l).compatible (remapShape d r) = l.compatible r := by
  unfold Shape.compatible remapShape
  simp only [Shape.length, Shape.tail, swapPos_length]
  rw [slotsAgree_swapPos_eq_of_bounds d l.slots r.slots (by omega) hl (by omega) hr]

/-! ## `refCount = 1` uniqueness

A firing seam target `B` has `refCount program B.label = 1`, so `B.label` is
referenced by EXACTLY ONE terminator across the whole program.  Any block whose
terminator lists a firing-target label must therefore be that unique referencer.
These are the list-count lemmas that turn `refCount = 1` into that uniqueness. -/

/-- A single member's target-count is a lower bound on the flat-mapped count. -/
theorem count_le_flatMap_of_mem {α : Type _} (l : List α) (f : α → List Label)
    (b : Label) {x : α} (hx : x ∈ l) :
    (f x).count b ≤ (l.flatMap f).count b := by
  induction l with
  | nil => simp at hx
  | cons a as ih =>
      simp only [List.flatMap_cons, List.count_append]
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact Nat.le_add_right _ _
      · exact le_trans (ih hx') (Nat.le_add_left _ _)

/-- Two DISTINCT members each contributing to the flat-mapped count give a
combined lower bound. -/
theorem count_flatMap_two_mem {α : Type _} (l : List α) (f : α → List Label)
    (b : Label) {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hne : x ≠ y) :
    (f x).count b + (f y).count b ≤ (l.flatMap f).count b := by
  induction l with
  | nil => simp at hx
  | cons a as ih =>
      simp only [List.flatMap_cons, List.count_append]
      rcases List.mem_cons.mp hx with rfl | hx'
      · have hy' : y ∈ as := by
          rcases List.mem_cons.mp hy with rfl | h
          · exact absurd rfl hne
          · exact h
        have := count_le_flatMap_of_mem as f b hy'
        omega
      · rcases List.mem_cons.mp hy with rfl | hy'
        · have := count_le_flatMap_of_mem as f b hx'
          omega
        · have := ih hx' hy'
          omega

/-- If `refCount program L = 1`, two distinct blocks cannot both reference `L`. -/
theorem two_le_refCount {program : Program} {L : Label} {A b0 : Block}
    (hA : A ∈ program.blocks) (hLA : L ∈ A.term.targets)
    (hb0 : b0 ∈ program.blocks) (hLb0 : L ∈ b0.term.targets)
    (hne : A ≠ b0) : 2 ≤ refCount program L := by
  unfold refCount
  have hAc : 1 ≤ (A.term.targets).count L := by
    rw [Nat.one_le_iff_ne_zero, Ne, List.count_eq_zero]; exact fun h => h hLA
  have hb0c : 1 ≤ (b0.term.targets).count L := by
    rw [Nat.one_le_iff_ne_zero, Ne, List.count_eq_zero]; exact fun h => h hLb0
  have hsum := count_flatMap_two_mem program.blocks (fun block => block.term.targets)
    L hA hb0 hne
  simp only at hsum
  omega

/-! ## Firing-query specifications

Structured unpackings of `sourceFire?` / `targetFire?` returning `some d`. -/

/-- Everything `sourceFire? program a = some d` asserts. -/
theorem sourceFire?_spec {program : Program} {a : Block} {d : Nat}
    (h : sourceFire? program a = some d) :
    ∃ bLabel b, a.term = Terminator.fallthrough bLabel ∧
      refCount program bLabel = 1 ∧ program.findBlock? bLabel = some b ∧
      a.body.getLast? = some (Instr.swap d) ∧ b.body.head? = some (Instr.swap d) ∧
      2 ≤ a.body.length ∧ 2 ≤ b.body.length := by
  unfold sourceFire? at h
  split at h
  case h_1 bLabel hterm =>
    split at h
    · rename_i href
      split at h
      · rename_i b hfind
        split at h
        · rename_i d1 d2 hla hhd
          split at h
          · rename_i hcond
            obtain ⟨hdd, hal, hbl⟩ := hcond
            subst hdd
            have hd : d1 = d := Option.some.inj h
            subst hd
            exact ⟨bLabel, b, hterm, href, hfind, hla, hhd, hal, hbl⟩
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  all_goals exact absurd h (by simp)

/-- Everything `targetFire? program b = some d` asserts. -/
theorem targetFire?_spec {program : Program} {b : Block} {d : Nat}
    (h : targetFire? program b = some d) :
    refCount program b.label = 1 ∧
      ∃ a, program.blocks.find?
            (fun a => a.term == Terminator.fallthrough b.label) = some a ∧
          sourceFire? program a = some d := by
  unfold targetFire? at h
  split at h
  · rename_i href
    split at h
    · rename_i a hfind
      exact ⟨href, a, hfind, h⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-! ## Field-shape descriptions of `seamBlock` -/

/-- The `input` of a seam-edited block, in terms of `targetFire?`. -/
theorem seamBlock_input (program : Program) (block : Block) :
    (seamBlock program block).input =
      match targetFire? program block with
      | some d => remapShape d block.input
      | none => block.input := by
  unfold seamBlock
  cases sourceFire? program block <;> cases targetFire? program block <;> rfl

/-- The `output` of a seam-edited block, in terms of `sourceFire?`. -/
theorem seamBlock_output (program : Program) (block : Block) :
    (seamBlock program block).output =
      match sourceFire? program block with
      | some d => remapShape d block.output
      | none => block.output := by
  unfold seamBlock
  cases sourceFire? program block <;> cases targetFire? program block <;> rfl

/-- `labelShape?` of the seam-cancelled program: the seam-target inputs move. -/
theorem labelShape?_seamCancelProgram (program : Program) (L : Label) :
    (seamCancelProgram program).labelShape? L =
      (program.findBlock? L).map (fun b =>
        match targetFire? program b with
        | some d => remapShape d b.input
        | none => b.input) := by
  unfold Program.labelShape?
  rw [findBlock?_seamCancelProgram]
  cases program.findBlock? L with
  | none => rfl
  | some b =>
      simp only [Option.map_some]
      rw [seamBlock_input]

/-! ## Bounds and firing connections -/

/-- A well-typed source block's output is long enough for the dropped tail swap. -/
theorem output_bound_of_sourceFire {program : Program} {a : Block} {d : Nat}
    (hTyped : a.WellTyped program) (h : sourceFire? program a = some d) :
    d + 1 < a.output.slots.length := by
  obtain ⟨bLabel, b, hterm, href, hfind, hla, hhd, hal, hbl⟩ := sourceFire?_spec h
  have hsplit : a.body.dropLast ++ [Instr.swap d] = a.body :=
    List.dropLast_append_getLast? _ (Option.mem_def.mpr hla)
  have hbody := hTyped.1
  rw [← hsplit, bodyType?_append, Option.bind_eq_some_iff] at hbody
  obtain ⟨mid, hpre, hswap⟩ := hbody
  rw [bodyType?_cons, Option.bind_eq_some_iff] at hswap
  obtain ⟨out, htype, hnil⟩ := hswap
  simp only [Block.bodyType?, Option.some.injEq] at hnil
  subst hnil
  obtain ⟨_, hle, hlen⟩ := Instr.length_of_type?_swap htype
  show d + 1 < a.output.slots.length
  have h1 : a.output.slots.length = a.output.length := rfl
  omega

/-- A well-typed target block's input is long enough for the dropped head swap. -/
theorem input_bound_of_head_swap {program : Program} {b : Block} {d : Nat}
    (hTyped : b.WellTyped program) (hhd : b.body.head? = some (Instr.swap d)) :
    d + 1 < b.input.slots.length := by
  have hbody := hTyped.1
  obtain ⟨rest, hb⟩ : ∃ rest, b.body = Instr.swap d :: rest := by
    cases hbb : b.body with
    | nil => rw [hbb] at hhd; simp at hhd
    | cons x xs =>
        rw [hbb] at hhd; simp only [List.head?_cons, Option.some.injEq] at hhd
        subst hhd; exact ⟨xs, rfl⟩
  rw [hb, bodyType?_cons, Option.bind_eq_some_iff] at hbody
  obtain ⟨mid, htype, _⟩ := hbody
  obtain ⟨_, hle, _⟩ := Instr.length_of_type?_swap htype
  show d + 1 < b.input.slots.length
  have h1 : b.input.slots.length = b.input.length := rfl
  omega

/-- The unique-predecessor target of a firing source itself has `targetFire?`. -/
theorem targetFire?_target_of_sourceFire {program : Program} {a B : Block}
    {bLabel : Label} {d : Nat}
    (hmem : a ∈ program.blocks)
    (hterm : a.term = Terminator.fallthrough bLabel)
    (hfind : program.findBlock? bLabel = some B)
    (href : refCount program bLabel = 1)
    (h : sourceFire? program a = some d) :
    targetFire? program B = some d := by
  have hBlabel : B.label = bLabel := by
    unfold Program.findBlock? at hfind
    have := List.find?_some hfind; simpa using this
  unfold targetFire?
  rw [hBlabel, if_pos href]
  cases hf : program.blocks.find?
      (fun a => a.term == Terminator.fallthrough bLabel) with
  | none =>
      exfalso
      have hp : (a.term == Terminator.fallthrough bLabel) = true := by rw [hterm]; simp
      exact (List.find?_eq_none.mp hf) a hmem hp
  | some a' =>
      have ha'mem := List.mem_of_find?_eq_some hf
      have ha'term : a'.term = Terminator.fallthrough bLabel := by
        have := List.find?_some hf; simpa using this
      have hEq : a' = a := by
        by_cases hne : a' = a
        · exact hne
        · exfalso
          have h2 := two_le_refCount (L := bLabel) ha'mem
            (by rw [ha'term]; simp [Terminator.targets]) hmem
            (by rw [hterm]; simp [Terminator.targets]) hne
          omega
      simp only [hEq]; exact h

/-- The head swap of a firing target (recoverable from `targetFire?`). -/
theorem head_swap_of_targetFire {program : Program} {b : Block} {d : Nat}
    (hUnique : program.LabelsUnique) (hmem : b ∈ program.blocks)
    (h : targetFire? program b = some d) :
    b.body.head? = some (Instr.swap d) := by
  obtain ⟨href, a, hfind, hsrc⟩ := targetFire?_spec h
  obtain ⟨bLabel, b', hterm, href', hfind', hla, hhd, hal, hbl⟩ := sourceFire?_spec hsrc
  have haterm : a.term = Terminator.fallthrough b.label := by
    have := List.find?_some hfind; simpa using this
  rw [hterm] at haterm
  have hbl_eq : bLabel = b.label := by injection haterm
  rw [hbl_eq] at hfind'
  have hfb : program.findBlock? b.label = some b :=
    Program.findBlock?_eq_some_of_mem hUnique hmem
  rw [hfb] at hfind'
  have : b = b' := Option.some.inj hfind'
  rw [this]; exact hhd

/-- If a firing seam target's label were referenced by `b0` (a non-source), the
`refCount = 1` uniqueness is violated: hence non-source targets never fire. -/
theorem targetFire?_none_of_sourceFire_none {program : Program} {b0 bL : Block}
    {L : Label}
    (hmemb0 : b0 ∈ program.blocks) (hLmem : L ∈ b0.term.targets)
    (hs : sourceFire? program b0 = none)
    (hfind : program.findBlock? L = some bL) :
    targetFire? program bL = none := by
  by_contra hne
  obtain ⟨d, htf⟩ := Option.ne_none_iff_exists'.mp hne
  obtain ⟨href, a', hf, hsrc⟩ := targetFire?_spec htf
  have hbLlabel : bL.label = L := by
    unfold Program.findBlock? at hfind
    have := List.find?_some hfind; simpa using this
  rw [hbLlabel] at href hf
  have ha'mem := List.mem_of_find?_eq_some hf
  have ha'term : a'.term = Terminator.fallthrough L := by
    have := List.find?_some hf; simpa using this
  by_cases hEq : a' = b0
  · subst hEq; simp [hs] at hsrc
  · have h2 := two_le_refCount ha'mem (by rw [ha'term]; simp [Terminator.targets]) hmemb0 hLmem hEq
    rw [href] at h2; omega

/-! ## Terminator `typeWith?` congruence over agreeing label maps -/

theorem targetsHaveShapeWith?_congr {f g : Label → Option Shape} {shape : Shape}
    {sites : List ReturnSite}
    (h : ∀ site ∈ sites, f site.target = g site.target) :
    Terminator.targetsHaveShapeWith? f shape sites =
      Terminator.targetsHaveShapeWith? g shape sites := by
  induction sites with
  | nil => rfl
  | cons site rest ih =>
      simp only [Terminator.targetsHaveShapeWith?]
      rw [h site (by simp)]
      cases g site.target with
      | none => rfl
      | some _ => rw [ih (fun s hs => h s (by simp [hs]))]

theorem typeWith?_congr {f g : Label → Option Shape} {shape : Shape}
    {term : Terminator}
    (h : ∀ L ∈ term.targets, f L = g L) :
    Terminator.typeWith? f shape term = Terminator.typeWith? g shape term := by
  cases term with
  | fallthrough next =>
      simp only [Terminator.typeWith?]; rw [h next (by simp [Terminator.targets])]
  | jump target =>
      simp only [Terminator.typeWith?]; rw [h target (by simp [Terminator.targets])]
  | jumpi target next =>
      simp only [Terminator.typeWith?]
      rw [h target (by simp [Terminator.targets]), h next (by simp [Terminator.targets])]
  | returnDispatch returnCount sites =>
      simp only [Terminator.typeWith?]
      congr 1
      funext depth
      rw [targetsHaveShapeWith?_congr (fun site hs => h site.target (by
        simp only [Terminator.targets]; exact List.mem_map_of_mem hs))]
  | halt kind => rfl
  | invalid => rfl

/-- The seam terminator type-check is invariant for a non-source block. -/
theorem term_type?_seamCancelProgram_eq {program : Program} {b0 : Block}
    {shape : Shape}
    (hmem : b0 ∈ program.blocks)
    (hs : sourceFire? program b0 = none) :
    b0.term.type? (seamCancelProgram program) shape =
      b0.term.type? program shape := by
  unfold Terminator.type?
  apply typeWith?_congr
  intro L hLmem
  rw [labelShape?_seamCancelProgram]
  cases hfind : program.findBlock? L with
  | none => unfold Program.labelShape?; rw [hfind]; rfl
  | some bL =>
      have htf := targetFire?_none_of_sourceFire_none hmem hLmem hs hfind
      simp only [Option.map_some, htf]
      unfold Program.labelShape?; rw [hfind]; rfl

/-! ## Head-preserving `dropLast` and the per-block WellTyped assembly -/

theorem head_tail_decomp {α : Type _} {l : List α} {x : α}
    (h : l.head? = some x) : l = x :: l.tail := by
  cases l with
  | nil => simp at h
  | cons a rest =>
      simp only [List.head?_cons, Option.some.injEq] at h; subst h; rfl

theorem dropLast_head_tail {α : Type _} {l : List α} {x : α}
    (h : l.head? = some x) (h2 : 2 ≤ l.length) :
    l.dropLast = x :: l.dropLast.tail := by
  cases l with
  | nil => simp at h
  | cons a rest =>
      simp only [List.head?_cons, Option.some.injEq] at h; subst h
      cases rest with
      | nil => simp at h2
      | cons y rest' => simp [List.dropLast_cons₂]

theorem blockWellTyped_of_mem {program : Program} {b : Block}
    (hAll : program.AllBlocksTyped) (hmem : b ∈ program.blocks) :
    b.WellTyped program :=
  (List.forall_iff_forall_mem.mp hAll) b hmem

/-- A `.fallthrough`'s type-check, reduced once its target shape is known. -/
theorem type?_fallthrough_some {program : Program} {shape : Shape} {next : Label}
    {ts : Shape} (h : program.labelShape? next = some ts) :
    (Terminator.fallthrough next).type? program shape =
      (if shape.compatible ts then some () else none) := by
  simp [Terminator.type?, Terminator.typeWith?, h]

/-- The seam terminator obligation. -/
theorem seamBlock_term_type? {program : Program} {b0 : Block}
    (hUnique : program.LabelsUnique) (hAll : program.AllBlocksTyped)
    (hmem : b0 ∈ program.blocks) :
    b0.term.type? (seamCancelProgram program) (seamBlock program b0).output
      = some () := by
  have hTyped := blockWellTyped_of_mem hAll hmem
  rw [seamBlock_output]
  cases hs : sourceFire? program b0 with
  | none =>
      rw [term_type?_seamCancelProgram_eq hmem hs]; exact hTyped.2
  | some d =>
      obtain ⟨bLabel, B, hterm, href, hfind, hla, hhd, hal, hbl⟩ :=
        sourceFire?_spec hs
      have hBmem : B ∈ program.blocks := by
        unfold Program.findBlock? at hfind; exact List.mem_of_find?_eq_some hfind
      have hBTyped := blockWellTyped_of_mem hAll hBmem
      have htf : targetFire? program B = some d :=
        targetFire?_target_of_sourceFire hmem hterm hfind href hs
      have hls : (seamCancelProgram program).labelShape? bLabel
          = some (remapShape d B.input) := by
        rw [labelShape?_seamCancelProgram, hfind]
        simp only [Option.map_some, htf]
      have hpls : program.labelShape? bLabel = some B.input := by
        unfold Program.labelShape?; rw [hfind]; rfl
      have hbo : d + 1 < b0.output.slots.length :=
        output_bound_of_sourceFire hTyped hs
      have hbi : d + 1 < B.input.slots.length :=
        input_bound_of_head_swap hBTyped hhd
      have horig := hTyped.2
      rw [hterm, type?_fallthrough_some hpls] at horig
      rw [hterm, type?_fallthrough_some hls, compatible_remapShape_eq hbo hbi]
      exact horig

/-- The seam body-typing obligation (four fire cases). -/
theorem seamBlock_bodyType? {program : Program} {b0 : Block}
    (hUnique : program.LabelsUnique) (hAll : program.AllBlocksTyped)
    (hmem : b0 ∈ program.blocks) :
    Block.bodyType? (seamBlock program b0).body (seamBlock program b0).input
      = some (seamBlock program b0).output := by
  have hTyped := blockWellTyped_of_mem hAll hmem
  have hbody := hTyped.1
  unfold seamBlock
  cases hs : sourceFire? program b0 with
  | none =>
      cases ht : targetFire? program b0 with
      | none => simpa using hbody
      | some dt =>
          simp only []
          have hhd := head_swap_of_targetFire hUnique hmem ht
          have hdecomp : b0.body = Instr.swap dt :: b0.body.tail :=
            head_tail_decomp hhd
          rw [hdecomp] at hbody
          exact bodyType?_dropHead_swap hbody
  | some ds =>
      have hla : b0.body.getLast? = some (Instr.swap ds) := by
        obtain ⟨_, _, _, _, _, hla, _, _, _⟩ := sourceFire?_spec hs; exact hla
      have hlen : 2 ≤ b0.body.length := by
        obtain ⟨_, _, _, _, _, _, _, hal, _⟩ := sourceFire?_spec hs; exact hal
      have hsplit : b0.body.dropLast ++ [Instr.swap ds] = b0.body :=
        List.dropLast_append_getLast? _ (Option.mem_def.mpr hla)
      cases ht : targetFire? program b0 with
      | none =>
          simp only []
          rw [← hsplit] at hbody
          exact bodyType?_dropTail_swap hbody
      | some dt =>
          simp only []
          have hpre : Block.bodyType? b0.body.dropLast b0.input
              = some (remapShape ds b0.output) := by
            rw [← hsplit] at hbody; exact bodyType?_dropTail_swap hbody
          have hhd := head_swap_of_targetFire hUnique hmem ht
          have hdecomp : b0.body.dropLast
              = Instr.swap dt :: b0.body.dropLast.tail :=
            dropLast_head_tail hhd hlen
          rw [hdecomp] at hpre
          exact bodyType?_dropHead_swap hpre

/-- Every seam-edited block is `WellTyped` in the seam-cancelled program. -/
theorem seamBlock_wellTyped {program : Program} {b0 : Block}
    (hUnique : program.LabelsUnique) (hAll : program.AllBlocksTyped)
    (hmem : b0 ∈ program.blocks) :
    (seamBlock program b0).WellTyped (seamCancelProgram program) := by
  refine ⟨seamBlock_bodyType? hUnique hAll hmem, ?_⟩
  rw [seamBlock_term]
  exact seamBlock_term_type? hUnique hAll hmem

/-- **The WellTyped gate.** Seam cancellation preserves whole-program
`WellTyped`. -/
theorem seamCancelProgram_wellTyped {program : Program}
    (h : program.WellTyped) :
    (seamCancelProgram program).WellTyped := by
  obtain ⟨hUnique, hAll, hEntry, hEmit⟩ := h
  refine ⟨labelsUnique_seamCancelProgram hUnique, ?_,
    entry_findBlock?_seamCancelProgram hEntry,
    emittedLabelsUnique_seamCancelProgram hEmit⟩
  unfold Program.AllBlocksTyped
  rw [seamCancelProgram_blocks, List.forall_iff_forall_mem]
  intro b hb
  rw [List.mem_map] at hb
  obtain ⟨b0, hb0mem, rfl⟩ := hb
  exact seamBlock_wellTyped hUnique hAll hb0mem

/-! ## Runtime kernels for the pending-swap bisimulation (gate 2, session 63)

The runtime frontier of Route A is a 2-state bisimulation.  At a fired seam the
source `A` drops its trailing `swap d` while the unique-predecessor target `B`
drops its leading `swap d`, so the two programs' states desync by a single
`0 ↔ d+1` stack transposition across the `A → B` fallthrough edge and re-sync the
moment `B`'s (dropped) head swap would have fired.  The whole-program lift rests
on exactly two body-level facts:

* the SOURCE side is `PeepholeOpen.openRunBody_append`: since `A.body =
  A.body.dropLast ++ [swap d]`, the original `A` runs `A'`'s (`= dropLast`) body
  and then one trailing `swap d` — this is where the pending desync is born;
* the TARGET side is `openRunBody_swap_cons_resync` (below): `B` run from the
  pending state is `Rel`-related, up to `SameRuntimeData`, to `B'` run from the
  synced state, because `B`'s head swap maps the pending state back (up to
  `SameRuntimeData`) to the synced one, after which both run the identical tail.

`PendingSwap` names the inter-block state relation that the (still-open) 2-state
source-threaded `openRunN` congruence carries at a fired target's entry. -/

open Assembly (EVMState SameRuntimeData)
open InteractionSemantics
open InteractionCongruence

/-- The pending-swap state relation across a fired seam's fallthrough edge: the
ORIGINAL program's state `s_o` at the fired target's entry is one `swap d` away
from being `SameRuntimeData` to the seam-cancelled program's state `s_c` at the
same entry. -/
def PendingSwap (d : Nat) (s_c s_o : EVMState) : Prop :=
  ∃ next, EvmYul.swap (d + 1) s_o = .ok next ∧ SameRuntimeData next s_c

/-- **Target-side re-sync kernel.**  The fired target `B` (`body = swap d ::
rest`) run from the pending state `s_o` is `Rel`-related — up to
`SameRuntimeData` — to the edited target `B'` (`body = rest`, entered at shape
`middle`) run from the synced state `s_c`, whenever `B`'s head swap lands
`SameRuntimeData` to `s_c`.  Direct from `openRunBody_swap_cons_ok` plus the
existing `SameRuntimeData` body congruence `openRunBody_runtimeRel`. -/
theorem openRunBody_swap_cons_resync
    {d : Nat} {rest : List Instr} {input middle output : Shape}
    {s_o s_c next : EVMState}
    (hType : Instr.type? (.swap d) input = some middle)
    (hRun : Instr.runState (.swap d) input s_o = .ok next)
    (hBody : Block.bodyType? rest middle = some output)
    (hIndep : rest.Forall Instr.ProgramCounterIndependent)
    (hSync : SameRuntimeData next s_c) :
    Simulation.Interaction.Rel (Instr.RuntimeAtRel output)
      (InteractionSemantics.Block.openRunBody (.swap d :: rest) input s_o)
      (InteractionSemantics.Block.openRunBody rest middle s_c) := by
  rw [openRunBody_swap_cons_ok hType hRun]
  exact InteractionCongruence.Block.openRunBody_runtimeRel hBody hIndep hSync

/-- Bridge: the target kernel's sync hypothesis `SameRuntimeData next s_c` (with
`next` the post-head-swap state) is exactly `PendingSwap d s_c s_o` unfolded
through `runState_swap_eq`.  Feeds `openRunBody_swap_cons_resync` at a fired
target entered in the pending state. -/
theorem sameRuntimeData_next_of_pendingSwap
    {d : Nat} {s_c s_o next : EVMState} (hd : d < 16) (input : Shape)
    (hRun : Instr.runState (.swap d) input s_o = .ok next)
    (hP : PendingSwap d s_c s_o) :
    SameRuntimeData next s_c := by
  obtain ⟨next', hswap, hsync⟩ := hP
  rw [runState_swap_eq hd] at hRun
  rw [hRun] at hswap
  injection hswap with h
  subst h
  exact hsync

/-! ### Open-body `StackRealizes` propagation (source-side depth supply)

The SOURCE-side birth kernel below needs the runtime stack to be deep enough for
the trailing `swap d` at the (internal) point where the dropped-tail body `pre`
has finished — i.e. `StackRealizes mid`, `mid` the shape after `pre`.  The
existing per-instruction `openRunAt_stackRealizes` propagates the realizes fact
one instruction at a time; these two lemmas lift it to the WHOLE open body run
as an `AllDone` invariant (shape-tagged), so `Rel.strengthen_right` can carry it
into the append kernel's bind continuation. -/

/-- Every `ok` leaf of the open one-instruction step reports the typed output
shape AND a state realizing it.  (`StackRealizes` half is `openRunAt_stackRealizes`;
the shape half is the `runAt` `type?`-tagging.) -/
theorem openRunAt_realizes_shape
    {instr : Instr} {input output : Shape} {state : EVMState}
    (hType : instr.type? input = some output)
    (hReal : StackRealizes input state) :
    Simulation.Interaction.AllDone
      (fun o : Except EVMException (EVMState × Shape) =>
        match o with
        | .error _ => True
        | .ok pair => pair.2 = output ∧ StackRealizes output pair.1)
      (InteractionSemantics.Instr.openRunAt instr input state) := by
  have hState := openRunState_stackRealizes hType hReal
  have hMapped :
      Simulation.Interaction.AllDone
        (fun o : Except EVMException (EVMState × Shape) =>
          match o with
          | .error _ => True
          | .ok pair => pair.2 = output ∧ StackRealizes output pair.1)
        (Simulation.Interaction.map (fun final => (final, output))
          (InteractionSemantics.Instr.openRunState instr input state)) := by
    refine Simulation.Interaction.AllDone.map (fun final => (final, output)) hState
      ?_ ?_
    · intro err _; exact True.intro
    · intro final hFinal; exact ⟨rfl, hFinal⟩
  simpa [InteractionSemantics.Instr.openRunAt, TypedCfg.Control.Instr.runAt, hType,
    Simulation.Interaction.map] using hMapped

/-- **Open-body `StackRealizes` propagation.**  If the body types `input` to
`output` and the entry state realizes `input`, then every `ok` leaf of the open
body run reports shape `output` and a state realizing it.  Lifts
`openRunAt_realizes_shape` across the list via `AllDone.bind`. -/
theorem openRunBody_stackRealizes :
    ∀ (body : List Instr) {input output : Shape} {state : EVMState},
      Block.bodyType? body input = some output →
      StackRealizes input state →
      Simulation.Interaction.AllDone
        (fun o : Except EVMException (EVMState × Shape) =>
          match o with
          | .error _ => True
          | .ok pair => pair.2 = output ∧ StackRealizes output pair.1)
        (InteractionSemantics.Block.openRunBody body input state)
  | [], input, output, state, hType, hReal => by
      simp only [Block.bodyType?, Option.some.injEq] at hType
      subst hType
      exact Simulation.Interaction.AllDone.done ⟨rfl, hReal⟩
  | instr :: rest, input, output, state, hType, hReal => by
      cases hHeadType : instr.type? input with
      | none => simp [Block.bodyType?, hHeadType] at hType
      | some middle =>
          have hTailType : Block.bodyType? rest middle = some output := by
            simpa [Block.bodyType?, hHeadType] using hType
          rw [openRunBody_cons_eq]
          refine Simulation.Interaction.AllDone.bind
            (openRunAt_realizes_shape hHeadType hReal) ?_ ?_
          · intro err _; exact True.intro
          · intro pair hPair
            obtain ⟨hShape, hRealMid⟩ := hPair
            rw [hShape]
            exact openRunBody_stackRealizes rest hTailType hRealMid

/-! ### Source-side pending-swap birth kernel (gate 2, session 64)

The dual of `openRunBody_swap_cons_resync`.  A fired seam SOURCE `A` runs the
dropped-tail body `A.body = pre ++ [swap d]`; the cancelled `A'` runs only `pre`.
Running from `SameRuntimeData` entry states, the two bodies' results desync by
exactly one `swap (d+1)` — i.e. the ORIGINAL result state is `PendingSwap`
w.r.t. the CANCELLED one.  This is §Session-63 frontier step (b)'s "trailing-swap
outcome IS `PendingSwap`", now green Lean.

`openRunBody_append` splits off the trailing swap; `openRunBody_runtimeRel`
handles `pre` up to `SameRuntimeData`; `openRunBody_stackRealizes` supplies the
depth for the trailing swap; `swap_swap_sameRuntimeData` (involution) closes the
`PendingSwap` witness (the second swap of the pair lands `SameRuntimeData`). -/

/-- **Source-side birth kernel.**  Running the original source body
`pre ++ [swap d]` from `s_o` is `Rel`-related to running the cancelled body `pre`
from a `SameRuntimeData` state `s_c`, with the results in `PendingSwap d` (the
original result is one `swap (d+1)` ahead of `SameRuntimeData` to the cancelled
one).  `output`/`mid` are the post-swap / pre-swap shapes; `mid` is the cancelled
block's output. -/
theorem openRunBody_dropLast_swap_pending
    {d : Nat} {pre : List Instr} {input mid output : Shape} {s_o s_c : EVMState}
    (hpre : Block.bodyType? pre input = some mid)
    (hswapType : Instr.type? (.swap d) mid = some output)
    (hIndPre : pre.Forall Instr.ProgramCounterIndependent)
    (hRel : SameRuntimeData s_o s_c)
    (hReal_c : StackRealizes input s_c) :
    Simulation.Interaction.Rel
      (Simulation.Interaction.ExceptRel (fun a b : EVMException => a = b)
        (fun lp rp : EVMState × Shape =>
          PendingSwap d rp.1 lp.1 ∧ lp.2 = output ∧ rp.2 = mid))
      (InteractionSemantics.Block.openRunBody (pre ++ [Instr.swap d]) input s_o)
      (InteractionSemantics.Block.openRunBody pre input s_c) := by
  obtain ⟨hd16, hDepthMid, _⟩ := Instr.length_of_type?_swap hswapType
  rw [openRunBody_append]
  -- Rewrite the RHS as a trivial `bind … pure` so `Rel.bind` applies.
  rw [← Simulation.Interaction.bind_pure
    (InteractionSemantics.Block.openRunBody pre input s_c)]
  -- Base congruence on `pre`, strengthened with the RIGHT-tree depth witness.
  have hPre := InteractionCongruence.Block.openRunBody_runtimeRel hpre hIndPre hRel
  have hReal := openRunBody_stackRealizes pre hpre hReal_c
  have hStrong := Simulation.Interaction.Rel.strengthen_right hPre hReal
  refine Simulation.Interaction.Rel.bind
    (errorRel := fun a b : EVMException => a = b)
    (sourceRel := fun lp rp : EVMState × Shape =>
      (SameRuntimeData lp.1 rp.1 ∧ lp.2 = mid ∧ rp.2 = mid) ∧
        (rp.2 = mid ∧ StackRealizes mid rp.1))
    (Simulation.Interaction.Rel.mono hStrong ?_) ?_
  · -- Re-seat the `strengthen_right` conjunction into the source relation.
    rintro l r ⟨hER, hProp⟩
    cases hER with
    | error he => exact .error he
    | ok hSS => exact .ok ⟨hSS, hProp⟩
  · -- Continuation: fire the trailing swap on the left, `pure` on the right.
    rintro lp rp ⟨⟨hSameStack, hLmid, hRmid⟩, _hRmid2, hRealMid⟩
    -- Depth for the trailing swap on `lp.1` (stacks equal via `SameRuntimeData`).
    have hStackEq : lp.1.stack = rp.1.stack := SameRuntimeData.stack_eq hSameStack
    have hDepth1 : (d + 1) + 1 ≤ lp.1.stack.length := by
      have h1 : mid.length ≤ rp.1.stack.length := hRealMid
      have h2 : mid.slots.length = mid.length := rfl
      rw [hStackEq]; omega
    obtain ⟨s1, s2, hE1, hE2, hSame2⟩ :=
      swap_swap_sameRuntimeData lp.1 (d + 1) (by omega) hDepth1
    have hRun1 : Instr.runState (.swap d) mid lp.1 = .ok s1 := by
      rw [runState_swap_eq hd16]; exact hE1
    show Simulation.Interaction.Rel _
      (InteractionSemantics.Block.openRunBody [Instr.swap d] lp.2 lp.1)
      (Simulation.Interaction.pure rp)
    rw [hLmid, openRunBody_swap_cons_ok hswapType hRun1]
    -- `openRunBody [] output s1 = .done (.ok (s1, output))`; RHS `pure rp`.
    refine Simulation.Interaction.Rel.done (.ok ⟨⟨s2, hE2, ?_⟩, rfl, hRmid⟩)
    exact SameRuntimeData.trans hSame2 hSameStack

end Peephole
end TypedCfg
end EvmCompiler
