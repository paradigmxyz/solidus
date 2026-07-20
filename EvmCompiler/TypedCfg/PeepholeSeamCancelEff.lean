import EvmCompiler.TypedCfg.PeepholeSeamCancel
import EvmCompiler.TypedCfg.Lower

/-!
# Route-α seam canceller: conjugating, clean-seam variant (session-70/71)

PEEPHOLE_PROGRESS §Session-70/71 established, by per-instruction provenance +
`wellTyped?`/`lower?` probes on the ExternalCallBox corpus, the exact shape of the
61 removable `SWAPn;SWAPn` seams and the **corrected** transform:

* Every source block of a firing seam has body **exactly** `[.swap d,
  .bindLocals 0 names]` (`d + 1 < names.length`), terminator `.jump G`, `G` a
  unique-predecessor non-entry block whose head is `.swap d`. The `.bindLocals`
  lowers to `[]` and runs as an EVMState identity, so `A` *emits* only `swap d`,
  which abuts `G`'s head `swap d` after `elideFallthroughJumps` — the removable
  pair (§60, confirmed 61/61).

* **The naive "drop the swap, keep the bind" edit is UNSOUND at the type level.**
  The trailing `bindLocals 0 names` *relabels* the swapped slots; dropping the
  upstream swap makes it mislabel the runtime values (probe: it named position 0
  `param` where `param_1` actually sits). The sound edit must **conjugate the
  bind's names** through the `0 ↔ d+1` transposition:
  `bindLocals 0 names ↦ bindLocals 0 (swapPos 0 (d+1) names)`, re-typing the
  source `output` as `remapShape d output` (exactly as the shipped
  `seamCancelProgram` does). `bindLocals` is a runtime identity for *any* names,
  so the runtime is untouched by the name permutation.

* Because these blocks emit a **single** swap (head = emitted-tail), a swap shared
  by a chain `C → A → B` would be double-claimed. The `2 ≤ length`-distinct-index
  disjointness of the shipped canceller does not hold here, so a seam fires only
  when **both endpoints' swaps are private** (`cleanSrc?` / `cleanTgt?`): the
  source is not itself a seam target and its target is not itself a seam source.
  On ECB this fires on 53/61 seams (8 dropped to overlap), yielding a **well-typed,
  lowerable** program (`wellTyped? = true`, probe) with a real byte delta.

This leaf is the **static half** of the corrected Route-α transform. It is
imported by **nobody** in the spine and hence cannot affect the `compile_correct`
axioms; the runtime pending-swap bisimulation + splice is the remaining frontier.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open TypedCfg (Instr Shape Terminator Block Program Label)

/-- Conjugate a body instruction by the `0 ↔ d+1` transposition. Only the trailing
`bindLocals` name list is permuted (a runtime no-op — `bindLocals` is an EVMState
identity for any names). Everything else is fixed. -/
def conjBind (d : Nat) : Instr → Instr
  | .bindLocals off names => .bindLocals off (swapPos 0 (d + 1) names)
  | other => other

/-- Raw source-firing predicate. Block `a` heads a removable seam iff it emits
**exactly** `[.swap d, .bindLocals 0 names]` (with `d + 1 < names.length`) and
jumps to a unique-predecessor, non-entry block `b` whose head is `.swap d`. -/
def srcRaw? (program : Program) (a : Block) : Option Nat :=
  match a.term with
  | .jump bLabel =>
      if bLabel ≠ program.entry ∧ refCount program bLabel = 1 then
        match program.findBlock? bLabel, a.body with
        | some b, [.swap d, .bindLocals 0 names] =>
            match b.body.head? with
            | some (.swap d') =>
                if d = d' ∧ d + 1 < names.length ∧ 2 ≤ b.body.length then some d
                else none
            | _ => none
        | _, _ => none
      else none
  | _ => none

/-- Raw target-firing predicate (mirror of the shipped `targetFire?`, using
`srcRaw?`). -/
def tgtRaw? (program : Program) (b : Block) : Option Nat :=
  if b.label ≠ program.entry ∧ refCount program b.label = 1 then
    match program.blocks.find? (fun a => a.term == Terminator.jump b.label) with
    | some a => srcRaw? program a
    | none => none
  else none

/-- Clean source-firing: `a` source-fires, is **not** itself a seam target, and its
target block is **not** itself a seam source (both endpoint swaps private). -/
def cleanSrc? (program : Program) (a : Block) : Option Nat :=
  match srcRaw? program a with
  | some d =>
      if tgtRaw? program a = none then
        match a.term with
        | .jump bLabel =>
            match program.findBlock? bLabel with
            | some b => if srcRaw? program b = none then some d else none
            | none => none
        | _ => none
      else none
  | none => none

/-- Clean target-firing: `b` target-fires, is **not** itself a seam source, and its
sole predecessor is **not** itself a seam target. -/
def cleanTgt? (program : Program) (b : Block) : Option Nat :=
  match tgtRaw? program b with
  | some d =>
      if srcRaw? program b = none then
        match program.blocks.find? (fun a => a.term == Terminator.jump b.label) with
        | some a => if tgtRaw? program a = none then some d else none
        | none => none
      else none
  | none => none

/-- Per-block corrected seam edit. A clean source drops its head/emitted swap and
**conjugates** the trailing bind (re-typing `output` by `remapShape d`); a clean
target drops its head swap (re-typing `input` by `remapShape d`). The two are
disjoint (`cleanSrc?_cleanTgt?_disjoint`), so the nesting order is immaterial. -/
def seamBlockEff (program : Program) (block : Block) : Block :=
  match cleanSrc? program block with
  | some d =>
      { block with output := remapShape d block.output,
                   body := (block.body.tail).map (conjBind d) }
  | none =>
      match cleanTgt? program block with
      | some d =>
          { block with input := remapShape d block.input, body := block.body.tail }
      | none => block

/-- Whole-program corrected seam cancellation. -/
def seamCancelProgramEff (program : Program) : Program :=
  { program with blocks := program.blocks.map (seamBlockEff program) }

/-! ## Disjointness of the source/target edits -/

/-- A block is never simultaneously a clean source and a clean target: `cleanSrc?`
requires `tgtRaw? = none` while `cleanTgt?` requires `tgtRaw? ≠ none`. -/
theorem cleanSrc?_cleanTgt?_disjoint (program : Program) (block : Block) :
    cleanSrc? program block = none ∨ cleanTgt? program block = none := by
  by_cases hs : cleanSrc? program block = none
  · exact Or.inl hs
  · refine Or.inr ?_
    -- cleanSrc? ≠ none ⟹ tgtRaw? = none ⟹ cleanTgt? = none.
    have hT : tgtRaw? program block = none := by
      by_contra hT
      apply hs
      unfold cleanSrc?
      split
      · rw [if_neg hT]
      · rfl
    unfold cleanTgt?
    split
    · rename_i d heq; rw [hT] at heq; exact absurd heq (by simp)
    · rfl

/-! ## Structural preservation (label / terminator / count / lookup / uniqueness)

The corrected edits only touch `input` / `output` / `body`, never `label` or
`term`, so the whole-program label structure is invariant. -/

@[simp] theorem seamBlockEff_label (program : Program) (block : Block) :
    (seamBlockEff program block).label = block.label := by
  unfold seamBlockEff
  cases cleanSrc? program block <;> cases cleanTgt? program block <;> rfl

@[simp] theorem seamBlockEff_term (program : Program) (block : Block) :
    (seamBlockEff program block).term = block.term := by
  unfold seamBlockEff
  cases cleanSrc? program block <;> cases cleanTgt? program block <;> rfl

@[simp] theorem seamCancelProgramEff_entry (program : Program) :
    (seamCancelProgramEff program).entry = program.entry := rfl

@[simp] theorem seamCancelProgramEff_blocks (program : Program) :
    (seamCancelProgramEff program).blocks =
      program.blocks.map (seamBlockEff program) := rfl

/-- Block lookup commutes with the corrected seam cancellation. -/
theorem findBlock?_seamCancelProgramEff (program : Program) (label : Label) :
    (seamCancelProgramEff program).findBlock? label =
      (program.findBlock? label).map (seamBlockEff program) := by
  simp only [seamCancelProgramEff, Program.findBlock?]
  induction program.blocks with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.map_cons, List.find?_cons, seamBlockEff_label]
      by_cases h : (b.label == label) = true
      · simp [h]
      · simp only [h, Bool.false_eq_true, if_false]; exact ih

/-- The corrected cancellation preserves the emitted-label multiset. -/
theorem emittedLabels_seamCancelProgramEff (program : Program) :
    (seamCancelProgramEff program).EmittedLabels = program.EmittedLabels := by
  unfold Program.EmittedLabels
  rw [seamCancelProgramEff_blocks, List.flatMap_map]
  apply List.flatMap_congr
  intro b _
  simp only [seamBlockEff_label, seamBlockEff_term]

/-- The corrected cancellation preserves whole-program `LabelsUnique`. -/
theorem labelsUnique_seamCancelProgramEff {program : Program}
    (h : program.LabelsUnique) :
    (seamCancelProgramEff program).LabelsUnique := by
  unfold Program.LabelsUnique at h ⊢
  rw [seamCancelProgramEff_blocks, List.pairwise_map]
  refine h.imp ?_
  intro a b hab
  simpa only [seamBlockEff_label] using hab

/-- The corrected cancellation preserves `EmittedLabelsUnique`. -/
theorem emittedLabelsUnique_seamCancelProgramEff {program : Program}
    (h : program.EmittedLabelsUnique) :
    (seamCancelProgramEff program).EmittedLabelsUnique := by
  unfold Program.EmittedLabelsUnique
  rw [emittedLabels_seamCancelProgramEff]
  exact h

/-- The corrected cancellation preserves the existence of the entry block. -/
theorem entry_findBlock?_seamCancelProgramEff {program : Program}
    (h : program.findBlock? program.entry ≠ none) :
    (seamCancelProgramEff program).findBlock? (seamCancelProgramEff program).entry
      ≠ none := by
  rw [seamCancelProgramEff_entry, findBlock?_seamCancelProgramEff]
  cases hFind : program.findBlock? program.entry with
  | none => exact absurd hFind h
  | some block => simp

/-! ## List transposition helpers for the body-conjugation kernel -/

/-- `swapPos` commutes with `List.map`. -/
theorem swapPos_map {α β : Type _} (f : α → β) (i j : Nat) (l : List α) :
    (swapPos i j l).map f = swapPos i j (l.map f) := by
  unfold swapPos
  rw [List.getElem?_map, List.getElem?_map]
  cases l[i]? <;> cases l[j]? <;>
    simp only [Option.map_none, Option.map_some] <;>
    rw [List.map_set, List.map_set]

/-- If either index is out of range, the transposition is a no-op. -/
theorem swapPos_eq_of_oob {α : Type _} (i j : Nat) (l : List α)
    (h : ¬ (i < l.length ∧ j < l.length)) : swapPos i j l = l := by
  unfold swapPos
  rcases Nat.lt_or_ge i l.length with hi | hi
  · have hj : ¬ j < l.length := fun hh => h ⟨hi, hh⟩
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hj)]
    cases l[i]? <;> rfl
  · rw [List.getElem?_eq_none hi]

/-- Transposing two positions that both lie in the left summand leaves the right
summand untouched. -/
theorem swapPos_append_left {α : Type _} (i j : Nat) (xs ys : List α)
    (hi : i < xs.length) (hj : j < xs.length) :
    swapPos i j (xs ++ ys) = swapPos i j xs ++ ys := by
  apply List.ext_getElem?
  intro k
  have hi' : i < (xs ++ ys).length := by rw [List.length_append]; omega
  have hj' : j < (xs ++ ys).length := by rw [List.length_append]; omega
  rw [swapPos_getElem? i j (xs ++ ys) k hi' hj']
  by_cases hk : k < xs.length
  · have e2 : (swapPos i j xs ++ ys)[k]? = (swapPos i j xs)[k]? :=
      List.getElem?_append_left (l₂ := ys) (by rw [swapPos_length]; exact hk)
    rw [e2, swapPos_getElem? i j xs k hi hj,
        List.getElem?_append_left (l₂ := ys) hi,
        List.getElem?_append_left (l₂ := ys) hj,
        List.getElem?_append_left (l₂ := ys) hk]
  · have hklen : xs.length ≤ k := Nat.le_of_not_lt hk
    have hjk : j ≠ k := by omega
    have hik : i ≠ k := by omega
    rw [if_neg hjk, if_neg hik,
        List.getElem?_append_right (l₂ := ys) hklen,
        List.getElem?_append_right (l₂ := ys)
          (show (swapPos i j xs).length ≤ k by rw [swapPos_length]; exact hklen),
        swapPos_length]

/-- Dropping past both transposed positions erases the transposition. -/
theorem swapPos_drop {α : Type _} (i j n : Nat) (l : List α)
    (hi : i < n) (hj : j < n) :
    (swapPos i j l).drop n = l.drop n := by
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_drop, List.getElem?_drop]
  by_cases hbound : i < l.length ∧ j < l.length
  · rw [swapPos_getElem? i j l (n + k) hbound.1 hbound.2]
    have hne1 : j ≠ n + k := by omega
    have hne2 : i ≠ n + k := by omega
    rw [if_neg hne1, if_neg hne2]
  · rw [swapPos_eq_of_oob i j l hbound]

/-! ## The body-typing conjugation kernel (source-arm WellTyped, the crux)

Running the conjugated edited body `[bindLocals 0 (swapPos 0 (d+1) names)]` from
`input` types to `remapShape d output`, whenever the original body
`[swap d, bindLocals 0 names]` types `input` to `output` with `d+1 < names.length`.
This is the "conjugate the transposition through the bind's shape map" identity
that §Session-70 flagged as the frontier — expressible here as a single permuted
`bindLocals` because the swap positions `0, d+1` fall within the (offset-0)
overwritten name range. -/

/-- `bindLocals 0 names` typing, computed. -/
theorem type?_bindLocals0 {names : List String} {s t : Shape}
    (h : Instr.type? (.bindLocals 0 names) s = some t) :
    names.length ≤ s.slots.length ∧
      t.slots = names.map Slot.local ++ s.slots.drop names.length ∧
      t.tail = s.tail := by
  simp only [Instr.type?, Shape.bindLocals?, Shape.length] at h
  by_cases hb : names.length ≤ s.slots.length
  · rw [if_pos (by simpa using hb)] at h
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨hb, ?_, rfl⟩
    simp [List.take_zero]
  · rw [if_neg (by simpa using hb)] at h
    exact absurd h (by simp)

/-- Construct `bindLocals 0 names` typing from the length bound. -/
theorem type?_bindLocals0_of_le {names : List String} {s : Shape}
    (h : names.length ≤ s.slots.length) :
    Instr.type? (.bindLocals 0 names) s
      = some { s with slots := names.map Slot.local ++ s.slots.drop names.length } := by
  simp only [Instr.type?, Shape.bindLocals?, Shape.length]
  rw [if_pos (by simpa using h)]
  simp [List.take_zero]

/-- **The conjugation kernel.** -/
theorem bodyType?_conj {d : Nat} {names : List String} {input output : Shape}
    (hlen : d + 1 < names.length)
    (h : Block.bodyType? [Instr.swap d, Instr.bindLocals 0 names] input = some output) :
    Block.bodyType? [Instr.bindLocals 0 (swapPos 0 (d + 1) names)] input
      = some (remapShape d output) := by
  -- Unpack the original body.
  rw [bodyType?_cons, Option.bind_eq_some_iff] at h
  obtain ⟨m, hswap, hrest⟩ := h
  rw [bodyType?_cons, Option.bind_eq_some_iff] at hrest
  obtain ⟨o, hbind, hnil⟩ := hrest
  simp only [Block.bodyType?, Option.some.injEq] at hnil
  subst hnil
  -- swap facts.
  obtain ⟨hslots_m, htail_m⟩ := type?_swap_eq hswap
  obtain ⟨hd16, hdepth, hmlen⟩ := Instr.length_of_type?_swap hswap
  -- m = remapShape d input.
  have hm_eq : m = remapShape d input := type?_swap_eq_remapShape hswap
  -- bindLocals facts on m.
  obtain ⟨hNamesLeM, hOslots, hOtail⟩ := type?_bindLocals0 hbind
  -- names.length ≤ input.slots.length (swap preserves length).
  have hNamesLeIn : names.length ≤ input.slots.length := by
    have : m.slots.length = input.slots.length := by
      rw [hslots_m, swapPos_length]
    omega
  have hLnames : (swapPos 0 (d + 1) names).length ≤ input.slots.length := by
    rw [swapPos_length]; exact hNamesLeIn
  -- Compute the conjugated body.
  rw [bodyType?_cons, Option.bind_eq_some_iff]
  refine ⟨_, type?_bindLocals0_of_le hLnames, ?_⟩
  simp only [Block.bodyType?, Option.some.injEq, swapPos_length]
  -- Reduce to a slots + tail equality via a small extensionality helper.
  have shapeExt : ∀ (s1 s2 : Shape), s1.slots = s2.slots → s1.tail = s2.tail → s1 = s2 := by
    intro s1 s2 h1 h2; cases s1; cases s2; simp_all
  refine shapeExt _ _ ?_ ?_
  · -- slots
    show (swapPos 0 (d + 1) names).map Slot.local ++ input.slots.drop names.length
        = (remapShape d o).slots
    rw [remapShape]
    show (swapPos 0 (d + 1) names).map Slot.local ++ input.slots.drop names.length
        = swapPos 0 (d + 1) o.slots
    rw [hOslots, hslots_m]
    -- RHS = swapPos 0 (d+1) (names.map local ++ (swapPos 0 (d+1) input.slots).drop names.length)
    have h0L : (0 : Nat) < (names.map Slot.local).length := by
      rw [List.length_map]; omega
    have hdL : d + 1 < (names.map Slot.local).length := by
      rw [List.length_map]; exact hlen
    rw [swapPos_append_left 0 (d + 1) _ _ h0L hdL]
    rw [← swapPos_map]
    congr 1
    -- (swapPos 0 (d+1) input.slots).drop names.length = input.slots.drop names.length
    rw [swapPos_drop 0 (d + 1) names.length input.slots (by omega) hlen]
  · -- tail
    show input.tail = (remapShape d o).tail
    rw [remapShape]
    show input.tail = o.tail
    rw [hOtail, htail_m]

end Peephole
end TypedCfg
end EvmCompiler
