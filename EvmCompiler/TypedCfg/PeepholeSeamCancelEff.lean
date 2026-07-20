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

end Peephole
end TypedCfg
end EvmCompiler
