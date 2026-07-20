import EvmCompiler.TypedCfg.PeepholeSeamCancel
import EvmCompiler.TypedCfg.Lower

/-!
# Route-α seam canceller: emitted-tail-swap identification (session-70)

PEEPHOLE_PROGRESS §Session-70 established, by per-instruction provenance
measurement on the ExternalCallBox corpus, that:

* all 61 removable `SWAPn;SWAPn` seams are **block-body → block-body** fallthrough
  seams (`A.term = .jump G`, `refCount G = 1`, `A` emits `…swap d` as its last
  body instruction, `G` emits `swap d` as its first) — **0** are terminator
  (return-dispatch) lowered (`removeBuriedUnder` ends in `pop`, never a swap), and
* the shipped `sourceFire?` (`PeepholeSeamCancel.lean`) fires on **0/1030** blocks
  because it keys the tail swap on `a.body.getLast?`, while the real source blocks
  are `A.body = [.swap 0, .bindLocals …]`: the swap is the last *emitted*
  instruction but a trailing **zero-lowering, runtime-identity** `.bindLocals`
  (`lower? = some []`, `runState _ s = .ok s`) is the CFG-last, so `getLast?`
  misses the swap.

This leaf is the **static half** of the Route-α correction: it re-keys the tail
swap on the last body instruction with **non-empty lowering** (`effTailSwap?`),
and removes *that* swap (`removeEffTail`) while retaining the trailing binds
(`dropLast` would wrongly delete the `.bindLocals` and leave the swap emitted —
an unsound half-cancel). Structural preservation (label / terminator / block
count / `findBlock?` / label-uniqueness) is proved here, mirroring the
`seamCancelProgram` spine. The runtime pending-swap bisimulation for the new edit
is the frontier (the trailing binds are runtime identities, so the EVMState
invariant is expected to carry through unchanged — only the `Shape` threading is
new); this leaf is imported by **nobody** in the spine and hence cannot affect the
`compile_correct` axioms.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open TypedCfg (Instr Shape Terminator Block Program Label)

/-- A body instruction that lowers to the empty assembly program (the zero-
lowering no-ops: `bindLocals` / `bindScratch` / `relabel`, and `bindLocals` with
empty binds). These are transparent to the emitted bytes. -/
def lowersToNothing (i : Instr) : Bool := i.lower? == some []

/-- The last body instruction with **non-empty** lowering — i.e. the last
instruction that actually emits bytes. Trailing zero-lowering binds are skipped. -/
def emittedTail? (body : List Instr) : Option Instr :=
  (body.filter (fun i => !lowersToNothing i)).getLast?

/-- The depth of the emitted-tail swap, if the last emitting body instruction is a
`.swap d`. This is the `getLast?`-with-trailing-binds-skipped replacement for the
shipped `sourceFire?`'s `a.body.getLast?` key. -/
def effTailSwap? (body : List Instr) : Option Nat :=
  match emittedTail? body with
  | some (.swap d) => some d
  | _ => none

/-- Remove the last **emitting** body instruction (the tail swap), keeping the
trailing zero-lowering binds in place. `dropLast` would remove the trailing bind
instead of the swap. -/
def removeEffTail (body : List Instr) : List Instr :=
  let rev := body.reverse
  match rev.dropWhile lowersToNothing with
  | [] => body
  | _ :: rest => ((rev.takeWhile lowersToNothing) ++ rest).reverse

/-- Corrected source-side firing: block `a` heads a firing seam if its terminator
is `.jump G` to a unique-predecessor, non-entry block `G` whose head swap matches
`a`'s **emitted-tail** swap. -/
def sourceFireEff? (program : Program) (a : Block) : Option Nat :=
  match a.term with
  | .jump bLabel =>
      if bLabel ≠ program.entry ∧ refCount program bLabel = 1 then
        match program.findBlock? bLabel with
        | some b =>
            match effTailSwap? a.body, b.body.head? with
            | some d, some (.swap d') =>
                if d = d' ∧ 2 ≤ a.body.length ∧ 2 ≤ b.body.length then
                  some d
                else
                  none
            | _, _ => none
        | none => none
      else
        none
  | _ => none

/-- Corrected target-side firing (mirror of `targetFire?`, using `sourceFireEff?`). -/
def targetFireEff? (program : Program) (b : Block) : Option Nat :=
  if b.label ≠ program.entry ∧ refCount program b.label = 1 then
    match program.blocks.find? (fun a => a.term == Terminator.jump b.label) with
    | some a => sourceFireEff? program a
    | none => none
  else
    none

/-- Per-block corrected seam edit: drop the emitted-tail swap if `block` heads a
firing seam (re-typing `output`), and drop the head swap if `block` tails a firing
seam (re-typing `input`). Both firing decisions read the **original** program. -/
def seamBlockEff (program : Program) (block : Block) : Block :=
  let block1 :=
    match sourceFireEff? program block with
    | some d => { block with output := remapShape d block.output, body := removeEffTail block.body }
    | none => block
  match targetFireEff? program block with
  | some d => { block1 with input := remapShape d block1.input, body := block1.body.tail }
  | none => block1

/-- Whole-program corrected seam cancellation. -/
def seamCancelProgramEff (program : Program) : Program :=
  { program with blocks := program.blocks.map (seamBlockEff program) }

/-! ## Structural preservation (label / terminator / count / lookup / uniqueness)

The corrected edits only touch `input` / `output` / `body`, never `label` or
`term`, so the whole-program label structure is invariant — exactly as for the
shipped `seamCancelProgram`. These are the structural obligations the WellTyped /
runtime tower will consume. -/

@[simp] theorem seamBlockEff_label (program : Program) (block : Block) :
    (seamBlockEff program block).label = block.label := by
  unfold seamBlockEff
  cases sourceFireEff? program block <;> cases targetFireEff? program block <;> rfl

@[simp] theorem seamBlockEff_term (program : Program) (block : Block) :
    (seamBlockEff program block).term = block.term := by
  unfold seamBlockEff
  cases sourceFireEff? program block <;> cases targetFireEff? program block <;> rfl

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
