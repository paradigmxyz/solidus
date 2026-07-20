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

end Peephole
end TypedCfg
end EvmCompiler
