import EvmCompiler.TypedCfg.Typing
import EvmCompiler.TypedCfg.Lower

/-!
# Shuffle-window canonicalisation (session-74, "the big vein")

## Empirical motivation (PEEPHOLE_PROGRESS §Session-74)

An opcode histogram of the live shipped runtime bytecode of the worst
size-ratio corpus contracts found that **`SWAP` opcodes are 55 %** of the
sample's bytes (90 % on `AdversarialStackPressure`). Every emitted `SWAP` sits
inside a maximal run of consecutive `SWAP`s, and a per-instruction provenance
probe (reconstructing `finalCfg.lower?` byte-exact and tagging each emitted
instr with its owning block) established the decisive altitude fact:

* **0 / 400 (ECB) and 0 / 2574 (DynamicStorage) emitted swap runs cross a block
  boundary.** Every run is emitted by the body of a *single* cfg block — a run of
  consecutive `.swap` `Instr`s. (Contrast the §60-73 seam campaign, whose
  redundancy was inherently cross-block.)

A run of `k` swaps realises some permutation of the stack top; the *minimal*
number of `(0,d)`-transpositions realising the same permutation is usually far
smaller (e.g. an `AdversarialStackPressure` run of **240** swaps has identity net
permutation → **0**). Minimising every run to a same-permutation swap list
recovers **22 244 B (43 % of the sample)** — the largest optimisation vein by
50×+ over any seam residual.

## The transform

`canonSwaps` takes a run's swap depths, computes its net permutation on the
touched stack prefix (`netStack`), decomposes that permutation back into a
`(0,d)`-transposition list (`starDecompose`, a selection sort — correct by
construction, minimality NOT required), and returns it **only when strictly
shorter** (so `canonSwaps s |>.length ≤ s.length` always). `canonBody` rewrites
every maximal literal `.swap` run in a block body; `canonBlock` /
`shuffleCanonProgram` lift it to a program, changing **only** block bodies.

Because both the old and new run realise the *same* permutation of the stack,
they induce the same `EVMState` and the same typed `Shape` transformation — so
`block.input`/`output`/`term`/`label` are all preserved verbatim, WellTyped is
preserved, and (unlike the seam bisimulation) the runtime relation is literal
`EVMState` **equality** at every block boundary.

This module banks the transform definitions and the structural
(label/entry/findBlock?/uniqueness) preservation lemmas. The permutation-algebra
core (`netStack` determines `bodyType?`/`runBody`; `starDecompose` realises its
argument), the WellTyped gate, the runtime equality congruence, and the splice
are the documented frontier (§Session-74). This leaf is imported by nobody in
the certified spine, so it cannot affect the `compile_correct` axioms.
-/

namespace EvmCompiler
namespace TypedCfg
namespace ShuffleCanon

/-! ## Permutation algebra on the touched stack prefix -/

/-- Swap the elements at positions `0` and `k` of `xs` (identity if either is
out of range). Models one `.swap k` acting on the stack top window. -/
def applySwap {α : Type _} (k : Nat) (xs : List α) : List α :=
  match xs[0]?, xs[k]? with
  | some a, some b => (xs.set 0 b).set k a
  | _, _ => xs

/-- Net reordering of the identity window `range m` produced by applying the
list of transposition positions (`(0, kᵢ)`) left to right. `netStack ps m [i]` is
the original slot now at position `i`. -/
def netStack (swaps : List Nat) (m : Nat) : List Nat :=
  swaps.foldl (fun acc k => applySwap k acc) (List.range m)

/-- Window size touched by a run: one past its deepest swap depth. -/
def maxDepth (swaps : List Nat) : Nat :=
  swaps.foldl Nat.max 0

/-- One selection-sort step: place the value `i` at position `i` using at most
two `(0,d)`-transpositions, threading the working array and the emitted swaps. -/
def sortStep (st : List Nat × List Nat) (i : Nat) : List Nat × List Nat :=
  let b := st.1
  let acc := st.2
  let p := b.findIdx (· == i)
  -- `p = i`: value `i` is already at position `i` — emit nothing (else two more
  -- spurious transpositions inflate the result and defeat the length gate).
  let sw := if p == i then [] else if p == 0 then [i] else [p, i]
  (sw.foldl (fun a k => applySwap k a) b, acc ++ sw)

/-- Swaps that sort `b0` back to the identity `range b0.length`, processing
positions `b0.length-1` down to `1`. -/
def sortToId (b0 : List Nat) : List Nat :=
  (((List.range b0.length).drop 1).reverse.foldl sortStep (b0, [])).2

/-- A `(0,d)`-transposition list realising the permutation whose net window is
`target` (i.e. `netStack (starDecompose target) target.length = target`, the
frontier correctness lemma). Selection sort is its own inverse under reversal. -/
def starDecompose (target : List Nat) : List Nat :=
  (sortToId target).reverse

/-- Canonicalise a run of **cfg** swap depths, used only when strictly shorter
(so `(canonSwaps s).length ≤ s.length` always).

A cfg `.swap d` is the opcode `SWAP(d+1)` = the transposition `(0, d+1)` of the
stack (see `Instr.type?`/`runState`), so we work in *position* units `p = d + 1`
inside `netStack`/`starDecompose` and convert back with `p - 1` at the boundary. -/
def canonSwaps (swaps : List Nat) : List Nat :=
  let positions := swaps.map (· + 1)
  let c := starDecompose (netStack positions (maxDepth positions + 1))
  if c.length < swaps.length then c.map (· - 1) else swaps

theorem canonSwaps_length_le (swaps : List Nat) :
    (canonSwaps swaps).length ≤ swaps.length := by
  unfold canonSwaps
  by_cases h :
      (starDecompose (netStack (swaps.map (· + 1))
        (maxDepth (swaps.map (· + 1)) + 1))).length < swaps.length
  · simp only [h, if_true, List.length_map]; exact Nat.le_of_lt h
  · simp only [h, if_false]; exact Nat.le_refl _

/-! ## Body rewrite -/

/-- Swap depth of an instruction, if it is a `.swap`. -/
def swapDepth? : Instr → Option Nat
  | .swap d => some d
  | _ => none

/-- Whether an instruction is a `.swap`. -/
def isSwapInstr (i : Instr) : Bool := (swapDepth? i).isSome

/-- Emit the canonicalised form of an accumulated swap run (as `.swap` instrs). -/
def emitRun (run : List Nat) : List Instr :=
  (canonSwaps run).map Instr.swap

/-- Body rewrite worker: `run` accumulates the depths of the swap run currently
being scanned; on any non-swap instruction the run is flushed (canonicalised)
and the instruction re-emitted. Structural recursion on the instruction list. -/
def canonBodyGo : List Nat → List Instr → List Instr
  | run, [] => emitRun run
  | run, i :: rest =>
      match swapDepth? i with
      | some d => canonBodyGo (run ++ [d]) rest
      | none => emitRun run ++ i :: canonBodyGo [] rest

/-- Rewrite every maximal literal run of consecutive `.swap` instructions in a
block body to its canonical (perm-equal, no-longer) form. Non-swap instructions
are untouched. -/
def canonBody (body : List Instr) : List Instr := canonBodyGo [] body

/-- Canonicalise one block: only the body changes. -/
def canonBlock (block : Block) : Block :=
  { block with body := canonBody block.body }

/-- Whole-program shuffle-window canonicalisation. Touches block bodies only. -/
def shuffleCanonProgram (program : Program) : Program :=
  { program with blocks := program.blocks.map canonBlock }

/-! ## Structural preservation (bodies-only ⇒ every label/shape/term preserved) -/

@[simp] theorem canonBlock_label (block : Block) :
    (canonBlock block).label = block.label := rfl

@[simp] theorem canonBlock_input (block : Block) :
    (canonBlock block).input = block.input := rfl

@[simp] theorem canonBlock_output (block : Block) :
    (canonBlock block).output = block.output := rfl

@[simp] theorem canonBlock_term (block : Block) :
    (canonBlock block).term = block.term := rfl

@[simp] theorem shuffleCanonProgram_entry (program : Program) :
    (shuffleCanonProgram program).entry = program.entry := rfl

@[simp] theorem shuffleCanonProgram_blocks (program : Program) :
    (shuffleCanonProgram program).blocks = program.blocks.map canonBlock := rfl

/-- Block lookup commutes with canonicalisation. -/
theorem findBlock?_shuffleCanonProgram (program : Program) (label : Label) :
    (shuffleCanonProgram program).findBlock? label =
      (program.findBlock? label).map canonBlock := by
  simp only [shuffleCanonProgram, Program.findBlock?]
  induction program.blocks with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.map_cons, List.find?_cons, canonBlock_label]
      by_cases h : (b.label == label) = true
      · simp [h]
      · simp only [h, Bool.false_eq_true, if_false]; exact ih

/-- Canonicalisation preserves the emitted-label multiset. -/
theorem emittedLabels_shuffleCanonProgram (program : Program) :
    (shuffleCanonProgram program).EmittedLabels = program.EmittedLabels := by
  unfold Program.EmittedLabels
  rw [shuffleCanonProgram_blocks, List.flatMap_map]
  apply List.flatMap_congr
  intro b _
  simp only [canonBlock_label, canonBlock_term]

/-- Canonicalisation preserves whole-program `LabelsUnique`. -/
theorem labelsUnique_shuffleCanonProgram {program : Program}
    (h : program.LabelsUnique) :
    (shuffleCanonProgram program).LabelsUnique := by
  unfold Program.LabelsUnique at h ⊢
  rw [shuffleCanonProgram_blocks, List.pairwise_map]
  refine h.imp ?_
  intro a b hab
  simpa only [canonBlock_label] using hab

/-- Canonicalisation preserves `EmittedLabelsUnique`. -/
theorem emittedLabelsUnique_shuffleCanonProgram {program : Program}
    (h : program.EmittedLabelsUnique) :
    (shuffleCanonProgram program).EmittedLabelsUnique := by
  unfold Program.EmittedLabelsUnique
  rw [emittedLabels_shuffleCanonProgram]
  exact h

/-- Canonicalisation preserves the existence of the entry block. -/
theorem entry_findBlock?_shuffleCanonProgram {program : Program}
    (h : program.findBlock? program.entry ≠ none) :
    (shuffleCanonProgram program).findBlock? (shuffleCanonProgram program).entry
      ≠ none := by
  rw [shuffleCanonProgram_entry, findBlock?_shuffleCanonProgram]
  cases hFind : program.findBlock? program.entry with
  | none => exact absurd hFind h
  | some block => simp

end ShuffleCanon
end TypedCfg
end EvmCompiler
