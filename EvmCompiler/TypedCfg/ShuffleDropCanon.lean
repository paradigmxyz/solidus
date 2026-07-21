import EvmCompiler.TypedCfg.ShuffleCanon

/-!
# Shuffle-drop window canonicalisation (session-95, "the post-chain vein")

## Empirical motivation (PEEPHOLE_PROGRESS §Session-95)

After `chainCanonProgram` went LIVE (§94: corpus −7.47 % gas, −30 % runtime
bytes), a fresh opcode histogram of the shipped runtime bytecode of the worst
size-ratio contracts shows the pure-`SWAP` vein is **essentially exhausted** —
only **646 B / 2.2 %** of the worst-9 sample is still reducible as a pure swap
permutation (`chainCanon` consumed the rest: `SWAP` fell 55 %→21 % of bytes).

The **new** dominant reducible structure is the mixed `{SWAP, POP}` window:
`SWAPn;POP` (1702×), `POP;SWAPn;POP` (537×) teardown/scheduling runs. Treating a
maximal run of consecutive `.swap`/`.pop` instructions as a single *shuffle-drop*
window and minimising it to a same-net-effect (permute-then-drop) op list has a
measured **savings ceiling of 2 480 B (8.5 % of the worst-9 sample)** — ≈4× the
pure-swap residual, because interior `POP`s break swap runs and the survivor
permutation (after accounting for drops) is frequently far simpler than the raw
swap sequence.

## The transform (this module)

This module banks the **drop-aware window algebra** (`SDOp`, `runDrop`, the
net-effect simulator `netEffect`, `sdDepth`) that the full cross-pop minimiser
needs, plus a **conservative, provably-correct** first transform
`canonAcrossPops`: it canonicalises each maximal `.swap` sub-run *between* pops
with the banked `ShuffleCanon.canonSwaps` (perm-equal, no-longer), leaving every
`.pop` in place. `canonDropBody`/`canonDropBlock`/`shuffleDropProgram` lift it to
a program, changing block bodies only — so every `label`/`input`/`output`/`term`
is preserved verbatim and the structural preservation lemmas below hold.

The **cross-pop** minimiser (the actual 2 480 B vein: cancelling swaps *through*
`POP` boundaries via `netEffect`), its WellTyped/runtime net-effect-preservation,
and the chain-alphabet splice (`SWAP` → `SWAP ∪ POP` in `chainCanonProgram`) are
the documented §Session-95 frontier. This leaf is imported by **nobody** in the
certified spine, so it cannot affect the `compile_correct` axioms.
-/

namespace EvmCompiler
namespace TypedCfg
namespace ShuffleDropCanon

/-! ## Drop-aware window alphabet and semantics -/

/-- One instruction of a shuffle-drop window: a `.swap` of the given cfg depth
(`= SWAP(d+1)`, the transposition `(0, d+1)`) or a `.pop` (drop the stack top). -/
inductive SDOp where
  | swap (d : Nat)
  | pop
  deriving DecidableEq, Repr

/-- Action of one shuffle-drop op on an abstract stack window (top = head). A
`.swap d` is the `(0, d+1)` transposition (`ShuffleCanon.applySwap (d+1)`); a
`.pop` drops the head. -/
def SDOp.apply {α : Type _} (op : SDOp) (xs : List α) : List α :=
  match op with
  | .swap d => ShuffleCanon.applySwap (d + 1) xs
  | .pop => xs.tail

/-- Net effect of a shuffle-drop op list on a window, applied left to right. -/
def runDrop {α : Type _} (ops : List SDOp) (xs : List α) : List α :=
  ops.foldl (fun acc o => SDOp.apply o acc) xs

@[simp] theorem runDrop_nil {α : Type _} (xs : List α) : runDrop [] xs = xs := rfl

@[simp] theorem runDrop_cons {α : Type _} (o : SDOp) (ops : List SDOp)
    (xs : List α) : runDrop (o :: ops) xs = runDrop ops (SDOp.apply o xs) := rfl

theorem runDrop_append {α : Type _} (a b : List SDOp) (xs : List α) :
    runDrop (a ++ b) xs = runDrop b (runDrop a xs) := by
  unfold runDrop; rw [List.foldl_append]

/-- Number of `.pop`s in a window (each is a *necessary* drop: a lower bound on
the length of any net-effect-equivalent realisation). -/
def popCount (ops : List SDOp) : Nat :=
  ops.foldl (fun n o => match o with | .pop => n + 1 | .swap _ => n) 0

/-- Window depth: one past the deepest swap position touched. `netEffect` needs
an identity window of at least this many slots (plus the pop count) to observe
the full effect. -/
def sdDepth (ops : List SDOp) : Nat :=
  ops.foldl (fun m o => match o with | .swap d => Nat.max m (d + 1) | .pop => m) 0

/-- The net effect of a window as the surviving original slots (top-first),
observed on a wide-enough identity window. This is the semantic object the
cross-pop minimiser (frontier) canonicalises. -/
def netEffect (ops : List SDOp) : List Nat :=
  runDrop ops (List.range (sdDepth ops + popCount ops + 1))

/-! ## Instruction ↔ SDOp bridge -/

/-- Read an `Instr` as a shuffle-drop op, if it is a `.swap` or `.pop`. -/
def sdOp? : Instr → Option SDOp
  | .swap d => some (.swap d)
  | .pop => some .pop
  | _ => none

/-- Whether an instruction participates in a shuffle-drop window. -/
def isSDInstr (i : Instr) : Bool := (sdOp? i).isSome

/-- Lower a shuffle-drop op back to its `Instr`. -/
def sdToInstr : SDOp → Instr
  | .swap d => .swap d
  | .pop => .pop

/-! ## Conservative transform (canonicalise swap sub-runs between pops)

`canonAcrossPops` re-emits every maximal `.swap` sub-run of the window in its
`ShuffleCanon.canonSwaps` (perm-equal, no-longer) form and leaves every `.pop`
untouched. It is the provably-correct conservative floor of the shuffle-drop
campaign; the cross-pop generalisation replaces the per-run `canonSwaps` with a
`netEffect`-based minimiser (frontier). -/

/-- Emit the canonicalised form of an accumulated swap sub-run as `.swap` ops. -/
def emitSwapRun (run : List Nat) : List SDOp :=
  (ShuffleCanon.canonSwaps run).map SDOp.swap

/-- Worker: `run` accumulates depths of the current `.swap` sub-run; every `.pop`
flushes the canonicalised sub-run then re-emits the pop. -/
def canonAcrossPopsGo : List Nat → List SDOp → List SDOp
  | run, [] => emitSwapRun run
  | run, .swap d :: rest => canonAcrossPopsGo (run ++ [d]) rest
  | run, .pop :: rest => emitSwapRun run ++ .pop :: canonAcrossPopsGo [] rest

/-- Canonicalise a whole shuffle-drop window (conservative floor). -/
def canonAcrossPops (ops : List SDOp) : List SDOp := canonAcrossPopsGo [] ops

/-! ### Length monotonicity (syntactic kernel) -/

theorem emitSwapRun_length_le (run : List Nat) :
    (emitSwapRun run).length ≤ run.length := by
  unfold emitSwapRun
  rw [List.length_map]
  exact ShuffleCanon.canonSwaps_length_le run

/-- The conservative transform never lengthens a window: the accumulated run's
length is repaid on flush (`emitSwapRun_length_le`), pops map one-to-one. -/
theorem canonAcrossPopsGo_length_le (run : List Nat) (ops : List SDOp) :
    (canonAcrossPopsGo run ops).length ≤ run.length + ops.length := by
  induction ops generalizing run with
  | nil => simpa [canonAcrossPopsGo] using emitSwapRun_length_le run
  | cons o rest ih =>
      cases o with
      | swap d =>
          have h := ih (run ++ [d])
          simp only [canonAcrossPopsGo, List.length_cons]
          calc (canonAcrossPopsGo (run ++ [d]) rest).length
              ≤ (run ++ [d]).length + rest.length := h
            _ = run.length + (rest.length + 1) := by
                  rw [List.length_append]; simp [Nat.add_right_comm, Nat.add_assoc]
      | pop =>
          simp only [canonAcrossPopsGo, List.length_append, List.length_cons]
          have h := ih []
          have hr := emitSwapRun_length_le run
          calc (emitSwapRun run).length + (canonAcrossPopsGo [] rest).length.succ
              ≤ run.length + (rest.length + 1) := by
                  have : (canonAcrossPopsGo [] rest).length ≤ rest.length := by
                    simpa using h
                  omega

theorem canonAcrossPops_length_le (ops : List SDOp) :
    (canonAcrossPops ops).length ≤ ops.length := by
  simpa [canonAcrossPops] using canonAcrossPopsGo_length_le [] ops

/-! ## Body rewrite (bodies only) -/

/-- Swap-or-pop op of an instruction, for the body scanner. -/
def bodyGo : List Nat → List Instr → List Instr
  | run, [] => (emitSwapRun run).map sdToInstr
  | run, i :: rest =>
      match sdOp? i with
      | some (.swap d) => bodyGo (run ++ [d]) rest
      | some .pop => (emitSwapRun run).map sdToInstr ++ .pop :: bodyGo [] rest
      | none => (emitSwapRun run).map sdToInstr ++ i :: bodyGo [] rest

/-- Rewrite every maximal `.swap`/`.pop` window of a block body with the
conservative shuffle-drop transform; non-window instructions are untouched. -/
def canonDropBody (body : List Instr) : List Instr := bodyGo [] body

/-- Canonicalise one block: only the body changes. -/
def canonDropBlock (block : Block) : Block :=
  { block with body := canonDropBody block.body }

/-- Whole-program shuffle-drop canonicalisation. Touches block bodies only. -/
def shuffleDropProgram (program : Program) : Program :=
  { program with blocks := program.blocks.map canonDropBlock }

/-! ## Structural preservation (bodies-only ⇒ every label/shape/term preserved) -/

@[simp] theorem canonDropBlock_label (block : Block) :
    (canonDropBlock block).label = block.label := rfl

@[simp] theorem canonDropBlock_input (block : Block) :
    (canonDropBlock block).input = block.input := rfl

@[simp] theorem canonDropBlock_output (block : Block) :
    (canonDropBlock block).output = block.output := rfl

@[simp] theorem canonDropBlock_term (block : Block) :
    (canonDropBlock block).term = block.term := rfl

@[simp] theorem shuffleDropProgram_entry (program : Program) :
    (shuffleDropProgram program).entry = program.entry := rfl

@[simp] theorem shuffleDropProgram_blocks (program : Program) :
    (shuffleDropProgram program).blocks = program.blocks.map canonDropBlock := rfl

theorem findBlock?_shuffleDropProgram (program : Program) (label : Label) :
    (shuffleDropProgram program).findBlock? label =
      (program.findBlock? label).map canonDropBlock := by
  simp only [shuffleDropProgram, Program.findBlock?]
  induction program.blocks with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.map_cons, List.find?_cons, canonDropBlock_label]
      by_cases h : (b.label == label) = true
      · simp [h]
      · simp only [h, Bool.false_eq_true, if_false]; exact ih

theorem emittedLabels_shuffleDropProgram (program : Program) :
    (shuffleDropProgram program).EmittedLabels = program.EmittedLabels := by
  unfold Program.EmittedLabels
  rw [shuffleDropProgram_blocks, List.flatMap_map]
  apply List.flatMap_congr
  intro b _
  simp only [canonDropBlock_label, canonDropBlock_term]

theorem labelsUnique_shuffleDropProgram {program : Program}
    (h : program.LabelsUnique) :
    (shuffleDropProgram program).LabelsUnique := by
  unfold Program.LabelsUnique at h ⊢
  rw [shuffleDropProgram_blocks, List.pairwise_map]
  refine h.imp ?_
  intro a b hab
  simpa only [canonDropBlock_label] using hab

theorem emittedLabelsUnique_shuffleDropProgram {program : Program}
    (h : program.EmittedLabelsUnique) :
    (shuffleDropProgram program).EmittedLabelsUnique := by
  unfold Program.EmittedLabelsUnique
  rw [emittedLabels_shuffleDropProgram]
  exact h

theorem entry_findBlock?_shuffleDropProgram {program : Program}
    (h : program.findBlock? program.entry ≠ none) :
    (shuffleDropProgram program).findBlock? (shuffleDropProgram program).entry
      ≠ none := by
  rw [shuffleDropProgram_entry, findBlock?_shuffleDropProgram]
  cases hFind : program.findBlock? program.entry with
  | none => exact absurd hFind h
  | some block => simp

end ShuffleDropCanon
end TypedCfg
end EvmCompiler
