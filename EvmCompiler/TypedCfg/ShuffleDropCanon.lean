import EvmCompiler.TypedCfg.ShuffleCanon
import EvmCompiler.TypedCfg.ShuffleCanonPerm

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

/-! ## Drop-aware naturality and the gather factoring (the §75 analogue)

`runDrop` is built from `applySwap` and `List.tail`, both natural under `List.map`.
Hence `runDrop` factors through the net window permutation-with-drops, exactly as
`applySwaps` did in `ShuffleCanonType` — the substrate the net-effect minimiser's
correctness rests on. -/

/-- `SDOp.apply` is natural under `List.map`. -/
theorem SDOp.apply_map {α β : Type _} (f : α → β) (o : SDOp) (l : List α) :
    o.apply (l.map f) = (o.apply l).map f := by
  cases o with
  | swap d => simpa [SDOp.apply] using ShuffleCanon.applySwap_map f (d + 1) l
  | pop => cases l with
    | nil => rfl
    | cons a l => rfl

/-- `runDrop` is natural under `List.map`. -/
theorem runDrop_map {α β : Type _} (f : α → β) (ops : List SDOp) (l : List α) :
    runDrop ops (l.map f) = (runDrop ops l).map f := by
  induction ops generalizing l with
  | nil => rfl
  | cons o ops ih => rw [runDrop_cons, runDrop_cons, SDOp.apply_map, ih]

/-- **The gather factoring.** `runDrop ops xs` is the net window trace
`runDrop ops (range xs.length)` used to gather from `xs`.  Drop-aware analogue of
`ShuffleCanon.applySwaps_eq_gather`. -/
theorem runDrop_eq_gather {α : Type _} [Inhabited α] (ops : List SDOp)
    (xs : List α) :
    runDrop ops xs = (runDrop ops (List.range xs.length)).map (fun j => xs[j]!) := by
  conv_lhs => rw [← ShuffleCanon.range_map_getElem! xs]
  rw [runDrop_map]

/-- **Net-trace congruence.** Two windows with equal net trace on the shared length
window act identically on any list. -/
theorem runDrop_congr_of_range {α : Type _} [Inhabited α]
    (ops qs : List SDOp) (xs : List α)
    (h : runDrop ops (List.range xs.length) = runDrop qs (List.range xs.length)) :
    runDrop ops xs = runDrop qs xs := by
  rw [runDrop_eq_gather ops xs, runDrop_eq_gather qs xs, h]

/-! ## Window locality: a wide-enough window is preserved as a suffix

`fits ops n` says a length-`n` window is wide enough to observe `ops` without the
operations ever reaching below position `n`: each swap depth is in range at the
current (post-pop) width and every pop has a head to drop.  Under `fits`, the tail
below the window is carried through untouched — the drop-aware analogue of
`ShuffleCanon.applySwaps_append_left`. -/

/-- Width sufficiency: the window never shrinks below the reach of the remaining
ops. Each `.pop` shrinks the observed width by one. -/
def fits : List SDOp → Nat → Prop
  | [], _ => True
  | .swap d :: rest, n => d + 1 < n ∧ fits rest n
  | .pop :: rest, n => 0 < n ∧ fits rest (n - 1)

/-- **Locality.** If a length-`xs` window fits `ops`, the sub-window `ys` below it
is preserved verbatim as a suffix. -/
theorem runDrop_append_left {α : Type _} (ops : List SDOp) (xs ys : List α)
    (h : fits ops xs.length) :
    runDrop ops (xs ++ ys) = runDrop ops xs ++ ys := by
  induction ops generalizing xs with
  | nil => rfl
  | cons o ops ih =>
      cases o with
      | swap d =>
          obtain ⟨hd, hrest⟩ := h
          simp only [runDrop_cons, SDOp.apply]
          rw [ShuffleCanon.applySwap_append_left (d + 1) xs ys hd,
              ih (ShuffleCanon.applySwap (d + 1) xs) (by
                rwa [ShuffleCanon.length_applySwap])]
      | pop =>
          obtain ⟨h0, hrest⟩ := h
          have hxs : xs ≠ [] := by
            intro hnil; rw [hnil] at h0; exact absurd h0 (by simp)
          obtain ⟨a, xs', rfl⟩ : ∃ a xs', xs = a :: xs' := by
            cases xs with
            | nil => exact absurd rfl hxs
            | cons a xs' => exact ⟨a, xs', rfl⟩
          simp only [runDrop_cons, SDOp.apply, List.cons_append, List.tail_cons]
          exact ih xs' (by simpa using hrest)

/-! ## Reusable realization lemmas (pops as `drop`, position-swaps as `applySwaps`) -/

/-- A run of `.pop`s drops that many head slots. -/
theorem runDrop_replicate_pop {α : Type _} (k : Nat) (xs : List α) :
    runDrop (List.replicate k .pop) xs = xs.drop k := by
  induction k generalizing xs with
  | zero => simp [runDrop]
  | succ k ih =>
      rw [List.replicate_succ, runDrop_cons, SDOp.apply, ih]
      cases xs with
      | nil => simp
      | cons a xs => simp [List.drop_succ_cons]

/-- A `.swap`-only window built from a **position** list `ps` (each `≥ 1`) realises
`ShuffleCanon.applySwaps ps` (recall `SDOp.swap d = applySwap (d+1)`, so position
`p` is depth `p - 1`). -/
theorem runDrop_swapmap {α : Type _} (ps : List Nat) (xs : List α)
    (h : ∀ p ∈ ps, 1 ≤ p) :
    runDrop (ps.map (fun p => SDOp.swap (p - 1))) xs =
      ShuffleCanon.applySwaps ps xs := by
  induction ps generalizing xs with
  | nil => rfl
  | cons p ps ih =>
      simp only [List.map_cons, runDrop_cons, SDOp.apply,
        ShuffleCanon.applySwaps_cons]
      have hp : p - 1 + 1 = p := by have := h p (by simp); omega
      rw [hp, ih _ (fun q hq => h q (by simp [hq]))]

/-- Every element of a net trace came from the input window. -/
theorem runDrop_mem (ops : List SDOp) (l : List Nat)
    {x : Nat} (hx : x ∈ runDrop ops l) : x ∈ l := by
  induction ops generalizing l with
  | nil => simpa using hx
  | cons o ops ih =>
      rw [runDrop_cons] at hx
      have hstep : x ∈ o.apply l := ih (o.apply l) hx
      cases o with
      | swap d =>
          simp only [SDOp.apply] at hstep
          exact (ShuffleCanon.applySwap_perm (d + 1) l).mem_iff.1 hstep
      | pop =>
          simp only [SDOp.apply] at hstep
          exact List.mem_of_mem_tail hstep

/-- A net trace of a `Nodup` window is `Nodup`. -/
theorem runDrop_nodup (ops : List SDOp) {l : List Nat} (hl : l.Nodup) :
    (runDrop ops l).Nodup := by
  induction ops generalizing l with
  | nil => simpa using hl
  | cons o ops ih =>
      rw [runDrop_cons]
      apply ih
      cases o with
      | swap d =>
          simp only [SDOp.apply]
          exact (ShuffleCanon.applySwap_perm (d + 1) l).nodup_iff.2 hl
      | pop =>
          simp only [SDOp.apply]
          exact hl.sublist (List.tail_sublist l)

/-! ## The drop-aware net-effect minimiser

`netEffect ops` (`= runDrop ops (range N)`, `N = sdDepth + popCount + 1`) is the
list of surviving original slots, top-first.  The minimal-length realisation of the
same net effect (a *permutation-then-drop*): bring the `popCount` dead slots to the
top and pop them, having reused `ShuffleCanon.starDecompose` on the survivor
permutation.  Concretely, realise the window permutation whose net image is
`dead ++ survivors` (`dead` = the complement of the survivors in `range N`), then
drop the `popCount` dead heads.  Fired only when strictly shorter, so the length
bound is immediate. -/

/-- The dropped original slots: the complement of the survivors in `range N`. -/
def deadSlots (ops : List SDOp) : List Nat :=
  (List.range (sdDepth ops + popCount ops + 1)).filter
    (fun j => decide (j ∉ netEffect ops))

/-- The realisation: canonical survivor-then-drop permutation, then the pops. -/
def realize (ops : List SDOp) : List SDOp :=
  (ShuffleCanon.starDecompose (deadSlots ops ++ netEffect ops)).map
      (fun p => SDOp.swap (p - 1))
    ++ List.replicate (popCount ops) SDOp.pop

/-- The minimiser: fire the realisation only when strictly shorter (fail-open on
savings, never lengthens — the cross-pop successor to `canonAcrossPops`). -/
def minimizeWindow (ops : List SDOp) : List SDOp :=
  if (realize ops).length < ops.length then realize ops else ops

/-- **Length bound.** The minimiser never lengthens a window (gated). -/
theorem minimizeWindow_length_le (ops : List SDOp) :
    (minimizeWindow ops).length ≤ ops.length := by
  unfold minimizeWindow
  split
  · exact Nat.le_of_lt (by assumption)
  · exact Nat.le_refl _

/-! ## Type-preservation kernel for the extended `{SWAP, POP}` alphabet

The single `.pop` typing dictionary (`type?` on a `.pop` drops the head slot,
leaving the frame `tail` fixed) plus the forward window-threading fact: a
`{SWAP,POP}` window's typed `Shape` transition threads the slots by exactly
`runDrop` and preserves the frame `tail` — the drop-aware analogue of
`ShuffleCanonType.bodyType?_map_swap_eq`.  `bodyType?` through a `.pop` is a
tail-shape step, matching `SDOp.apply .pop = List.tail`. -/

/-- **The `.pop` typing dictionary.** `type? .pop` succeeds iff the slots are
non-empty, and then drops the head slot while leaving the frame `tail` fixed. -/
theorem type?_pop_eq_tail {input output : Shape}
    (hType : Instr.type? .pop input = some output) :
    input.slots ≠ [] ∧
      output = { slots := input.slots.tail, tail := input.tail } := by
  cases input with
  | mk slots tail =>
    cases slots with
    | nil => simp [Instr.type?] at hType
    | cons a rest =>
        simp only [Instr.type?, Option.some.injEq] at hType
        subst hType
        exact ⟨by simp, by simp⟩

/-- **Per-op shape step.**  Applying one shuffle-drop op at the type level threads
the slots by `SDOp.apply` and leaves the frame `tail` fixed. -/
theorem type?_sdOp_slots (op : SDOp) {input output : Shape}
    (hType : Instr.type? (sdToInstr op) input = some output) :
    output.slots = op.apply input.slots ∧ output.tail = input.tail := by
  cases op with
  | swap d =>
      obtain ⟨_, _, hEq⟩ := ShuffleCanon.type?_swap_eq_applySwap (d := d) hType
      rw [hEq]; exact ⟨rfl, rfl⟩
  | pop =>
      obtain ⟨_, hEq⟩ := type?_pop_eq_tail hType
      rw [hEq]; exact ⟨rfl, rfl⟩

/-- **Forward window threading.**  If a `{SWAP,POP}` window types from `input`, its
output slots are exactly `runDrop ops input.slots` and its frame `tail` is fixed. -/
theorem bodyType?_sdWindow_eq (ops : List SDOp) (input out : Shape)
    (hType : Block.bodyType? (ops.map sdToInstr) input = some out) :
    out.slots = runDrop ops input.slots ∧ out.tail = input.tail := by
  induction ops generalizing input with
  | nil =>
      simp only [List.map_nil, Block.bodyType?, Option.some.injEq] at hType
      subst hType; exact ⟨rfl, rfl⟩
  | cons o ops ih =>
      simp only [List.map_cons, Block.bodyType?] at hType
      cases hMid : Instr.type? (sdToInstr o) input with
      | none => rw [hMid] at hType; simp at hType
      | some mid =>
          rw [hMid] at hType
          obtain ⟨hslots, htail⟩ := type?_sdOp_slots o hMid
          obtain ⟨hout, houttail⟩ := ih mid hType
          rw [runDrop_cons]
          refine ⟨?_, ?_⟩
          · rw [hout, hslots]
          · rw [houttail, htail]

/-- **Typing implies `fits` (with the depth-`< 16` lowering gate).**  If a
`{SWAP, POP}` window types from `input`, then it `fits input.slots.length` (each
swap depth is in range, each pop has a head) — so the canonical-width correctness
applies whenever `input.slots.length` reaches the canonical width — and moreover
every swap depth is `< 16`, i.e. the window already lowers to real `SWAP1..16`
opcodes.  This is the bridge the single-block WellTyped gate rests on. -/
theorem fits_of_bodyType? (ops : List SDOp) (input out : Shape)
    (hType : Block.bodyType? (ops.map sdToInstr) input = some out) :
    fits ops input.slots.length ∧ (∀ d, SDOp.swap d ∈ ops → d < 16) := by
  induction ops generalizing input with
  | nil => exact ⟨trivial, by intro d hd; simp at hd⟩
  | cons o ops ih =>
      simp only [List.map_cons, Block.bodyType?] at hType
      cases hMid : Instr.type? (sdToInstr o) input with
      | none => rw [hMid] at hType; simp at hType
      | some mid =>
          rw [hMid] at hType
          obtain ⟨ihFits, ihLt⟩ := ih mid hType
          cases o with
          | swap d =>
              obtain ⟨hLt16, hIdx, _⟩ := ShuffleCanon.type?_swap_eq_applySwap hMid
              obtain ⟨_, htail⟩ := type?_sdOp_slots (SDOp.swap d) hMid
              refine ⟨⟨hIdx, ?_⟩, ?_⟩
              · have hslots : mid.slots = ShuffleCanon.applySwap (d + 1) input.slots :=
                  (type?_sdOp_slots (SDOp.swap d) hMid).1
                have : mid.slots.length = input.slots.length := by
                  rw [hslots, ShuffleCanon.length_applySwap]
                rwa [this] at ihFits
              · intro e he
                rcases List.mem_cons.1 he with h | h
                · cases h; exact hLt16
                · exact ihLt e h
          | pop =>
              obtain ⟨hne, hEq⟩ := type?_pop_eq_tail hMid
              have hlen : mid.slots.length = input.slots.length - 1 := by
                rw [hEq]; simp [List.length_tail]
              refine ⟨⟨?_, ?_⟩, ?_⟩
              · exact List.length_pos_of_ne_nil hne
              · rw [hlen] at ihFits; exact ihFits
              · intro e he
                rcases List.mem_cons.1 he with h | h
                · exact absurd h (by simp)
                · exact ihLt e h

/-! ## Fold accounting for `popCount` / `sdDepth`

`popCount` and `sdDepth` are left folds with an accumulator; the following
cons-recursion lemmas (via the standard additive/`max`-distributing accumulator
lemmas) are what the length and `fits` accounting below need. -/

private theorem popCount_acc (ops : List SDOp) (a : Nat) :
    ops.foldl (fun n o => match o with | .pop => n + 1 | .swap _ => n) a
      = a + popCount ops := by
  induction ops generalizing a with
  | nil => simp [popCount]
  | cons o ops ih =>
      rw [List.foldl_cons, ih]
      conv_rhs => rw [popCount, List.foldl_cons, ih]
      cases o <;> simp <;> omega

theorem popCount_cons_swap (d : Nat) (ops : List SDOp) :
    popCount (SDOp.swap d :: ops) = popCount ops := rfl

theorem popCount_cons_pop (ops : List SDOp) :
    popCount (SDOp.pop :: ops) = popCount ops + 1 := by
  show List.foldl (fun n o => match o with | .pop => n + 1 | .swap _ => n) 1 ops
      = popCount ops + 1
  rw [popCount_acc]; omega

private theorem sdDepth_acc (ops : List SDOp) (a : Nat) :
    ops.foldl (fun m o => match o with | .swap d => Nat.max m (d + 1) | .pop => m) a
      = Nat.max a (sdDepth ops) := by
  induction ops generalizing a with
  | nil => simp [sdDepth]
  | cons o ops ih =>
      rw [List.foldl_cons, ih]
      conv_rhs => rw [sdDepth, List.foldl_cons, ih]
      cases o <;> simp <;> omega

theorem sdDepth_cons_swap (d : Nat) (ops : List SDOp) :
    sdDepth (SDOp.swap d :: ops) = Nat.max (d + 1) (sdDepth ops) := by
  show List.foldl (fun m o => match o with | .swap d => Nat.max m (d + 1) | .pop => m)
      (Nat.max 0 (d + 1)) ops = Nat.max (d + 1) (sdDepth ops)
  rw [sdDepth_acc]; simp

theorem sdDepth_cons_pop (ops : List SDOp) :
    sdDepth (SDOp.pop :: ops) = sdDepth ops := by
  show List.foldl (fun m o => match o with | .swap d => Nat.max m (d + 1) | .pop => m)
      0 ops = sdDepth ops
  rw [sdDepth_acc]; simp

/-! ## `fits` monotonicity and the canonical-width witness -/

/-- `fits` is monotone in the observed width. -/
theorem fits_mono {ops : List SDOp} {n m : Nat} (hnm : n ≤ m) (h : fits ops n) :
    fits ops m := by
  induction ops generalizing n m with
  | nil => trivial
  | cons o rest ih =>
      cases o with
      | swap d =>
          obtain ⟨hd, hrest⟩ := h
          exact ⟨by omega, ih hnm hrest⟩
      | pop =>
          obtain ⟨h0, hrest⟩ := h
          exact ⟨by omega, ih (by omega) hrest⟩

/-- **Accounting (c).** The canonical window width `N = sdDepth + popCount + 1`
always fits: every swap depth is in range and every pop has a head to drop. -/
theorem fits_canonical (ops : List SDOp) :
    fits ops (sdDepth ops + popCount ops + 1) := by
  induction ops with
  | nil => trivial
  | cons o rest ih =>
      cases o with
      | swap d =>
          rw [popCount_cons_swap]
          have h1 : d + 1 ≤ sdDepth (SDOp.swap d :: rest) := by
            rw [sdDepth_cons_swap]; exact Nat.le_max_left _ _
          have h2 : sdDepth rest ≤ sdDepth (SDOp.swap d :: rest) := by
            rw [sdDepth_cons_swap]; exact Nat.le_max_right _ _
          exact ⟨by omega, fits_mono (by omega) ih⟩
      | pop =>
          rw [sdDepth_cons_pop, popCount_cons_pop]
          exact ⟨by omega, by simpa using ih⟩

/-! ## Length accounting under `fits` -/

/-- **Accounting (a).** Under `fits`, each `.pop` drops exactly one slot and each
`.swap` preserves length, so a window shortens the stack by its `popCount`. -/
theorem runDrop_length {α : Type _} (ops : List SDOp) (xs : List α)
    (h : fits ops xs.length) :
    (runDrop ops xs).length = xs.length - popCount ops := by
  induction ops generalizing xs with
  | nil => simp [popCount]
  | cons o rest ih =>
      cases o with
      | swap d =>
          obtain ⟨hd, hrest⟩ := h
          rw [runDrop_cons, SDOp.apply, popCount_cons_swap]
          rw [ih (ShuffleCanon.applySwap (d + 1) xs)
              (by rw [ShuffleCanon.length_applySwap]; exact hrest)]
          rw [ShuffleCanon.length_applySwap]
      | pop =>
          obtain ⟨h0, hrest⟩ := h
          rw [runDrop_cons, SDOp.apply, popCount_cons_pop]
          have hlen : xs.tail.length = xs.length - 1 := by
            cases xs with
            | nil => simp at h0
            | cons a xs => simp
          rw [ih xs.tail (by rw [hlen]; exact hrest), hlen]
          omega

/-! ## Survivor / dead-slot accounting for the minimiser

`netEffect ops` (the survivors) has length `sdDepth + 1`, `deadSlots ops` (the
dropped slots) has length `popCount`, and `deadSlots ++ netEffect` is a
permutation of `range N` (`N = sdDepth + popCount + 1`).  These feed P1
(`netStack_starDecompose_of_perm`) at the canonical width. -/

/-- **Accounting (a′).** The survivor count is `sdDepth + 1` (the window drops
exactly its `popCount` slots from the canonical width `N`). -/
theorem netEffect_length (ops : List SDOp) :
    (netEffect ops).length = sdDepth ops + 1 := by
  unfold netEffect
  rw [runDrop_length ops _ (by rw [List.length_range]; exact fits_canonical ops),
    List.length_range]
  omega

theorem netEffect_nodup (ops : List SDOp) : (netEffect ops).Nodup :=
  runDrop_nodup ops (List.nodup_range)

theorem netEffect_subset (ops : List SDOp) :
    netEffect ops ⊆ List.range (sdDepth ops + popCount ops + 1) := by
  intro x hx; exact runDrop_mem ops _ hx

theorem deadSlots_nodup (ops : List SDOp) : (deadSlots ops).Nodup :=
  (List.nodup_range).filter _

theorem deadSlots_subset (ops : List SDOp) :
    deadSlots ops ⊆ List.range (sdDepth ops + popCount ops + 1) :=
  List.filter_subset' _

/-- Membership in `deadSlots`: a canonical slot that did **not** survive. -/
theorem mem_deadSlots {ops : List SDOp} {x : Nat} :
    x ∈ deadSlots ops ↔
      x ∈ List.range (sdDepth ops + popCount ops + 1) ∧ x ∉ netEffect ops := by
  unfold deadSlots
  rw [List.mem_filter]
  constructor
  · rintro ⟨hx, hd⟩; exact ⟨hx, by simpa using hd⟩
  · rintro ⟨hx, hd⟩; exact ⟨hx, by simpa using hd⟩

/-- **Accounting (b).** `deadSlots ++ netEffect` is a permutation of the canonical
window `range N` — both are nodup with the same membership. -/
theorem deadSlots_append_netEffect_perm (ops : List SDOp) :
    (deadSlots ops ++ netEffect ops).Perm
      (List.range (sdDepth ops + popCount ops + 1)) := by
  have hdisj : ∀ a ∈ deadSlots ops, ∀ b ∈ netEffect ops, a ≠ b := by
    intro a ha b hb hab
    subst hab
    exact absurd hb (mem_deadSlots.1 ha).2
  have hnodup : (deadSlots ops ++ netEffect ops).Nodup :=
    List.nodup_append.2 ⟨deadSlots_nodup ops, netEffect_nodup ops, hdisj⟩
  have hsub : (deadSlots ops ++ netEffect ops) ⊆
      List.range (sdDepth ops + popCount ops + 1) := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact deadSlots_subset ops h
    · exact netEffect_subset ops h
  have hsup : List.range (sdDepth ops + popCount ops + 1) ⊆
      (deadSlots ops ++ netEffect ops) := by
    intro x hx
    by_cases hxn : x ∈ netEffect ops
    · exact List.mem_append_right _ hxn
    · exact List.mem_append_left _ (mem_deadSlots.2 ⟨hx, hxn⟩)
  exact (List.subperm_of_subset hnodup hsub).antisymm
    (List.subperm_of_subset (List.nodup_range) hsup)

theorem deadSlots_append_netEffect_length (ops : List SDOp) :
    (deadSlots ops ++ netEffect ops).length = sdDepth ops + popCount ops + 1 := by
  rw [(deadSlots_append_netEffect_perm ops).length_eq, List.length_range]

theorem deadSlots_length (ops : List SDOp) :
    (deadSlots ops).length = popCount ops := by
  have h := deadSlots_append_netEffect_length ops
  rw [List.length_append, netEffect_length] at h
  omega

/-! ## The minimiser runtime correctness (canonical width, then any wider stack)

`realize ops` reproduces the window's net effect: on the canonical width it
equals `netEffect ops`; on any stack at least that wide it agrees with `ops`
pointwise (via the gather factoring / `runDrop_append_left`). -/

/-- **Core.**  On the canonical observation window `range N`, the realisation
reproduces the survivors — the P1 assembly (`netStack_starDecompose_of_perm`). -/
theorem runDrop_realize_range (ops : List SDOp) :
    runDrop (realize ops) (List.range (sdDepth ops + popCount ops + 1))
      = netEffect ops := by
  have hperm : (deadSlots ops ++ netEffect ops).Perm
      (List.range (deadSlots ops ++ netEffect ops).length) := by
    rw [deadSlots_append_netEffect_length]; exact deadSlots_append_netEffect_perm ops
  have hbounds : ∀ p ∈ ShuffleCanon.starDecompose (deadSlots ops ++ netEffect ops),
      1 ≤ p :=
    fun p hp => (ShuffleCanon.starDecompose_elem_bounds _ hperm p hp).1
  unfold realize
  rw [runDrop_append, runDrop_swapmap _ _ hbounds,
    ← ShuffleCanon.netStack_eq_applySwaps]
  rw [show sdDepth ops + popCount ops + 1
        = (deadSlots ops ++ netEffect ops).length from
      (deadSlots_append_netEffect_length ops).symm]
  rw [ShuffleCanon.netStack_starDecompose_of_perm _ hperm, runDrop_replicate_pop]
  rw [show popCount ops = (deadSlots ops).length from (deadSlots_length ops).symm,
    List.drop_left]

/-! ### `fits` for the realisation (feeds the width-extension) -/

theorem popCount_map_swap (ps : List Nat) :
    popCount (ps.map (fun p => SDOp.swap (p - 1))) = 0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => rw [List.map_cons, popCount_cons_swap]; exact ih

theorem fits_append (a b : List SDOp) (n : Nat)
    (ha : fits a n) (hb : fits b (n - popCount a)) : fits (a ++ b) n := by
  induction a generalizing n with
  | nil => simpa using hb
  | cons o rest ih =>
      cases o with
      | swap d =>
          obtain ⟨hd, hrest⟩ := ha
          rw [popCount_cons_swap] at hb
          exact ⟨hd, ih n hrest hb⟩
      | pop =>
          obtain ⟨h0, hrest⟩ := ha
          rw [popCount_cons_pop] at hb
          refine ⟨h0, ih (n - 1) hrest ?_⟩
          have hEq : n - 1 - popCount rest = n - (popCount rest + 1) := by omega
          rw [hEq]; exact hb

theorem fits_map_swap (ps : List Nat) (n : Nat)
    (h : ∀ p ∈ ps, 1 ≤ p ∧ p < n) :
    fits (ps.map (fun p => SDOp.swap (p - 1))) n := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
      obtain ⟨hp1, hpn⟩ := h p (by simp)
      refine ⟨by omega, ih (fun q hq => h q (by simp [hq]))⟩

theorem fits_replicate_pop (k n : Nat) (h : k ≤ n) :
    fits (List.replicate k SDOp.pop) n := by
  induction k generalizing n with
  | zero => trivial
  | succ k ih =>
      rw [List.replicate_succ]
      exact ⟨by omega, ih (n - 1) (by omega)⟩

/-- **Accounting (c′).**  The realisation also fits the canonical width: its swap
positions are `< N` (P1 element bounds) and it pops at most `popCount ≤ N`. -/
theorem fits_realize_canonical (ops : List SDOp) :
    fits (realize ops) (sdDepth ops + popCount ops + 1) := by
  have hperm : (deadSlots ops ++ netEffect ops).Perm
      (List.range (deadSlots ops ++ netEffect ops).length) := by
    rw [deadSlots_append_netEffect_length]; exact deadSlots_append_netEffect_perm ops
  unfold realize
  apply fits_append
  · apply fits_map_swap
    intro p hp
    obtain ⟨hp1, hpN⟩ := ShuffleCanon.starDecompose_elem_bounds _ hperm p hp
    rw [deadSlots_append_netEffect_length] at hpN
    exact ⟨hp1, hpN⟩
  · rw [popCount_map_swap, Nat.sub_zero]
    exact fits_replicate_pop _ _ (by omega)

/-- **The minimiser reproduces the net effect on any stack at least as wide as the
canonical window.**  Extends the core via the gather factoring: both `realize ops`
and `ops` agree with their net trace on `range xs.length`. -/
theorem runDrop_realize_eq (ops : List SDOp) (xs : List Nat)
    (hlen : sdDepth ops + popCount ops + 1 ≤ xs.length) :
    runDrop (realize ops) xs = runDrop ops xs := by
  apply runDrop_congr_of_range
  have hsplit : List.range xs.length
      = List.range (sdDepth ops + popCount ops + 1)
        ++ (List.range xs.length).drop (sdDepth ops + popCount ops + 1) := by
    conv_lhs => rw [← List.take_append_drop (sdDepth ops + popCount ops + 1)
      (List.range xs.length)]
    congr 1
    rw [List.take_range, Nat.min_eq_left hlen]
  rw [hsplit]
  rw [runDrop_append_left ops _ _
      (by rw [List.length_range]; exact fits_canonical ops)]
  rw [runDrop_append_left (realize ops) _ _
      (by rw [List.length_range]; exact fits_realize_canonical ops)]
  rw [runDrop_realize_range ops, netEffect]

/-- **The minimiser is runtime-transparent on a wide-enough stack.** `minimizeWindow`
either fires `realize` (net-effect equal by `runDrop_realize_eq`) or keeps `ops`
verbatim — so it never changes the window's action on any stack at least as wide as
the canonical observation window `N = sdDepth + popCount + 1`.  This is the exact
fact a single-block body-rewrite congruence consumes. -/
theorem runDrop_minimizeWindow_eq (ops : List SDOp) (xs : List Nat)
    (hlen : sdDepth ops + popCount ops + 1 ≤ xs.length) :
    runDrop (minimizeWindow ops) xs = runDrop ops xs := by
  unfold minimizeWindow
  split
  · exact runDrop_realize_eq ops xs hlen
  · rfl

end ShuffleDropCanon
end TypedCfg
end EvmCompiler
