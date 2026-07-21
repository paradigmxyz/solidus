import EvmCompiler.TypedCfg.ShuffleCanonPerm
import EvmCompiler.TypedCfg.PeepholeSeamCancel

/-!
# Cross-block shuffle-window canonicalisation — the CHAIN transform (session-77)

## Empirical motivation + the CORRECTED chain predicate (PEEPHOLE_PROGRESS §Session-77)

The single-block canonicaliser `shuffleCanonProgram` (WellTyped gate closed §76) fires
on nothing: every emitted swap run is one block's whole body, already minimal
pre-compaction.  §74 proved the entire **22 244 B / 43 %** swap vein is created by
`Assembly.Compact.prepare`'s `elideFallthroughJumps` merging fallthrough-adjacent
blocks.

**Session-77 probe finding (refutes the §75/§76 "refCount-1 jump-follow" recipe).**  A
decisive Lean probe reconstructing the real ECB/ASP cfgs and reproducing §74's
post-compaction canon-saving (ECB **412**, ASP **7430**, byte-exact) established the
*actual* merge predicate:

* `elideFallthroughJumps` elides `jump L; label L` in the **lowered assembly stream** —
  i.e. it merges blocks that are **consecutive in `blocksInLoweringOrder?`** where the
  earlier block's terminator is `jump (next block's label)`.  This is *lowering-order
  adjacency*, NOT the refCount-1 jump-follow of §72.
* The swap-carrying blocks are **not literal `.swap` runs**: they carry trailing
  `.bindLocals` instructions (the ONLY non-swap body instr observed in chain blocks:
  ECB 377, ASP 779), which lower to `[]` (runtime + byte transparent) but *relabel*
  slots at the type level.
* Requiring every non-head chain member to be non-entry with `refCount = 1` (needed so
  emptying it is sound — interior entries then unobserved) costs **zero** savings
  (ECB 412, ASP 7430 unchanged): every merged interior already is refCount-1.
* Two facts hold on **100 %** of chains (ECB 168/168, ASP 108/108): the concatenated
  chain bodies type `head.input → tail.output`, and the shape after applying
  `canonSwaps` to `head.input` is `relabelCompatible` with `tail.output`.

## The transform (fail-closed concentrate-in-head)

A **chain** is a maximal `A → B → … → Z` of consecutive `blocksInLoweringOrder?` blocks
whose bodies are `.swap`/`.bindLocals` only, each linked by `A.term = jump B.label`, with
every non-head member non-entry and `refCount = 1`.  With `merged` = the concatenated
swap depths and `finalOut = Z.output`:

* **Head `A`** ↦ body `(canonSwaps merged).map .swap ++ [.relabel finalOut]`, output
  `finalOut`.  The trailing `.relabel finalOut` absorbs the dropped `.bindLocals`
  relabelings (it lowers to `[]`, so byte-wise the head is just the canonical swaps).
* **Consumed `B..Z`** ↦ emptied: `input := output := finalOut`, `body := []`.

The edit **fires only if** `bodyType? headBody A.input = some finalOut` (a decidable
check subsuming the `relabelCompatible` fact) — so WellTyped of the head is immediate
from the firing condition.  Both streams realise the same net stack permutation, so the
runtime `EVMState` at the chain **exit** is identical (interiors differ by a pending
permutation — the §63-65 `PendingPerm σ` runtime tower, the item-2 frontier).  Only
`input`/`output`/`body` change; `label`/`term` are preserved verbatim.

This module banks the transform **definitions**, the structural (label/entry/uniqueness)
preservation, and helper lemmas.  Imported by **nobody** in the certified spine ⟹ it
cannot affect the `compile_correct` axioms.
-/

namespace EvmCompiler
namespace TypedCfg
namespace ShuffleCanon

open TypedCfg (Instr Shape Terminator Block Program Label)
open Peephole (refCount)

/-! ## Chain-body recognition (`.swap` modulo transparent `.bindLocals`) -/

/-- `some ds` iff `body` is `.swap`/`.bindLocals` only, with swap depths `ds` (in order).
`.bindLocals` lowers to `[]` so it is byte/runtime transparent; it is skipped here. -/
def chainBodyDepths? : List Instr → Option (List Nat)
  | [] => some []
  | .swap d :: rest => (chainBodyDepths? rest).map (d :: ·)
  | .bindLocals _ _ :: rest => chainBodyDepths? rest
  | _ :: _ => none

/-- A block eligible for chain membership: its body is `.swap`/`.bindLocals` only. -/
def chainBodyOk (b : Block) : Bool := (chainBodyDepths? b.body).isSome

/-! ## Chain identification over `blocksInLoweringOrder?` -/

/-- One chain step: `a` links to its lowering-order successor `nxt` iff both bodies are
chain-eligible, `a` jumps to `nxt`, and `nxt` is a non-entry `refCount = 1` block. -/
def chainStep (prog : Program) (a nxt : Block) : Bool :=
  (a.term == Terminator.jump nxt.label) && chainBodyOk a && chainBodyOk nxt &&
    (refCount prog nxt.label == 1) && (nxt.label != prog.entry)

/-- Grow a maximal chain starting at `b` through the remaining lowering-order blocks. -/
def growChain (prog : Program) : Block → List Block → List Block
  | b, [] => [b]
  | b, nxt :: rest =>
      if chainStep prog b nxt then b :: growChain prog nxt rest else [b]

/-- Per-block edit produced by the scan. -/
inductive Edit where
  | head (body : List Instr) (out : Shape)
  | consumed (out : Shape)
  deriving Repr

/-- Edits for one grown chain (length ≥ 2).  Fail-closed: emits nothing unless the
canonicalised head body types `head.input → finalOut`. -/
def chainEdits (chain : List Block) : List (Label × Edit) :=
  match chain with
  | [] => []
  | hd :: tailBlocks =>
      let finalOut := (chain.getLastD hd).output
      let merged := chain.flatMap (fun b => (chainBodyDepths? b.body).getD [])
      let canonBody := (canonSwaps merged).map Instr.swap ++ [Instr.relabel finalOut]
      if Block.bodyType? canonBody hd.input == some finalOut then
        (hd.label, Edit.head canonBody finalOut) ::
          tailBlocks.map (fun b => (b.label, Edit.consumed finalOut))
      else []

/-- Scan the lowering order left to right, accumulating chain edits (fuel-bounded). -/
def scanEdits (prog : Program) : Nat → List Block → List (Label × Edit)
  | 0, _ => []
  | _, [] => []
  | fuel + 1, b :: rest =>
      let chain := growChain prog b rest
      if 2 ≤ chain.length then
        chainEdits chain ++ scanEdits prog fuel (rest.drop (chain.length - 1))
      else
        scanEdits prog fuel rest

/-- The whole-program edit table, keyed by block label. -/
def editTable (program : Program) : List (Label × Edit) :=
  match program.blocksInLoweringOrder? with
  | none => []
  | some ordered => scanEdits program program.blocks.length ordered

/-! ## The transform (bodies + retyped interior shapes only; labels/terms fixed) -/

/-- Apply an edit-table entry to one block (identity if absent). -/
def applyEdit (tbl : List (Label × Edit)) (block : Block) : Block :=
  match tbl.lookup block.label with
  | some (.head body out) => { block with body := body, output := out }
  | some (.consumed out) => { block with input := out, output := out, body := [] }
  | none => block

/-- Whole-program cross-block chain canonicalisation. -/
def chainCanonProgram (program : Program) : Program :=
  { program with blocks := program.blocks.map (applyEdit (editTable program)) }

/-! ## `chainBodyDepths?` characterisation -/

/-- Empty body is a (trivial) chain body. -/
@[simp] theorem chainBodyDepths?_nil : chainBodyDepths? [] = some [] := rfl

/-! ## `growChain` structure -/

/-- A grown chain always begins with its seed block. -/
theorem growChain_head (prog : Program) (b : Block) (bs : List Block) :
    ∃ t, growChain prog b bs = b :: t := by
  cases bs with
  | nil => exact ⟨[], rfl⟩
  | cons nxt rest =>
      unfold growChain
      by_cases h : chainStep prog b nxt = true
      · rw [if_pos h]; exact ⟨growChain prog nxt rest, rfl⟩
      · rw [if_neg h]; exact ⟨[], rfl⟩

/-- Consecutive members of a grown chain are `chainStep`-linked. -/
theorem growChain_chain' (prog : Program) (b : Block) (bs : List Block) :
    List.Chain' (fun x y => chainStep prog x y = true) (growChain prog b bs) := by
  induction bs generalizing b with
  | nil => exact List.chain'_singleton b
  | cons nxt rest ih =>
      unfold growChain
      by_cases h : chainStep prog b nxt = true
      · rw [if_pos h]
        obtain ⟨t, ht⟩ := growChain_head prog nxt rest
        have ihn := ih nxt
        rw [ht] at ihn ⊢
        exact List.IsChain.cons_cons h ihn
      · rw [if_neg h]; exact List.isChain_singleton b

/-- A grown chain is a prefix of its seed-plus-remaining list. -/
theorem growChain_prefix (prog : Program) (b : Block) (bs : List Block) :
    growChain prog b bs <+: b :: bs := by
  induction bs generalizing b with
  | nil => exact ⟨[], rfl⟩
  | cons nxt rest ih =>
      unfold growChain
      by_cases h : chainStep prog b nxt = true
      · rw [if_pos h]
        obtain ⟨t, ht⟩ := ih nxt
        exact ⟨t, by rw [List.cons_append, ht]⟩
      · rw [if_neg h]; exact ⟨nxt :: rest, rfl⟩

/-! ## Scan membership decomposition -/

/-- Any entry produced by `scanEdits` comes from a fired chain grown at the front of
some suffix of the scanned block list. -/
theorem scanEdits_mem {prog : Program} {fuel : Nat} {ordered : List Block}
    {p : Label × Edit} (h : p ∈ scanEdits prog fuel ordered) :
    ∃ b rest, (b :: rest) <:+ ordered ∧
      2 ≤ (growChain prog b rest).length ∧ p ∈ chainEdits (growChain prog b rest) := by
  induction fuel generalizing ordered with
  | zero => simp only [scanEdits, List.not_mem_nil] at h
  | succ fuel ih =>
      cases ordered with
      | nil => simp only [scanEdits, List.not_mem_nil] at h
      | cons b rest =>
          rw [scanEdits] at h
          by_cases hlen : 2 ≤ (growChain prog b rest).length
          · rw [if_pos hlen, List.mem_append] at h
            cases h with
            | inl h => exact ⟨b, rest, List.suffix_refl _, hlen, h⟩
            | inr h =>
                obtain ⟨b', rest', hsuf, hlen', hmem'⟩ := ih h
                exact ⟨b', rest', hsuf.trans ((List.drop_suffix _ _).trans (List.suffix_cons b rest)),
                  hlen', hmem'⟩
          · rw [if_neg hlen] at h
            obtain ⟨b', rest', hsuf, hlen', hmem'⟩ := ih h
            exact ⟨b', rest', hsuf.trans (List.suffix_cons b rest), hlen', hmem'⟩

/-- The structure of a fired chain's edit list, unpacked from any of its members. -/
theorem chainEdits_fired {chain : List Block} {p : Label × Edit}
    (h : p ∈ chainEdits chain) :
    ∃ hd tl, chain = hd :: tl ∧
      Block.bodyType?
          ((canonSwaps (chain.flatMap (fun b => (chainBodyDepths? b.body).getD []))).map Instr.swap
            ++ [Instr.relabel (chain.getLastD hd).output]) hd.input
        = some (chain.getLastD hd).output ∧
      (p = (hd.label, Edit.head
              ((canonSwaps (chain.flatMap (fun b => (chainBodyDepths? b.body).getD []))).map Instr.swap
                ++ [Instr.relabel (chain.getLastD hd).output]) (chain.getLastD hd).output)
        ∨ ∃ C ∈ tl, p = (C.label, Edit.consumed (chain.getLastD hd).output)) := by
  cases chain with
  | nil => simp only [chainEdits, List.not_mem_nil] at h
  | cons hd tl =>
      rw [chainEdits] at h
      split at h
      · rename_i hc
        refine ⟨hd, tl, rfl, eq_of_beq hc, ?_⟩
        rw [List.mem_cons] at h
        cases h with
        | inl h => exact Or.inl h
        | inr h =>
            rw [List.mem_map] at h
            obtain ⟨C, hC, hCeq⟩ := h
            exact Or.inr ⟨C, hC, hCeq.symm⟩
      · simp only [List.not_mem_nil] at h

/-! ## Fail-closed head typing (the reusable WellTyped crux)

`chainEdits` emits a `.head` edit **only** when its (relabel-terminated) canonical body
already type-checks `head.input → finalOut`.  This lemma extracts that guarantee — the
body half of the future head `WellTyped` obligation — directly from the firing branch,
and pins the consumed tail structure.  (The remaining WellTyped work is the terminator
obligation + edit-table/refCount consistency, mirroring §72's
`seamBlockEff_term_type?` / `cleanTgt?_none_of_cleanSrc?_none`.) -/
theorem chainEdits_head_spec {chain : List Block} {l : Label}
    {body : List Instr} {out : Shape} {rest : List (Label × Edit)}
    (h : chainEdits chain = (l, .head body out) :: rest) :
    ∃ hd tl, chain = hd :: tl ∧ l = hd.label ∧
      Block.bodyType? body hd.input = some out ∧
      out = (chain.getLastD hd).output ∧
      rest = tl.map (fun b => (b.label, Edit.consumed out)) := by
  cases chain with
  | nil => simp only [chainEdits, reduceCtorEq] at h
  | cons hd tl =>
      simp only [chainEdits] at h
      split at h
      · rename_i hc
        simp only [List.cons.injEq, Prod.mk.injEq, Edit.head.injEq] at h
        obtain ⟨⟨hl, hbody, hout⟩, hrest⟩ := h
        subst hout
        refine ⟨hd, tl, rfl, hl.symm, ?_, rfl, hrest.symm⟩
        rw [← hbody]; exact eq_of_beq hc
      · simp only [reduceCtorEq] at h

/-! ## Shape / body accessors of the transform -/

/-- The transform moves a block's `input` only when it is *consumed* (`input := out`);
head and untouched blocks keep their `input`. -/
theorem applyEdit_input_eq (tbl : List (Label × Edit)) (block : Block) :
    (applyEdit tbl block).input =
      (match tbl.lookup block.label with
       | some (.consumed out) => out
       | _ => block.input) := by
  unfold applyEdit
  cases tbl.lookup block.label with
  | none => rfl
  | some e => cases e <;> rfl

/-- The transform moves a block's `output` to `out` for head/consumed edits. -/
theorem applyEdit_output_eq (tbl : List (Label × Edit)) (block : Block) :
    (applyEdit tbl block).output =
      (match tbl.lookup block.label with
       | some (.head _ out) => out
       | some (.consumed out) => out
       | none => block.output) := by
  unfold applyEdit
  cases tbl.lookup block.label with
  | none => rfl
  | some e => cases e <;> rfl

/-! ## `Shape.compatible` reflexivity -/

theorem slotsAgree_self : ∀ xs : List Slot, Shape.slotsAgree xs xs = true
  | [] => rfl
  | x :: xs => by
      cases x <;> simp only [Shape.slotsAgree, slotsAgree_self xs, Bool.and_true,
        decide_true, Bool.or_true, Bool.true_or]

@[simp] theorem compatible_self (s : Shape) : Shape.compatible s s = true := by
  simp only [Shape.compatible, slotsAgree_self, Bool.true_and, if_true, ite_self]

/-! ## Structural preservation (bodies/shapes only ⇒ labels/terms/entry fixed) -/

@[simp] theorem applyEdit_label (tbl : List (Label × Edit)) (block : Block) :
    (applyEdit tbl block).label = block.label := by
  unfold applyEdit
  cases tbl.lookup block.label with
  | none => rfl
  | some e => cases e <;> rfl

@[simp] theorem applyEdit_term (tbl : List (Label × Edit)) (block : Block) :
    (applyEdit tbl block).term = block.term := by
  unfold applyEdit
  cases tbl.lookup block.label with
  | none => rfl
  | some e => cases e <;> rfl

@[simp] theorem chainCanonProgram_entry (program : Program) :
    (chainCanonProgram program).entry = program.entry := rfl

@[simp] theorem chainCanonProgram_blocks (program : Program) :
    (chainCanonProgram program).blocks =
      program.blocks.map (applyEdit (editTable program)) := rfl

/-- Block lookup commutes with the transform. -/
theorem findBlock?_chainCanonProgram (program : Program) (label : Label) :
    (chainCanonProgram program).findBlock? label =
      (program.findBlock? label).map (applyEdit (editTable program)) := by
  simp only [chainCanonProgram, Program.findBlock?]
  induction program.blocks with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.map_cons, List.find?_cons, applyEdit_label]
      by_cases h : (b.label == label) = true
      · simp [h]
      · simp only [h, Bool.false_eq_true, if_false]; exact ih

/-- The transform preserves the emitted-label multiset. -/
theorem emittedLabels_chainCanonProgram (program : Program) :
    (chainCanonProgram program).EmittedLabels = program.EmittedLabels := by
  unfold Program.EmittedLabels
  rw [chainCanonProgram_blocks, List.flatMap_map]
  apply List.flatMap_congr
  intro b _
  simp only [applyEdit_label, applyEdit_term]

/-- The transform preserves whole-program `LabelsUnique`. -/
theorem labelsUnique_chainCanonProgram {program : Program}
    (h : program.LabelsUnique) : (chainCanonProgram program).LabelsUnique := by
  unfold Program.LabelsUnique at h ⊢
  rw [chainCanonProgram_blocks, List.pairwise_map]
  refine h.imp ?_
  intro a b hab
  simpa only [applyEdit_label] using hab

/-- The transform preserves `EmittedLabelsUnique`. -/
theorem emittedLabelsUnique_chainCanonProgram {program : Program}
    (h : program.EmittedLabelsUnique) :
    (chainCanonProgram program).EmittedLabelsUnique := by
  unfold Program.EmittedLabelsUnique
  rw [emittedLabels_chainCanonProgram]
  exact h

/-- The transform preserves existence of the entry block. -/
theorem entry_findBlock?_chainCanonProgram {program : Program}
    (h : program.findBlock? program.entry ≠ none) :
    (chainCanonProgram program).findBlock? (chainCanonProgram program).entry ≠ none := by
  rw [chainCanonProgram_entry, findBlock?_chainCanonProgram]
  cases hFind : program.findBlock? program.entry with
  | none => exact absurd hFind h
  | some block => simp

/-- `labelShape?` of the chain-canonicalised program: only *consumed* blocks move
their input (to `finalOut`); heads and untouched blocks keep it.  Analog of §72's
`labelShape?_seamCancelProgramEff`. -/
theorem labelShape?_chainCanonProgram (program : Program) (L : Label) :
    (chainCanonProgram program).labelShape? L =
      (program.findBlock? L).map (fun b =>
        match (editTable program).lookup b.label with
        | some (.consumed out) => out
        | _ => b.input) := by
  unfold Program.labelShape?
  rw [findBlock?_chainCanonProgram]
  cases hFind : program.findBlock? L with
  | none => rfl
  | some b => simp only [Option.map_some]; rw [applyEdit_input_eq]

end ShuffleCanon
end TypedCfg
end EvmCompiler
