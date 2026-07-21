import EvmCompiler.TypedCfg.Syntax

/-!
# Block-reorder canonicalisation (session-99, "the jump-threading vein")

## Empirical motivation (PEEPHOLE_PROGRESS §Session-99)

After the shuffle-drop vein was closed as exhausted (§98: the banked `realize`
minimiser recovers only 8 B live, the §95 "2 480 B ceiling" was an unphysical
cost model), a fresh probe of the §95 *fallback* candidate — block-merge /
jump-threading — was run PROBE-FIRST through the REAL pipeline
(`chainCanonProgram (seamCancelEff (peephole (normalize cfg))) → lower? →
Assembly.Compact.compile? → bytes`).

The frozen serializer `Assembly.Compact.prepare` already performs the *whole*
block-merge (`elideFallthroughJumps` removes `jump L; label L`, then
`pruneUnreferencedLabels` removes the now-dead `JUMPDEST`) — **but only for
blocks that are physically adjacent in `blocksInLoweringOrder?`**.  And
`blocksInLoweringOrder?` does **no** fallthrough-greedy ordering: it pins the
entry block first and otherwise keeps `program.blocks` list order verbatim
(`Syntax.lean`).  `chainCanonProgram` (§94, LIVE) rewrites bodies of
already-adjacent chains but **never reorders**.

So the entire block-merge vein reduces to one cfg-altitude lever: **reorder
`program.blocks` so that unconditional-`jump` unique-successor edges become
physically adjacent**, letting the frozen `prepare` consume them.  Semantically
this is a *pure permutation* of the block list (blocks are label-addressed via
`findBlock?`/`JUMPDEST`), with every block's `body`/`term`/`input`/`output`
**verbatim** — far cheaper to justify than the `chainCanon`/shuffle-drop body
rewrites.

## Measured reachability (§Session-99, the SOUND transform, not a deduced ceiling)

Greedy fallthrough layout (`layoutBlocks` below), measured on 15 corpus contracts
(60 % of corpus runtime bytes) through the real pipeline:

* **891 B measured** total delta (2.05 % of the 43 496 B measured base);
  extrapolates to ≈1 100–1 300 B / ≈ −1.5 %…−1.8 % corpus-wide.
* Every measured reorder was a genuine permutation (`isPerm = true`) with
  **zero** `.fallthrough` terminators (`ftTerms = 0`) ⟹ the reordered bytecode is
  semantically equivalent (only PCs move; jumps re-resolve).
* The §95 block-merge "≈2 300 B ceiling" (927 `PUSHn;JUMP;JUMPDEST` triples) is
  itself a ≈4× mirage under the §98 discipline: the sound-reachable delta on the
  worst-7 is 547 B, not 2 300 B — a block can fall through to only ONE successor,
  and most surviving triples target multi-predecessor (`refCount ≥ 2`) blocks.

This is ≈110× the shuffle-drop live delta (8 B), sound, and proof-cheaper than
`chainCanon`.  This module banks the **total transform + structural floor**
(the §57/§95 "transform + structural kernels FIRST" pattern).  The deep
preservation tower (block-multiset `Perm`, `findBlock?` permutation-congruence of
the cfg operational semantics, `WellTyped`/PCI/fuel invariance, the OIC
`_of_source` forward-refinement + the 8-site `CertifiedChoice` rewire) is the
successor's frontier — see §Session-99.

This module is imported by nobody ⟹ it cannot touch the `compile_correct` cone.
-/

namespace EvmCompiler.TypedCfg.BlockReorder

open EvmCompiler.TypedCfg

/-- The unconditional-jump fallthrough candidate of a block: the target label of
its terminator when that terminator is an unconditional `jump`. -/
def succLabel? (b : Block) : Option Label :=
  match b.term with
  | .jump t => some t
  | _ => none

/-- List-`find?` block lookup by label (returns an actual member of `blocks`,
which makes the structural-floor membership lemmas below provable). -/
def lookup? (blocks : List Block) (l : Label) : Option Block :=
  blocks.find? (fun b => b.label == l)

/-- Grow one fallthrough chain from `start`: emit `start`, then follow its
unconditional-`jump` successor while unplaced.  Fuel-bounded (total). -/
def growLayout (blocks : List Block) :
    Nat → Label → List Label → (List Block × List Label)
  | 0, _, placed => ([], placed)
  | fuel + 1, start, placed =>
      if placed.contains start then ([], placed)
      else
        match lookup? blocks start with
        | none => ([], placed)
        | some b =>
            let placed := start :: placed
            match succLabel? b with
            | some t =>
                let (rest, placed) := growLayout blocks fuel t placed
                (b :: rest, placed)
            | none => ([b], placed)

/-- Greedy fallthrough-maximising block order: seed chains at the entry then at
every block label in order, laying each block right after its unconditional-jump
predecessor whenever possible. -/
def layoutBlocks (p : Program) : List Block :=
  let seeds := p.entry :: p.blocks.map (·.label)
  (seeds.foldl
    (fun (st : List Block × List Label) s =>
      let g := growLayout p.blocks p.blocks.length s st.2
      (st.1 ++ g.1, g.2))
    ([], [])).1

/-- The whole-program block-reorder transform: permute `blocks`, everything else
(entry, and each block verbatim) fixed. -/
def reorderProgram (p : Program) : Program :=
  { p with blocks := layoutBlocks p }

@[simp] theorem reorderProgram_entry (p : Program) :
    (reorderProgram p).entry = p.entry := rfl

@[simp] theorem reorderProgram_blocks (p : Program) :
    (reorderProgram p).blocks = layoutBlocks p := rfl

/-- Structural floor (a): every block a chain emits is an original block,
**verbatim** (bodies/terms/shapes untouched). -/
theorem growLayout_mem (blocks : List Block) :
    ∀ (fuel : Nat) (start : Label) (placed : List Label) (b : Block),
      b ∈ (growLayout blocks fuel start placed).1 → b ∈ blocks := by
  intro fuel
  induction fuel with
  | zero =>
      intro start placed b hb
      simp [growLayout] at hb
  | succ fuel ih =>
      intro start placed b hb
      simp only [growLayout] at hb
      split at hb
      · simp at hb
      · split at hb
        · simp at hb
        · rename_i c hl
          have hcMem : c ∈ blocks :=
            List.mem_of_find?_eq_some (by simpa [lookup?] using hl)
          split at hb
          · rename_i t _hs
            rcases List.mem_cons.mp hb with h | h
            · subst h; exact hcMem
            · exact ih t (start :: placed) b h
          · rename_i _hs
            simp only [List.mem_singleton] at hb
            subst hb; exact hcMem

/-- Structural floor (b): every laid-out block is an original block, verbatim. -/
theorem layoutBlocks_mem (p : Program) {b : Block}
    (hb : b ∈ layoutBlocks p) : b ∈ p.blocks := by
  unfold layoutBlocks at hb
  -- The fold accumulates `st.1 ++ rest`; each `rest ⊆ p.blocks` by `growLayout_mem`.
  set seeds := p.entry :: p.blocks.map (·.label) with hseeds
  clear hseeds
  suffices H : ∀ (ss : List Label) (acc : List Block × List Label),
      (∀ x ∈ acc.1, x ∈ p.blocks) →
      ∀ y ∈ (ss.foldl
          (fun (st : List Block × List Label) s =>
            let (rest, placed) := growLayout p.blocks p.blocks.length s st.2
            (st.1 ++ rest, placed)) acc).1,
        y ∈ p.blocks by
    exact H seeds ([], []) (by intro x hx; simp at hx) b hb
  intro ss
  induction ss with
  | nil => intro acc hacc y hy; exact hacc y hy
  | cons s rest ih =>
      intro acc hacc y hy
      rw [List.foldl_cons] at hy
      refine ih _ ?_ y hy
      intro x hx
      have hxa : x ∈ acc.1 ++ (growLayout p.blocks p.blocks.length s acc.2).1 := hx
      cases List.mem_append.mp hxa with
      | inl h => exact hacc x h
      | inr h => exact growLayout_mem p.blocks p.blocks.length s acc.2 x h

/-- Structural floor (c): the reordered program's blocks are all original,
verbatim — the transform changes only the ORDER, never a block's contents. -/
theorem reorderProgram_blocks_mem (p : Program) {b : Block}
    (hb : b ∈ (reorderProgram p).blocks) : b ∈ p.blocks :=
  layoutBlocks_mem p (by simpa using hb)

end EvmCompiler.TypedCfg.BlockReorder
