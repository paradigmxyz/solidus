import EvmCompiler.TypedCfg.Syntax
import EvmCompiler.TypedCfg.Typing
import EvmCompiler.TypedCfg.InteractionSemantics
import EvmCompiler.TypedCfg.Certificate

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
open List

/-- The fallthrough candidate of a block: the label its terminator's *final*
lowered instruction jumps to.  `fallthrough`/`jump` lower to `[jump t]` and
`jumpi target next` lowers to `[jumpi target, jump next]`, so in all three cases
placing that label next lets the frozen serializer elide the trailing
`jump L; label L` seam. -/
def succLabel? (b : Block) : Option Label :=
  match b.term with
  | .fallthrough t => some t
  | .jump t => some t
  | .jumpi _ next => some next
  -- `returnDispatch` lowers to test chain ++ case blocks, and the last case
  -- block ends in `jump (last site).target`.
  | .returnDispatch _ sites => sites.getLast?.map ReturnSite.target
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

/-- Labels some block wants to fall through to. -/
def succLabels (blocks : List Block) : List Label :=
  blocks.filterMap succLabel?

/-- Chain heads: blocks no other block can fall through to.  Seeding a chain at
a non-head steals the head's seam, so heads go first. -/
def headLabels (blocks : List Block) : List Label :=
  let succs := succLabels blocks
  (blocks.filter (fun b => !succs.contains b.label)).map (·.label)

/-- Chain seeds: the entry, then the chain heads, then every label as a fallback
(duplicates are skipped by `growLayout`, so this only has to *cover* the labels). -/
def layoutSeeds (p : Program) : List Label :=
  p.entry :: (headLabels p.blocks ++ p.blocks.map (·.label))

/-- Greedy fallthrough-maximising block order: seed chains at the entry, then at
the chain heads, then at every block label in order, laying each block right
after its fallthrough predecessor whenever possible. -/
def layoutBlocks (p : Program) : List Block :=
  let seeds := layoutSeeds p
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
  set seeds := layoutSeeds p with hseeds
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

/-! ## The equality core (session-100)

The reorder is a *pure permutation* of the block list, so the label-addressed
`findBlock?` is extensionally unchanged.  Because the cfg operational semantics
(`InteractionSemantics.openStep`/`openRunN`) read `source` **only** through
`source.findBlock?`, this extensional equality is the whole semantic content of
the reorder at the cfg altitude.  The chain is:

* `growLayout_spec` — every chain emits `Nodup`, `placed`-disjoint labels and the
  outgoing `placed` set is exactly the incoming set plus the emitted labels;
* `foldLabels_spec` / `foldl_seed_mem` — the layout fold is `Nodup` and covers
  every original block label;
* `layoutBlocks_coverage` + the banked `layoutBlocks_mem` — block membership is
  preserved *both ways* (a genuine permutation);
* `reorderProgram_blocks_perm`, `reorderProgram_labelsUnique`, and
  `findBlock?_reorderProgram` — the observable conclusions.
-/

/-- `lookup?` returns a block whose label is the queried one. -/
theorem lookup?_label {blocks : List Block} {l : Label} {b : Block}
    (h : lookup? blocks l = some b) : b.label = l := by
  unfold lookup? at h
  have hp := List.find?_some h
  simp only [beq_iff_eq] at hp
  exact hp

/-- Master `growLayout` invariant: the emitted blocks' labels are `Nodup`, each
emitted label is disjoint from the incoming `placed` set, and the outgoing
`placed` set is exactly the incoming set plus the emitted labels. -/
theorem growLayout_spec (blocks : List Block) :
    ∀ (fuel : Nat) (start : Label) (placed : List Label),
      ((growLayout blocks fuel start placed).1.map Block.label).Nodup ∧
      (∀ b' ∈ (growLayout blocks fuel start placed).1, b'.label ∉ placed) ∧
      (∀ l, l ∈ (growLayout blocks fuel start placed).2 ↔
          l ∈ (growLayout blocks fuel start placed).1.map Block.label ∨
            l ∈ placed) := by
  intro fuel
  induction fuel with
  | zero =>
      intro start placed
      simp [growLayout]
  | succ fuel ih =>
      intro start placed
      rw [growLayout]
      split
      · simp
      · rename_i hcns
        have hstart : start ∉ placed := fun hmem =>
          hcns (List.contains_iff_mem.mpr hmem)
        split
        · simp
        · rename_i b hl
          have hblabel : b.label = start := lookup?_label hl
          split
          · rename_i t _hs
            obtain ⟨ihNodup, ihDisj, ihPlaced⟩ := ih t (start :: placed)
            cases hg : growLayout blocks fuel t (start :: placed) with
            | mk rest placed' =>
                rw [hg] at ihNodup ihDisj ihPlaced
                simp only [hg]
                refine ⟨?_, ?_, ?_⟩
                · simp only [List.map_cons, List.nodup_cons]
                  refine ⟨?_, ihNodup⟩
                  rw [List.mem_map]
                  rintro ⟨b', hb'rest, hb'eq⟩
                  apply ihDisj b' hb'rest
                  rw [hb'eq, hblabel]
                  exact List.mem_cons_self ..
                · intro b' hb'
                  rcases List.mem_cons.mp hb' with h | h
                  · subst h; rw [hblabel]; exact hstart
                  · exact fun hp =>
                      ihDisj b' h (List.mem_cons_of_mem _ hp)
                · intro l
                  rw [ihPlaced l]
                  simp only [List.map_cons, List.mem_cons, hblabel]
                  tauto
          · rename_i _hs
            refine ⟨?_, ?_, ?_⟩
            · simp
            · intro b' hb'
              simp only [List.mem_singleton] at hb'
              subst hb'; rw [hblabel]; exact hstart
            · intro l
              simp only [List.map_cons, List.map_nil,
                List.mem_cons, hblabel]
              tauto

/-- Fold invariant: the outgoing `placed` set tracks exactly the emitted-block
labels, and those labels are `Nodup`. -/
theorem foldLabels_spec (blocks : List Block) (n : Nat) :
    ∀ (ss : List Label) (acc : List Block × List Label),
      (∀ l, l ∈ acc.2 ↔ l ∈ acc.1.map Block.label) →
      (acc.1.map Block.label).Nodup →
      (∀ l, l ∈ (ss.foldl (fun st s =>
                  let g := growLayout blocks n s st.2
                  (st.1 ++ g.1, g.2)) acc).2 ↔
            l ∈ (ss.foldl (fun st s =>
                  let g := growLayout blocks n s st.2
                  (st.1 ++ g.1, g.2)) acc).1.map Block.label) ∧
      ((ss.foldl (fun st s =>
                  let g := growLayout blocks n s st.2
                  (st.1 ++ g.1, g.2)) acc).1.map Block.label).Nodup := by
  intro ss
  induction ss with
  | nil => intro acc h1 h2; exact ⟨h1, h2⟩
  | cons s rest ih =>
      intro acc h1 h2
      rw [List.foldl_cons]
      apply ih
      · intro l
        obtain ⟨_gN, gD, gP⟩ := growLayout_spec blocks n s acc.2
        dsimp only
        rw [gP l, h1 l, List.map_append, List.mem_append]
        tauto
      · obtain ⟨gN, gD, _gP⟩ := growLayout_spec blocks n s acc.2
        dsimp only
        rw [List.map_append]
        apply List.Nodup.append h2 gN
        intro a ha
        rw [List.mem_map]
        rintro ⟨b', hb'g, hb'eq⟩
        have haAcc2 : a ∈ acc.2 := (h1 a).mpr ha
        rw [← hb'eq] at haAcc2
        exact gD b' hb'g haAcc2

/-- One `growLayout` chain seeded at `start` places `start` whenever the block
exists and there is fuel. -/
theorem growLayout_start_mem (blocks : List Block) {n : Nat} (hn : 0 < n)
    (start : Label) (placed : List Label) {b : Block}
    (hlk : lookup? blocks start = some b) :
    start ∈ (growLayout blocks n start placed).2 := by
  obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  obtain ⟨_, _, gP⟩ := growLayout_spec blocks (fuel + 1) start placed
  rw [gP start]
  by_cases hc : placed.contains start
  · exact Or.inr (List.contains_iff_mem.mp hc)
  · left
    have hblabel : b.label = start := lookup?_label hlk
    simp only [growLayout, if_neg hc, hlk]
    cases succLabel? b <;> simp [hblabel]

/-- The fold's `placed` set is monotone. -/
theorem foldl_placed_mono (blocks : List Block) (n : Nat) :
    ∀ (ss : List Label) (acc : List Block × List Label) (l : Label),
      l ∈ acc.2 →
      l ∈ (ss.foldl (fun st s =>
              let g := growLayout blocks n s st.2
              (st.1 ++ g.1, g.2)) acc).2 := by
  intro ss
  induction ss with
  | nil => intro acc l hl; exact hl
  | cons s rest ih =>
      intro acc l hl
      rw [List.foldl_cons]
      apply ih
      obtain ⟨_, _, gP⟩ := growLayout_spec blocks n s acc.2
      dsimp only
      exact (gP l).mpr (Or.inr hl)

/-- Every seed with an existing block ends up placed after the whole fold. -/
theorem foldl_seed_mem (blocks : List Block) {n : Nat} (hn : 0 < n) :
    ∀ (ss : List Label) (acc : List Block × List Label) (s : Label) {b : Block},
      s ∈ ss → lookup? blocks s = some b →
      s ∈ (ss.foldl (fun st x =>
              let g := growLayout blocks n x st.2
              (st.1 ++ g.1, g.2)) acc).2 := by
  intro ss
  induction ss with
  | nil => intro acc s b hmem _; simp at hmem
  | cons x rest ih =>
      intro acc s b hmem hlk
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hmem with h | h
      · subst h
        apply foldl_placed_mono blocks n rest
        dsimp only
        exact growLayout_start_mem blocks hn s acc.2 hlk
      · exact ih _ s h hlk

/-- Coverage: every original block is laid out. -/
theorem layoutBlocks_coverage (p : Program) (h : p.LabelsUnique)
    {b0 : Block} (hb0 : b0 ∈ p.blocks) : b0 ∈ layoutBlocks p := by
  have hseed : b0.label ∈ layoutSeeds p :=
    List.mem_cons_of_mem _
      (List.mem_append_right _ (List.mem_map.mpr ⟨b0, hb0, rfl⟩))
  have hlk : lookup? p.blocks b0.label = some b0 := by
    unfold lookup?
    have := Program.findBlock?_eq_some_of_mem h hb0
    unfold Program.findBlock? at this
    exact this
  have hpos : 0 < p.blocks.length := List.length_pos_of_mem hb0
  have hin : b0.label ∈
      ((layoutSeeds p).foldl (fun st x =>
          let g := growLayout p.blocks p.blocks.length x st.2
          (st.1 ++ g.1, g.2)) ([], [])).2 :=
    foldl_seed_mem p.blocks hpos _ ([], []) b0.label hseed hlk
  obtain ⟨hH1, _hND⟩ :=
    foldLabels_spec p.blocks p.blocks.length (layoutSeeds p)
      ([], []) (by intro l; simp) (by simp)
  have hlab : b0.label ∈ (layoutBlocks p).map Block.label := by
    have := (hH1 b0.label).mp hin
    simpa [layoutBlocks] using this
  rw [List.mem_map] at hlab
  obtain ⟨b', hb'mem, hb'eq⟩ := hlab
  have hb'p : b' ∈ p.blocks := layoutBlocks_mem p hb'mem
  have hbb : b' = b0 := by
    have h1 := Program.findBlock?_eq_some_of_mem h hb'p
    have h2 := Program.findBlock?_eq_some_of_mem h hb0
    rw [hb'eq] at h1
    rw [h1] at h2
    exact Option.some.inj h2
  rw [← hbb]; exact hb'mem

/-- The reordered program's block labels are `Nodup` (uniquely labelled). -/
theorem layoutBlocks_labels_nodup (p : Program) :
    ((layoutBlocks p).map Block.label).Nodup := by
  have := (foldLabels_spec p.blocks p.blocks.length
    (layoutSeeds p) ([], [])
    (by intro l; simp) (by simp)).2
  simpa [layoutBlocks] using this

/-- The reorder preserves whole-program `LabelsUnique`. -/
theorem reorderProgram_labelsUnique (p : Program) :
    (reorderProgram p).LabelsUnique := by
  rw [← Program.blockLabels_nodup_iff]
  simpa [reorderProgram] using layoutBlocks_labels_nodup p

/-- Block-membership is preserved exactly (both directions ⟹ a permutation). -/
theorem layoutBlocks_mem_iff (p : Program) (h : p.LabelsUnique) {b : Block} :
    b ∈ layoutBlocks p ↔ b ∈ p.blocks :=
  ⟨fun hb => layoutBlocks_mem p hb, fun hb => layoutBlocks_coverage p h hb⟩

/-- The block list is a genuine permutation. -/
theorem reorderProgram_blocks_perm (p : Program) (h : p.LabelsUnique) :
    (reorderProgram p).blocks.Perm p.blocks := by
  rw [reorderProgram_blocks]
  have hnd1 : (layoutBlocks p).Nodup :=
    (layoutBlocks_labels_nodup p).of_map _
  have hnd2 : p.blocks.Nodup :=
    (Program.blockLabels_nodup_iff p |>.mpr h).of_map _
  exact (List.perm_ext_iff_of_nodup hnd1 hnd2).mpr
    (fun b => layoutBlocks_mem_iff p h)

/-- **THE EQUALITY CORE.**  `findBlock?` is extensionally unchanged by the
reorder — hence every cfg observation that reads `source` only through
`findBlock?` is literally invariant. -/
theorem findBlock?_reorderProgram (p : Program) (h : p.LabelsUnique) :
    ∀ l, (reorderProgram p).findBlock? l = p.findBlock? l := by
  intro l
  cases hp : p.findBlock? l with
  | none =>
      cases hr : (reorderProgram p).findBlock? l with
      | none => rfl
      | some b' =>
          exfalso
          have hb'mem : b' ∈ (reorderProgram p).blocks :=
            List.mem_of_find?_eq_some hr
          have hb'lab : b'.label = l := by
            have := List.find?_some hr; simpa using this
          have hb'p : b' ∈ p.blocks := reorderProgram_blocks_mem p hb'mem
          have hcontra := Program.findBlock?_eq_some_of_mem h hb'p
          rw [hb'lab, hp] at hcontra
          exact absurd hcontra (by simp)
  | some b =>
      have hbmem : b ∈ p.blocks := List.mem_of_find?_eq_some hp
      have hblab : b.label = l := by
        have := List.find?_some hp; simpa using this
      have hbr : b ∈ (reorderProgram p).blocks := by
        rw [reorderProgram_blocks]; exact layoutBlocks_coverage p h hbmem
      have hres :=
        Program.findBlock?_eq_some_of_mem (reorderProgram_labelsUnique p) hbr
      rw [hblab] at hres
      exact hres

/-! ## Literal semantic equality (session-100)

Because `Control.Program.step` reads `program` **only** through
`program.findBlock?`, and `findBlock?` is extensionally preserved
(`findBlock?_reorderProgram`), the whole-program CFG operational semantics is
**literally equal** under the reorder — no simulation/step-relation is needed
(contrast the `chainCanon` `ChainCombinedStepRelEff` machinery, which exists only
because chain-canon rewrites block bodies).  This realizes the §99 frontier
item 2 ("the congruence should be simpler … a `simp`/congruence one-liner"). -/

/-- `Control.Program.step` is literally equal for programs with the same
`findBlock?`. -/
theorem step_findBlock_congr {M : Type → Type}
    [Monad M] [MonadExceptOf EVMException M]
    (runState : TypedCfg.Instr → Shape → EVMState → M EVMState)
    {P1 P2 : Program} (h : ∀ l, P1.findBlock? l = P2.findBlock? l)
    (label : Label) (state : EVMState) :
    Control.Program.step runState P1 label state =
      Control.Program.step runState P2 label state := by
  unfold Control.Program.step
  rw [h label]

/-- The whole fuel-bounded runner is literally equal for programs with the same
`findBlock?`. -/
theorem runNWithStopAs_findBlock_congr {M : Type → Type} {Result : Type}
    [Monad M] [MonadExceptOf EVMException M]
    (runState : TypedCfg.Instr → Shape → EVMState → M EVMState)
    (stopJump : Label → EVMState → Bool)
    (exhausted : Label → EVMState → Result)
    (stopped : Nat → TypedCfg.Outcome → Result)
    {P1 P2 : Program} (h : ∀ l, P1.findBlock? l = P2.findBlock? l) :
    ∀ (fuel : Nat) (label : Label) (state : EVMState),
      Control.Program.runNWithStopAs runState stopJump exhausted stopped
          P1 fuel label state =
        Control.Program.runNWithStopAs runState stopJump exhausted stopped
          P2 fuel label state := by
  intro fuel
  induction fuel with
  | zero => intro label state; rfl
  | succ fuel ih =>
      intro label state
      simp only [Control.Program.runNWithStopAs,
        step_findBlock_congr runState h label state]
      apply bind_congr
      intro outcome
      cases outcome with
      | jump next state' =>
          by_cases hs : stopJump next state' <;> simp [hs, ih]
      | fallthrough state' => rfl
      | returnDispatch state' => rfl
      | halt kind state' => rfl
      | invalid state' => rfl

/-- The whole-program CFG run is literally unchanged by the reorder. -/
theorem openRunN_reorderProgram (Q : Program) (h : Q.LabelsUnique)
    (fuel : Nat) (label : Label) (state : EVMState) :
    InteractionSemantics.Program.openRunN (reorderProgram Q) fuel label state =
      InteractionSemantics.Program.openRunN Q fuel label state := by
  unfold InteractionSemantics.Program.openRunN
    InteractionSemantics.Program.openRunNWithStop
    Control.Program.runNWithStop
  exact runNWithStopAs_findBlock_congr _ _ _ _
    (findBlock?_reorderProgram Q h) fuel label state

/-- The canonical finite-prefix CFG semantics is literally unchanged — the
reorder analog of `openRunNPrefix_chainCombinedEff_congr_of_source`, but an
**equality** rather than a relation. -/
theorem openRunNPrefix_reorderProgram (Q : Program) (h : Q.LabelsUnique)
    (fuel : Nat) (label : Label) (state : EVMState) :
    InteractionSemantics.Program.openRunNPrefix (reorderProgram Q) fuel label state =
      InteractionSemantics.Program.openRunNPrefix Q fuel label state := by
  unfold InteractionSemantics.Program.openRunNPrefix
  rw [openRunN_reorderProgram Q h]

/-- The result-carrying stopped run is literally unchanged. -/
theorem openRunNResultWithStop_reorderProgram (Q : Program) (h : Q.LabelsUnique)
    (stopJump : Label → EVMState → Bool)
    (fuel : Nat) (label : Label) (state : EVMState) :
    InteractionSemantics.Program.openRunNResultWithStop stopJump
        (reorderProgram Q) fuel label state =
      InteractionSemantics.Program.openRunNResultWithStop stopJump
        Q fuel label state := by
  unfold InteractionSemantics.Program.openRunNResultWithStop
    Control.Program.runNResultWithStop
  exact runNWithStopAs_findBlock_congr _ _ _ _
    (findBlock?_reorderProgram Q h) fuel label state

/-- One open CFG step is literally unchanged by the reorder. -/
theorem openStep_reorderProgram (Q : Program) (h : Q.LabelsUnique)
    (label : Label) (state : EVMState) :
    InteractionSemantics.Program.openStep (reorderProgram Q) label state =
      InteractionSemantics.Program.openStep Q label state := by
  unfold InteractionSemantics.Program.openStep
  exact step_findBlock_congr _ (findBlock?_reorderProgram Q h) label state

/-! ## Static-gate preservation (permutation-invariant folds) -/

/-- `labelShape?` is preserved (it reads the program only through `findBlock?`). -/
theorem labelShape?_reorderProgram (Q : Program) (h : Q.LabelsUnique) :
    ∀ l, (reorderProgram Q).labelShape? l = Q.labelShape? l := by
  intro l
  unfold Program.labelShape?
  rw [findBlock?_reorderProgram Q h]

/-- Block typing is preserved (it reads the program only through `labelShape?`). -/
theorem block_wellTyped_reorderProgram (Q : Program) (h : Q.LabelsUnique)
    (b : Block) :
    Block.WellTyped (reorderProgram Q) b ↔ Block.WellTyped Q b := by
  unfold Block.WellTyped Terminator.type?
  rw [show (reorderProgram Q).labelShape? = Q.labelShape? from
        funext (labelShape?_reorderProgram Q h)]

/-- `AllBlocksTyped` is preserved. -/
theorem allBlocksTyped_reorderProgram (Q : Program) (h : Q.LabelsUnique)
    (hA : Q.AllBlocksTyped) : (reorderProgram Q).AllBlocksTyped := by
  unfold Program.AllBlocksTyped at hA ⊢
  rw [List.forall_iff_forall_mem] at hA ⊢
  intro b hb
  exact (block_wellTyped_reorderProgram Q h b).mpr
    (hA b (reorderProgram_blocks_mem Q hb))

/-- `EmittedLabels` is a permutation of the original. -/
theorem emittedLabels_reorderProgram_perm (Q : Program) (h : Q.LabelsUnique) :
    (reorderProgram Q).EmittedLabels.Perm Q.EmittedLabels := by
  unfold Program.EmittedLabels
  exact (reorderProgram_blocks_perm Q h).flatMap_right _

/-- `EmittedLabelsUnique` is preserved (`Nodup` is permutation-invariant). -/
theorem emittedLabelsUnique_reorderProgram (Q : Program) (h : Q.LabelsUnique)
    (hE : Q.EmittedLabelsUnique) : (reorderProgram Q).EmittedLabelsUnique := by
  unfold Program.EmittedLabelsUnique at hE ⊢
  exact (emittedLabels_reorderProgram_perm Q h).nodup_iff.mpr hE

/-- The entry block still exists. -/
theorem findBlock?_entry_reorderProgram (Q : Program) (h : Q.LabelsUnique)
    (hE : Q.findBlock? Q.entry ≠ none) :
    (reorderProgram Q).findBlock? (reorderProgram Q).entry ≠ none := by
  rw [reorderProgram_entry, findBlock?_reorderProgram Q h]; exact hE

/-- **`WellTyped` is preserved by the reorder.** -/
theorem wellTyped_reorderProgram (Q : Program) (hW : Q.WellTyped) :
    (reorderProgram Q).WellTyped := by
  obtain ⟨hU, hA, hEntry, hEmit⟩ := hW
  exact ⟨reorderProgram_labelsUnique Q,
    allBlocksTyped_reorderProgram Q hU hA,
    findBlock?_entry_reorderProgram Q hU hEntry,
    emittedLabelsUnique_reorderProgram Q hU hEmit⟩

/-- **`ProgramCounterIndependent` is preserved** (a per-block, program-free
predicate — only block membership matters). -/
theorem programCounterIndependent_reorderProgram (Q : Program)
    (hP : Q.ProgramCounterIndependent) :
    (reorderProgram Q).ProgramCounterIndependent := by
  unfold Program.ProgramCounterIndependent at hP ⊢
  rw [List.forall_iff_forall_mem] at hP ⊢
  intro b hb
  exact hP b (reorderProgram_blocks_mem Q hb)

/-- **The fuel budget is exactly preserved** (a `.sum` over the permuted
blocks — even sharper than `chainCanon`'s `≤`). -/
theorem fuelBudget_reorderProgram_eq (Q : Program) (h : Q.LabelsUnique) :
    InteractionSemantics.CompiledProgram.fuelBudget (reorderProgram Q) =
      InteractionSemantics.CompiledProgram.fuelBudget Q := by
  unfold InteractionSemantics.CompiledProgram.fuelBudget
  exact ((reorderProgram_blocks_perm Q h).map
    InteractionSemantics.CompiledBlock.fuelBudget).sum_nat

end EvmCompiler.TypedCfg.BlockReorder
