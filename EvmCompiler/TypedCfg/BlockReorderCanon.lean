import EvmCompiler.TypedCfg.Syntax
import EvmCompiler.TypedCfg.Typing
import EvmCompiler.TypedCfg.InteractionSemantics
import EvmCompiler.TypedCfg.Certificate
import EvmCompiler.Assembly.Compact

/-!
# Block-reorder canonicalisation (session-99/100, "the jump-threading vein";
  session-101, the **policy-parameterised** successor relation)

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
`program.blocks` so that cfg edges become physically adjacent**, letting the
frozen `prepare` consume them.  Semantically this is a *pure permutation* of the
block list (blocks are label-addressed via `findBlock?`/`JUMPDEST`), with every
block's `body`/`term`/`input`/`output` **verbatim** — far cheaper to justify than
the `chainCanon`/shuffle-drop body rewrites.

## §Session-101: the successor policy was leaving 8 % of the bytes on the table

The §99/§100 layout followed only `.jump` edges (`succLabel?` below).  But
`Terminator.lowerAt?` lowers `.jumpi t n` to `[.jumpi t, .jump n]` — a *full*
4-byte `PUSH2 n; JUMP` for the **fallthrough** arm — and the natural emission
order of `Structured.TypedCfgCompiler` always puts the **taken** arm next
(`.if_`: `head :: bodyResult.blocks`; `.for_`: `init ++ [loop] ++ body ++ post`;
switch case: `test :: bodyEntry :: body ++ tail`), so the fallthrough block is
*never* adjacent by accident.  A probe over the 36-contract runtime corpus
measured **960 `.jumpi` terminators, of which exactly 0 had their fallthrough
block physically next**, and 868 of those fallthroughs have `refCount = 1`
(a guaranteed 4 B jump + 1 B `JUMPDEST` win each).  Likewise a
`.returnDispatch` block ends its lowering with `.jump (sites.getLast?).target`,
another free adjacency.

Measured on the corpus (36 runtime objects, 54 786 B under the §100 layout):

| policy                                    | Δ bytes | Δ %    |
|-------------------------------------------|--------:|-------:|
| §100 `.jump` only                         |       0 |  0.00 %|
| + `refCount = 1` jumpi fallthrough        |  −4 321 | −7.89 %|
| + any jumpi fallthrough                   |  −4 335 | −7.91 %|
| + returnDispatch last-target chaining     |  −4 782 | −8.73 %|
| + root-first seeding                      |  −4 924 | −8.99 %|
| per-contract argmin over all of the above |  −4 924 | −8.99 %|

## Why the whole tower is policy-agnostic

`Control.Program.step` reads the program **only** through `findBlock?`, so a
transform that leaves every block verbatim and only permutes the list gets
literal semantic equality for free.  *Nothing* in the preservation tower ever
inspects the successor function: every proof discharges it by `split`/`cases`.
So the successor relation and the chain seed order are taken as **arbitrary
parameters** (`succ`, `extra`) throughout, and the shipped `reorderProgram`
picks, per program, the candidate policy whose `Assembly.Compact` layout is
smallest — deterministically, with the §100 policy at index 0 so the result can
never be larger than what §100 shipped.  The single bridge lemma
`reorderProgram_exists_policy` is `rfl`, and every §100-era conclusion is
re-exported under its original name and signature.

The size oracle `compactSize` has **no correctness role whatsoever**: it only
selects which permutation is emitted, and *every* permutation is proved sound.

## §Session-102: the argmin was nine evaluations wide and two wide is enough

The oracle is expensive and the contest scores compile time as a *validity*
condition, so the §101 search width was a submission risk.  `candidatePolicies`
is now the two policies that provably reproduce the full nine-way argmin on the
corpus (see the §102 note there) and `chosenPolicy` no longer re-evaluates index
0 as its own seed.  Corpus output is byte-identical; corpus compile wall time
drops 20 %, and the largest contract's 42 %.  This section is *selection* only —
soundness is untouched, because every theorem above is universally quantified
over `succ` and `extra`.
-/

namespace EvmCompiler.TypedCfg.BlockReorder

open EvmCompiler.TypedCfg
open List

/-- The unconditional-jump fallthrough candidate of a block: the target label of
its terminator when that terminator is an unconditional `jump`.  This is the
§100 successor policy, retained as candidate index 0. -/
def succLabel? (b : Block) : Option Label :=
  match b.term with
  | .jump t => some t
  | _ => none

/-- List-`find?` block lookup by label (returns an actual member of `blocks`,
which makes the structural-floor membership lemmas below provable). -/
def lookup? (blocks : List Block) (l : Label) : Option Block :=
  blocks.find? (fun b => b.label == l)

/-- Grow one fallthrough chain from `start`: emit `start`, then follow its
`succ`-successor while unplaced.  Fuel-bounded (total).  `succ` is an arbitrary
successor policy — nothing below ever inspects it. -/
def growLayoutWith (succ : Block → Option Label) (blocks : List Block) :
    Nat → Label → List Label → (List Block × List Label)
  | 0, _, placed => ([], placed)
  | fuel + 1, start, placed =>
      if placed.contains start then ([], placed)
      else
        match lookup? blocks start with
        | none => ([], placed)
        | some b =>
            let placed := start :: placed
            match succ b with
            | some t =>
                let (rest, placed) := growLayoutWith succ blocks fuel t placed
                (b :: rest, placed)
            | none => ([b], placed)

/-- The canonical seed list: the entry, then every block label in list order.
Every layout appends this suffix, which is what makes coverage unconditional. -/
def baseSeeds (p : Program) : List Label :=
  p.entry :: p.blocks.map Block.label

/-- Greedy fallthrough-maximising block order under successor policy `succ`,
seeded first at `extra` (an arbitrary priority prefix) and then at
`baseSeeds p`. -/
def layoutBlocksWith (succ : Block → Option Label) (extra : List Label)
    (p : Program) : List Block :=
  ((extra ++ baseSeeds p).foldl
    (fun (st : List Block × List Label) s =>
      let g := growLayoutWith succ p.blocks p.blocks.length s st.2
      (st.1 ++ g.1, g.2))
    ([], [])).1

/-- The whole-program block-reorder transform under an arbitrary policy:
permute `blocks`, everything else (entry, and each block verbatim) fixed. -/
def reorderProgramWith (succ : Block → Option Label) (extra : List Label)
    (p : Program) : Program :=
  { p with blocks := layoutBlocksWith succ extra p }

@[simp] theorem reorderProgramWith_entry (succ : Block → Option Label)
    (extra : List Label) (p : Program) :
    (reorderProgramWith succ extra p).entry = p.entry := rfl

@[simp] theorem reorderProgramWith_blocks (succ : Block → Option Label)
    (extra : List Label) (p : Program) :
    (reorderProgramWith succ extra p).blocks = layoutBlocksWith succ extra p :=
  rfl

/-- Structural floor (a): every block a chain emits is an original block,
**verbatim** (bodies/terms/shapes untouched). -/
theorem growLayoutWith_mem (succ : Block → Option Label) (blocks : List Block) :
    ∀ (fuel : Nat) (start : Label) (placed : List Label) (b : Block),
      b ∈ (growLayoutWith succ blocks fuel start placed).1 → b ∈ blocks := by
  intro fuel
  induction fuel with
  | zero =>
      intro start placed b hb
      simp [growLayoutWith] at hb
  | succ fuel ih =>
      intro start placed b hb
      simp only [growLayoutWith] at hb
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
theorem layoutBlocksWith_mem (succ : Block → Option Label) (extra : List Label)
    (p : Program) {b : Block}
    (hb : b ∈ layoutBlocksWith succ extra p) : b ∈ p.blocks := by
  unfold layoutBlocksWith at hb
  -- The fold accumulates `st.1 ++ rest`; each `rest ⊆ p.blocks` by `growLayoutWith_mem`.
  set seeds := extra ++ baseSeeds p with hseeds
  clear hseeds
  suffices H : ∀ (ss : List Label) (acc : List Block × List Label),
      (∀ x ∈ acc.1, x ∈ p.blocks) →
      ∀ y ∈ (ss.foldl
          (fun (st : List Block × List Label) s =>
            let (rest, placed) := growLayoutWith succ p.blocks p.blocks.length s st.2
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
      have hxa : x ∈ acc.1 ++ (growLayoutWith succ p.blocks p.blocks.length s acc.2).1 := hx
      cases List.mem_append.mp hxa with
      | inl h => exact hacc x h
      | inr h => exact growLayoutWith_mem succ p.blocks p.blocks.length s acc.2 x h

/-- Structural floor (c): the reordered program's blocks are all original,
verbatim — the transform changes only the ORDER, never a block's contents. -/
theorem reorderProgramWith_blocks_mem (succ : Block → Option Label)
    (extra : List Label) (p : Program) {b : Block}
    (hb : b ∈ (reorderProgramWith succ extra p).blocks) : b ∈ p.blocks :=
  layoutBlocksWith_mem succ extra p (by simpa using hb)

/-! ## The equality core (session-100)

The reorder is a *pure permutation* of the block list, so the label-addressed
`findBlock?` is extensionally unchanged.  Because the cfg operational semantics
(`InteractionSemantics.openStep`/`openRunN`) read `source` **only** through
`source.findBlock?`, this extensional equality is the whole semantic content of
the reorder at the cfg altitude.  The chain is:

* `growLayoutWith_spec` — every chain emits `Nodup`, `placed`-disjoint labels and
  the outgoing `placed` set is exactly the incoming set plus the emitted labels;
* `foldLabels_spec` / `foldl_seed_mem` — the layout fold is `Nodup` and covers
  every original block label;
* `layoutBlocksWith_coverage` + the banked `layoutBlocksWith_mem` — block
  membership is preserved *both ways* (a genuine permutation);
* `reorderProgramWith_blocks_perm`, `reorderProgramWith_labelsUnique`, and
  `findBlock?_reorderProgramWith` — the observable conclusions.
-/

/-- `lookup?` returns a block whose label is the queried one. -/
theorem lookup?_label {blocks : List Block} {l : Label} {b : Block}
    (h : lookup? blocks l = some b) : b.label = l := by
  unfold lookup? at h
  have hp := List.find?_some h
  simp only [beq_iff_eq] at hp
  exact hp

/-- Master `growLayoutWith` invariant: the emitted blocks' labels are `Nodup`,
each emitted label is disjoint from the incoming `placed` set, and the outgoing
`placed` set is exactly the incoming set plus the emitted labels. -/
theorem growLayoutWith_spec (succ : Block → Option Label) (blocks : List Block) :
    ∀ (fuel : Nat) (start : Label) (placed : List Label),
      ((growLayoutWith succ blocks fuel start placed).1.map Block.label).Nodup ∧
      (∀ b' ∈ (growLayoutWith succ blocks fuel start placed).1, b'.label ∉ placed) ∧
      (∀ l, l ∈ (growLayoutWith succ blocks fuel start placed).2 ↔
          l ∈ (growLayoutWith succ blocks fuel start placed).1.map Block.label ∨
            l ∈ placed) := by
  intro fuel
  induction fuel with
  | zero =>
      intro start placed
      simp [growLayoutWith]
  | succ fuel ih =>
      intro start placed
      rw [growLayoutWith]
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
            cases hg : growLayoutWith succ blocks fuel t (start :: placed) with
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
theorem foldLabels_spec (succ : Block → Option Label) (blocks : List Block)
    (n : Nat) :
    ∀ (ss : List Label) (acc : List Block × List Label),
      (∀ l, l ∈ acc.2 ↔ l ∈ acc.1.map Block.label) →
      (acc.1.map Block.label).Nodup →
      (∀ l, l ∈ (ss.foldl (fun st s =>
                  let g := growLayoutWith succ blocks n s st.2
                  (st.1 ++ g.1, g.2)) acc).2 ↔
            l ∈ (ss.foldl (fun st s =>
                  let g := growLayoutWith succ blocks n s st.2
                  (st.1 ++ g.1, g.2)) acc).1.map Block.label) ∧
      ((ss.foldl (fun st s =>
                  let g := growLayoutWith succ blocks n s st.2
                  (st.1 ++ g.1, g.2)) acc).1.map Block.label).Nodup := by
  intro ss
  induction ss with
  | nil => intro acc h1 h2; exact ⟨h1, h2⟩
  | cons s rest ih =>
      intro acc h1 h2
      rw [List.foldl_cons]
      apply ih
      · intro l
        obtain ⟨_gN, gD, gP⟩ := growLayoutWith_spec succ blocks n s acc.2
        dsimp only
        rw [gP l, h1 l, List.map_append, List.mem_append]
        tauto
      · obtain ⟨gN, gD, _gP⟩ := growLayoutWith_spec succ blocks n s acc.2
        dsimp only
        rw [List.map_append]
        apply List.Nodup.append h2 gN
        intro a ha
        rw [List.mem_map]
        rintro ⟨b', hb'g, hb'eq⟩
        have haAcc2 : a ∈ acc.2 := (h1 a).mpr ha
        rw [← hb'eq] at haAcc2
        exact gD b' hb'g haAcc2

/-- One `growLayoutWith` chain seeded at `start` places `start` whenever the
block exists and there is fuel. -/
theorem growLayoutWith_start_mem (succ : Block → Option Label)
    (blocks : List Block) {n : Nat} (hn : 0 < n)
    (start : Label) (placed : List Label) {b : Block}
    (hlk : lookup? blocks start = some b) :
    start ∈ (growLayoutWith succ blocks n start placed).2 := by
  obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  obtain ⟨_, _, gP⟩ := growLayoutWith_spec succ blocks (fuel + 1) start placed
  rw [gP start]
  by_cases hc : placed.contains start
  · exact Or.inr (List.contains_iff_mem.mp hc)
  · left
    have hblabel : b.label = start := lookup?_label hlk
    simp only [growLayoutWith, if_neg hc, hlk]
    cases succ b <;> simp [hblabel]

/-- The fold's `placed` set is monotone. -/
theorem foldl_placed_mono (succ : Block → Option Label) (blocks : List Block)
    (n : Nat) :
    ∀ (ss : List Label) (acc : List Block × List Label) (l : Label),
      l ∈ acc.2 →
      l ∈ (ss.foldl (fun st s =>
              let g := growLayoutWith succ blocks n s st.2
              (st.1 ++ g.1, g.2)) acc).2 := by
  intro ss
  induction ss with
  | nil => intro acc l hl; exact hl
  | cons s rest ih =>
      intro acc l hl
      rw [List.foldl_cons]
      apply ih
      obtain ⟨_, _, gP⟩ := growLayoutWith_spec succ blocks n s acc.2
      dsimp only
      exact (gP l).mpr (Or.inr hl)

/-- Every seed with an existing block ends up placed after the whole fold. -/
theorem foldl_seed_mem (succ : Block → Option Label) (blocks : List Block)
    {n : Nat} (hn : 0 < n) :
    ∀ (ss : List Label) (acc : List Block × List Label) (s : Label) {b : Block},
      s ∈ ss → lookup? blocks s = some b →
      s ∈ (ss.foldl (fun st x =>
              let g := growLayoutWith succ blocks n x st.2
              (st.1 ++ g.1, g.2)) acc).2 := by
  intro ss
  induction ss with
  | nil => intro acc s b hmem _; simp at hmem
  | cons x rest ih =>
      intro acc s b hmem hlk
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hmem with h | h
      · subst h
        apply foldl_placed_mono succ blocks n rest
        dsimp only
        exact growLayoutWith_start_mem succ blocks hn s acc.2 hlk
      · exact ih _ s h hlk

/-- Coverage: every original block is laid out — for **any** successor policy and
**any** seed prefix, because `baseSeeds p` is always a suffix of the seed list. -/
theorem layoutBlocksWith_coverage (succ : Block → Option Label)
    (extra : List Label) (p : Program) (h : p.LabelsUnique)
    {b0 : Block} (hb0 : b0 ∈ p.blocks) : b0 ∈ layoutBlocksWith succ extra p := by
  have hseed : b0.label ∈ extra ++ baseSeeds p :=
    List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨b0, hb0, rfl⟩))
  have hlk : lookup? p.blocks b0.label = some b0 := by
    unfold lookup?
    have := Program.findBlock?_eq_some_of_mem h hb0
    unfold Program.findBlock? at this
    exact this
  have hpos : 0 < p.blocks.length := List.length_pos_of_mem hb0
  have hin : b0.label ∈
      ((extra ++ baseSeeds p).foldl (fun st x =>
          let g := growLayoutWith succ p.blocks p.blocks.length x st.2
          (st.1 ++ g.1, g.2)) ([], [])).2 :=
    foldl_seed_mem succ p.blocks hpos _ ([], []) b0.label hseed hlk
  obtain ⟨hH1, _hND⟩ :=
    foldLabels_spec succ p.blocks p.blocks.length (extra ++ baseSeeds p)
      ([], []) (by intro l; simp) (by simp)
  have hlab : b0.label ∈ (layoutBlocksWith succ extra p).map Block.label := by
    have := (hH1 b0.label).mp hin
    simpa [layoutBlocksWith] using this
  rw [List.mem_map] at hlab
  obtain ⟨b', hb'mem, hb'eq⟩ := hlab
  have hb'p : b' ∈ p.blocks := layoutBlocksWith_mem succ extra p hb'mem
  have hbb : b' = b0 := by
    have h1 := Program.findBlock?_eq_some_of_mem h hb'p
    have h2 := Program.findBlock?_eq_some_of_mem h hb0
    rw [hb'eq] at h1
    rw [h1] at h2
    exact Option.some.inj h2
  rw [← hbb]; exact hb'mem

/-- The reordered program's block labels are `Nodup` (uniquely labelled). -/
theorem layoutBlocksWith_labels_nodup (succ : Block → Option Label)
    (extra : List Label) (p : Program) :
    ((layoutBlocksWith succ extra p).map Block.label).Nodup := by
  have := (foldLabels_spec succ p.blocks p.blocks.length
    (extra ++ baseSeeds p) ([], [])
    (by intro l; simp) (by simp)).2
  simpa [layoutBlocksWith] using this

/-- The reorder preserves whole-program `LabelsUnique`. -/
theorem reorderProgramWith_labelsUnique (succ : Block → Option Label)
    (extra : List Label) (p : Program) :
    (reorderProgramWith succ extra p).LabelsUnique := by
  rw [← Program.blockLabels_nodup_iff]
  simpa [reorderProgramWith] using layoutBlocksWith_labels_nodup succ extra p

/-- Block-membership is preserved exactly (both directions ⟹ a permutation). -/
theorem layoutBlocksWith_mem_iff (succ : Block → Option Label)
    (extra : List Label) (p : Program) (h : p.LabelsUnique) {b : Block} :
    b ∈ layoutBlocksWith succ extra p ↔ b ∈ p.blocks :=
  ⟨fun hb => layoutBlocksWith_mem succ extra p hb,
   fun hb => layoutBlocksWith_coverage succ extra p h hb⟩

/-- The block list is a genuine permutation. -/
theorem reorderProgramWith_blocks_perm (succ : Block → Option Label)
    (extra : List Label) (p : Program) (h : p.LabelsUnique) :
    (reorderProgramWith succ extra p).blocks.Perm p.blocks := by
  rw [reorderProgramWith_blocks]
  have hnd1 : (layoutBlocksWith succ extra p).Nodup :=
    (layoutBlocksWith_labels_nodup succ extra p).of_map _
  have hnd2 : p.blocks.Nodup :=
    (Program.blockLabels_nodup_iff p |>.mpr h).of_map _
  exact (List.perm_ext_iff_of_nodup hnd1 hnd2).mpr
    (fun b => layoutBlocksWith_mem_iff succ extra p h)

/-- **THE EQUALITY CORE.**  `findBlock?` is extensionally unchanged by the
reorder — hence every cfg observation that reads `source` only through
`findBlock?` is literally invariant. -/
theorem findBlock?_reorderProgramWith (succ : Block → Option Label)
    (extra : List Label) (p : Program) (h : p.LabelsUnique) :
    ∀ l, (reorderProgramWith succ extra p).findBlock? l = p.findBlock? l := by
  intro l
  cases hp : p.findBlock? l with
  | none =>
      cases hr : (reorderProgramWith succ extra p).findBlock? l with
      | none => rfl
      | some b' =>
          exfalso
          have hb'mem : b' ∈ (reorderProgramWith succ extra p).blocks :=
            List.mem_of_find?_eq_some hr
          have hb'lab : b'.label = l := by
            have := List.find?_some hr; simpa using this
          have hb'p : b' ∈ p.blocks := reorderProgramWith_blocks_mem succ extra p hb'mem
          have hcontra := Program.findBlock?_eq_some_of_mem h hb'p
          rw [hb'lab, hp] at hcontra
          exact absurd hcontra (by simp)
  | some b =>
      have hbmem : b ∈ p.blocks := List.mem_of_find?_eq_some hp
      have hblab : b.label = l := by
        have := List.find?_some hp; simpa using this
      have hbr : b ∈ (reorderProgramWith succ extra p).blocks := by
        rw [reorderProgramWith_blocks]; exact layoutBlocksWith_coverage succ extra p h hbmem
      have hres :=
        Program.findBlock?_eq_some_of_mem
          (reorderProgramWith_labelsUnique succ extra p) hbr
      rw [hblab] at hres
      exact hres

/-! ## Literal semantic equality (session-100)

Because `Control.Program.step` reads `program` **only** through
`program.findBlock?`, and `findBlock?` is extensionally preserved
(`findBlock?_reorderProgramWith`), the whole-program CFG operational semantics is
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
theorem openRunN_reorderProgramWith (succ : Block → Option Label)
    (extra : List Label) (Q : Program) (h : Q.LabelsUnique)
    (fuel : Nat) (label : Label) (state : EVMState) :
    InteractionSemantics.Program.openRunN (reorderProgramWith succ extra Q)
        fuel label state =
      InteractionSemantics.Program.openRunN Q fuel label state := by
  unfold InteractionSemantics.Program.openRunN
    InteractionSemantics.Program.openRunNWithStop
    Control.Program.runNWithStop
  exact runNWithStopAs_findBlock_congr _ _ _ _
    (findBlock?_reorderProgramWith succ extra Q h) fuel label state

/-- The canonical finite-prefix CFG semantics is literally unchanged — the
reorder analog of `openRunNPrefix_chainCombinedEff_congr_of_source`, but an
**equality** rather than a relation. -/
theorem openRunNPrefix_reorderProgramWith (succ : Block → Option Label)
    (extra : List Label) (Q : Program) (h : Q.LabelsUnique)
    (fuel : Nat) (label : Label) (state : EVMState) :
    InteractionSemantics.Program.openRunNPrefix (reorderProgramWith succ extra Q)
        fuel label state =
      InteractionSemantics.Program.openRunNPrefix Q fuel label state := by
  unfold InteractionSemantics.Program.openRunNPrefix
  rw [openRunN_reorderProgramWith succ extra Q h]

/-- The result-carrying stopped run is literally unchanged. -/
theorem openRunNResultWithStop_reorderProgramWith (succ : Block → Option Label)
    (extra : List Label) (Q : Program) (h : Q.LabelsUnique)
    (stopJump : Label → EVMState → Bool)
    (fuel : Nat) (label : Label) (state : EVMState) :
    InteractionSemantics.Program.openRunNResultWithStop stopJump
        (reorderProgramWith succ extra Q) fuel label state =
      InteractionSemantics.Program.openRunNResultWithStop stopJump
        Q fuel label state := by
  unfold InteractionSemantics.Program.openRunNResultWithStop
    Control.Program.runNResultWithStop
  exact runNWithStopAs_findBlock_congr _ _ _ _
    (findBlock?_reorderProgramWith succ extra Q h) fuel label state

/-- One open CFG step is literally unchanged by the reorder. -/
theorem openStep_reorderProgramWith (succ : Block → Option Label)
    (extra : List Label) (Q : Program) (h : Q.LabelsUnique)
    (label : Label) (state : EVMState) :
    InteractionSemantics.Program.openStep (reorderProgramWith succ extra Q)
        label state =
      InteractionSemantics.Program.openStep Q label state := by
  unfold InteractionSemantics.Program.openStep
  exact step_findBlock_congr _ (findBlock?_reorderProgramWith succ extra Q h) label state

/-! ## Static-gate preservation (permutation-invariant folds) -/

/-- `labelShape?` is preserved (it reads the program only through `findBlock?`). -/
theorem labelShape?_reorderProgramWith (succ : Block → Option Label)
    (extra : List Label) (Q : Program) (h : Q.LabelsUnique) :
    ∀ l, (reorderProgramWith succ extra Q).labelShape? l = Q.labelShape? l := by
  intro l
  unfold Program.labelShape?
  rw [findBlock?_reorderProgramWith succ extra Q h]

/-- Block typing is preserved (it reads the program only through `labelShape?`). -/
theorem block_wellTyped_reorderProgramWith (succ : Block → Option Label)
    (extra : List Label) (Q : Program) (h : Q.LabelsUnique) (b : Block) :
    Block.WellTyped (reorderProgramWith succ extra Q) b ↔ Block.WellTyped Q b := by
  unfold Block.WellTyped Terminator.type?
  rw [show (reorderProgramWith succ extra Q).labelShape? = Q.labelShape? from
        funext (labelShape?_reorderProgramWith succ extra Q h)]

/-- `AllBlocksTyped` is preserved. -/
theorem allBlocksTyped_reorderProgramWith (succ : Block → Option Label)
    (extra : List Label) (Q : Program) (h : Q.LabelsUnique)
    (hA : Q.AllBlocksTyped) : (reorderProgramWith succ extra Q).AllBlocksTyped := by
  unfold Program.AllBlocksTyped at hA ⊢
  rw [List.forall_iff_forall_mem] at hA ⊢
  intro b hb
  exact (block_wellTyped_reorderProgramWith succ extra Q h b).mpr
    (hA b (reorderProgramWith_blocks_mem succ extra Q hb))

/-- `EmittedLabels` is a permutation of the original. -/
theorem emittedLabels_reorderProgramWith_perm (succ : Block → Option Label)
    (extra : List Label) (Q : Program) (h : Q.LabelsUnique) :
    (reorderProgramWith succ extra Q).EmittedLabels.Perm Q.EmittedLabels := by
  unfold Program.EmittedLabels
  exact (reorderProgramWith_blocks_perm succ extra Q h).flatMap_right _

/-- `EmittedLabelsUnique` is preserved (`Nodup` is permutation-invariant). -/
theorem emittedLabelsUnique_reorderProgramWith (succ : Block → Option Label)
    (extra : List Label) (Q : Program) (h : Q.LabelsUnique)
    (hE : Q.EmittedLabelsUnique) :
    (reorderProgramWith succ extra Q).EmittedLabelsUnique := by
  unfold Program.EmittedLabelsUnique at hE ⊢
  exact (emittedLabels_reorderProgramWith_perm succ extra Q h).nodup_iff.mpr hE

/-- The entry block still exists. -/
theorem findBlock?_entry_reorderProgramWith (succ : Block → Option Label)
    (extra : List Label) (Q : Program) (h : Q.LabelsUnique)
    (hE : Q.findBlock? Q.entry ≠ none) :
    (reorderProgramWith succ extra Q).findBlock?
      (reorderProgramWith succ extra Q).entry ≠ none := by
  rw [reorderProgramWith_entry, findBlock?_reorderProgramWith succ extra Q h]
  exact hE

/-- **`WellTyped` is preserved by the reorder.** -/
theorem wellTyped_reorderProgramWith (succ : Block → Option Label)
    (extra : List Label) (Q : Program) (hW : Q.WellTyped) :
    (reorderProgramWith succ extra Q).WellTyped := by
  obtain ⟨hU, hA, hEntry, hEmit⟩ := hW
  exact ⟨reorderProgramWith_labelsUnique succ extra Q,
    allBlocksTyped_reorderProgramWith succ extra Q hU hA,
    findBlock?_entry_reorderProgramWith succ extra Q hU hEntry,
    emittedLabelsUnique_reorderProgramWith succ extra Q hU hEmit⟩

/-- **`ProgramCounterIndependent` is preserved** (a per-block, program-free
predicate — only block membership matters). -/
theorem programCounterIndependent_reorderProgramWith (succ : Block → Option Label)
    (extra : List Label) (Q : Program) (hP : Q.ProgramCounterIndependent) :
    (reorderProgramWith succ extra Q).ProgramCounterIndependent := by
  unfold Program.ProgramCounterIndependent at hP ⊢
  rw [List.forall_iff_forall_mem] at hP ⊢
  intro b hb
  exact hP b (reorderProgramWith_blocks_mem succ extra Q hb)

/-- **The fuel budget is exactly preserved** (a `.sum` over the permuted
blocks — even sharper than `chainCanon`'s `≤`). -/
theorem fuelBudget_reorderProgramWith_eq (succ : Block → Option Label)
    (extra : List Label) (Q : Program) (h : Q.LabelsUnique) :
    InteractionSemantics.CompiledProgram.fuelBudget (reorderProgramWith succ extra Q) =
      InteractionSemantics.CompiledProgram.fuelBudget Q := by
  unfold InteractionSemantics.CompiledProgram.fuelBudget
  exact ((reorderProgramWith_blocks_perm succ extra Q h).map
    InteractionSemantics.CompiledBlock.fuelBudget).sum_nat

/-! ## §Session-101: the candidate policies and the deterministic size argmin

Everything below is **selection machinery only**.  It decides *which* sound
permutation is emitted; it can never affect soundness, because every conclusion
above is universally quantified over `succ` and `extra`. -/

/-- Sentinel "infinitely large" program size, used when a candidate does not
lower at all (such a candidate can then never win the argmin). -/
def sizeUnavailable : Nat := 1 <<< 60

/-- A byte-exact model of the frozen serializer's physical code length: the
`Assembly.Compact` layout of `Compact.prepare (p.lower?)` at the branch width
the serializer itself would choose.  Purely a **selection heuristic** — it has
no correctness role and appears in no theorem statement. -/
def compactSize (p : Program) : Nat :=
  match p.lower? with
  | none => sizeUnavailable
  | some code =>
      let physical := Assembly.Compact.prepare code
      match Assembly.Compact.branchWidthFor? [] physical with
      | none => sizeUnavailable
      | some width =>
          match Assembly.Compact.layout? [] physical width with
          | none => sizeUnavailable
          | some (_, codeLength) => codeLength

/-! The four definitions that follow are the §101 policy alternatives that
`candidatePolicies` no longer searches (see the §102 note there: none of them
ever *strictly* beat a kept candidate on any object of the corpus — they only
ever tied — while together they were seven of the nine oracle evaluations).
They are retained, unused, as the documented re-widening points: adding any of
them back to `candidatePolicies` is sound by construction and can only lower the
emitted size, at the cost of one more `compactSize` per program. -/

/-- How many times each label is referenced as a terminator target, as a map
(the `Peephole.refCount` fold, batched).  Closed over by the `refCount = 1`
policies; incurs **zero** proof obligation because `succ` is arbitrary. -/
def refCountMap (p : Program) : Std.HashMap Label Nat :=
  p.blocks.foldl
    (fun m b =>
      b.term.targets.foldl (fun m t => m.insert t ((m.getD t 0) + 1)) m)
    (Std.HashMap.emptyWithCapacity (2 * p.blocks.length))

/-- Policy: `.jump` targets, plus the fallthrough arm of a `.jumpi` whose target
has a single predecessor (the guaranteed 4 B + 1 B win). -/
def succJumpOrRc1JumpiFall (rc : Std.HashMap Label Nat) (b : Block) :
    Option Label :=
  match b.term with
  | .jump t => some t
  | .jumpi _ n => if rc.getD n 0 == 1 then some n else none
  | _ => none

/-- Policy: `.jump` targets, plus the fallthrough arm of every `.jumpi`. -/
def succJumpOrJumpiFall (b : Block) : Option Label :=
  match b.term with
  | .jump t => some t
  | .jumpi _ n => some n
  | _ => none

/-- Policy: as `succJumpOrRc1JumpiFall`, plus the last dispatch site's target
(a `.returnDispatch` block's lowering ends with `jump (sites.getLast?).target`). -/
def succJumpOrRc1JumpiFallOrDispatch (rc : Std.HashMap Label Nat) (b : Block) :
    Option Label :=
  match b.term with
  | .jump t => some t
  | .jumpi _ n => if rc.getD n 0 == 1 then some n else none
  | .returnDispatch _ sites => (sites.getLast?).map ReturnSite.target
  | _ => none

/-- Policy: as `succJumpOrJumpiFall`, plus the last dispatch site's target. -/
def succJumpOrJumpiFallOrDispatch (b : Block) : Option Label :=
  match b.term with
  | .jump t => some t
  | .jumpi _ n => some n
  | .returnDispatch _ sites => (sites.getLast?).map ReturnSite.target
  | _ => none

/-- Seed prefix: the labels with in-degree 0 under `succ`, in block order.
Seeding roots first maximises realised adjacency on a functional successor
graph (a block placed before its own predecessor loses that edge). -/
def rootSeeds (succ : Block → Option Label) (p : Program) : List Label :=
  let preds : Std.HashSet Label :=
    p.blocks.foldl
      (fun s b =>
        match succ b with
        | some t => s.insert t
        | none => s)
      (Std.HashSet.emptyWithCapacity p.blocks.length)
  (p.blocks.filter (fun b => !preds.contains b.label)).map Block.label

/-- A layout policy: a successor relation plus a seed prefix. -/
abbrev Policy := (Block → Option Label) × List Label

/-- The candidate policies for `p`, **index 0 being the §100 `.jump`-only
policy** so that the argmin below can never be larger than what §100 emitted.

## §Session-102: why this list is two long and not nine

`compactSize` is not cheap — one evaluation is a full `reorderProgramWith`
(quadratic in the block count) plus `lower?`, `Compact.prepare` and the `Compact`
layout passes — and it is paid once *per candidate*, on every object of every
contract.  The §101 list had eight entries and `chosenPolicy` additionally
re-evaluated index 0 as its own seed, so **nine** evaluations were paid per
program.  Measured on the 40-contract corpus, that search is the single largest
term in compile time on the big contracts and it grows superlinearly with
program size (≈ 4.2 s per candidate on the 17 kB `DynamicStorageSurfaceBox`
against ≈ 0.02 s on a 1 kB contract).  `CHALLENGE.md` makes the per-contract
timeout and the total wall-clock budget *validity* conditions and the compiler
is fail-closed, so search width is a submission risk, not a nuisance.

The §101 probe over the 36 runtime objects settles what the width buys.  Per
policy, total bytes relative to the `.jump`-only layout:

| policy                                        | index | Δ bytes |
|-----------------------------------------------|------:|--------:|
| `.jump` only                                  |     0 |       0 |
| + `refCount = 1` jumpi fallthrough            |     — |  −4 321 |
| + any jumpi fallthrough                       |     — |  −4 335 |
| + `refCount = 1` jumpi + returnDispatch       |     — |  −4 748 |
| + any jumpi + returnDispatch                  |     — |  −4 782 |
| + `refCount = 1` jumpi, root-first seeds      |     — |  −4 379 |
| + any jumpi, root-first seeds                 |     — |  −4 389 |
| **+ any jumpi + returnDispatch, root-first**  |     1 |  −4 924 |
| per-contract argmin over all eight            |       |  −4 924 |

The argmin bought **exactly zero** bytes over the single best policy.  And
because a per-contract argmin is pointwise ≤ every fixed policy, equal totals
force pointwise equality: index 1 attains the minimum on *every* object of the
corpus, and `{index 0, index 1}` is the unique two-element subset containing
index 0 that reproduces the full nine-way argmin.  Re-measured end to end on the
corpus this list emits **byte-identical** output to the nine-way search
(56 597 runtime + 59 516 creation bytes either way) while cutting corpus compile
wall time by 20 % and the largest contract's by 42 %.

A three-candidate variant that also kept `any jumpi + returnDispatch` at the
default seeds was measured: it produced byte-identical *and* gas-identical
output to this two-candidate list, i.e. the extra candidate never once changed
the emitted program, and cost 10 % more compile time on the largest contract.
It was dropped.  Re-widening is a one-line change and can never cost bytes (the
argmin is over the whole list); it only costs time.

Index 0 stays first for the §101 reason: the emitted layout can never be larger
than what §100 shipped, and ties keep the earliest index. -/
def candidatePolicies (p : Program) : List Policy :=
  let sAllD := succJumpOrJumpiFallOrDispatch
  [ (succLabel?, [])
  , (sAllD, rootSeeds sAllD p)
  ]

/-- Deterministic argmin over the candidate list: a later candidate replaces the
incumbent only on a **strict** size decrease, so ties always keep the earliest
index and the whole choice is a pure function of `p`. -/
def bestPolicyFrom (p : Program) :
    List Policy → Policy → Nat → Policy
  | [], best, _ => best
  | pol :: rest, best, bestSize =>
      let size := compactSize (reorderProgramWith pol.1 pol.2 p)
      if size < bestSize then
        bestPolicyFrom p rest pol size
      else
        bestPolicyFrom p rest best bestSize

/-- The policy actually chosen for `p`.

The fold is seeded with the `sizeUnavailable` sentinel rather than with
`compactSize` of the fallback policy.  The fallback *is* `candidatePolicies`
index 0, so seeding with its size evaluated that policy's oracle twice — a free
~1/(n+1) of the whole search.  The outcome is unchanged: index 0 is the first
candidate, and it replaces the sentinel iff its size is `< sizeUnavailable`; if
it is not (the candidate does not lower), the incumbent is *already* that same
policy at that same size, so both the winner and the running minimum agree with
the old code in every case. -/
def chosenPolicy (p : Program) : Policy :=
  bestPolicyFrom p (candidatePolicies p) (succLabel?, []) sizeUnavailable

/-- The whole-program block-reorder transform: permute `blocks` under the
size-minimal candidate policy; everything else (entry, and each block verbatim)
fixed.  The `let` is load-bearing at run time only — it keeps the whole
`chosenPolicy` search from being evaluated once per projection. -/
def reorderProgram (p : Program) : Program :=
  let policy := chosenPolicy p
  reorderProgramWith policy.1 policy.2 p

/-- **The single bridge lemma.**  Whatever the size oracle decides, the emitted
program is `reorderProgramWith` at *some* policy — and every fact above holds at
*every* policy.  It is `rfl`: `chosenPolicy` returns the policy itself. -/
theorem reorderProgram_exists_policy (p : Program) :
    ∃ (succ : Block → Option Label) (extra : List Label),
      reorderProgram p = reorderProgramWith succ extra p :=
  ⟨(chosenPolicy p).1, (chosenPolicy p).2, rfl⟩

/-! ## §100-era conclusions, re-exported at their original names/signatures

These are exactly the statements the OIC `_reorder` twins and the
`CertifiedChoice` wiring consume; each is the corresponding `…With` fact
instantiated at the chosen policy. -/

@[simp] theorem reorderProgram_entry (p : Program) :
    (reorderProgram p).entry = p.entry := rfl

@[simp] theorem reorderProgram_blocks (p : Program) :
    (reorderProgram p).blocks =
      layoutBlocksWith (chosenPolicy p).1 (chosenPolicy p).2 p := rfl

theorem reorderProgram_blocks_mem (p : Program) {b : Block}
    (hb : b ∈ (reorderProgram p).blocks) : b ∈ p.blocks :=
  reorderProgramWith_blocks_mem _ _ p hb

theorem layoutBlocks_mem (p : Program) {b : Block}
    (hb : b ∈ layoutBlocksWith (chosenPolicy p).1 (chosenPolicy p).2 p) :
    b ∈ p.blocks :=
  layoutBlocksWith_mem _ _ p hb

theorem reorderProgram_labelsUnique (p : Program) :
    (reorderProgram p).LabelsUnique := by
  obtain ⟨s, e, hs⟩ := reorderProgram_exists_policy p
  rw [hs]; exact reorderProgramWith_labelsUnique s e p

theorem reorderProgram_blocks_perm (p : Program) (h : p.LabelsUnique) :
    (reorderProgram p).blocks.Perm p.blocks := by
  obtain ⟨s, e, hs⟩ := reorderProgram_exists_policy p
  rw [hs]; exact reorderProgramWith_blocks_perm s e p h

theorem findBlock?_reorderProgram (p : Program) (h : p.LabelsUnique) :
    ∀ l, (reorderProgram p).findBlock? l = p.findBlock? l := by
  obtain ⟨s, e, hs⟩ := reorderProgram_exists_policy p
  rw [hs]; exact findBlock?_reorderProgramWith s e p h

theorem openRunN_reorderProgram (Q : Program) (h : Q.LabelsUnique)
    (fuel : Nat) (label : Label) (state : EVMState) :
    InteractionSemantics.Program.openRunN (reorderProgram Q) fuel label state =
      InteractionSemantics.Program.openRunN Q fuel label state := by
  obtain ⟨s, e, hs⟩ := reorderProgram_exists_policy Q
  rw [hs]; exact openRunN_reorderProgramWith s e Q h fuel label state

theorem openRunNPrefix_reorderProgram (Q : Program) (h : Q.LabelsUnique)
    (fuel : Nat) (label : Label) (state : EVMState) :
    InteractionSemantics.Program.openRunNPrefix (reorderProgram Q) fuel label state =
      InteractionSemantics.Program.openRunNPrefix Q fuel label state := by
  obtain ⟨s, e, hs⟩ := reorderProgram_exists_policy Q
  rw [hs]; exact openRunNPrefix_reorderProgramWith s e Q h fuel label state

theorem openRunNResultWithStop_reorderProgram (Q : Program) (h : Q.LabelsUnique)
    (stopJump : Label → EVMState → Bool)
    (fuel : Nat) (label : Label) (state : EVMState) :
    InteractionSemantics.Program.openRunNResultWithStop stopJump
        (reorderProgram Q) fuel label state =
      InteractionSemantics.Program.openRunNResultWithStop stopJump
        Q fuel label state := by
  obtain ⟨s, e, hs⟩ := reorderProgram_exists_policy Q
  rw [hs]
  exact openRunNResultWithStop_reorderProgramWith s e Q h stopJump fuel label state

theorem openStep_reorderProgram (Q : Program) (h : Q.LabelsUnique)
    (label : Label) (state : EVMState) :
    InteractionSemantics.Program.openStep (reorderProgram Q) label state =
      InteractionSemantics.Program.openStep Q label state := by
  obtain ⟨s, e, hs⟩ := reorderProgram_exists_policy Q
  rw [hs]; exact openStep_reorderProgramWith s e Q h label state

theorem labelShape?_reorderProgram (Q : Program) (h : Q.LabelsUnique) :
    ∀ l, (reorderProgram Q).labelShape? l = Q.labelShape? l := by
  obtain ⟨s, e, hs⟩ := reorderProgram_exists_policy Q
  rw [hs]; exact labelShape?_reorderProgramWith s e Q h

theorem block_wellTyped_reorderProgram (Q : Program) (h : Q.LabelsUnique)
    (b : Block) :
    Block.WellTyped (reorderProgram Q) b ↔ Block.WellTyped Q b := by
  obtain ⟨s, e, hs⟩ := reorderProgram_exists_policy Q
  rw [hs]; exact block_wellTyped_reorderProgramWith s e Q h b

theorem allBlocksTyped_reorderProgram (Q : Program) (h : Q.LabelsUnique)
    (hA : Q.AllBlocksTyped) : (reorderProgram Q).AllBlocksTyped := by
  obtain ⟨s, e, hs⟩ := reorderProgram_exists_policy Q
  rw [hs]; exact allBlocksTyped_reorderProgramWith s e Q h hA

theorem emittedLabels_reorderProgram_perm (Q : Program) (h : Q.LabelsUnique) :
    (reorderProgram Q).EmittedLabels.Perm Q.EmittedLabels := by
  obtain ⟨s, e, hs⟩ := reorderProgram_exists_policy Q
  rw [hs]; exact emittedLabels_reorderProgramWith_perm s e Q h

theorem emittedLabelsUnique_reorderProgram (Q : Program) (h : Q.LabelsUnique)
    (hE : Q.EmittedLabelsUnique) : (reorderProgram Q).EmittedLabelsUnique := by
  obtain ⟨s, e, hs⟩ := reorderProgram_exists_policy Q
  rw [hs]; exact emittedLabelsUnique_reorderProgramWith s e Q h hE

theorem findBlock?_entry_reorderProgram (Q : Program) (h : Q.LabelsUnique)
    (hE : Q.findBlock? Q.entry ≠ none) :
    (reorderProgram Q).findBlock? (reorderProgram Q).entry ≠ none := by
  obtain ⟨s, e, hs⟩ := reorderProgram_exists_policy Q
  rw [hs]; exact findBlock?_entry_reorderProgramWith s e Q h hE

theorem wellTyped_reorderProgram (Q : Program) (hW : Q.WellTyped) :
    (reorderProgram Q).WellTyped := by
  obtain ⟨s, e, hs⟩ := reorderProgram_exists_policy Q
  rw [hs]; exact wellTyped_reorderProgramWith s e Q hW

theorem programCounterIndependent_reorderProgram (Q : Program)
    (hP : Q.ProgramCounterIndependent) :
    (reorderProgram Q).ProgramCounterIndependent := by
  obtain ⟨s, e, hs⟩ := reorderProgram_exists_policy Q
  rw [hs]; exact programCounterIndependent_reorderProgramWith s e Q hP

theorem fuelBudget_reorderProgram_eq (Q : Program) (h : Q.LabelsUnique) :
    InteractionSemantics.CompiledProgram.fuelBudget (reorderProgram Q) =
      InteractionSemantics.CompiledProgram.fuelBudget Q := by
  obtain ⟨s, e, hs⟩ := reorderProgram_exists_policy Q
  rw [hs]; exact fuelBudget_reorderProgramWith_eq s e Q h

end EvmCompiler.TypedCfg.BlockReorder
