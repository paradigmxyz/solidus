import EvmCompiler.TypedCfg.ShuffleCanonChain
import EvmCompiler.Structured.PeepholeSeamCombined

/-!
# Fuel-budget accounting for the cross-block chain canonicaliser

This orphan leaf collects the *fuel-budget* reductions for `chainCanonProgram`
that feed the (still-open) dual-hypothesis global bound

```
fuelBudget (chainCanonProgram program) ≤ fuelBudget program
```

banked green + axiom-clean.  §Session-91 established the bound needs BOTH
`(chainCanonProgram program).lower?.isSome` (F-side non-collapse) and
`program.lower?.isSome` (G-side non-collapse); §Session-92 reduced it — with no
`Nat` subtraction — to a permutation-to-lowering-order rewrite plus a per-chain
`canonSwaps_length_le` inequality (see `PEEPHOLE_PROGRESS.md`, §Session-92).

Nothing here is imported by the `compile_correct` cone: `chainCanonProgram` is
still referenced only inside the `ShuffleCanon*` cluster, so these lemmas cannot
touch the public axiom footprint.
-/

namespace EvmCompiler
namespace TypedCfg
namespace ShuffleCanon

open TypedCfg (Instr Shape Terminator Block Program Label)
open InteractionSemantics

/-! ## Lowered-length of chain bodies and the canonical head body -/

/-- A single `swap` whose `lowerAt?` succeeds lowers to exactly one instruction. -/
theorem lowerAt?_swap_length {d : Nat} {input : Shape}
    {code : Assembly.Program} {out : Shape}
    (h : Instr.lowerAt? (.swap d) input = some (code, out)) : code.length = 1 := by
  have hT : (Instr.type? (.swap d) input).isSome := by
    unfold Instr.lowerAt? at h
    rcases hh : Instr.type? (.swap d) input with _ | o
    · rw [hh] at h; simp at h
    · rfl
  rw [Option.isSome_iff_exists] at hT
  obtain ⟨o, ho⟩ := hT
  obtain ⟨hd, _, _⟩ := Instr.length_of_type?_swap ho
  unfold Instr.lowerAt? at h
  rw [ho] at h
  interval_cases d <;>
    · simp only [Instr.lower?, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rfl

/-- A single `bindLocals` whose `lowerAt?` succeeds lowers to zero instructions. -/
theorem lowerAt?_bindLocals_length {off : Nat} {names : List String} {input : Shape}
    {code : Assembly.Program} {out : Shape}
    (h : Instr.lowerAt? (.bindLocals off names) input = some (code, out)) :
    code.length = 0 := by
  have hT : (Instr.type? (.bindLocals off names) input).isSome := by
    unfold Instr.lowerAt? at h
    rcases hh : Instr.type? (.bindLocals off names) input with _ | o
    · rw [hh] at h; simp at h
    · rfl
  rw [Option.isSome_iff_exists] at hT
  obtain ⟨o, ho⟩ := hT
  unfold Instr.lowerAt? at h
  rw [ho] at h
  simp only [Instr.lower?, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  rfl

/-- If a chain body (`.swap`/`.bindLocals` only) lowers, its lowered length equals
its swap count (`.bindLocals` lowers to `[]`, so it contributes nothing). -/
theorem lowerBodyFrom?_chainBody_length (body : List Instr) {ds : List Nat}
    (hds : chainBodyDepths? body = some ds)
    {input : Shape} {code : Assembly.Program} {out : Shape}
    (hlow : Block.lowerBodyFrom? body input = some (code, out)) :
    code.length = ds.length := by
  induction body generalizing ds input code out with
  | nil =>
      simp only [chainBodyDepths?, Option.some.injEq] at hds
      subst hds
      simp only [Block.lowerBodyFrom?, Option.some.injEq, Prod.mk.injEq] at hlow
      simp [← hlow.1]
  | cons hd tl ih =>
      cases hd
      case swap d =>
          simp only [chainBodyDepths?] at hds
          rcases hh : chainBodyDepths? tl with _ | ds'
          · rw [hh] at hds; simp at hds
          · rw [hh] at hds
            simp only [Option.map_some, Option.some.injEq] at hds
            subst hds
            rw [Peephole.lowerBodyFrom?_cons] at hlow
            rcases hp : Instr.lowerAt? (.swap d) input with _ | ⟨pc, po⟩
            · rw [hp] at hlow; simp at hlow
            · rw [hp, Option.bind_some] at hlow
              rcases hq : Block.lowerBodyFrom? tl po with _ | ⟨qc, qo⟩
              · rw [hq] at hlow; simp at hlow
              · rw [hq, Option.bind_some] at hlow
                simp only [Option.some.injEq, Prod.mk.injEq] at hlow
                obtain ⟨hcode, _⟩ := hlow
                subst hcode
                rw [List.length_append, lowerAt?_swap_length hp, ih hh hq,
                  List.length_cons]
                omega
      case bindLocals off names =>
          simp only [chainBodyDepths?] at hds
          rw [Peephole.lowerBodyFrom?_cons] at hlow
          rcases hp : Instr.lowerAt? (.bindLocals off names) input with _ | ⟨pc, po⟩
          · rw [hp] at hlow; simp at hlow
          · rw [hp, Option.bind_some] at hlow
            rcases hq : Block.lowerBodyFrom? tl po with _ | ⟨qc, qo⟩
            · rw [hq] at hlow; simp at hlow
            · rw [hq, Option.bind_some] at hlow
              simp only [Option.some.injEq, Prod.mk.injEq] at hlow
              obtain ⟨hcode, _⟩ := hlow
              subst hcode
              rw [List.length_append, lowerAt?_bindLocals_length hp, ih hds hq]
              omega
      all_goals (exact absurd hds (by simp [chainBodyDepths?]))

/-- `chainBodyDepths?` of a pure `.swap` list is exactly its depths. -/
theorem chainBodyDepths?_map_swap (ns : List Nat) :
    chainBodyDepths? (ns.map Instr.swap) = some ns := by
  induction ns with
  | nil => rfl
  | cons d ds ih =>
      simp only [List.map_cons, chainBodyDepths?, ih, Option.map_some]

/-- A `.relabel` whose `lowerAt?` succeeds lowers to zero instructions. -/
theorem lowerAt?_relabel_length {t : Shape} {input : Shape}
    {code : Assembly.Program} {out : Shape}
    (h : Instr.lowerAt? (.relabel t) input = some (code, out)) : code.length = 0 := by
  have hT : (Instr.type? (.relabel t) input).isSome := by
    unfold Instr.lowerAt? at h
    rcases hh : Instr.type? (.relabel t) input with _ | o
    · rw [hh] at h; simp at h
    · rfl
  rw [Option.isSome_iff_exists] at hT
  obtain ⟨o, ho⟩ := hT
  unfold Instr.lowerAt? at h
  rw [ho] at h
  simp only [Instr.lower?, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  rfl

/-- The canonical head body `(canonSwaps merged).map .swap ++ [.relabel finalOut]`,
if it lowers, lowers to exactly `(canonSwaps merged).length` instructions
(the `.relabel` lowers to `[]`). -/
theorem lowerBodyFrom?_canonBody_length {ns : List Nat} {t : Shape}
    {input : Shape} {code : Assembly.Program} {out : Shape}
    (hlow : Block.lowerBodyFrom? ((ns.map Instr.swap) ++ [Instr.relabel t]) input
      = some (code, out)) :
    code.length = ns.length := by
  rw [Peephole.lowerBodyFrom?_append] at hlow
  rcases h1 : Block.lowerBodyFrom? (ns.map Instr.swap) input with _ | ⟨c1, m1⟩
  · rw [h1] at hlow; simp at hlow
  · rw [h1, Option.bind_some] at hlow
    rcases h2 : Block.lowerBodyFrom? [Instr.relabel t] m1 with _ | ⟨c2, m2⟩
    · rw [h2] at hlow; simp at hlow
    · rw [h2, Option.bind_some] at hlow
      simp only [Option.some.injEq, Prod.mk.injEq] at hlow
      obtain ⟨hcode, _⟩ := hlow
      subst hcode
      have hc1 : c1.length = ns.length :=
        lowerBodyFrom?_chainBody_length _ (chainBodyDepths?_map_swap ns) h1
      have hc2 : c2.length = 0 := by
        rw [Peephole.lowerBodyFrom?_cons] at h2
        rcases hp : Instr.lowerAt? (.relabel t) m1 with _ | ⟨pc, po⟩
        · rw [hp] at h2; simp at h2
        · rw [hp, Option.bind_some] at h2
          simp only [Block.lowerBodyFrom?, Option.bind_some, Option.some.injEq,
            Prod.mk.injEq] at h2
          obtain ⟨hc2eq, _⟩ := h2
          subst hc2eq
          simpa using lowerAt?_relabel_length hp
      rw [List.length_append, hc1, hc2]
      omega

/-- When a block's `lower?` succeeds, its fuel budget is `1 + |body code| + |term
code|`, with the body lowering from `b.input` to `b.output` and the terminator
lowering at `b.output`. -/
theorem fuelBudget_of_lower {b : Block} (h : b.lower?.isSome) :
    ∃ bc tc, Block.lowerBodyFrom? b.body b.input = some (bc, b.output) ∧
      b.term.lowerAt? b.output = some tc ∧
      CompiledBlock.fuelBudget b = 1 + bc.length + tc.length := by
  unfold Block.lower? at h
  rcases hbody : Block.lowerBodyFrom? b.body b.input with _ | ⟨bc, out⟩
  · rw [hbody] at h; simp at h
  · rw [hbody] at h
    by_cases hout : out = b.output
    · subst hout
      rcases hterm : b.term.lowerAt? b.output with _ | tc
      · simp [hterm] at h
      · refine ⟨bc, tc, rfl, rfl, ?_⟩
        unfold CompiledBlock.fuelBudget
        rw [hbody]
        simp only [↓reduceIte, hterm]
    · simp [hout] at h

/-! ## Chain-structure helpers (terminator invariance, `chainBodyOk`) -/

/-- Both bodies of a `chainStep` link are chain-eligible. -/
theorem chainStep_bodyOk {prog : Program} {a nxt : Block}
    (h : chainStep prog a nxt = true) : chainBodyOk a = true ∧ chainBodyOk nxt = true := by
  unfold chainStep at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.2, h.1.1.2⟩

/-- Every member of a `chainStep`-chain is either terminated by a `jump` (it has a
successor) or is the chain's last block. -/
theorem term_jump_or_getLastD (prog : Program) :
    ∀ (chain : List Block) (dflt : Block),
      List.Chain' (fun x y => chainStep prog x y = true) chain →
      ∀ b ∈ chain, (∃ L, b.term = Terminator.jump L) ∨ b = chain.getLastD dflt
  | [], _, _, b, hb => by simp at hb
  | [x], dflt, _, b, hb => by
      rw [List.mem_singleton] at hb; exact Or.inr (by rw [hb]; rfl)
  | x :: y :: rest, dflt, hc, b, hb => by
      obtain ⟨hxy, hrest⟩ := List.isChain_cons_cons.mp hc
      rw [List.mem_cons] at hb
      rcases hb with hb | hb
      · exact Or.inl ⟨y.label, by rw [hb]; exact (chainStep_spec hxy).1⟩
      · have := term_jump_or_getLastD prog (y :: rest) dflt hrest b hb
        rcases this with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [h]; simp only [List.getLastD_cons])

/-- Every member of a `chainStep`-chain of length ≥ 2 is chain-eligible
(`chainBodyOk`): a non-last member is the `a` of its outgoing step, the last member
is the `nxt` of its incoming step. -/
theorem chainBodyOk_of_mem_chain {prog : Program} :
    ∀ (chain : List Block),
      2 ≤ chain.length →
      List.Chain' (fun x y => chainStep prog x y = true) chain →
      ∀ b ∈ chain, chainBodyOk b = true
  | [], hlen, _, b, _ => by simp at hlen
  | [_], hlen, _, b, _ => by simp at hlen
  | x :: y :: rest, _, hc, b, hb => by
      obtain ⟨hxy, hrest⟩ := List.isChain_cons_cons.mp hc
      rw [List.mem_cons] at hb
      rcases hb with hb | hb
      · rw [hb]; exact (chainStep_bodyOk hxy).1
      · -- b ∈ y :: rest, and every member of a chainStep-chain that has a
        -- predecessor is `chainBodyOk` (as the `nxt` of some step)
        obtain ⟨P, _hP, hPC⟩ :=
          chainStep_pred_of_mem_tail (List.isChain_cons_cons.mpr ⟨hxy, hrest⟩) hb
        exact (chainStep_bodyOk hPC).2

/-- **Terminator invariance across the chain.**  Every member's terminator lowers
identically at the chain's `finalOut` as at its own output: non-last members are
`jump`-terminated (shape-independent), the last member has `finalOut = its output`. -/
theorem term_lowerAt?_finalOut_eq {prog : Program} {chain : List Block} {hd : Block}
    (hchain : chain = hd :: chain.tail)
    (hc : List.Chain' (fun x y => chainStep prog x y = true) chain) :
    ∀ b ∈ chain, b.term.lowerAt? (chain.getLastD hd).output = b.term.lowerAt? b.output := by
  intro b hb
  rcases term_jump_or_getLastD prog chain hd hc b hb with ⟨L, hjump⟩ | hlast
  · rw [hjump]; rfl
  · rw [hlast]

/-! ## `List.lookup` on appended tables -/

private theorem lookup_append_left {α β : Type _} [BEq α] {l1 l2 : List (α × β)}
    {k : α} {v : β} (h : l1.lookup k = some v) : (l1 ++ l2).lookup k = some v := by
  induction l1 with
  | nil => simp only [List.lookup_nil, reduceCtorEq] at h
  | cons p ps ih =>
      obtain ⟨a, b⟩ := p
      simp only [List.cons_append, List.lookup_cons] at h ⊢
      cases hbeq : k == a with
      | true => simp only [hbeq] at h ⊢; exact h
      | false => simp only [hbeq] at h ⊢; exact ih h

private theorem lookup_append_right {α β : Type _} [BEq α] {l1 l2 : List (α × β)}
    {k : α} (h : l1.lookup k = none) : (l1 ++ l2).lookup k = l2.lookup k := by
  induction l1 with
  | nil => rfl
  | cons p ps ih =>
      obtain ⟨a, b⟩ := p
      simp only [List.cons_append, List.lookup_cons] at h ⊢
      cases hbeq : k == a with
      | true => simp only [hbeq] at h; simp at h
      | false => simp only [hbeq] at h ⊢; exact ih h

/-! ## Small list-sum helpers -/

private theorem sum_map_add {α : Type _} (l : List α) (f g : α → Nat) :
    (l.map (fun a => f a + g a)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private theorem sum_map_const_one {α : Type _} (l : List α) :
    (l.map (fun _ => 1)).sum = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; omega

private theorem length_flatMap_eq {α β : Type _} (l : List α) (f : α → List β) :
    (l.flatMap f).length = (l.map (fun a => (f a).length)).sum := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons, ih]

/-! ## The per-chain fuel closure -/

/-- **Per-chain fuel closure.**  Under the two lowering hypotheses, canonicalising a
fired chain never increases its total compiled fuel budget.  The terminator code
length is preserved identically per member (`term_lowerAt?_finalOut_eq`), the
consumed bodies collapse to `[]`, and the head absorbs `canonSwaps merged`, whose
length is `≤ merged` (`canonSwaps_length_le`); the `1`s and the terminator sum
cancel between the two sides with no `Nat` subtraction. -/
theorem chainEdits_fuelBudget_le {prog : Program} {chain : List Block}
    (hlen : 2 ≤ chain.length)
    (hc : List.Chain' (fun x y => chainStep prog x y = true) chain)
    (hne : chainEdits chain ≠ [])
    (hNodup : (chain.map Block.label).Nodup)
    (hG : ∀ b ∈ chain, b.lower?.isSome)
    (hF : ∀ b ∈ chain, (applyEdit (chainEdits chain) b).lower?.isSome) :
    (chain.map (fun b => CompiledBlock.fuelBudget (applyEdit (chainEdits chain) b))).sum
      ≤ (chain.map CompiledBlock.fuelBudget).sum := by
  obtain ⟨hd, tl, hchaineq, htbl⟩ := chainEdits_entries hne
  subst hchaineq
  -- abbreviations matching the fired-chain edit shape
  set fo := ((hd :: tl).getLastD hd).output with hfo
  set merged := (hd :: tl).flatMap (fun b => (chainBodyDepths? b.body).getD []) with hmerged
  set cb := (canonSwaps merged).map Instr.swap ++ [Instr.relabel fo] with hcb
  -- per-member terminator length
  set TC : Block → Nat := fun b => ((b.term.lowerAt? b.output).getD []).length with hTC
  -- keys of the edit table are exactly the chain labels (nodup)
  have hmapfst : (chainEdits (hd :: tl)).map Prod.fst = (hd :: tl).map Block.label := by
    rw [htbl]; simp [List.map_map, Function.comp_def]
  have hkeys : ((chainEdits (hd :: tl)).map Prod.fst).Nodup := by rw [hmapfst]; exact hNodup
  -- terminator invariance across the chain
  have htail : (hd :: tl) = hd :: (hd :: tl).tail := rfl
  have hterm := term_lowerAt?_finalOut_eq htail hc
  -- applyEdit on the head and on consumed members
  have happly_hd : applyEdit (chainEdits (hd :: tl)) hd
      = { hd with body := cb, output := fo } := by
    have hlk : (chainEdits (hd :: tl)).lookup hd.label = some (Edit.head cb fo) :=
      lookup_eq_of_mem_nodup hkeys (by rw [htbl]; exact List.mem_cons_self ..)
    unfold applyEdit; rw [hlk]
  have happly_m : ∀ m ∈ tl, applyEdit (chainEdits (hd :: tl)) m
      = { m with input := fo, output := fo, body := [] } := by
    intro m hm
    have hlk : (chainEdits (hd :: tl)).lookup m.label = some (Edit.consumed fo) :=
      lookup_eq_of_mem_nodup hkeys
        (by rw [htbl]; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨m, hm, rfl⟩))
    unfold applyEdit; rw [hlk]
  -- G-side per-block value: fuelBudget b = 1 + |depths b| + TC b
  have hG_val : ∀ b ∈ (hd :: tl),
      CompiledBlock.fuelBudget b = 1 + ((chainBodyDepths? b.body).getD []).length + TC b := by
    intro b hb
    obtain ⟨bc, tc, hbody, hterm', hval⟩ := fuelBudget_of_lower (hG b hb)
    have hok : chainBodyOk b = true := chainBodyOk_of_mem_chain (hd :: tl) hlen hc b hb
    rw [chainBodyOk, Option.isSome_iff_exists] at hok
    obtain ⟨ds, hds⟩ := hok
    have hbc : bc.length = ((chainBodyDepths? b.body).getD []).length := by
      rw [lowerBodyFrom?_chainBody_length b.body hds hbody, hds, Option.getD_some]
    have htc : tc.length = TC b := by rw [hTC]; simp only [hterm', Option.getD_some]
    rw [hval, hbc, htc]
  -- F-side head value: 1 + |canonSwaps merged| + TC hd
  have hF_hd : CompiledBlock.fuelBudget (applyEdit (chainEdits (hd :: tl)) hd)
      = 1 + (canonSwaps merged).length + TC hd := by
    rw [happly_hd]
    have hlow := hF hd (List.mem_cons_self ..)
    rw [happly_hd] at hlow
    obtain ⟨bc, tc, hbody, hterm', hval⟩ := fuelBudget_of_lower hlow
    have hbc : bc.length = (canonSwaps merged).length :=
      lowerBodyFrom?_canonBody_length hbody
    have hti : hd.term.lowerAt? fo = hd.term.lowerAt? hd.output :=
      hterm hd (List.mem_cons_self ..)
    have htc : tc.length = TC hd := by
      rw [hTC]; simp only; rw [← hti, hterm']; simp only [Option.getD_some]
    rw [hval, hbc, htc]
  -- F-side consumed value: 1 + TC m
  have hF_m : ∀ m ∈ tl, CompiledBlock.fuelBudget (applyEdit (chainEdits (hd :: tl)) m)
      = 1 + TC m := by
    intro m hm
    rw [happly_m m hm]
    have hlow := hF m (List.mem_cons_of_mem _ hm)
    rw [happly_m m hm] at hlow
    obtain ⟨bc, tc, hbody, hterm', hval⟩ := fuelBudget_of_lower hlow
    have hbc : bc.length = 0 := by
      simp only [Block.lowerBodyFrom?, Option.some.injEq, Prod.mk.injEq] at hbody
      simp [← hbody.1]
    have hti : m.term.lowerAt? fo = m.term.lowerAt? m.output :=
      hterm m (List.mem_cons_of_mem _ hm)
    have htc : tc.length = TC m := by
      rw [hTC]; simp only; rw [← hti, hterm']; simp only [Option.getD_some]
    rw [hval, hbc, htc]
  -- assemble the two sums into shared atoms
  have hle : (canonSwaps merged).length ≤ merged.length := canonSwaps_length_le merged
  have hmergedlen : merged.length
      = ((hd :: tl).map (fun b => ((chainBodyDepths? b.body).getD []).length)).sum := by
    rw [hmerged]; exact length_flatMap_eq _ _
  -- G-sum closed form
  have hGsum : ((hd :: tl).map CompiledBlock.fuelBudget).sum
      = 1 + tl.length + TC hd + (tl.map TC).sum + merged.length := by
    rw [List.map_congr_left hG_val]
    rw [sum_map_add (hd :: tl) (fun b => 1 + ((chainBodyDepths? b.body).getD []).length) TC]
    rw [sum_map_add (hd :: tl) (fun _ => 1) (fun b => ((chainBodyDepths? b.body).getD []).length)]
    rw [sum_map_const_one, ← hmergedlen]
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega
  -- F-sum closed form
  have hFsum : ((hd :: tl).map
        (fun b => CompiledBlock.fuelBudget (applyEdit (chainEdits (hd :: tl)) b))).sum
      = 1 + tl.length + TC hd + (tl.map TC).sum + (canonSwaps merged).length := by
    rw [List.map_cons, List.sum_cons, hF_hd, List.map_congr_left hF_m]
    rw [sum_map_add tl (fun _ => 1) TC, sum_map_const_one]
    omega
  rw [hFsum, hGsum]
  omega

/-- `applyEdit` is the identity on any block whose label is absent from the
edit table, so it leaves the compiled fuel budget unchanged.  This is the
zero-difference contribution of every non-chain block in the global sum. -/
theorem fuelBudget_applyEdit_none {tbl : List (Label × Edit)} {b : Block}
    (h : tbl.lookup b.label = none) :
    CompiledBlock.fuelBudget (applyEdit tbl b) = CompiledBlock.fuelBudget b := by
  unfold applyEdit
  rw [h]

/-- The chain-canonicalised program's fuel budget as an explicit block-indexed
sum over the ORIGINAL block list (same order as `program.blocks`): the transform
only rewrites bodies/shapes via `applyEdit`, never reorders blocks.  Both this
sum and `fuelBudget program` therefore range over the identical list — the
per-chain rebalancing is a redistribution of summands, not a reordering. -/
theorem fuelBudget_chainCanonProgram_eq (program : Program) :
    CompiledProgram.fuelBudget (chainCanonProgram program) =
      (program.blocks.map
        (fun b => CompiledBlock.fuelBudget (applyEdit (editTable program) b))).sum := by
  simp only [CompiledProgram.fuelBudget, chainCanonProgram_blocks, List.map_map,
    Function.comp_def]

/-- Fuel budget is invariant under the lowering-order permutation: it may be
computed over `blocksInLoweringOrder?` instead of `program.blocks`.  This is the
bridge that makes chains **contiguous** (they are runs in the lowering order),
enabling the `scanEdits`-mirrored segment induction for the global bound. -/
theorem fuelBudget_eq_sum_ordered {program : Program} {ordered : List Block}
    (h : program.blocksInLoweringOrder? = some ordered) :
    CompiledProgram.fuelBudget program =
      (ordered.map CompiledBlock.fuelBudget).sum := by
  unfold CompiledProgram.fuelBudget
  exact (Program.blocksInLoweringOrder?_perm h).map CompiledBlock.fuelBudget
    |>.sum_eq

/-- The chain program's fuel budget likewise computed over the lowering order,
applying the SAME edit table `editTable program` (the transform reads the table
by label, which the permutation preserves). -/
theorem fuelBudget_chainCanonProgram_eq_sum_ordered
    {program : Program} {ordered : List Block}
    (h : program.blocksInLoweringOrder? = some ordered) :
    CompiledProgram.fuelBudget (chainCanonProgram program) =
      (ordered.map
        (fun b => CompiledBlock.fuelBudget (applyEdit (editTable program) b))).sum := by
  rw [fuelBudget_chainCanonProgram_eq]
  exact (Program.blocksInLoweringOrder?_perm h).map
    (fun b => CompiledBlock.fuelBudget (applyEdit (editTable program) b)) |>.sum_eq

/-! ## The `scanEdits`-mirrored segment induction and the top-level dual bound -/

/-- **Segment induction.**  Over any suffix `cur` of the lowering order, the
chain-canonicalised fuel sum is bounded by the original, provided the applied table
`tbl` routes each block's lookup exactly as `scanEdits` does on `cur`.  The proof
mirrors `scanEdits`: peel a fired chain (a contiguous run) and close it with
`chainEdits_fuelBudget_le`; a non-firing front block is unedited (`F = G`); recurse
on the remainder. -/
theorem fuelBudget_segment_le {prog : Program} {ordered : List Block}
    (hnd : (ordered.map Block.label).Nodup)
    (hGall : ∀ b ∈ ordered, b.lower?.isSome)
    {tbl : List (Label × Edit)}
    (hFall : ∀ b ∈ ordered, (applyEdit tbl b).lower?.isSome) :
    ∀ (fuel : Nat) (cur : List Block), cur.length ≤ fuel → cur <:+ ordered →
      (∀ b ∈ cur, tbl.lookup b.label = (scanEdits prog fuel cur).lookup b.label) →
      (cur.map (fun b => CompiledBlock.fuelBudget (applyEdit tbl b))).sum
        ≤ (cur.map CompiledBlock.fuelBudget).sum := by
  intro fuel
  induction fuel with
  | zero =>
      intro cur hlen _ _
      have : cur = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      subst this; simp
  | succ n ih =>
      intro cur hlen hsuf hlook
      cases cur with
      | nil => simp
      | cons b rest =>
          -- labels of `cur` are nodup (suffix of the nodup lowering order)
          have hcurnd : ((b :: rest).map Block.label).Nodup :=
            (hsuf.sublist.map Block.label).nodup hnd
          set chain := growChain prog b rest with hchdef
          have hlenpos : 1 ≤ chain.length := by
            rw [hchdef]; obtain ⟨tt, hcc⟩ := growChain_head prog b rest; rw [hcc]; simp
          by_cases hlenc : 2 ≤ chain.length
          · -- fired-length segment: `cur = chain ++ tailAfter`
            set tailAfter := rest.drop (chain.length - 1) with htadef
            have hscan : scanEdits prog (n + 1) (b :: rest)
                = chainEdits chain ++ scanEdits prog n tailAfter := by
              conv_lhs => rw [scanEdits]
              simp only [← hchdef, ← htadef, if_pos hlenc]
            have hcursplit : b :: rest = chain ++ tailAfter := by
              obtain ⟨t, ht⟩ := growChain_prefix prog b rest
              have htdrop : t = (b :: rest).drop chain.length := by
                have hc := congrArg (List.drop chain.length) ht
                rwa [List.drop_left] at hc
              have hdc : (b :: rest).drop chain.length = rest.drop (chain.length - 1) := by
                obtain ⟨m, hm⟩ : ∃ m, chain.length = m + 1 := ⟨chain.length - 1, by omega⟩
                rw [hm]; simp
              have htt : t = tailAfter := by rw [htdrop, hdc]
              rw [← htt]; exact ht.symm
            -- chain and tailAfter labels are disjoint (nodup of the split)
            have hdisj : (chain.map Block.label).Disjoint (tailAfter.map Block.label) := by
              have hh : ((chain ++ tailAfter).map Block.label).Nodup := by
                rw [← hcursplit]; exact hcurnd
              rw [List.map_append, List.nodup_append] at hh
              intro a ha hb
              exact hh.2.2 a ha a hb rfl
            have hchainnd : (chain.map Block.label).Nodup := by
              have : ((chain ++ tailAfter).map Block.label).Nodup := by rw [← hcursplit]; exact hcurnd
              rw [List.map_append, List.nodup_append] at this; exact this.1
            -- membership helpers
            have hcmemcur : ∀ c ∈ chain, c ∈ b :: rest := fun c hc => by
              rw [hcursplit]; exact List.mem_append_left _ hc
            have htmemcur : ∀ t' ∈ tailAfter, t' ∈ b :: rest := fun t' ht' => by
              rw [hcursplit]; exact List.mem_append_right _ ht'
            -- `T_tail` lookup vanishes on chain labels (disjointness)
            have hTtail_none : ∀ c ∈ chain,
                (scanEdits prog n tailAfter).lookup c.label = none := by
              intro c hc
              rcases hh : (scanEdits prog n tailAfter).lookup c.label with _ | e'
              · rfl
              · exfalso
                have hmem := lookup_mem hh
                have hkt : c.label ∈ tailAfter.map Block.label :=
                  (scanEdits_keys_sublist prog n tailAfter).subset
                    (List.mem_map.mpr ⟨_, hmem, rfl⟩)
                exact hdisj (List.mem_map.mpr ⟨c, hc, rfl⟩) hkt
            -- routing: `tbl` agrees with `chainEdits chain` on chain labels
            have hrw : ∀ c ∈ chain, applyEdit tbl c = applyEdit (chainEdits chain) c := by
              intro c hc
              have h1 : tbl.lookup c.label = (scanEdits prog (n + 1) (b :: rest)).lookup c.label :=
                hlook c (hcmemcur c hc)
              rw [hscan] at h1
              have hlookeq : tbl.lookup c.label = (chainEdits chain).lookup c.label := by
                rw [h1]
                by_cases hkey : (chainEdits chain).lookup c.label = none
                · rw [lookup_append_right hkey, hkey]; exact hTtail_none c hc
                · obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hkey
                  rw [lookup_append_left he, he]
              unfold applyEdit; rw [hlookeq]
            -- chain segment bound
            have hchainseg :
                (chain.map (fun c => CompiledBlock.fuelBudget (applyEdit tbl c))).sum
                  ≤ (chain.map CompiledBlock.fuelBudget).sum := by
              rw [List.map_congr_left (fun c hc => by rw [hrw c hc])]
              by_cases hfired : chainEdits chain = []
              · rw [hfired]; apply le_of_eq; simp only [applyEdit, List.lookup_nil]
              · refine chainEdits_fuelBudget_le hlenc (hchdef ▸ growChain_chain' prog b rest)
                  hfired hchainnd (fun c hc => hGall c (hsuf.subset (hcmemcur c hc))) ?_
                intro c hc
                have := hFall c (hsuf.subset (hcmemcur c hc))
                rwa [hrw c hc] at this
            -- tail recursion
            have hlook_tail : ∀ t' ∈ tailAfter,
                tbl.lookup t'.label = (scanEdits prog n tailAfter).lookup t'.label := by
              intro t' ht'
              have h1 := hlook t' (htmemcur t' ht')
              rw [hscan] at h1
              have hkey : (chainEdits chain).lookup t'.label = none := by
                rcases hh : (chainEdits chain).lookup t'.label with _ | e'
                · rfl
                · exfalso
                  have hmem := lookup_mem hh
                  have hkc : t'.label ∈ chain.map Block.label :=
                    (chainEdits_keys_sublist chain).subset (List.mem_map.mpr ⟨_, hmem, rfl⟩)
                  exact hdisj hkc (List.mem_map.mpr ⟨t', ht', rfl⟩)
              rwa [lookup_append_right hkey] at h1
            have htailrec :
                (tailAfter.map (fun b => CompiledBlock.fuelBudget (applyEdit tbl b))).sum
                  ≤ (tailAfter.map CompiledBlock.fuelBudget).sum := by
              refine ih tailAfter ?_ ?_ hlook_tail
              · have hh : (b :: rest).length = chain.length + tailAfter.length := by
                  rw [hcursplit, List.length_append]
                simp only [List.length_cons] at hlen hh ⊢
                omega
              · have hs : tailAfter <:+ b :: rest := by
                  rw [hcursplit]; exact List.suffix_append chain tailAfter
                exact hs.trans hsuf
            calc (( b :: rest).map (fun b => CompiledBlock.fuelBudget (applyEdit tbl b))).sum
                = (chain.map (fun b => CompiledBlock.fuelBudget (applyEdit tbl b))).sum
                    + (tailAfter.map (fun b => CompiledBlock.fuelBudget (applyEdit tbl b))).sum := by
                  rw [hcursplit, List.map_append, List.sum_append]
              _ ≤ (chain.map CompiledBlock.fuelBudget).sum
                    + (tailAfter.map CompiledBlock.fuelBudget).sum :=
                  Nat.add_le_add hchainseg htailrec
              _ = ((b :: rest).map CompiledBlock.fuelBudget).sum := by
                  rw [hcursplit, List.map_append, List.sum_append]
          · -- non-firing front block `b`: unedited, then recurse on `rest`
            have hscan : scanEdits prog (n + 1) (b :: rest) = scanEdits prog n rest := by
              conv_lhs => rw [scanEdits]
              simp only [← hchdef, if_neg hlenc]
            have hbnd : b.label ∉ rest.map Block.label := by
              simp only [List.map_cons, List.nodup_cons] at hcurnd; exact hcurnd.1
            have hbnone : (scanEdits prog n rest).lookup b.label = none := by
              rcases hh : (scanEdits prog n rest).lookup b.label with _ | e'
              · rfl
              · exfalso
                have hmem := lookup_mem hh
                exact hbnd ((scanEdits_keys_sublist prog n rest).subset
                  (List.mem_map.mpr ⟨_, hmem, rfl⟩))
            have hbid : applyEdit tbl b = b := by
              have h1 := hlook b (List.mem_cons_self ..)
              rw [hscan, hbnone] at h1
              unfold applyEdit; rw [h1]
            have hlook_rest : ∀ t' ∈ rest,
                tbl.lookup t'.label = (scanEdits prog n rest).lookup t'.label := by
              intro t' ht'
              have h1 := hlook t' (List.mem_cons_of_mem _ ht')
              rwa [hscan] at h1
            have hrestrec :
                (rest.map (fun b => CompiledBlock.fuelBudget (applyEdit tbl b))).sum
                  ≤ (rest.map CompiledBlock.fuelBudget).sum := by
              refine ih rest ?_ ((List.suffix_cons b rest).trans hsuf) hlook_rest
              simp only [List.length_cons] at hlen; omega
            simp only [List.map_cons, List.sum_cons, hbid]
            exact Nat.add_le_add (le_refl _) hrestrec

/-- If a whole program lowers, every one of its blocks lowers. -/
theorem lower?_isSome_of_mem_blocks {p : Program} (h : p.lower?.isSome) {b : Block}
    (hb : b ∈ p.blocks) : b.lower?.isSome := by
  obtain ⟨code, hcode⟩ := Option.isSome_iff_exists.mp h
  unfold Program.lower? at hcode
  cases hord : p.blocksInLoweringOrder? with
  | none => simp [hord] at hcode
  | some ordered =>
      simp [hord] at hcode
      have hbo : b ∈ ordered := (Program.blocksInLoweringOrder?_perm hord).mem_iff.mp hb
      obtain ⟨frag⟩ := Program.lowerBlocks?_fragment_of_mem hcode hbo
      exact Option.isSome_iff_exists.mpr ⟨frag.code, frag.lower⟩

/-- **The dual-hypothesis fuel bound (frontier item 3).**  If both the
chain-canonicalised program and the source program lower, chain canonicalisation
never increases the total compiled fuel budget. -/
theorem fuelBudget_chainCanonProgram_le {program : Program}
    (hUnique : program.LabelsUnique)
    (hF : (chainCanonProgram program).lower?.isSome)
    (hG : program.lower?.isSome) :
    CompiledProgram.fuelBudget (chainCanonProgram program)
      ≤ CompiledProgram.fuelBudget program := by
  obtain ⟨gcode, hglow⟩ := Option.isSome_iff_exists.mp hG
  unfold Program.lower? at hglow
  cases hord : program.blocksInLoweringOrder? with
  | none => simp [hord] at hglow
  | some ordered =>
      rw [fuelBudget_eq_sum_ordered hord, fuelBudget_chainCanonProgram_eq_sum_ordered hord]
      have hperm := Program.blocksInLoweringOrder?_perm hord
      have hnd : (ordered.map Block.label).Nodup := by
        have hbnd : (program.blocks.map Block.label).Nodup :=
          (Program.blockLabels_nodup_iff program).mpr hUnique
        exact (hperm.map Block.label).nodup_iff.mp hbnd
      have hGall : ∀ b ∈ ordered, b.lower?.isSome :=
        fun b hb => lower?_isSome_of_mem_blocks hG (hperm.mem_iff.mpr hb)
      have hFall : ∀ b ∈ ordered,
          (applyEdit (editTable program) b).lower?.isSome := by
        intro b hb
        refine lower?_isSome_of_mem_blocks hF ?_
        rw [chainCanonProgram_blocks]
        exact List.mem_map.mpr ⟨b, hperm.mem_iff.mpr hb, rfl⟩
      have hediteq : editTable program = scanEdits program program.blocks.length ordered := by
        unfold editTable; rw [hord]
      have hlook : ∀ b ∈ ordered, (editTable program).lookup b.label
          = (scanEdits program program.blocks.length ordered).lookup b.label :=
        fun b _ => by rw [hediteq]
      have hlen : ordered.length ≤ program.blocks.length := by
        rw [hperm.length_eq]
      exact fuelBudget_segment_le hnd hGall hFall program.blocks.length ordered
        hlen (List.suffix_refl _) hlook

end ShuffleCanon
end TypedCfg
end EvmCompiler
