import EvmCompiler.TypedCfg.ShuffleCanonChainRel

/-!
# Chain-transform step congruence (session-81)

Item 2 *tail* of the PEEPHOLE_PROGRESS §Session-74..80 campaign.  Discharges the
two kernel hypotheses the §80 block-level `Rel` kernels
(`headBlock_rel`/`consumedBlock_rel`) were left carrying, then assembles the
per-label `ChainStepRel` invariant + the disjunctive step congruence.

* **Frontier 1 — `runBody`-success from typing.**  A chain body (only
  `.swap`/identity instrs) that `WellTyped`-checks (`bodyType? body input = some
  out`) and whose input is `StackRealizes`d runs to `.ok (s', out)`: every swap
  is depth-feasible (`length_of_type?_swap` + `StackRealizes` threaded by
  `runState_stackRealizes`), every bookkeeping instr is a runtime identity.
* **Frontier 2 — the type→runtime `netStack` lift.**  `canonSwaps` preserves the
  net stack permutation in *position* units (`netStack (merged.map (·+1)) L =
  netStack ((canonSwaps merged).map (·+1)) L`), extended from the touched window
  to the full stack length via `netStack_congr_window`.

Imported by **nobody** in the spine ⟹ cannot affect the `compile_correct` axioms.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState SameRuntimeData)

/-! ## Frontier 1 — a well-typed, stack-realized chain body runs successfully -/

/-- **`runBody`-success from typing (chain bodies).**  A chain body — only
`.swap`/`.bindLocals`/`.bindScratch`/`.relabel` — that `bodyType?`-checks
`input → out` and whose `input` is realized by the runtime stack runs to
`.ok (s', out)` in the closed evaluator.  Discharges the `hrun*` hypotheses of
`headBlock_rel`/`consumedBlock_rel`.  The swap depth-feasibility is the typing
bound `depth + 2 ≤ input.length` composed with `StackRealizes`, threaded across
the body by `runState_stackRealizes`; the bookkeeping instrs are EVMState
identities. -/
theorem runBody_chain_ok :
    ∀ (body : List Instr) {input out : Shape} {s : EVMState},
      (∀ i ∈ body, ChainInstr i) →
      Block.bodyType? body input = some out →
      StackRealizes input s →
      ∃ s', TypedCfg.Block.runBody body input s = .ok (s', out)
  | [], input, out, s, _, hType, _ => by
      simp only [Block.bodyType?, Option.some.injEq] at hType
      subst hType
      exact ⟨s, rfl⟩
  | instr :: rest, input, out, s, hChain, hType, hReal => by
      rw [bodyType?_cons, Option.bind_eq_some_iff] at hType
      obtain ⟨mid, htype, hrest⟩ := hType
      have hHead : ChainInstr instr := hChain instr List.mem_cons_self
      -- The head instruction's `runState` succeeds.
      have hrun : ∃ s1, Instr.runState instr input s = .ok s1 := by
        cases instr with
        | swap d =>
            obtain ⟨hd16, hdlen, _⟩ := Instr.length_of_type?_swap htype
            have hReal' : input.length ≤ s.stack.length := hReal
            have hfeas : d + 1 + 1 ≤ s.stack.length := by omega
            rw [runState_swap_eq hd16, swap_eq_of_depth (by omega) hfeas]
            exact ⟨_, rfl⟩
        | bindLocals _ _ => exact ⟨s, rfl⟩
        | bindScratch _ _ _ => exact ⟨s, rfl⟩
        | relabel _ => exact ⟨s, rfl⟩
        | push _ => exact absurd hHead (by simp [ChainInstr])
        | returnToken _ => exact absurd hHead (by simp [ChainInstr])
        | prim _ => exact absurd hHead (by simp [ChainInstr])
        | pop => exact absurd hHead (by simp [ChainInstr])
        | dup _ => exact absurd hHead (by simp [ChainInstr])
        | unwind _ => exact absurd hHead (by simp [ChainInstr])
      obtain ⟨s1, hs1⟩ := hrun
      have hrunAt : Instr.runAt instr input s = .ok (s1, mid) := by
        simp only [Instr.runAt, htype, Option.elim, hs1, bind, Except.bind]
      have hReal1 : StackRealizes mid s1 := runState_stackRealizes htype hs1 hReal
      have hChainTail : ∀ i ∈ rest, ChainInstr i :=
        fun i hi => hChain i (List.mem_cons_of_mem _ hi)
      obtain ⟨s', hs'⟩ := runBody_chain_ok rest hChainTail hrest hReal1
      refine ⟨s', ?_⟩
      simp only [Block.runBody, hrunAt, bind, Except.bind]
      exact hs'

/-! ## Frontier 2 — the type→runtime `netStack` lift -/

/-- `bodyRunPositions` distributes over concatenation. -/
theorem bodyRunPositions_append (l1 l2 : List Instr) :
    bodyRunPositions (l1 ++ l2) = bodyRunPositions l1 ++ bodyRunPositions l2 := by
  induction l1 with
  | nil => rfl
  | cons i rest ih =>
      cases i <;> simp only [List.cons_append, bodyRunPositions, ih] <;> rfl

/-- Running positions of a literal `.swap` run: the depths shifted by one. -/
theorem bodyRunPositions_map_swap (r : List Nat) :
    bodyRunPositions (r.map Instr.swap) = r.map (· + 1) := by
  induction r with
  | nil => rfl
  | cons d ds ih => simp only [List.map_cons, bodyRunPositions, ih]

/-- A `.relabel`-terminated block contributes no running positions from its tail. -/
theorem bodyRunPositions_relabel_singleton (t : Shape) :
    bodyRunPositions [Instr.relabel t] = [] := rfl

/-- **Running positions of a chain-member body = its swap depths shifted by one.**
A chain body (`chainBodyDepths? body = some ds`) contributes exactly the runtime
positions `ds.map (·+1)`: the `.bindLocals` bookkeeping is skipped identically by
both the type-level `chainBodyDepths?` and the runtime-level `bodyRunPositions`. -/
theorem bodyRunPositions_eq_of_chainBodyDepths :
    ∀ {body : List Instr} {ds : List Nat},
      ShuffleCanon.chainBodyDepths? body = some ds →
      bodyRunPositions body = ds.map (· + 1)
  | [], ds, h => by
      simp only [ShuffleCanon.chainBodyDepths?, Option.some.injEq] at h
      subst h; rfl
  | Instr.swap d :: rest, ds, h => by
      simp only [ShuffleCanon.chainBodyDepths?, Option.map_eq_some_iff] at h
      obtain ⟨ds', hds', rfl⟩ := h
      simp only [bodyRunPositions, bodyRunPositions_eq_of_chainBodyDepths hds',
        List.map_cons]
  | Instr.bindLocals _ _ :: rest, ds, h => by
      simp only [ShuffleCanon.chainBodyDepths?] at h
      simp only [bodyRunPositions, bodyRunPositions_eq_of_chainBodyDepths h]

/-- **`canonSwaps` preserves the net stack permutation in position units.**  The
canonicalised swap run `(canonSwaps r).map (·+1)` induces the same `netStack` over
any window `L` at least as wide as the touched window `maxDepth (r.map (·+1)) + 1`.
This is the frontier-2 heart: the two `bodyType?`-agreeing runs realise the same
runtime stack permutation.  Extracted from the local `hcnet` of
`canonSwaps_bodyType?_preserve_uncond` and window-extended via
`netStack_congr_window`. -/
theorem netStack_canonSwaps_positions (r : List Nat) (L : Nat)
    (hL : ShuffleCanon.maxDepth (r.map (· + 1)) + 1 ≤ L) :
    ShuffleCanon.netStack ((ShuffleCanon.canonSwaps r).map (· + 1)) L
      = ShuffleCanon.netStack (r.map (· + 1)) L := by
  have hcanon : ShuffleCanon.canonSwaps r =
      if (ShuffleCanon.starDecompose (ShuffleCanon.netStack (r.map (· + 1))
            (ShuffleCanon.maxDepth (r.map (· + 1)) + 1))).length < r.length
      then (ShuffleCanon.starDecompose (ShuffleCanon.netStack (r.map (· + 1))
            (ShuffleCanon.maxDepth (r.map (· + 1)) + 1))).map (· - 1)
      else r := rfl
  -- Abbreviations (kept as plain lets so `hcanon`'s `rfl` shape is intact).
  set ps := r.map (· + 1) with hps
  set W := ShuffleCanon.maxDepth ps + 1 with hW
  set c := ShuffleCanon.starDecompose (ShuffleCanon.netStack ps W) with hc
  have htlen : (ShuffleCanon.netStack ps W).length = W := ShuffleCanon.netStack_length ps W
  have hperm : List.Perm (ShuffleCanon.netStack ps W)
      (List.range (ShuffleCanon.netStack ps W).length) := ShuffleCanon.netStack_perm_range ps W
  have hcnet : ShuffleCanon.netStack c W = ShuffleCanon.netStack ps W := by
    have h := ShuffleCanon.netStack_starDecompose_of_perm (ShuffleCanon.netStack ps W) hperm
    rw [htlen] at h; rw [hc]; exact h
  have hcW : ∀ e ∈ c, 1 ≤ e ∧ e < W := by
    intro e he
    have h := ShuffleCanon.starDecompose_elem_bounds (ShuffleCanon.netStack ps W) hperm e (hc ▸ he)
    rw [htlen] at h; exact h
  have hpsW : ∀ q ∈ ps, q < W := fun q hq =>
    Nat.lt_succ_of_le (ShuffleCanon.mem_le_maxDepth ps q hq)
  have hmap : (c.map (· - 1)).map (· + 1) = c := by
    rw [List.map_map]
    have hcong : c.map ((· + 1) ∘ (· - 1)) = c.map id := by
      apply List.map_congr_left
      intro e he
      have h1 := (hcW e he).1
      simp only [Function.comp_apply, id]; omega
    rw [hcong, List.map_id]
  by_cases hfire :
      (ShuffleCanon.starDecompose (ShuffleCanon.netStack ps W)).length < r.length
  · rw [hcanon]
    simp only [hc] at hfire ⊢
    rw [if_pos hfire, hmap]
    exact ShuffleCanon.netStack_congr_window c ps W L (fun e he => (hcW e he).2) hpsW hL hcnet
  · rw [hcanon]
    simp only [hc] at hfire ⊢
    rw [if_neg hfire]

/-! ## Chain-body side-condition helpers (ChainInstr / depth bounds / feasibility) -/

/-- A chain-eligible body (`chainBodyDepths? = some _`) consists only of
`ChainInstr` instructions. -/
theorem chainInstr_of_chainBodyDepths :
    ∀ {body : List Instr} {ds : List Nat},
      ShuffleCanon.chainBodyDepths? body = some ds →
      ∀ i ∈ body, ChainInstr i
  | [], _, _, i, hi => absurd hi (List.not_mem_nil)
  | Instr.swap d :: rest, ds, h, i, hi => by
      simp only [ShuffleCanon.chainBodyDepths?, Option.map_eq_some_iff] at h
      obtain ⟨ds', hds', rfl⟩ := h
      rcases List.mem_cons.1 hi with rfl | hi'
      · simp [ChainInstr]
      · exact chainInstr_of_chainBodyDepths hds' i hi'
  | Instr.bindLocals _ _ :: rest, ds, h, i, hi => by
      simp only [ShuffleCanon.chainBodyDepths?] at h
      rcases List.mem_cons.1 hi with rfl | hi'
      · simp [ChainInstr]
      · exact chainInstr_of_chainBodyDepths h i hi'

/-- The canonicalised head body `(swaps).map .swap ++ [.relabel t]` is all
`ChainInstr`. -/
theorem chainInstr_canonBody (r : List Nat) (t : Shape) :
    ∀ i ∈ (r.map Instr.swap ++ [Instr.relabel t]), ChainInstr i := by
  intro i hi
  rw [List.mem_append] at hi
  rcases hi with hi | hi
  · rw [List.mem_map] at hi; obtain ⟨d, _, rfl⟩ := hi; simp [ChainInstr]
  · simp only [List.mem_singleton] at hi; subst hi; simp [ChainInstr]

/-- Every `.swap` in a `bodyType?`-checked body has depth `< 16`. -/
theorem chain_swap_lt16 :
    ∀ (body : List Instr) {input out : Shape},
      Block.bodyType? body input = some out →
      ∀ d, Instr.swap d ∈ body → d < 16
  | [], _, _, _, _, hd => absurd hd List.not_mem_nil
  | instr :: rest, input, out, hType, d, hd => by
      rw [bodyType?_cons, Option.bind_eq_some_iff] at hType
      obtain ⟨mid, htype, hrest⟩ := hType
      rcases List.mem_cons.1 hd with rfl | hd'
      · exact (Instr.length_of_type?_swap htype).1
      · exact chain_swap_lt16 rest hrest d hd'

/-- **Position feasibility.**  In a `bodyType?`-checked chain body, every runtime
position `p ∈ bodyRunPositions body` satisfies `1 ≤ p` and `p + 1 ≤ input.length`
(the swap-depth typing bound, propagated by length-preserving bookkeeping). -/
theorem bodyRunPositions_bound :
    ∀ (body : List Instr) {input out : Shape},
      (∀ i ∈ body, ChainInstr i) →
      Block.bodyType? body input = some out →
      ∀ p ∈ bodyRunPositions body, 1 ≤ p ∧ p + 1 ≤ input.length
  | [], _, _, _, _, p, hp => by simp only [bodyRunPositions, List.not_mem_nil] at hp
  | instr :: rest, input, out, hChain, hType, p, hp => by
      rw [bodyType?_cons, Option.bind_eq_some_iff] at hType
      obtain ⟨mid, htype, hrest⟩ := hType
      have hChainTail : ∀ i ∈ rest, ChainInstr i :=
        fun i hi => hChain i (List.mem_cons_of_mem _ hi)
      have hHead : ChainInstr instr := hChain instr List.mem_cons_self
      cases instr with
      | swap d =>
          obtain ⟨_, hdlen, hmidlen⟩ := Instr.length_of_type?_swap htype
          simp only [bodyRunPositions, List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact ⟨by omega, by omega⟩
          · have h := bodyRunPositions_bound rest hChainTail hrest p hp
            rw [hmidlen] at h; exact h
      | bindLocals _ _ =>
          simp only [bodyRunPositions] at hp
          have h := bodyRunPositions_bound rest hChainTail hrest p hp
          rw [Instr.length_of_type?_bindLocals htype] at h; exact h
      | bindScratch _ _ _ =>
          simp only [bodyRunPositions] at hp
          have h := bodyRunPositions_bound rest hChainTail hrest p hp
          rw [Instr.length_of_type?_bindScratch htype] at h; exact h
      | relabel _ =>
          simp only [bodyRunPositions] at hp
          have h := bodyRunPositions_bound rest hChainTail hrest p hp
          rw [Instr.length_of_type?_relabel htype] at h; exact h
      | push _ => exact absurd hHead (by simp [ChainInstr])
      | returnToken _ => exact absurd hHead (by simp [ChainInstr])
      | prim _ => exact absurd hHead (by simp [ChainInstr])
      | pop => exact absurd hHead (by simp [ChainInstr])
      | dup _ => exact absurd hHead (by simp [ChainInstr])
      | unwind _ => exact absurd hHead (by simp [ChainInstr])

/-- `canonSwaps` of the empty run is empty. -/
theorem canonSwaps_nil : ShuffleCanon.canonSwaps [] = [] := by decide

/-- **The netStack lift from a position bound.**  If every position of the
merged run stays within the stack window `L`, the merged run and its
`canonSwaps` induce the same `netStack` over `L` (handling the empty run, where
both sides are `List.range L`). -/
theorem netStack_canonSwaps_bound (r : List Nat) (L : Nat)
    (hb : ∀ p ∈ r.map (· + 1), p + 1 ≤ L) :
    ShuffleCanon.netStack (r.map (· + 1)) L
      = ShuffleCanon.netStack ((ShuffleCanon.canonSwaps r).map (· + 1)) L := by
  rcases r with _ | ⟨d, ds⟩
  · rw [canonSwaps_nil]
  · have hmem : (d + 1) ∈ (d :: ds).map (· + 1) := by simp
    have hL : d + 1 + 1 ≤ L := hb _ hmem
    have hwin : ShuffleCanon.maxDepth ((d :: ds).map (· + 1)) + 1 ≤ L := by
      have hle : ShuffleCanon.maxDepth ((d :: ds).map (· + 1)) ≤ L - 1 :=
        ShuffleCanon.maxDepth_le _ (L - 1) (fun q hq => by
          have := hb q hq; omega)
      omega
    exact (netStack_canonSwaps_positions (d :: ds) L hwin).symm

/-! ## The carried invariant + disjunctive outcome relation -/

open ShuffleCanon (editTable Edit chainCanonProgram)

/-- The inter-block state invariant carried across a fired fallthrough chain.
`SameRuntimeData` unless the block is a *consumed* chain member, in which case the
original side is `residual` swaps behind the (fixed) transformed end state —
`PendingPerm (residual program label)`.  `residual` is threaded per-label by the
step congruence; here it is left as a parameter (the value computed off the chain
suffix). -/
def ChainStepRel (program : Program) (residual : Label → List Nat)
    (label : Label) (s_o s_c : EVMState) : Prop :=
  match (editTable program).lookup label with
  | some (.consumed _) => PendingPerm (residual label) s_c s_o
  | _ => SameRuntimeData s_o s_c

/-- The disjunctive one-step outcome relation for the chain canonicaliser: either
a synchronised `jump` landing in `ChainStepRel` at the next label, or a plain
runtime-related non-jump outcome. -/
def ChainOutcomeRel (program : Program) (residual : Label → List Nat) :
    Except EVMException TypedCfg.Outcome →
      Except EVMException TypedCfg.Outcome → Prop :=
  fun a b =>
    (∃ (next : Label) (so sc : EVMState),
      a = .ok (.jump next so) ∧ b = .ok (.jump next sc) ∧
        ChainStepRel program residual next so sc)
    ∨ (InteractionCongruence.Block.RuntimeOutcomeRel a b ∧
        ∀ (next : Label) (s : EVMState), a ≠ .ok (.jump next s))

/-! ## Discharged block-body Rel kernels (§80 kernels with side conditions closed) -/

/-- **Consumed body kernel, side conditions discharged.**  `consumedBlock_rel`
with its `hrun`/`ChainInstr`/`hsw16` hypotheses closed from `WellTyped` +
chain-eligibility + `StackRealizes`. -/
theorem consumedBlock_rel_discharged {program : Program}
    {b0 : Block} {out : Shape} {ds σ : List Nat} {s_o s_c : EVMState}
    (hb0typed : b0.WellTyped program)
    (helig : ShuffleCanon.chainBodyDepths? b0.body = some ds)
    (hP : PendingPerm (bodyRunPositions b0.body ++ σ) s_c s_o)
    (hReal_o : StackRealizes b0.input s_o) :
    Simulation.Interaction.Rel
      (Simulation.Interaction.ExceptRel (fun a b : EVMException => a = b)
        (fun lp rp : EVMState × Shape =>
          PendingPerm σ rp.1 lp.1 ∧ lp.2 = b0.output ∧ rp.2 = out))
      (InteractionSemantics.Block.openRunBody b0.body b0.input s_o)
      (InteractionSemantics.Block.openRunBody [] out s_c) := by
  have hbt : Block.bodyType? b0.body b0.input = some b0.output := hb0typed.1
  have hChain : ∀ i ∈ b0.body, ChainInstr i := chainInstr_of_chainBodyDepths helig
  have hsw16 : ∀ d, Instr.swap d ∈ b0.body → d < 16 := chain_swap_lt16 b0.body hbt
  obtain ⟨s_o', hrun⟩ := runBody_chain_ok b0.body hChain hbt hReal_o
  exact consumedBlock_rel hChain hsw16 hP hrun

/-- **Head body kernel (birth), side conditions discharged.**  `headBlock_rel`
with all its `ChainInstr`/`hsw16`/`hpos`/`hlen`/`hnet`/`hrun` hypotheses closed
from typing, chain-eligibility, `StackRealizes`, the merged-position bound, and
the chain-consistency identity `bodyRunPositions b0.body ++ rest = merged.map
(·+1)` (frontiers 1 & 2). -/
theorem headBlock_rel_discharged {program : Program}
    {b0 : Block} {body : List Instr} {out : Shape} {merged ds rest : List Nat}
    {s_o s_c : EVMState}
    (hb0typed : b0.WellTyped program)
    (helig : ShuffleCanon.chainBodyDepths? b0.body = some ds)
    (hbody : body = (ShuffleCanon.canonSwaps merged).map Instr.swap ++ [Instr.relabel out])
    (htypeBody : Block.bodyType? body b0.input = some out)
    (hident : bodyRunPositions b0.body ++ rest = merged.map (· + 1))
    (hmergedBound : ∀ p ∈ merged.map (· + 1), p + 1 ≤ b0.input.length)
    (hSRD : SameRuntimeData s_o s_c)
    (hReal_o : StackRealizes b0.input s_o)
    (hReal_c : StackRealizes b0.input s_c) :
    Simulation.Interaction.Rel
      (Simulation.Interaction.ExceptRel (fun a b : EVMException => a = b)
        (fun lp rp : EVMState × Shape =>
          PendingPerm rest rp.1 lp.1 ∧ lp.2 = b0.output ∧ rp.2 = out))
      (InteractionSemantics.Block.openRunBody b0.body b0.input s_o)
      (InteractionSemantics.Block.openRunBody body b0.input s_c) := by
  have hbt : Block.bodyType? b0.body b0.input = some b0.output := hb0typed.1
  have hChainH : ∀ i ∈ b0.body, ChainInstr i := chainInstr_of_chainBodyDepths helig
  have hsw16H : ∀ d, Instr.swap d ∈ b0.body → d < 16 := chain_swap_lt16 b0.body hbt
  have hChainC : ∀ i ∈ body, ChainInstr i := by
    rw [hbody]; exact chainInstr_canonBody (ShuffleCanon.canonSwaps merged) out
  have hsw16C : ∀ d, Instr.swap d ∈ body → d < 16 := chain_swap_lt16 body htypeBody
  obtain ⟨s_o', hrunO⟩ := runBody_chain_ok b0.body hChainH hbt hReal_o
  obtain ⟨s_c', hrunC⟩ := runBody_chain_ok body hChainC htypeBody hReal_c
  -- position facts, via the merged identity
  have hposConcat : ∀ p ∈ bodyRunPositions b0.body ++ rest, 1 ≤ p := by
    intro p hp; rw [hident, List.mem_map] at hp; obtain ⟨d, _, rfl⟩ := hp; omega
  have hlenConcat : ∀ p ∈ bodyRunPositions b0.body ++ rest, p + 1 ≤ s_o.stack.length := by
    intro p hp; rw [hident] at hp
    exact le_trans (hmergedBound p hp) hReal_o.le
  have hposC : ∀ p ∈ bodyRunPositions body, 1 ≤ p := fun p hp =>
    (bodyRunPositions_bound body hChainC htypeBody p hp).1
  have hlenC : ∀ p ∈ bodyRunPositions body, p + 1 ≤ s_c.stack.length := fun p hp =>
    le_trans (bodyRunPositions_bound body hChainC htypeBody p hp).2 hReal_c.le
  -- netStack lift
  have hnet : ShuffleCanon.netStack (bodyRunPositions b0.body ++ rest) s_o.stack.length
      = ShuffleCanon.netStack (bodyRunPositions body) s_o.stack.length := by
    rw [hident, hbody, bodyRunPositions_append, bodyRunPositions_map_swap,
      bodyRunPositions_relabel_singleton, List.append_nil]
    exact netStack_canonSwaps_bound merged s_o.stack.length (fun p hp =>
      le_trans (hmergedBound p hp) hReal_o)
  have hR := headBlock_rel (headBody := b0.body) (canonBody := body) (rest := rest)
    (hin := b0.input) (hout := b0.output) (cin := b0.input) (cout := out)
    hChainH hsw16H hChainC hsw16C hSRD hposConcat hposC hlenConcat hlenC hnet hrunO hrunC
  exact hR

/-! ## Entry seed: the entry block is never a consumed chain member -/

/-- The program entry is never a *consumed* chain member: consumed members are the
non-head chain blocks, each of which has a `chainStep`-predecessor whose step
guard forces `nxt.label ≠ program.entry`. -/
theorem editTable_entry_ne_consumed {program : Program} {out : Shape} :
    (editTable program).lookup program.entry ≠ some (Edit.consumed out) := by
  intro h
  have hmem := ShuffleCanon.lookup_mem h
  unfold editTable at hmem
  split at hmem
  · simp only [List.not_mem_nil] at hmem
  · rename_i ordered hord
    obtain ⟨b, rest, _hsuf, _hlen, hmem', _hsub⟩ := ShuffleCanon.scanEdits_mem hmem
    obtain ⟨hd, tl, hchain, _hbody, hcases⟩ := ShuffleCanon.chainEdits_fired hmem'
    rcases hcases with heq | ⟨C, hC, hCeq⟩
    · rw [Prod.mk.injEq] at heq; exact absurd heq.2 (by simp)
    · rw [Prod.mk.injEq] at hCeq
      have hClabel : program.entry = C.label := hCeq.1
      have hgc := ShuffleCanon.growChain_chain' program b rest
      rw [hchain] at hgc
      obtain ⟨P, _, hstep⟩ := ShuffleCanon.chainStep_pred_of_mem_tail hgc hC
      obtain ⟨_, _, hne⟩ := ShuffleCanon.chainStep_spec hstep
      exact hne hClabel.symm

/-- **Entry seed (`ChainStepRel`).**  At the program entry, equal states satisfy
`ChainStepRel` via its `SameRuntimeData` branch (the entry is never consumed). -/
theorem chainStepRel_entry (program : Program) (residual : Label → List Nat)
    (s : EVMState) : ChainStepRel program residual program.entry s s := by
  unfold ChainStepRel
  cases hlk : (editTable program).lookup program.entry with
  | none => exact SameRuntimeData.refl s
  | some e =>
      cases e with
      | head _ _ => exact SameRuntimeData.refl s
      | consumed out => exact absurd hlk editTable_entry_ne_consumed

/-! ## The residual specification (chain structure the congruence consumes)

`ChainResidualSpec program residual` bundles the per-block chain-consistency facts
each congruence branch reads off — the head's merged/successor/position link and
the consumed member's interior/last dichotomy — as a predicate a residual
*construction* discharges.  This decouples the (banked, below) step congruence
from the residual construction (the remaining frontier). -/
structure ChainResidualSpec (program : Program) (residual : Label → List Nat) : Prop where
  head : ∀ {b0 : Block} {body : List Instr} {out : Shape},
      b0 ∈ program.blocks →
      (editTable program).lookup b0.label = some (Edit.head body out) →
      ∃ (B : Block) (merged ds : List Nat),
        ShuffleCanon.chainBodyDepths? b0.body = some ds ∧
        b0.term = Terminator.jump B.label ∧
        (editTable program).lookup B.label = some (Edit.consumed out) ∧
        body = (ShuffleCanon.canonSwaps merged).map Instr.swap ++ [Instr.relabel out] ∧
        bodyRunPositions b0.body ++ residual B.label = merged.map (· + 1) ∧
        (∀ p ∈ merged.map (· + 1), p + 1 ≤ b0.input.length)
  consumed : ∀ {b0 : Block} {out : Shape},
      b0 ∈ program.blocks →
      (editTable program).lookup b0.label = some (Edit.consumed out) →
      (∃ ds, ShuffleCanon.chainBodyDepths? b0.body = some ds) ∧
      ((∃ D : Block, b0.term = Terminator.jump D.label ∧
           (editTable program).lookup D.label = some (Edit.consumed out) ∧
           residual b0.label = bodyRunPositions b0.body ++ residual D.label)
        ∨ (out = b0.output ∧ residual b0.label = bodyRunPositions b0.body ∧
           ∀ (L : Label), L ∈ b0.term.targets →
             ∀ o, (editTable program).lookup L ≠ some (Edit.consumed o)))

/-! ## Terminator-composition tail lemmas -/

/-- **Jump-with-pending tail.**  After a chain block body runs (leaving the two
states in `PendingPerm (residual next)`), the preserved `jump next` terminator on
both sides lands in `ChainOutcomeRel`'s synchronised-jump branch at `next`
(consumed ⟹ `ChainStepRel next = PendingPerm (residual next)`). -/
theorem chainOutcome_jump_pending {program : Program} {residual : Label → List Nat}
    {next : Label} {shapeL shapeR : Shape} {sL sR : EVMState} {out : Shape}
    (hlkNext : (editTable program).lookup next = some (Edit.consumed out))
    (hP : PendingPerm (residual next) sR sL) :
    ChainOutcomeRel program residual
      (TypedCfg.Block.runTermChecked shapeL (Terminator.jump next) sL)
      (TypedCfg.Block.runTermChecked shapeR (Terminator.jump next) sR) := by
  rw [TypedCfg.Block.runTermChecked_jump, TypedCfg.Block.runTermChecked_jump,
    TypedCfg.Block.runTerm, TypedCfg.Block.runTerm]
  refine Or.inl ⟨next, sL, sR, rfl, rfl, ?_⟩
  unfold ChainStepRel
  rw [hlkNext]
  exact hP

/-- **SRD-resync tail.**  From re-synchronised (`SameRuntimeData`) states, a
block's (unchanged) terminator run on the SAME output shape lands in
`ChainOutcomeRel` — a synchronised jump when the target is not consumed (SRD
branch of `ChainStepRel`), else a plain runtime-related non-jump. -/
theorem chainOutcome_srd_resync {program : Program} {residual : Label → List Nat}
    {b0 : Block} {sL sR : EVMState}
    (htargets : ∀ (L : Label), L ∈ b0.term.targets →
      ∀ o, (editTable program).lookup L ≠ some (Edit.consumed o))
    (hSRD : SameRuntimeData sL sR) :
    Simulation.Interaction.Rel (ChainOutcomeRel program residual)
      (match TypedCfg.Block.runTermChecked b0.output b0.term sL with
        | .ok outcome => pure outcome | .error err => throw err)
      (match TypedCfg.Block.runTermChecked b0.output b0.term sR with
        | .ok outcome => pure outcome | .error err => throw err) := by
  have hChecked := InteractionCongruence.Block.runTermChecked_runtimeRel
    (shape := b0.output) (term := b0.term) hSRD
  cases hL : TypedCfg.Block.runTermChecked b0.output b0.term sL with
  | error eL =>
      cases hR : TypedCfg.Block.runTermChecked b0.output b0.term sR with
      | error eR =>
          rw [hL, hR] at hChecked
          exact Simulation.Interaction.Rel.done (Or.inr ⟨hChecked, by simp⟩)
      | ok oR => rw [hL, hR] at hChecked; cases hChecked
  | ok oL =>
      cases hR : TypedCfg.Block.runTermChecked b0.output b0.term sR with
      | error eR => rw [hL, hR] at hChecked; cases hChecked
      | ok oR =>
          rw [hL, hR] at hChecked
          refine Simulation.Interaction.Rel.done ?_
          cases hChecked with
          | ok hrr =>
              cases hrr with
              | jump lbl hSt =>
                  have hmemT : lbl ∈ b0.term.targets :=
                    runTerm_jump_mem_targets
                      (TypedCfg.Block.runTerm_eq_of_runTermChecked_eq_ok hL)
                  refine Or.inl ⟨lbl, _, _, rfl, rfl, ?_⟩
                  unfold ChainStepRel
                  cases hfindL : (editTable program).lookup lbl with
                  | none => exact hSt
                  | some e =>
                      cases e with
                      | head _ _ => exact hSt
                      | consumed o => exact absurd hfindL (htargets lbl hmemT o)
              | fallthrough hSt => exact Or.inr ⟨.ok (.fallthrough hSt), by simp⟩
              | returnDispatch hSt => exact Or.inr ⟨.ok (.returnDispatch hSt), by simp⟩
              | halt kind hSt => exact Or.inr ⟨.ok (.halt kind hSt), by simp⟩
              | invalid hSt => exact Or.inr ⟨.ok (.invalid hSt), by simp⟩

/-! ## The block-level chain-canonicalisation step congruence -/

/-- **Block-level chain-canonicalisation congruence.**  Under the residual spec,
running the original block from `s_o` is `ChainOutcomeRel`-related to running its
transformed image from `s_c`, given the entry invariant `ChainStepRel` and runtime
feasibility.  Head births the pending permutation, consumed members thread/resync
it, untouched blocks stay `SameRuntimeData`. -/
theorem openRun_chainCanon_congr {program : Program} {residual : Label → List Nat}
    (hUnique : program.LabelsUnique) (hTyped : program.WellTyped)
    (hSpec : ChainResidualSpec program residual)
    {b0 : Block} (hmem : b0 ∈ program.blocks) (hIndep : b0.ProgramCounterIndependent)
    {s_o s_c : EVMState}
    (hStep : ChainStepRel program residual b0.label s_o s_c)
    (hReal_o : StackRealizes b0.input s_o)
    (hReal_c : StackRealizes (ShuffleCanon.applyEdit (editTable program) b0).input s_c) :
    Simulation.Interaction.Rel (ChainOutcomeRel program residual)
      (InteractionSemantics.Block.openRun b0 s_o)
      (InteractionSemantics.Block.openRun (ShuffleCanon.applyEdit (editTable program) b0) s_c) := by
  have hb0Typed : b0.WellTyped program := blockWellTyped_of_mem hTyped.2.1 hmem
  cases hlk : (editTable program).lookup b0.label with
  | none =>
      -- Untouched block: transformed = original, SRD entry, plain runtime congruence.
      have hEb : ShuffleCanon.applyEdit (editTable program) b0 = b0 := by
        unfold ShuffleCanon.applyEdit; rw [hlk]
      rw [hEb] at hReal_c ⊢
      simp only [ChainStepRel, hlk] at hStep
      have hbody := InteractionCongruence.Block.openRunBody_runtimeRel
        hb0Typed.1 hIndep hStep
      unfold InteractionSemantics.Block.openRun Control.Block.run
      refine Simulation.Interaction.Rel.bind_custom hbody ?_
      intro leftDone rightDone hDone
      cases hDone with
      | error he => exact Simulation.Interaction.Rel.done (Or.inr ⟨.error he, by simp⟩)
      | ok hpair =>
          rename_i lpair rpair
          obtain ⟨hAfter, hlp2, hrp2⟩ := hpair
          simp only [hlp2, hrp2, ↓reduceIte]
          exact chainOutcome_srd_resync
            (fun L hL o => ShuffleCanon.untouched_target_not_consumed hmem hlk hL o) hAfter
  | some e =>
      cases e with
      | head body out =>
          -- Head: births PendingPerm (residual B) then jumps to consumed B.
          obtain ⟨B, merged, ds, helig, hb0term, hlkB, hbodyEq, hident, hmergedBd⟩ :=
            hSpec.head hmem hlk
          have hEb : ShuffleCanon.applyEdit (editTable program) b0
              = { b0 with body := body, output := out } := by
            unfold ShuffleCanon.applyEdit; rw [hlk]
          rw [hEb] at hReal_c ⊢
          simp only [ChainStepRel, hlk] at hStep
          have htypeBody : Block.bodyType? body b0.input = some out :=
            (ShuffleCanon.head_edit_spec hUnique hmem hlk).1
          have hbody := headBlock_rel_discharged (program := program) (b0 := b0)
            (body := body) (out := out) (merged := merged) (ds := ds) (rest := residual B.label)
            hb0Typed helig hbodyEq htypeBody hident hmergedBd hStep hReal_o hReal_c
          unfold InteractionSemantics.Block.openRun Control.Block.run
          refine Simulation.Interaction.Rel.bind_custom hbody ?_
          intro leftDone rightDone hDone
          cases hDone with
          | error he => exact Simulation.Interaction.Rel.done (Or.inr ⟨.error he, by simp⟩)
          | ok hpair =>
              rename_i lpair rpair
              obtain ⟨hP, hlp2, hrp2⟩ := hpair
              simp only [hlp2, hrp2, ↓reduceIte, hb0term]
              exact Simulation.Interaction.Rel.done (chainOutcome_jump_pending hlkB hP)
      | consumed out =>
          -- Consumed: peel/resync per the interior/last dichotomy.
          obtain ⟨⟨ds, helig⟩, hdich⟩ := hSpec.consumed hmem hlk
          have hEb : ShuffleCanon.applyEdit (editTable program) b0
              = { b0 with input := out, output := out, body := [] } := by
            unfold ShuffleCanon.applyEdit; rw [hlk]
          rw [hEb] at hReal_c ⊢
          simp only [ChainStepRel, hlk] at hStep
          rcases hdich with ⟨D, hb0term, hlkD, hres⟩ | ⟨houtEq, hres, htargets⟩
          · -- interior: residual b0.label = bodyRunPositions b0.body ++ residual D.label
            rw [hres] at hStep
            have hbody := consumedBlock_rel_discharged (program := program) (b0 := b0)
              (out := out) (ds := ds) (σ := residual D.label)
              hb0Typed helig hStep hReal_o
            unfold InteractionSemantics.Block.openRun Control.Block.run
            refine Simulation.Interaction.Rel.bind_custom hbody ?_
            intro leftDone rightDone hDone
            cases hDone with
            | error he => exact Simulation.Interaction.Rel.done (Or.inr ⟨.error he, by simp⟩)
            | ok hpair =>
                rename_i lpair rpair
                obtain ⟨hP, hlp2, hrp2⟩ := hpair
                simp only [hlp2, hrp2, ↓reduceIte, hb0term]
                exact Simulation.Interaction.Rel.done (chainOutcome_jump_pending hlkD hP)
          · -- last: residual b0.label = bodyRunPositions b0.body, resync to SRD
            rw [hres] at hStep
            have hStep' : PendingPerm (bodyRunPositions b0.body ++ []) s_c s_o := by
              rwa [List.append_nil]
            have hbody := consumedBlock_rel_discharged (program := program) (b0 := b0)
              (out := out) (ds := ds) (σ := []) hb0Typed helig hStep' hReal_o
            unfold InteractionSemantics.Block.openRun Control.Block.run
            refine Simulation.Interaction.Rel.bind_custom hbody ?_
            intro leftDone rightDone hDone
            cases hDone with
            | error he => exact Simulation.Interaction.Rel.done (Or.inr ⟨.error he, by simp⟩)
            | ok hpair =>
                rename_i lpair rpair
                obtain ⟨hP, hlp2, hrp2⟩ := hpair
                have hSRD : SameRuntimeData lpair.1 rpair.1 :=
                  pendingPerm_nil_iff.mp hP
                simp only [hlp2, hrp2, ↓reduceIte]
                rw [houtEq]
                exact chainOutcome_srd_resync htargets hSRD

end Peephole
end TypedCfg
end EvmCompiler
