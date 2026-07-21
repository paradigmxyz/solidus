import EvmCompiler.TypedCfg.ShuffleCanonChainStep

/-!
# Chain-transform residual construction (session-82)

Item 1 (residual construction) of the PEEPHOLE_PROGRESS §Session-81 frontier: define
a concrete `residual : Label → List Nat` and discharge `ChainResidualSpec program
residual`, closing the last hypothesis of the §81 step congruence
`openStep_chainCanon_congr`.

`residual` follows the terminator chain through *consumed* members, accumulating each
member's runtime swap positions (`bodyRunPositions`).  The construction is fuel-bounded
(fuel = `blocks.length`); the correctness reduces, via a for-all-fuel suffix induction,
to the banked chain-consistency (`growChain`/`editTable`/`consumed_edit_spec`/
`head_edit_spec`/`chainEdits_fired`).

Imported by **nobody** in the spine ⟹ cannot affect the `compile_correct` axioms.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState)
open ShuffleCanon (editTable Edit chainCanonProgram chainBodyDepths?)

/-! ## The residual definition (fuel-bounded terminator-follow through consumed members) -/

/-- One-fuel unfolding of the residual: the current block's runtime swap positions,
plus (when its terminator jumps to a *consumed* successor) the successor's residual. -/
def residualAux (program : Program) : Nat → Label → List Nat
  | 0, _ => []
  | fuel + 1, label =>
      match program.findBlock? label with
      | none => []
      | some b0 =>
          bodyRunPositions b0.body ++
            (match b0.term with
             | .jump next =>
                 match (editTable program).lookup next with
                 | some (.consumed _) => residualAux program fuel next
                 | _ => []
             | _ => [])

/-- The concrete per-label residual consumed by `ChainResidualSpec`: a terminator-follow
through consumed members bounded by the block count. -/
def residual (program : Program) (label : Label) : List Nat :=
  residualAux program program.blocks.length label

/-! ## The `merged` ↔ `flatMap bodyRunPositions` bridge -/

/-- A chain-eligible body's runtime positions are its stored depths shifted by one
(the `getD` form). -/
theorem bodyRunPositions_eq_getD {body : List Instr}
    (h : (chainBodyDepths? body).isSome) :
    bodyRunPositions body = ((chainBodyDepths? body).getD []).map (· + 1) := by
  cases hd : chainBodyDepths? body with
  | none => rw [hd] at h; simp at h
  | some ds =>
      rw [bodyRunPositions_eq_of_chainBodyDepths hd]; simp [hd]

/-- **The merged bridge.**  For a chain of eligible blocks, the concatenated depths
shifted by one equal the concatenated runtime positions:
`(chain.flatMap depths).map (·+1) = chain.flatMap bodyRunPositions`. -/
theorem merged_map_succ_eq_flatMap (chain : List Block)
    (helig : ∀ b ∈ chain, (chainBodyDepths? b.body).isSome) :
    (chain.flatMap (fun b => (chainBodyDepths? b.body).getD [])).map (· + 1)
      = chain.flatMap (fun b => bodyRunPositions b.body) := by
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro b hb
  exact (bodyRunPositions_eq_getD (helig b hb)).symm

/-! ## The residual run predicate + the for-all-fuel suffix induction -/

/-- A *residual run* is a list of consumed chain members threaded by the terminator
follow: each non-last member jumps to the next (a consumed successor), and the last
member's terminator does not jump to any consumed block.  This is exactly the shape the
fuel-bounded `residualAux` walks. -/
def IsResidualRun (program : Program) : List Block → Prop
  | [] => True
  | [Z] =>
      program.findBlock? Z.label = some Z ∧
      ∀ W o, Z.term = Terminator.jump W →
        (editTable program).lookup W ≠ some (Edit.consumed o)
  | C :: D :: rest =>
      program.findBlock? C.label = some C ∧
      C.term = Terminator.jump D.label ∧
      (∃ o, (editTable program).lookup D.label = some (Edit.consumed o)) ∧
      IsResidualRun program (D :: rest)

/-- **The residual walk realises the run's concatenated positions.**  On a residual run
`C :: cs` with fuel at least its length, `residualAux` returns exactly the concatenated
`bodyRunPositions` of the run's members. -/
theorem residualAux_of_run {program : Program} :
    ∀ (cs : List Block) (C : Block) (fuel : Nat),
      IsResidualRun program (C :: cs) →
      (C :: cs).length ≤ fuel →
      residualAux program fuel C.label = (C :: cs).flatMap (fun b => bodyRunPositions b.body)
  | [], C, fuel, hrun, hlen => by
      obtain ⟨hfind, hlast⟩ := hrun
      cases fuel with
      | zero => simp at hlen
      | succ f =>
          simp only [residualAux, hfind, List.flatMap_cons, List.flatMap_nil, List.append_nil]
          have hbranch :
              (match C.term with
               | .jump next =>
                   match (editTable program).lookup next with
                   | some (.consumed _) => residualAux program f next
                   | _ => []
               | _ => []) = ([] : List Nat) := by
            cases hterm : C.term with
            | jump W =>
                cases hlk : (editTable program).lookup W with
                | none => simp only [hlk]
                | some e =>
                    cases e with
                    | head _ _ => simp only [hlk]
                    | consumed o => exact absurd hlk (hlast W o hterm)
            | fallthrough _ => rfl
            | jumpi _ _ => rfl
            | returnDispatch _ _ => rfl
            | halt _ => rfl
            | invalid => rfl
          rw [hbranch, List.append_nil]
  | D :: rest, C, fuel, hrun, hlen => by
      obtain ⟨hfind, hterm, ⟨o, hlkD⟩, hrun'⟩ := hrun
      cases fuel with
      | zero => simp at hlen
      | succ f =>
          have hlen' : (D :: rest).length ≤ f := by
            simp only [List.length_cons] at hlen ⊢; omega
          have hIH := residualAux_of_run rest D f hrun' hlen'
          simp only [residualAux, hfind, hterm, hlkD, hIH]
          simp only [List.flatMap_cons]

/-! ## Consumed members are chain-eligible -/

/-- A `chainStep`-linked successor is chain-eligible. -/
theorem chainStep_chainBodyOk_nxt {prog : Program} {a nxt : Block}
    (h : ShuffleCanon.chainStep prog a nxt = true) :
    (chainBodyDepths? nxt.body).isSome := by
  unfold ShuffleCanon.chainStep ShuffleCanon.chainBodyOk at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

/-- **Consumed members are chain-eligible** (the first conjunct of
`ChainResidualSpec.consumed`): a consumed block's body is `.swap`/`.bindLocals` only,
so `chainBodyDepths?` succeeds.  A consumed member is a non-head chain member, hence has
a `chainStep`-predecessor whose step guard forces `chainBodyOk` of the member. -/
theorem consumed_chainBodyOk {program : Program} (hUnique : program.LabelsUnique)
    {b0 : Block} {out : Shape}
    (hb0mem : b0 ∈ program.blocks)
    (hlk : (editTable program).lookup b0.label = some (Edit.consumed out)) :
    ∃ ds, chainBodyDepths? b0.body = some ds := by
  have hmemtbl := ShuffleCanon.lookup_mem hlk
  unfold editTable at hmemtbl
  split at hmemtbl
  · simp only [List.not_mem_nil] at hmemtbl
  · rename_i ordered hord
    obtain ⟨b, rest, hsuf, _hlen, hmem, _hsub⟩ := ShuffleCanon.scanEdits_mem hmemtbl
    obtain ⟨hd, tl, hchain, _hbody, hcases⟩ := ShuffleCanon.chainEdits_fired hmem
    have hCcase : ∃ C ∈ tl, (b0.label, Edit.consumed out) =
        (C.label, Edit.consumed ((ShuffleCanon.growChain program b rest).getLastD hd).output) := by
      rcases hcases with heq | hc
      · rw [Prod.mk.injEq] at heq; exact absurd heq.2 (by simp)
      · exact hc
    obtain ⟨C, hCtl, hCeq⟩ := hCcase
    have hb0label : b0.label = C.label := by rw [Prod.mk.injEq] at hCeq; exact hCeq.1
    have hCblocks : C ∈ program.blocks :=
      ShuffleCanon.growChain_mem_blocks hord hsuf (hchain ▸ List.mem_cons_of_mem hd hCtl)
    have hb0C : b0 = C := by
      have h1 : program.findBlock? b0.label = some b0 :=
        Program.findBlock?_eq_some_of_mem hUnique hb0mem
      rw [hb0label, Program.findBlock?_eq_some_of_mem hUnique hCblocks] at h1
      exact ((Option.some.injEq _ _).mp h1).symm
    -- C has a chainStep-predecessor, so C is chain-eligible.
    have hgc := ShuffleCanon.growChain_chain' program b rest
    rw [hchain] at hgc
    obtain ⟨P, _, hstep⟩ := ShuffleCanon.chainStep_pred_of_mem_tail hgc hCtl
    have hOk : (chainBodyDepths? C.body).isSome := chainStep_chainBodyOk_nxt hstep
    rw [hb0C]
    cases hd' : chainBodyDepths? C.body with
    | none => rw [hd'] at hOk; simp at hOk
    | some ds => exact ⟨ds, rfl⟩

/-! ## Generic list order lemmas -/

theorem mem_gives_suffix {α : Type*} {a : α} : ∀ {L : List α}, a ∈ L → ∃ s, a :: s <:+ L
  | x :: xs, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨xs, List.suffix_refl _⟩
      · obtain ⟨s, hs⟩ := mem_gives_suffix h
        exact ⟨s, hs.trans (List.suffix_cons x xs)⟩

theorem suffix_head_unique {α : Type*} {L : List α} (hnd : L.Nodup)
    {a : α} {s1 s2 : List α} (h1 : a :: s1 <:+ L) (h2 : a :: s2 <:+ L) : s1 = s2 := by
  rcases List.suffix_or_suffix_of_suffix h1 h2 with h | h
  · obtain ⟨p, hp⟩ := h
    cases p with
    | nil => simpa using hp
    | cons x p' =>
        rw [List.cons_append, List.cons.injEq] at hp
        exfalso
        have hnd2 : (a :: s2).Nodup := h2.sublist.nodup hnd
        rw [List.nodup_cons] at hnd2
        apply hnd2.1
        rw [← hp.2]
        exact List.mem_append_right _ List.mem_cons_self
  · obtain ⟨p, hp⟩ := h
    cases p with
    | nil => simpa using hp.symm
    | cons x p' =>
        rw [List.cons_append, List.cons.injEq] at hp
        exfalso
        have hnd1 : (a :: s1).Nodup := h1.sublist.nodup hnd
        rw [List.nodup_cons] at hnd1
        apply hnd1.1
        rw [← hp.2]
        exact List.mem_append_right _ List.mem_cons_self

/-! ## growChain stopping lemma -/

theorem growChain_stop (prog : Program) (Z W : Block) :
    ∀ (b : Block) (bs suf : List Block),
      (ShuffleCanon.growChain prog b bs).getLast? = some Z →
      b :: bs = ShuffleCanon.growChain prog b bs ++ (W :: suf) →
      ShuffleCanon.chainStep prog Z W = false := by
  intro b bs
  induction bs generalizing b with
  | nil =>
      intro suf hlast heq
      simp only [ShuffleCanon.growChain, List.singleton_append, List.cons.injEq] at heq
      exact absurd heq.2.symm (by simp)
  | cons nxt rest ih =>
      intro suf hlast heq
      by_cases h : ShuffleCanon.chainStep prog b nxt = true
      · rw [ShuffleCanon.growChain, if_pos h] at hlast heq
        obtain ⟨t, ht⟩ := ShuffleCanon.growChain_head prog nxt rest
        rw [ht] at hlast heq
        rw [List.cons_append, List.cons.injEq] at heq
        have hlast' : (ShuffleCanon.growChain prog nxt rest).getLast? = some Z := by
          rw [ht]; simpa using hlast
        exact ih nxt suf hlast' (by rw [ht]; exact heq.2)
      · rw [ShuffleCanon.growChain, if_neg h] at hlast heq
        rw [List.getLast?_singleton, Option.some.injEq] at hlast
        subst hlast
        rw [List.singleton_append, List.cons.injEq, List.cons.injEq] at heq
        rw [← heq.2.1]
        rw [Bool.not_eq_true] at h; exact h

/-! ## Adjacency in a chain -/

theorem chainStep_adjacent_split {prog : Program} {hd : Block} {tl : List Block} {C : Block}
    (hc : List.IsChain (fun x y => ShuffleCanon.chainStep prog x y = true) (hd :: tl))
    (hC : C ∈ tl) :
    ∃ P pre post, (hd :: tl) = pre ++ P :: C :: post ∧ ShuffleCanon.chainStep prog P C = true := by
  obtain ⟨k, hk, hCeq⟩ := List.getElem_of_mem hC
  set L := hd :: tl with hL
  have hk1 : k + 1 < L.length := by simp only [hL, List.length_cons]; omega
  have hrel := hc.getElem k hk1
  rw [List.getElem_cons_succ, hCeq] at hrel
  have hk0 : k < L.length := by omega
  have hd1 : L.drop k = L[k] :: L.drop (k + 1) := (List.drop_eq_getElem_cons hk0).symm ▸ rfl
  have hd2 : L.drop (k + 1) = L[k+1] :: L.drop (k + 2) := (List.drop_eq_getElem_cons hk1).symm ▸ rfl
  rw [List.getElem_cons_succ, hCeq] at hd2
  refine ⟨L[k], L.take k, L.drop (k + 2), ?_, hrel⟩
  conv_lhs => rw [← List.take_append_drop k L]
  rw [hd1, hd2]

/-! ## getLast? decomposition -/

theorem getLast?_append_singleton {α : Type*} {l : List α} {z : α}
    (h : l.getLast? = some z) : ∃ pre, l = pre ++ [z] := by
  exact List.getLast?_eq_some_iff.mp h

/-! ## Consumed-chain witness -/

theorem consumed_chain_witness {program : Program}
    {ordered : List Block} (hord : program.blocksInLoweringOrder? = some ordered)
    {L : Label} {o : Shape}
    (h : (editTable program).lookup L = some (Edit.consumed o)) :
    ∃ bW restW hdW tlW Cw,
      (bW :: restW) <:+ ordered ∧
      ShuffleCanon.growChain program bW restW = hdW :: tlW ∧
      Cw ∈ tlW ∧ Cw.label = L := by
  have hmem := ShuffleCanon.lookup_mem h
  unfold editTable at hmem
  rw [hord] at hmem
  obtain ⟨b, rest, hsuf, _hlen, hcmem, _hsub⟩ := ShuffleCanon.scanEdits_mem hmem
  obtain ⟨hd, tl, hchain, _hbody, hcases⟩ := ShuffleCanon.chainEdits_fired hcmem
  rcases hcases with heq | ⟨C, hCtl, hCeq⟩
  · rw [Prod.mk.injEq] at heq; exact absurd heq.2 (by simp)
  · exact ⟨b, rest, hd, tl, C, hsuf, hchain, hCtl,
      by rw [Prod.mk.injEq] at hCeq; exact hCeq.1.symm⟩

/-! ## THE LINCHPIN: the last chain member does not jump to a consumed block -/

theorem last_member_no_consumed_target {program : Program}
    (hUnique : program.LabelsUnique)
    {ordered : List Block} (hord : program.blocksInLoweringOrder? = some ordered)
    {b0 : Block} {rest0 : List Block} (hsuf0 : (b0 :: rest0) <:+ ordered)
    {Z : Block} (hZlast : (ShuffleCanon.growChain program b0 rest0).getLast? = some Z) :
    ∀ (W : Label) (o : Shape), Z.term = Terminator.jump W →
      (editTable program).lookup W ≠ some (Edit.consumed o) := by
  intro W o hZterm hlk
  -- `ordered` is Nodup.
  have hnd_ord : ordered.Nodup := by
    have hperm := Program.blocksInLoweringOrder?_perm hord
    have hnd_blocks : program.blocks.Nodup := by
      have hp : program.blocks.Pairwise (fun l r => l.label ≠ r.label) := hUnique
      exact hp.imp (fun hab h => hab (by rw [h]))
    exact hperm.nodup_iff.mp hnd_blocks
  -- Z is a program block.
  obtain ⟨pre_our, hpre_our⟩ := getLast?_append_singleton hZlast
  have hZmem_chain : Z ∈ ShuffleCanon.growChain program b0 rest0 := by
    rw [hpre_our]; exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have hZblocks : Z ∈ program.blocks :=
    ShuffleCanon.growChain_mem_blocks hord hsuf0 hZmem_chain
  -- W's chain and the consumed member Cw with label W.
  obtain ⟨bW, restW, hdW, tlW, Cw, hsufW, hchainW, hCwtl, hCwlabel⟩ :=
    consumed_chain_witness hord hlk
  have hcW : List.IsChain (fun x y => ShuffleCanon.chainStep program x y = true)
      (hdW :: tlW) := by
    have hgc := ShuffleCanon.growChain_chain' program bW restW
    rw [hchainW] at hgc; exact hgc
  obtain ⟨P, preW, postW, hsplit, hPC⟩ := chainStep_adjacent_split hcW hCwtl
  -- P jumps to Cw.label = W.
  obtain ⟨hPterm, _href, _⟩ := ShuffleCanon.chainStep_spec hPC
  rw [hCwlabel] at hPterm
  -- refCount W = 1 forces P = Z.
  obtain ⟨_Pd, _hPdmem, _hPdterm, hrefW, _⟩ :=
    ShuffleCanon.consumed_predecessor (ShuffleCanon.lookup_mem hlk)
  have hPblocks : P ∈ program.blocks := by
    have hPmem_chain : P ∈ hdW :: tlW := by
      rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_self ..)
    rw [← hchainW] at hPmem_chain
    exact ShuffleCanon.growChain_mem_blocks hord hsufW hPmem_chain
  have hWP : W ∈ P.term.targets := by rw [hPterm]; simp [Terminator.targets]
  have hWZ : W ∈ Z.term.targets := by rw [hZterm]; simp [Terminator.targets]
  have hPZ : Z = P := by
    by_contra hne
    have h2 := Peephole.two_le_refCount hPblocks hWP hZblocks hWZ (fun h => hne h.symm)
    rw [hrefW] at h2; omega
  subst hPZ
  -- Ordered adjacency: Z immediately precedes Cw in `ordered`.
  obtain ⟨gd, hgd⟩ := ShuffleCanon.growChain_prefix program bW restW
  have hsufBW : (Z :: Cw :: (postW ++ gd)) <:+ (bW :: restW) := by
    refine ⟨preW, ?_⟩
    rw [← hgd, hchainW, hsplit]; simp [List.append_assoc]
  have hadj_ord : (Z :: Cw :: (postW ++ gd)) <:+ ordered := hsufBW.trans hsufW
  -- Our chain's suffix headed by Z.
  have hZgtail : ∃ gtail, (b0 :: rest0) = ShuffleCanon.growChain program b0 rest0 ++ gtail
      ∧ (Z :: gtail) <:+ (b0 :: rest0) := by
    obtain ⟨gd0, hgd0⟩ := ShuffleCanon.growChain_prefix program b0 rest0
    refine ⟨gd0, hgd0.symm, ?_⟩
    refine ⟨pre_our, ?_⟩
    rw [← hgd0, hpre_our]; simp
  obtain ⟨gtail, hb0eq, hZsuf⟩ := hZgtail
  have hZsuf_ord : (Z :: gtail) <:+ ordered := hZsuf.trans hsuf0
  -- Uniqueness of the suffix headed by Z pins gtail = Cw :: (postW ++ gd).
  have hgtail : gtail = Cw :: (postW ++ gd) :=
    suffix_head_unique hnd_ord hZsuf_ord hadj_ord
  -- growChain stopped at Z, but chainStep Z Cw = true — contradiction.
  have hstop := growChain_stop program Z Cw b0 rest0 (postW ++ gd) hZlast
    (by rw [hb0eq, hgtail])
  rw [hstop] at hPC
  exact absurd hPC (by simp)


end Peephole
end TypedCfg
end EvmCompiler
