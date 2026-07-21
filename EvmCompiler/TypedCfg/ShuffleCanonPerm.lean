import EvmCompiler.TypedCfg.ShuffleCanonType

/-!
# Shuffle-window canonicalisation — (P1) selection-sort realisability
(session-76, Route 2 second milestone)

`ShuffleCanonType.lean` (§75) reduced single-block type-preservation of
`canonSwaps` to two pure `List Nat` permutation facts.  (P2) naturality is
already green there.  This module discharges **(P1)**, the flagged hard
combinatorial fact:

> `netStack (starDecompose t) t.length = t` — the selection-sort round-trip.

**Corrected statement.**  As literally written for *arbitrary* `t` this is FALSE
(e.g. `t = [0,0]`: `netStack (starDecompose [0,0]) 2 = [1,0] ≠ [0,0]`).  It holds
exactly when `t` is a **permutation of `List.range t.length`** — which is always
the case at the one call site, where `starDecompose` is applied to
`netStack ps m` (a permutation of `range m` by construction).  So the banked
lemma is `netStack_starDecompose_of_perm`, plus the fact that every `netStack ps
m` satisfies its hypothesis (`netStack_perm_range`).

**Proof architecture** (avoids reasoning about `starDecompose` directly):
`starDecompose t = (sortToId t).reverse`, and `applySwap` is an **involution**,
so `applySwaps (sortToId t).reverse` is the inverse of `applySwaps (sortToId t)`.
Hence `netStack (starDecompose t) n = applySwaps (sortToId t).reverse (range n)`,
and if the selection sort is **correct** — `applySwaps (sortToId t) t = range n`
— the inverse maps `range n` back to `t`.  So (P1) reduces to:

* `applySwap_involutive` / `applySwaps_reverse_cancel` — the inverse structure;
* `sortToId_correct` — selection-sort correctness for permutations (the genuine
  combinatorial core, a downward foldr invariant "processed suffix in place").

This leaf is imported by nobody in the certified spine, so it cannot affect the
`compile_correct` axioms.
-/

namespace EvmCompiler
namespace TypedCfg
namespace ShuffleCanon

open EvmCompiler.TypedCfg

/-! ## `applySwap` getElem? characterisation + involution -/

/-- The index acted on by `applySwap k` at output position `j`: it transposes
positions `0` and `k`, fixing all others. -/
def swapIdx (k j : Nat) : Nat :=
  if j = 0 then k else if j = k then 0 else j

theorem swapIdx_involutive (k j : Nat) : swapIdx k (swapIdx k j) = j := by
  unfold swapIdx
  by_cases hk0 : k = 0
  · subst hk0; by_cases hj : j = 0 <;> simp [hj]
  · by_cases hj0 : j = 0
    · subst hj0; simp [hk0]
    · by_cases hjk : j = k
      · subst hjk; simp [hk0, hj0]
      · simp [hj0, hjk]

/-- `applySwap k xs` reads position `j` from the transposed index `swapIdx k j`
of `xs` when both endpoints are in range, and is the identity otherwise. -/
theorem getElem?_applySwap {α : Type _} (k j : Nat) (xs : List α) :
    (applySwap k xs)[j]? =
      if xs[0]?.isSome = true ∧ xs[k]?.isSome = true then xs[swapIdx k j]?
      else xs[j]? := by
  unfold applySwap
  cases h0 : xs[0]? with
  | none => simp [h0]
  | some a =>
      cases hk : xs[k]? with
      | none => simp [h0, hk]
      | some b =>
          have hx0 : 0 < xs.length := by
            rcases List.getElem?_eq_some_iff.1 h0 with ⟨h, _⟩; exact h
          have hxk : k < xs.length := by
            rcases List.getElem?_eq_some_iff.1 hk with ⟨h, _⟩; exact h
          rw [if_pos (by constructor <;> simp [h0, hk])]
          -- ((xs.set 0 b).set k a)[j]? = xs[swapIdx k j]?
          rw [List.getElem?_set, List.getElem?_set]
          simp only [List.length_set, hx0, hxk, if_true]
          by_cases hj0 : j = 0 <;> by_cases hjk : j = k <;>
            simp_all [swapIdx, h0, hk, eq_comm]

/-- Length is preserved (restate for this file's convenience). -/
theorem length_applySwap' {α : Type _} (k : Nat) (xs : List α) :
    (applySwap k xs).length = xs.length := length_applySwap k xs

/-- **`applySwap` is an involution.** -/
theorem applySwap_involutive {α : Type _} (k : Nat) (xs : List α) :
    applySwap k (applySwap k xs) = xs := by
  by_cases hcond : xs[0]?.isSome = true ∧ xs[k]?.isSome = true
  · -- active: characterise both layers via `getElem?_applySwap`
    apply List.ext_getElem?
    intro j
    have h0s : (applySwap k xs)[0]?.isSome = true := by
      rw [getElem?_applySwap, if_pos hcond]; simpa [swapIdx] using hcond.2
    have hks : (applySwap k xs)[k]?.isSome = true := by
      rw [getElem?_applySwap, if_pos hcond]
      by_cases hk0 : k = 0
      · subst hk0; simpa [swapIdx] using hcond.2
      · simp only [swapIdx, if_neg hk0, if_pos rfl]; simpa using hcond.1
    rw [getElem?_applySwap, if_pos ⟨h0s, hks⟩, getElem?_applySwap, if_pos hcond,
        swapIdx_involutive]
  · -- inactive: applySwap k xs = xs, so applying twice is xs
    have hxx : applySwap k xs = xs := by
      unfold applySwap
      rcases h0 : xs[0]? with _ | a
      · rfl
      · rcases hk : xs[k]? with _ | b
        · rfl
        · exact absurd ⟨by rw [h0]; rfl, by rw [hk]; rfl⟩ hcond
    rw [hxx, hxx]

/-- **Reverse cancels.**  `applySwaps` of the reversed list undoes `applySwaps`. -/
theorem applySwaps_reverse_cancel {α : Type _} (ps : List Nat) (xs : List α) :
    applySwaps ps.reverse (applySwaps ps xs) = xs := by
  induction ps generalizing xs with
  | nil => simp
  | cons p ps ih =>
      rw [List.reverse_cons, applySwaps_append, applySwaps_cons, applySwaps_cons,
          applySwaps_nil, ih (applySwap p xs), applySwap_involutive]

/-! ## `applySwap` preserves the multiset (permutation) -/

/-- `applySwap 0` is the identity (it would swap position `0` with itself). -/
theorem applySwap_zero {α : Type _} (xs : List α) : applySwap 0 xs = xs := by
  apply List.ext_getElem?
  intro j
  rw [getElem?_applySwap]
  have hs : swapIdx 0 j = j := by unfold swapIdx; by_cases hj : j = 0 <;> simp [hj]
  rw [hs]; split <;> rfl

/-- Active-window read: when both `0` and `k` are in range, `applySwap k` reindexes
by `swapIdx k`. -/
theorem applySwap_getElem?_active {α : Type _} (k j : Nat) (xs : List α)
    (h0 : 0 < xs.length) (hk : k < xs.length) :
    (applySwap k xs)[j]? = xs[swapIdx k j]? := by
  have c0 : xs[0]?.isSome = true := by rw [List.getElem?_eq_getElem h0]; rfl
  have ck : xs[k]?.isSome = true := by rw [List.getElem?_eq_getElem hk]; rfl
  rw [getElem?_applySwap, if_pos ⟨c0, ck⟩]

/-- **`applySwap` preserves the underlying multiset.** -/
theorem applySwap_perm (k : Nat) (xs : List Nat) : List.Perm (applySwap k xs) xs := by
  by_cases hk0 : k = 0
  · subst hk0; rw [applySwap_zero]
  · unfold applySwap
    cases h0 : xs[0]? with
    | none => exact List.Perm.refl _
    | some a =>
        cases hk : xs[k]? with
        | none => exact List.Perm.refl _
        | some b =>
            have hx0 : 0 < xs.length := by
              rcases List.getElem?_eq_some_iff.1 h0 with ⟨h, _⟩; exact h
            have hxk : k < xs.length := by
              rcases List.getElem?_eq_some_iff.1 hk with ⟨h, _⟩; exact h
            have ha : xs[0] = a := by
              rcases List.getElem?_eq_some_iff.1 h0 with ⟨_, h⟩; exact h
            have hb : xs[k] = b := by
              rcases List.getElem?_eq_some_iff.1 hk with ⟨_, h⟩; exact h
            rw [List.perm_iff_count]
            intro z
            have hlen1 : k < (xs.set 0 b).length := by rw [List.length_set]; exact hxk
            rw [List.count_set hlen1, List.count_set hx0,
                List.getElem_set_ne (Ne.symm hk0) hlen1]
            simp only [hb, ha]
            have hPC : (if a == z then 1 else 0) ≤ List.count z xs := by
              by_cases h : (a == z) = true
              · simp only [h, if_true]
                have hz : z = a := by rw [beq_iff_eq] at h; exact h.symm
                rw [hz]
                exact (List.count_pos_iff).2 (ha ▸ List.getElem_mem hx0)
              · simp only [Bool.not_eq_true] at h; simp [h]
            omega

/-! ## getElem! bridging + findIdx facts (all on `List Nat`) -/

theorem getElem!_of_getElem? {l : List Nat} {j v : Nat} (h : l[j]? = some v) :
    l[j]! = v := by
  rw [List.getElem!_eq_getElem?_getD, h]; rfl

theorem findIdx_beq_lt {k : Nat} {b : List Nat} (hmem : k ∈ b) :
    b.findIdx (· == k) < b.length :=
  List.findIdx_lt_length_of_exists ⟨k, hmem, by simp⟩

theorem findIdx_beq_getElem {k : Nat} {b : List Nat}
    (h : b.findIdx (· == k) < b.length) :
    b[b.findIdx (· == k)] = k := by
  have := @List.findIdx_getElem _ (· == k) b h
  simpa using this

theorem getElem?_of_getElem! {l : List Nat} {j v : Nat}
    (hj : j < l.length) (h : l[j]! = v) : l[j]? = some v := by
  have hg : l[j] = v := by rw [getElem!_pos l j hj] at h; exact h
  rw [List.getElem?_eq_getElem hj, hg]

/-! ## Positional reads of `applySwap` runs (used by the sort suffix invariant) -/

/-- Reading position `k` after `applySwap k`: it comes from position `0`
(`swapIdx k k = 0` unconditionally). -/
theorem applySwap_getElem?_self {α : Type _} (k : Nat) (b : List α)
    (h0 : 0 < b.length) (hk : k < b.length) :
    (applySwap k b)[k]? = b[0]? := by
  rw [applySwap_getElem?_active k k b h0 hk]
  have : swapIdx k k = 0 := by unfold swapIdx; by_cases hk0 : k = 0 <;> simp [hk0]
  rw [this]

/-- Reading position `0` after `applySwap k`: it comes from position `k`. -/
theorem applySwap_getElem?_zero_read {α : Type _} (k : Nat) (b : List α)
    (h0 : 0 < b.length) (hk : k < b.length) :
    (applySwap k b)[0]? = b[k]? := by
  rw [applySwap_getElem?_active k 0 b h0 hk]
  have : swapIdx k 0 = k := by unfold swapIdx; simp
  rw [this]

/-- Positions strictly above every touched index are fixed by `applySwap`. -/
theorem applySwap_getElem?_high {α : Type _} (k' j : Nat) (b : List α)
    (hj : 0 < j) (hjk : j ≠ k') : (applySwap k' b)[j]? = b[j]? := by
  rw [getElem?_applySwap]
  have hs : swapIdx k' j = j := by
    unfold swapIdx
    have hj0 : j ≠ 0 := by omega
    simp [hj0, hjk]
  rw [hs]; split <;> rfl

/-- A whole run of transpositions, all below a positive index `j`, fixes `j`. -/
theorem applySwaps_getElem?_high {α : Type _} (sw : List Nat) (b : List α) (j : Nat)
    (hj : 0 < j) (hall : ∀ q ∈ sw, q < j) : (applySwaps sw b)[j]? = b[j]? := by
  induction sw generalizing b with
  | nil => rfl
  | cons k' sw ih =>
      rw [applySwaps_cons]
      rw [ih (applySwap k' b) (fun q hq => hall q (by simp [hq]))]
      exact applySwap_getElem?_high k' j b hj (by
        have := hall k' (by simp); omega)

/-! ## The selection-sort foldr invariant -/

/-- `sortStep` in closed form: applying the swap list to the working array and
appending it to the accumulator (`rfl`, since `applySwaps` unfolds to the same
`foldl`). -/
theorem sortStep_eq (b acc : List Nat) (i : Nat) :
    sortStep (b, acc) i =
      (applySwaps (if b.findIdx (· == i) == i then []
                   else if b.findIdx (· == i) == 0 then [i]
                   else [b.findIdx (· == i), i]) b,
       acc ++ (if b.findIdx (· == i) == i then []
               else if b.findIdx (· == i) == 0 then [i]
               else [b.findIdx (· == i), i])) := rfl

/-- **Selection-sort partial correctness (the combinatorial core).**  Folding
`sortStep` over the contiguous value list `range' k m` (with `k + m = n`) leaves a
length-`n` permutation of `range n` whose positions `k .. n-1` already hold their
identity value, and the working array is `applySwaps` of the accumulated swaps. -/
theorem sortFoldr_inv (b0 : List Nat) (n : Nat)
    (hlen0 : b0.length = n) (hperm0 : List.Perm b0 (List.range n)) :
    ∀ (m k : Nat), 1 ≤ k → k + m = n →
      (List.foldr (fun i st => sortStep st i) (b0, []) (List.range' k m)).1.length = n ∧
      List.Perm (List.foldr (fun i st => sortStep st i) (b0, []) (List.range' k m)).1
          (List.range n) ∧
      (List.foldr (fun i st => sortStep st i) (b0, []) (List.range' k m)).1
        = applySwaps (List.foldr (fun i st => sortStep st i) (b0, []) (List.range' k m)).2 b0 ∧
      (∀ j, k ≤ j → j < n →
        (List.foldr (fun i st => sortStep st i) (b0, []) (List.range' k m)).1[j]! = j) ∧
      (∀ e ∈ (List.foldr (fun i st => sortStep st i) (b0, []) (List.range' k m)).2,
        1 ≤ e ∧ e < n) := by
  intro m
  induction m with
  | zero =>
      intro k hk hkm
      simp only [List.range'_zero, List.foldr_nil]
      refine ⟨hlen0, hperm0, by simp [applySwaps], ?_, ?_⟩
      · intro j hj1 hj2; omega
      · intro e he; exact absurd he (by simp)
  | succ m ih =>
      intro k hk hkm
      have IH := ih (k + 1) (by omega) (by omega)
      rw [List.range'_succ, List.foldr_cons]
      generalize hID :
          List.foldr (fun i st => sortStep st i) (b0, []) (List.range' (k + 1) m) = inner
          at IH ⊢
      obtain ⟨b, acc⟩ := inner
      obtain ⟨hIlen, hIperm, hIacc, hIsuf, hIbnd⟩ := IH
      dsimp only at hIlen hIperm hIacc hIsuf ⊢
      -- basic facts
      have hkn : k < n := by omega
      have hn0 : 0 < b.length := by rw [hIlen]; omega
      have hkb : k < b.length := by rw [hIlen]; exact hkn
      have hbmem : k ∈ b := (hIperm.mem_iff).2 (List.mem_range.2 hkn)
      have hplt : b.findIdx (· == k) < b.length := findIdx_beq_lt hbmem
      have hpn : b.findIdx (· == k) < n := by rw [hIlen] at hplt; exact hplt
      have hbp : b[b.findIdx (· == k)] = k := findIdx_beq_getElem hplt
      have hbp! : b[b.findIdx (· == k)]! = k :=
        getElem!_of_getElem? (by rw [List.getElem?_eq_getElem hplt, hbp])
      have hple : b.findIdx (· == k) ≤ k := by
        by_contra hlt; push_neg at hlt
        have := hIsuf (b.findIdx (· == k)) (by omega) hpn
        rw [hbp!] at this; omega
      set p := b.findIdx (· == k) with hpdef
      have hbpp : b[p] = k := hbp
      rw [sortStep_eq]
      dsimp only
      simp only [← hpdef]
      -- the suffix claim for j > k is common to all branches (positions used ≤ k < j)
      by_cases hpk : p = k
      · -- sw = []
        simp only [hpk, beq_self_eq_true, if_true, applySwaps_nil, List.append_nil]
        refine ⟨hIlen, hIperm, hIacc, ?_, hIbnd⟩
        intro j hj1 hj2
        rcases Nat.eq_or_lt_of_le hj1 with hjk | hjk
        · rw [← hjk]; exact hpk ▸ hbp!
        · exact hIsuf j (by omega) hj2
      · have hpk' : (p == k) = false := by simp [hpk]
        by_cases hp0 : p = 0
        · -- sw = [k]
          have hp0' : (p == 0) = true := by simp [hp0]
          simp only [hpk', Bool.false_eq_true, if_false, hp0', if_true]
          -- st.1 = applySwaps [k] b = applySwap k b
          have hrun : applySwaps [k] b = applySwap k b := by
            rw [applySwaps_cons, applySwaps_nil]
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · rw [length_applySwaps, hIlen]
          · rw [hrun]; exact (applySwap_perm k b).trans hIperm
          · rw [applySwaps_append, ← hIacc]
          · intro j hj1 hj2
            rw [hrun]
            rcases Nat.eq_or_lt_of_le hj1 with hjk | hjk
            · -- j = k
              rw [← hjk]
              apply getElem!_of_getElem?
              rw [applySwap_getElem?_self k b hn0 hkb, List.getElem?_eq_getElem hn0]
              have hb0 : b[0] = k := by
                have h0 : b[0]! = k := by rw [← hp0]; exact hbp!
                rwa [getElem!_pos b 0 hn0] at h0
              rw [hb0]
            · -- j > k
              apply getElem!_of_getElem?
              rw [applySwap_getElem?_high k j b (by omega) (by omega)]
              exact getElem?_of_getElem! (by rw [hIlen]; exact hj2) (hIsuf j (by omega) hj2)
          · intro e he
            rw [List.mem_append] at he
            rcases he with he | he
            · exact hIbnd e he
            · simp only [List.mem_singleton] at he; subst he; exact ⟨hk, hkn⟩
        · -- sw = [p, k]
          have hp0' : (p == 0) = false := by simp [hp0]
          simp only [hpk', Bool.false_eq_true, if_false, hp0']
          set b1 := applySwap p b with hb1
          have hb1len : 0 < b1.length := by rw [hb1, length_applySwap]; exact hn0
          have hb1k : k < b1.length := by rw [hb1, length_applySwap]; exact hkb
          have hrun : applySwaps [p, k] b = applySwap k b1 := by
            rw [applySwaps_cons, applySwaps_cons, applySwaps_nil, hb1]
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · rw [length_applySwaps, hIlen]
          · rw [hrun]
            exact (applySwap_perm k b1).trans ((applySwap_perm p b).trans hIperm)
          · rw [applySwaps_append, ← hIacc]
          · intro j hj1 hj2
            rw [hrun]
            rcases Nat.eq_or_lt_of_le hj1 with hjk | hjk
            · -- j = k
              rw [← hjk]
              apply getElem!_of_getElem?
              rw [applySwap_getElem?_self k b1 hb1len hb1k, hb1]
              rw [applySwap_getElem?_zero_read p b hn0 hplt]
              rw [List.getElem?_eq_getElem hplt, hbpp]
            · -- j > k
              apply getElem!_of_getElem?
              rw [applySwap_getElem?_high k j b1 (by omega) (by omega), hb1,
                  applySwap_getElem?_high p j b (by omega) (by omega)]
              exact getElem?_of_getElem! (by rw [hIlen]; exact hj2) (hIsuf j (by omega) hj2)
          · intro e he
            rw [List.mem_append] at he
            rcases he with he | he
            · exact hIbnd e he
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
              rcases he with he | he <;> subst he
              · exact ⟨by omega, hpn⟩
              · exact ⟨hk, hkn⟩

/-! ## Selection-sort round-trip and (P1) -/

/-- `applySwaps` preserves the multiset for any input. -/
theorem applySwaps_perm (ps xs : List Nat) : List.Perm (applySwaps ps xs) xs := by
  induction ps generalizing xs with
  | nil => exact List.Perm.refl _
  | cons k ps ih =>
      rw [applySwaps_cons]
      exact (ih (applySwap k xs)).trans (applySwap_perm k xs)

/-- **Selection-sort correctness.**  For a permutation of `range n`, the
accumulated `sortToId` swaps sort it back to the identity. -/
theorem sortToId_correct (b0 : List Nat)
    (hperm : List.Perm b0 (List.range b0.length)) :
    applySwaps (sortToId b0) b0 = List.range b0.length := by
  rcases eq_or_ne b0.length 0 with hn0 | hn0
  · -- empty list
    have hb : b0 = [] := List.eq_nil_of_length_eq_zero hn0
    subst hb; rfl
  · set n := b0.length with hn
    -- n ≥ 1: use the foldr invariant with m = n-1, k = 1
    have hone : (1 : Nat) ≤ n := by omega
    have hL : ((List.range n).drop 1) = List.range' 1 (n - 1) := by
      rw [List.range_eq_range', List.drop_range']
    -- rewrite sortToId as the foldr, then apply the invariant
    have hfold :
        sortToId b0 =
          (List.foldr (fun i st => sortStep st i) (b0, []) (List.range' 1 (n - 1))).2 := by
      unfold sortToId
      rw [← hn, List.foldl_reverse, hL]
    obtain ⟨hIlen, hIperm, hIacc, hIsuf, _⟩ :=
      sortFoldr_inv b0 n rfl hperm (n - 1) 1 (le_refl 1) (by omega)
    set st := List.foldr (fun i st => sortStep st i) (b0, []) (List.range' 1 (n - 1)) with hst
    -- position 0 also holds its identity value (nodup + suffix)
    have hnodup : st.1.Nodup := (hIperm.nodup_iff).2 List.nodup_range
    have h0val : st.1[0]! = 0 := by
      have h0lt : 0 < st.1.length := by rw [hIlen]; omega
      have hv! : st.1[0]! = st.1[0] := getElem!_pos st.1 0 h0lt
      rw [hv!]
      by_contra hvne
      have hvn : st.1[0] ∈ List.range n := (hIperm.mem_iff).1 (List.getElem_mem h0lt)
      have hvlt : st.1[0] < n := List.mem_range.1 hvn
      have hv1 : 1 ≤ st.1[0] := by omega
      have hvidx : st.1[st.1[0]]! = st.1[0] := hIsuf st.1[0] hv1 hvlt
      have hvlt' : st.1[0] < st.1.length := by rw [hIlen]; exact hvlt
      have hval2 : st.1[st.1[0]] = st.1[0] := by
        rw [getElem!_pos st.1 st.1[0] hvlt'] at hvidx; exact hvidx
      have hinj := (List.Nodup.getElem_inj_iff hnodup).1 hval2.symm
      omega
    -- st.1 = range n
    have hst1 : st.1 = List.range n := by
      apply List.ext_getElem?
      intro j
      by_cases hjn : j < n
      · have hval : st.1[j]! = j := by
          rcases Nat.eq_zero_or_pos j with hj0 | hj0
          · subst hj0; exact h0val
          · exact hIsuf j hj0 hjn
        rw [getElem?_of_getElem! (by rw [hIlen]; exact hjn) hval, List.getElem?_range hjn]
      · rw [List.getElem?_eq_none (by rw [hIlen]; omega),
            List.getElem?_eq_none (by rw [List.length_range]; omega)]
    -- conclude
    rw [hfold, ← hIacc]
    exact hst1

/-- **(P1) selection-sort realisability.**  For any permutation `t` of
`range t.length`, `starDecompose` realises exactly `t` under `netStack`.  (False
without the permutation hypothesis, e.g. `t = [0,0]`.) -/
theorem netStack_starDecompose_of_perm (t : List Nat)
    (hperm : List.Perm t (List.range t.length)) :
    netStack (starDecompose t) t.length = t := by
  unfold starDecompose
  rw [netStack_eq_applySwaps, ← sortToId_correct t hperm]
  exact applySwaps_reverse_cancel (sortToId t) t

/-! ## `netStack` outputs are permutations (feeds `starDecompose` at the call site) -/

/-- `netStack ps m` has length `m`. -/
theorem netStack_length (ps : List Nat) (m : Nat) : (netStack ps m).length = m := by
  rw [netStack_eq_applySwaps, length_applySwaps, List.length_range]

/-- `netStack ps m` is a permutation of `range m` — hence of `range` of its own
length, the hypothesis `netStack_starDecompose_of_perm` needs at the call site. -/
theorem netStack_perm_range (ps : List Nat) (m : Nat) :
    List.Perm (netStack ps m) (List.range (netStack ps m).length) := by
  rw [netStack_length, netStack_eq_applySwaps]
  exact applySwaps_perm ps (List.range m)

/-! ## Support (i): `starDecompose` element bounds (positions in `[1, length)`) -/

theorem sortToId_elem_bounds (t : List Nat)
    (hperm : List.Perm t (List.range t.length)) :
    ∀ e ∈ sortToId t, 1 ≤ e ∧ e < t.length := by
  rcases eq_or_ne t.length 0 with hn0 | hn0
  · have ht : t = [] := List.eq_nil_of_length_eq_zero hn0
    subst ht; intro e he; exact absurd he (by simp [sortToId])
  · set n := t.length with hn
    have hL : ((List.range n).drop 1) = List.range' 1 (n - 1) := by
      rw [List.range_eq_range', List.drop_range']
    have hfold : sortToId t =
        (List.foldr (fun i st => sortStep st i) (t, []) (List.range' 1 (n - 1))).2 := by
      unfold sortToId; rw [← hn, List.foldl_reverse, hL]
    obtain ⟨_, _, _, _, hbnd⟩ :=
      sortFoldr_inv t n rfl hperm (n - 1) 1 (le_refl 1) (by omega)
    rw [hfold]; exact hbnd

/-- Support (i): every position in `starDecompose t` lies in `[1, t.length)`
(for a permutation `t`). -/
theorem starDecompose_elem_bounds (t : List Nat)
    (hperm : List.Perm t (List.range t.length)) :
    ∀ e ∈ starDecompose t, 1 ≤ e ∧ e < t.length := by
  intro e he
  unfold starDecompose at he
  rw [List.mem_reverse] at he
  exact sortToId_elem_bounds t hperm e he

/-! ## Support: `maxDepth` upper-bounds every element -/

theorem le_foldl_max_acc (l : List Nat) (acc : Nat) : acc ≤ l.foldl Nat.max acc := by
  induction l generalizing acc with
  | nil => exact Nat.le_refl _
  | cons a l ih =>
      rw [List.foldl_cons]
      exact le_trans (Nat.le_max_left acc a) (ih _)

theorem mem_le_foldl_max (l : List Nat) (acc q : Nat) (hq : q ∈ l) :
    q ≤ l.foldl Nat.max acc := by
  induction l generalizing acc with
  | nil => simp at hq
  | cons a l ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.1 hq with h | h
      · subst h
        exact le_trans (Nat.le_max_right acc q) (le_foldl_max_acc l _)
      · exact ih (Nat.max acc a) h

theorem mem_le_maxDepth (swaps : List Nat) (q : Nat) (hq : q ∈ swaps) :
    q ≤ maxDepth swaps := mem_le_foldl_max swaps 0 q hq

/-! ## Support (window-extension): `netStack` over a wider window -/

theorem applySwap_append_left {α : Type _} (q : Nat) (xs ys : List α)
    (hq : q < xs.length) : applySwap q (xs ++ ys) = applySwap q xs ++ ys := by
  have h0lt : 0 < xs.length := by omega
  obtain ⟨a, ha⟩ : ∃ a, xs[0]? = some a := ⟨xs[0], List.getElem?_eq_getElem h0lt⟩
  obtain ⟨b, hb⟩ : ∃ b, xs[q]? = some b := ⟨xs[q], List.getElem?_eq_getElem hq⟩
  unfold applySwap
  rw [List.getElem?_append_left h0lt, List.getElem?_append_left hq, ha, hb]
  show ((xs ++ ys).set 0 b).set q a = (xs.set 0 b).set q a ++ ys
  rw [List.set_append_left 0 b h0lt,
      List.set_append_left q a (by rw [List.length_set]; exact hq)]

theorem applySwaps_append_left {α : Type _} (ps : List Nat) (xs ys : List α)
    (hall : ∀ q ∈ ps, q < xs.length) :
    applySwaps ps (xs ++ ys) = applySwaps ps xs ++ ys := by
  induction ps generalizing xs with
  | nil => rfl
  | cons q ps ih =>
      rw [applySwaps_cons, applySwaps_cons]
      have hq : q < xs.length := hall q (by simp)
      rw [applySwap_append_left q xs ys hq,
          ih (applySwap q xs) (by
            intro r hr; rw [length_applySwap]; exact hall r (by simp [hr]))]

theorem range_split (W L : Nat) (h : W ≤ L) :
    List.range L = List.range W ++ List.range' W (L - W) := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < W
  · rw [List.getElem?_append_left (by rw [List.length_range]; exact hi),
        List.getElem?_range (by omega), List.getElem?_range hi]
  · by_cases hiL : i < L
    · rw [List.getElem?_append_right (by rw [List.length_range]; omega),
          List.getElem?_range hiL, List.length_range,
          List.getElem?_range' (by omega)]
      congr 1; omega
    · rw [List.getElem?_eq_none_iff.2 (by rw [List.length_range]; omega),
          List.getElem?_eq_none_iff.2 (by
            rw [List.length_append, List.length_range, List.length_range']; omega)]

theorem netStack_window_extend (ps : List Nat) (W L : Nat)
    (hpos : ∀ q ∈ ps, q < W) (hWL : W ≤ L) :
    netStack ps L = netStack ps W ++ List.range' W (L - W) := by
  rw [netStack_eq_applySwaps, netStack_eq_applySwaps, range_split W L hWL,
      applySwaps_append_left ps (List.range W) (List.range' W (L - W))
        (by intro q hq; rw [List.length_range]; exact hpos q hq)]

/-- Window-extension corollary: two position lists below `W` with equal
`netStack` over `W` agree over any wider window. -/
theorem netStack_congr_window (a b : List Nat) (W L : Nat)
    (ha : ∀ q ∈ a, q < W) (hb : ∀ q ∈ b, q < W) (hWL : W ≤ L)
    (heq : netStack a W = netStack b W) :
    netStack a L = netStack b L := by
  rw [netStack_window_extend a W L ha hWL, netStack_window_extend b W L hb hWL, heq]

/-! ## Support (ii): the typed `.swap` run bounds every depth -/

theorem bodyType?_map_swap_bound (r : List Nat) :
    ∀ (input : Shape), (Block.bodyType? (r.map Instr.swap) input).isSome →
    ∀ d ∈ r, d < 16 ∧ d + 1 < input.slots.length := by
  induction r with
  | nil => intro input _ d hd; simp at hd
  | cons d ds ih =>
      intro input hsome e he
      simp only [List.map_cons, Block.bodyType?] at hsome
      cases hMid : Instr.type? (.swap d) input with
      | none => rw [hMid] at hsome; simp at hsome
      | some mid =>
          rw [hMid] at hsome
          obtain ⟨hd16, hdlen, hmidEq⟩ := type?_swap_eq_applySwap hMid
          rcases List.mem_cons.1 he with h | h
          · subst h; exact ⟨hd16, hdlen⟩
          · have hlen : mid.slots.length = input.slots.length := by
              rw [hmidEq]; simp [length_applySwap]
            have hb := ih mid hsome e h
            rw [hlen] at hb; exact hb

/-- `foldl Nat.max` stays below any bound of the accumulator and elements. -/
theorem foldl_max_le (l : List Nat) (M : Nat) :
    ∀ (acc : Nat), acc ≤ M → (∀ q ∈ l, q ≤ M) → l.foldl Nat.max acc ≤ M := by
  induction l with
  | nil => intro acc hacc _; exact hacc
  | cons a l ih =>
      intro acc hacc h
      rw [List.foldl_cons]
      exact ih (Nat.max acc a) (Nat.max_le.2 ⟨hacc, h a (by simp)⟩)
        (fun q hq => h q (by simp [hq]))

/-- `maxDepth` upper bound: if every element is `≤ M`, so is `maxDepth`. -/
theorem maxDepth_le (ps : List Nat) (M : Nat) (h : ∀ q ∈ ps, q ≤ M) :
    maxDepth ps ≤ M :=
  foldl_max_le ps M 0 (Nat.zero_le M) h

/-! ## Unconditional single-run type-preservation (P1 + supports discharge §75 frontier) -/

/-- **Unconditional per-run preservation.**  With (P1) and the supports both
`hNet` and `hBound` of `canonSwaps_bodyType?_preserve` are discharged: a typed
swap run is preserved by `canonSwaps` — no side hypotheses. -/
theorem canonSwaps_bodyType?_preserve_uncond (r : List Nat) (input out : Shape)
    (hType : Block.bodyType? (r.map Instr.swap) input = some out) :
    Block.bodyType? ((canonSwaps r).map Instr.swap) input = some out := by
  have hIsome : (Block.bodyType? (r.map Instr.swap) input).isSome := by rw [hType]; rfl
  have hrb := bodyType?_map_swap_bound r input hIsome
  have hcanon : canonSwaps r =
      if (starDecompose (netStack (r.map (· + 1)) (maxDepth (r.map (· + 1)) + 1))).length
          < r.length
      then (starDecompose (netStack (r.map (· + 1)) (maxDepth (r.map (· + 1)) + 1))).map (· - 1)
      else r := rfl
  set ps := r.map (· + 1) with hps
  set W := maxDepth ps + 1 with hW
  set c := starDecompose (netStack ps W) with hc
  -- window facts (valid regardless of firing)
  have hpsW : ∀ q ∈ ps, q < W := by
    intro q hq; rw [hW]; exact Nat.lt_succ_of_le (mem_le_maxDepth ps q hq)
  have htlen : (netStack ps W).length = W := netStack_length ps W
  have hcW : ∀ e ∈ c, 1 ≤ e ∧ e < W := by
    intro e he; rw [hc] at he
    have h := starDecompose_elem_bounds (netStack ps W) (netStack_perm_range ps W) e he
    rw [htlen] at h; exact h
  have hcnet : netStack c W = netStack ps W := by
    have h := netStack_starDecompose_of_perm (netStack ps W) (netStack_perm_range ps W)
    rw [htlen] at h; rw [hc]; exact h
  have hmap : (c.map (· - 1)).map (· + 1) = c := by
    rw [List.map_map]
    have hcong : c.map ((· + 1) ∘ (· - 1)) = c.map id := by
      apply List.map_congr_left
      intro e he
      have h1 := (hcW e he).1
      simp only [Function.comp_apply, id]; omega
    rw [hcong, List.map_id]
  refine canonSwaps_bodyType?_preserve r input out hType ?_ ?_
  · -- hBound
    intro e he
    rw [hcanon] at he
    by_cases hfire : c.length < r.length
    · rw [if_pos hfire, List.mem_map] at he
      obtain ⟨e', he'c, rfl⟩ := he
      obtain ⟨he'1, he'W⟩ := hcW e' he'c
      have hW17 : W ≤ 17 := by
        rw [hW]
        have hmd : maxDepth ps ≤ 16 := maxDepth_le ps 16 (by
          intro q hq; rw [hps, List.mem_map] at hq
          obtain ⟨d, hd, rfl⟩ := hq
          have := (hrb d hd).1; omega)
        omega
      have hrne : r ≠ [] := by
        intro h; rw [h] at hfire; simp at hfire
      have hWL : W ≤ input.slots.length := by
        rw [hW]
        have hmd : maxDepth ps ≤ input.slots.length - 1 := maxDepth_le ps _ (by
          intro q hq; rw [hps, List.mem_map] at hq
          obtain ⟨d, hd, rfl⟩ := hq
          have := (hrb d hd).2; omega)
        obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil r hrne
        have := (hrb d hd).2; omega
      exact ⟨by omega, by omega⟩
    · rw [if_neg hfire] at he
      exact hrb e he
  · -- hNet
    rw [hcanon]
    by_cases hfire : c.length < r.length
    · rw [if_pos hfire, hmap]
      have hrne : r ≠ [] := by
        intro h; rw [h] at hfire; simp at hfire
      have hWL : W ≤ input.slots.length := by
        rw [hW]
        have hmd : maxDepth ps ≤ input.slots.length - 1 := maxDepth_le ps _ (by
          intro q hq; rw [hps, List.mem_map] at hq
          obtain ⟨d, hd, rfl⟩ := hq
          have := (hrb d hd).2; omega)
        obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil r hrne
        have := (hrb d hd).2; omega
      exact netStack_congr_window c ps W input.slots.length
        (fun q hq => (hcW q hq).2) hpsW hWL hcnet
    · rw [if_neg hfire]

end ShuffleCanon
end TypedCfg
end EvmCompiler
