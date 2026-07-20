import EvmCompiler.TypedCfg.PeepholeNoopSwap

/-!
# `type?`-preservation for `normalizeBody` (session-57 step 3, type half)

The soundness of the Route-3 no-op-swap normalization rests on a *type*
transposition fact: replacing a `swap d ; z ; swap d` window (with `z`
zero-width) by `remapZeroWidth d z` reaches the **same output shape**.  The
runtime is trivially preserved (all three of `z`, the two swaps, and the residue
are runtime-`id` up to control counters), but the *shape* fed to the block's
remaining instructions must be identical or the block's later instructions could
stop typing.

This module establishes the shape half: the `swapPos 0 (d+1)` transposition
infrastructure, the bridge `Instr.type? (.swap d)` ↦ `swapPos 0 (d+1)`, and the
per-constructor transposition-preservation lemmas for the zero-width
instructions (`bindScratch`, `relabel`; `bindLocals` is the documented
frontier).
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open TypedCfg (Instr Shape Slot)

/-! ## `swapPos` index calculus -/

/-- The image of an index under the `i ↔ j` transposition. -/
def transpIdx (i j b : Nat) : Nat :=
  if b = i then j else if b = j then i else b

theorem remapDepth_eq_transpIdx (d b : Nat) :
    remapDepth d b = transpIdx 0 (d + 1) b := rfl

@[simp] theorem swapPos_length {α : Type _} (i j : Nat) (l : List α) :
    (swapPos i j l).length = l.length := by
  unfold swapPos
  cases l[i]? <;> cases l[j]? <;> simp [List.length_set]

/-- Pointwise description of the `i ↔ j` transposition on a list.  The branch
order matches `List.getElem?_set` so the proof is near-definitional. -/
theorem swapPos_getElem? {α : Type _} (i j : Nat) (l : List α) (k : Nat)
    (hi : i < l.length) (hj : j < l.length) :
    (swapPos i j l)[k]? =
      if j = k then l[i]? else if i = k then l[j]? else l[k]? := by
  unfold swapPos
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
  simp only []
  rw [List.getElem?_set, List.getElem?_set, List.length_set]
  simp only [hi, hj, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
    if_true]

/-- The transposition is an involution (on any list whose indices are valid). -/
theorem swapPos_involutive {α : Type _} (i j : Nat) (l : List α)
    (hi : i < l.length) (hj : j < l.length) :
    swapPos i j (swapPos i j l) = l := by
  apply List.ext_getElem?
  intro k
  have hi' : i < (swapPos i j l).length := by rw [swapPos_length]; exact hi
  have hj' : j < (swapPos i j l).length := by rw [swapPos_length]; exact hj
  rw [swapPos_getElem? i j (swapPos i j l) k hi' hj']
  rw [swapPos_getElem? i j l j hi hj, swapPos_getElem? i j l i hi hj,
    swapPos_getElem? i j l k hi hj]
  by_cases hji : j = i <;> by_cases hjk : j = k <;> by_cases hik : i = k <;>
    subst_vars <;> simp_all

/-- The transposition commutes with `set`, moving the index through `transpIdx`. -/
theorem swapPos_set_comm {α : Type _} (i j : Nat) (l : List α) (b : Nat) (v : α)
    (hi : i < l.length) (hj : j < l.length) :
    swapPos i j (l.set b v) = (swapPos i j l).set (transpIdx i j b) v := by
  apply List.ext_getElem?
  intro k
  have hi' : i < (l.set b v).length := by rw [List.length_set]; exact hi
  have hj' : j < (l.set b v).length := by rw [List.length_set]; exact hj
  rw [swapPos_getElem? i j (l.set b v) k hi' hj']
  simp only [List.getElem?_set, swapPos_length]
  rw [swapPos_getElem? i j l k hi hj]
  unfold transpIdx
  by_cases hbi : b = i <;> by_cases hbj : b = j <;>
    by_cases hjk : j = k <;> by_cases hik : i = k <;>
      by_cases hbk : b = k <;>
        subst_vars <;> simp_all

/-! ## The swap `type?` bridge -/

/-- Running `swap d`'s typing exactly performs the `0 ↔ d+1` transposition on the
shape's slots (and preserves the tail). -/
theorem type?_swap_eq {d : Nat} {s s' : Shape}
    (hType : Instr.type? (.swap d) s = some s') :
    s'.slots = swapPos 0 (d + 1) s.slots ∧ s'.tail = s.tail := by
  obtain ⟨hd, hdepth, _⟩ := Instr.length_of_type?_swap hType
  simp only [Instr.type?] at hType
  rw [if_pos hd] at hType
  cases hSlots : s.slots with
  | nil => rw [hSlots] at hType; simp [Shape.get?, hSlots] at hType
  | cons top rest =>
      have hdd : d < rest.length := by
        have h2 : d + 2 ≤ s.slots.length := hdepth
        rw [hSlots] at h2; simpa using h2
      have hGet : s.get? (d + 1) = some rest[d] := by
        rw [Shape.get?, hSlots, List.getElem?_cons_succ,
          List.getElem?_eq_getElem hdd]
      rw [hSlots] at hType
      simp only [hGet] at hType
      cases hType
      refine ⟨?_, rfl⟩
      show rest[d] :: rest.set d top = swapPos 0 (d + 1) (top :: rest)
      have e0 : (top :: rest)[0]? = some top := rfl
      have ed : (top :: rest)[d + 1]? = some rest[d] := by
        rw [List.getElem?_cons_succ, List.getElem?_eq_getElem hdd]
      unfold swapPos
      rw [e0, ed]
      rfl

/-- Reading position `b` after the transposition equals reading the
`remapDepth`-image position before it. -/
theorem getElem?_swapPos_remapDepth {α : Type _} (d : Nat) (l : List α) (b : Nat)
    (h0 : 0 < l.length) (hd : d + 1 < l.length) :
    (swapPos 0 (d + 1) l)[b]? = l[remapDepth d b]? := by
  rw [swapPos_getElem? 0 (d + 1) l b h0 hd]
  unfold remapDepth
  by_cases hb0 : b = 0
  · subst hb0; simp
  · by_cases hbd : b = d + 1
    · subst hbd; simp
    · have hne1 : ¬ (d + 1 = b) := fun h => hbd h.symm
      have hne2 : ¬ (0 = b) := fun h => hb0 h.symm
      rw [if_neg hne1, if_neg hne2, if_neg hb0, if_neg hbd]

/-! ## Per-constructor window `type?`-preservation -/

/-- Bounds carried by a well-typed `swap d`: the two exchanged positions exist. -/
theorem swap_bounds {d : Nat} {s s' : Shape}
    (hType : Instr.type? (.swap d) s = some s') :
    0 < s.slots.length ∧ d + 1 < s.slots.length := by
  obtain ⟨_, hdepth, _⟩ := Instr.length_of_type?_swap hType
  have : d + 2 ≤ s.slots.length := hdepth
  omega

/-- **`bindScratch` window preservation.**  Cancelling `swap d ; bindScratch b ;
swap d` in favour of the remapped `bindScratch (remapDepth d b)` reaches the same
output shape. -/
theorem type?_window_bindScratch {d baseDepth : Nat} {name : String} {slot : Nat}
    {s0 s1 s2 s3 : Shape}
    (h1 : Instr.type? (.swap d) s0 = some s1)
    (h2 : Instr.type? (.bindScratch baseDepth name slot) s1 = some s2)
    (h3 : Instr.type? (.swap d) s2 = some s3) :
    Instr.type? (remapZeroWidth d (.bindScratch baseDepth name slot)) s0
      = some s3 := by
  obtain ⟨h0, hd1⟩ := swap_bounds h1
  obtain ⟨hs1slots, hs1tail⟩ := type?_swap_eq h1
  obtain ⟨hs3slots, hs3tail⟩ := type?_swap_eq h3
  -- unfold bindScratch's typing
  simp only [Instr.type?, Shape.bindScratch?] at h2
  cases hLook : s1.slots[baseDepth]? with
  | none => rw [hLook] at h2; simp at h2
  | some existing =>
      rw [hLook] at h2
      simp only [Option.some.injEq] at h2
      -- s2 = { s1 with slots := s1.slots.set baseDepth .scratchBase }
      subst h2
      -- rewrite s2's slots in h3-derived facts
      simp only at hs3slots hs3tail
      -- side condition (a): s0 has a slot at remapDepth d baseDepth
      have hSide : s0.slots[remapDepth d baseDepth]? = some existing := by
        rw [← getElem?_swapPos_remapDepth d s0.slots baseDepth h0 hd1,
          ← hs1slots]; exact hLook
      -- compute the goal shape
      simp only [remapZeroWidth, Instr.type?, Shape.bindScratch?, hSide]
      -- goal: some { s0 with slots := s0.slots.set (remapDepth d baseDepth) .scratchBase } = some s3
      refine congrArg some ?_
      -- lengths for involution / set-comm on l = swapPos 0 (d+1) s0.slots
      have hlen : (swapPos 0 (d + 1) s0.slots).length = s0.slots.length :=
        swapPos_length 0 (d + 1) s0.slots
      have h0' : 0 < (swapPos 0 (d + 1) s0.slots).length := by rw [hlen]; exact h0
      have hd1' : d + 1 < (swapPos 0 (d + 1) s0.slots).length := by
        rw [hlen]; exact hd1
      -- s3.slots = s0.slots.set (remapDepth d baseDepth) scratchBase
      have hslots : s3.slots = s0.slots.set (remapDepth d baseDepth) .scratchBase := by
        rw [hs3slots]
        simp only [hs1slots]
        rw [swapPos_set_comm 0 (d + 1) (swapPos 0 (d + 1) s0.slots) baseDepth
            .scratchBase h0' hd1',
          swapPos_involutive 0 (d + 1) s0.slots h0 hd1,
          ← remapDepth_eq_transpIdx]
      -- tail
      have htail : s3.tail = s0.tail := by rw [hs3tail, hs1tail]
      -- assemble Shape equality
      obtain ⟨sl3, tl3⟩ := s3
      simp only at hslots htail
      subst hslots htail
      rfl

/-! ## `slotsAgree` under the transposition (for `relabel`) -/

/-- Per-position agreement, matching `Shape.slotsAgree`'s head rule. -/
def pairAgree : Slot → Slot → Bool
  | .returnPC _, .returnToken => true
  | .returnToken, .returnPC _ => true
  | l, r => decide (l = .word) || decide (r = .word) || decide (l = r)

/-- Lifted to positions that may be out of range (vacuously agreeing). -/
def pairAgree? : Option Slot → Option Slot → Bool
  | some l, some r => pairAgree l r
  | _, _ => true

theorem slotsAgree_cons (x y : Slot) (as bs : List Slot) :
    Shape.slotsAgree (x :: as) (y :: bs)
      = (pairAgree x y && Shape.slotsAgree as bs) := by
  cases x <;> cases y <;> simp [Shape.slotsAgree, pairAgree]

/-- `slotsAgree` is exactly pairwise agreement on the common prefix. -/
theorem slotsAgree_iff_pointwise (a b : List Slot) :
    Shape.slotsAgree a b = true ↔ ∀ k : Nat, pairAgree? a[k]? b[k]? = true := by
  induction a generalizing b with
  | nil =>
      simp only [Shape.slotsAgree]
      exact ⟨fun _ k => by simp [pairAgree?, List.getElem?_nil], fun _ => trivial⟩
  | cons x as ih =>
      cases b with
      | nil =>
          constructor
          · intro _ k
            simp [pairAgree?, List.getElem?_nil]
          · intro _; rfl
      | cons y bs =>
          rw [slotsAgree_cons, Bool.and_eq_true, ih bs]
          constructor
          · rintro ⟨hHead, hTail⟩ k
            cases k with
            | zero => simpa [pairAgree?] using hHead
            | succ n => simpa using hTail n
          · intro h
            refine ⟨?_, fun n => ?_⟩
            · simpa [pairAgree?] using h 0
            · simpa using h (n + 1)

/-- Simultaneously transposing two positions preserves `slotsAgree` (given the
positions are valid on both equal-length lists). -/
theorem slotsAgree_swapPos (d : Nat) (a b : List Slot)
    (hlen : a.length = b.length)
    (h0 : 0 < a.length) (hd : d + 1 < a.length)
    (hAgree : Shape.slotsAgree a b = true) :
    Shape.slotsAgree (swapPos 0 (d + 1) a) (swapPos 0 (d + 1) b) = true := by
  have h0b : 0 < b.length := hlen ▸ h0
  have hdb : d + 1 < b.length := hlen ▸ hd
  rw [slotsAgree_iff_pointwise] at hAgree ⊢
  intro k
  rw [swapPos_getElem? 0 (d + 1) a k h0 hd,
    swapPos_getElem? 0 (d + 1) b k h0b hdb]
  by_cases hdk : d + 1 = k
  · simpa [hdk] using hAgree 0
  · by_cases hzk : 0 = k
    · simpa [hdk, hzk] using hAgree (d + 1)
    · simpa [hdk, hzk] using hAgree k

/-- **`relabel` window preservation.** -/
theorem type?_window_relabel {d : Nat} {target : Shape} {s0 s1 s2 s3 : Shape}
    (h1 : Instr.type? (.swap d) s0 = some s1)
    (h2 : Instr.type? (.relabel target) s1 = some s2)
    (h3 : Instr.type? (.swap d) s2 = some s3) :
    Instr.type? (remapZeroWidth d (.relabel target)) s0 = some s3 := by
  obtain ⟨h0, hd1⟩ := swap_bounds h1
  obtain ⟨hs1slots, hs1tail⟩ := type?_swap_eq h1
  -- relabel: relabelCompatible s1 target ∧ s2 = target
  simp only [Instr.type?] at h2
  by_cases hCompat : s1.relabelCompatible target
  · rw [if_pos hCompat] at h2
    simp only [Option.some.injEq] at h2
    subst h2
    obtain ⟨hs3slots, hs3tail⟩ := type?_swap_eq h3
    -- unpack relabelCompatible s1 target
    unfold Shape.relabelCompatible at hCompat
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hCompat
    obtain ⟨⟨hAgree, hLenEq⟩, hTailEq⟩ := hCompat
    -- lengths / involution helpers
    have hlen : (swapPos 0 (d + 1) s0.slots).length = s0.slots.length :=
      swapPos_length 0 (d + 1) s0.slots
    -- s0.slots = swapPos (s1.slots)
    have hs0 : s0.slots = swapPos 0 (d + 1) s1.slots := by
      rw [hs1slots, swapPos_involutive 0 (d + 1) s0.slots h0 hd1]
    -- bounds on s1.slots
    have h0s1 : 0 < s1.slots.length := by rw [hs1slots, hlen]; exact h0
    have hd1s1 : d + 1 < s1.slots.length := by rw [hs1slots, hlen]; exact hd1
    -- goal reduces via remapZeroWidth = relabel (remapShape d target)
    have hRemapCompat : s0.relabelCompatible (remapShape d target) = true := by
      unfold Shape.relabelCompatible remapShape
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · -- slotsAgree s0.slots (swapPos target.slots)
        rw [hs0]
        exact slotsAgree_swapPos d s1.slots target.slots hLenEq h0s1 hd1s1 hAgree
      · -- length
        show s0.length = (swapPos 0 (d + 1) target.slots).length
        rw [swapPos_length]
        have hswap : s1.length = s0.length := (Instr.length_of_type?_swap h1).2.2
        exact hswap ▸ hLenEq
      · -- tail
        show s0.tail = target.tail
        rw [← hTailEq, ← hs1tail]
    simp only [remapZeroWidth, Instr.type?, hRemapCompat, if_true]
    refine congrArg some ?_
    -- remapShape d target = s3
    obtain ⟨sl3, tl3⟩ := s3
    simp only at hs3slots hs3tail
    unfold remapShape
    simp only [Shape.mk.injEq]
    exact ⟨hs3slots.symm, hs3tail.symm⟩
  · rw [if_neg hCompat] at h2; simp at h2

/-! ## `bindLocals` window preservation (single-name case)

A single-name `bindLocals offset [name]` rebinds exactly one position, so it is a
`set` — the same shape mutation as `bindScratch` — and its window cancellation is
sound by the identical transposition argument.  The **multi-name** case is the
documented frontier: when `[offset, offset+len)` straddles exactly one of the
transposed positions `{0, d+1}`, the image is non-contiguous and cannot be a
single `bindLocals` with the same name list — it needs either a firing guard
(`len ≤ 1`) or a multi-instruction residue (see PEEPHOLE_PROGRESS §Session-57). -/

theorem take_append_single_drop {α : Type _} :
    ∀ (l : List α) (n : Nat) (a : α), n < l.length →
      l.take n ++ a :: l.drop (n + 1) = l.set n a
  | [], n, a, h => by simp at h
  | x :: xs, 0, a, _ => by simp
  | x :: xs, n + 1, a, h => by
      have ih := take_append_single_drop xs n a (by simpa using h)
      simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append,
        List.set_cons_succ]
      exact congrArg (x :: ·) ih

/-- Single-name `bindLocals` types exactly as a `set` of the one bound slot. -/
theorem type?_bindLocals_single (offset : Nat) (name : String) (s : Shape)
    (h : offset < s.slots.length) :
    Instr.type? (.bindLocals offset [name]) s
      = some { s with slots := s.slots.set offset (.local name) } := by
  simp only [Instr.type?, Shape.bindLocals?, Shape.length, List.length_cons,
    List.length_nil, List.map_cons, List.map_nil, Nat.zero_add,
    List.append_assoc, List.singleton_append]
  rw [if_pos (by omega : offset + 1 ≤ s.slots.length)]
  rw [take_append_single_drop s.slots offset (.local name) h]

/-- **`bindLocals` (single name) window preservation.** -/
theorem type?_window_bindLocals_single {d offset : Nat} {name : String}
    {s0 s1 s2 s3 : Shape}
    (h1 : Instr.type? (.swap d) s0 = some s1)
    (h2 : Instr.type? (.bindLocals offset [name]) s1 = some s2)
    (h3 : Instr.type? (.swap d) s2 = some s3) :
    Instr.type? (remapZeroWidth d (.bindLocals offset [name])) s0 = some s3 := by
  obtain ⟨h0, hd1⟩ := swap_bounds h1
  obtain ⟨hs1slots, hs1tail⟩ := type?_swap_eq h1
  obtain ⟨hs3slots, hs3tail⟩ := type?_swap_eq h3
  -- side bound: offset < s1.slots.length (else bindLocals? = none)
  have hOff1 : offset < s1.slots.length := by
    by_contra hle
    push_neg at hle
    simp only [Instr.type?, Shape.bindLocals?, Shape.length, List.length_cons,
      List.length_nil] at h2
    rw [if_neg (by omega)] at h2
    simp at h2
  rw [type?_bindLocals_single offset name s1 hOff1] at h2
  simp only [Option.some.injEq] at h2
  subst h2
  simp only at hs3slots hs3tail
  -- side condition on s0
  have hOff0 : remapDepth d offset < s0.slots.length := by
    have hlt : offset < (swapPos 0 (d + 1) s0.slots).length := by
      rw [← hs1slots]; exact hOff1
    have heq := getElem?_swapPos_remapDepth d s0.slots offset h0 hd1
    rw [List.getElem?_eq_getElem hlt] at heq
    obtain ⟨hh, _⟩ := List.getElem?_eq_some_iff.mp heq.symm
    exact hh
  rw [remapZeroWidth, type?_bindLocals_single (remapDepth d offset) name s0 hOff0]
  refine congrArg some ?_
  have hlen : (swapPos 0 (d + 1) s0.slots).length = s0.slots.length :=
    swapPos_length 0 (d + 1) s0.slots
  have h0' : 0 < (swapPos 0 (d + 1) s0.slots).length := by rw [hlen]; exact h0
  have hd1' : d + 1 < (swapPos 0 (d + 1) s0.slots).length := by rw [hlen]; exact hd1
  have hslots : s3.slots = s0.slots.set (remapDepth d offset) (.local name) := by
    rw [hs3slots]
    simp only [hs1slots]
    rw [swapPos_set_comm 0 (d + 1) (swapPos 0 (d + 1) s0.slots) offset
        (.local name) h0' hd1',
      swapPos_involutive 0 (d + 1) s0.slots h0 hd1, ← remapDepth_eq_transpIdx]
  have htail : s3.tail = s0.tail := by rw [hs3tail, hs1tail]
  obtain ⟨sl3, tl3⟩ := s3
  simp only at hslots htail
  subst hslots htail
  rfl

/-! ## Unified window `type?`-preservation (step-3 type capstone) -/

/-- **Window `type?`-preservation.** For any remap-safe zero-width `z`, cancelling
`swap d ; z ; swap d` in favour of `remapZeroWidth d z` reaches the identical
output shape. -/
theorem type?_remapZeroWidth_window {d : Nat} {z : Instr} {s0 s1 s2 s3 : Shape}
    (hSafe : RemapSafe z = true)
    (h1 : Instr.type? (.swap d) s0 = some s1)
    (h2 : Instr.type? z s1 = some s2)
    (h3 : Instr.type? (.swap d) s2 = some s3) :
    Instr.type? (remapZeroWidth d z) s0 = some s3 := by
  cases z with
  | bindScratch baseDepth name slot =>
      exact type?_window_bindScratch h1 h2 h3
  | relabel target =>
      exact type?_window_relabel h1 h2 h3
  | bindLocals offset names =>
      -- RemapSafe forces `names = [name]`.
      match names, hSafe with
      | [name], _ => exact type?_window_bindLocals_single h1 h2 h3
  | _ => simp [RemapSafe] at hSafe

end Peephole
end TypedCfg
end EvmCompiler
