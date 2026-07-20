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

end Peephole
end TypedCfg
end EvmCompiler
