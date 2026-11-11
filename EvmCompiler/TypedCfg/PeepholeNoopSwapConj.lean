import EvmCompiler.TypedCfg.PeepholeNoopSwapType

/-!
# Conjugation commuting lemma + run-level `type?`-preservation (session-58)

The §Session-57 type half (`PeepholeNoopSwapType`) proves the per-window fact for
a SINGLE interior instruction: `swap d ; z ; swap d ↦ remapZeroWidth d z` reaches
the same output shape.  A real `normalizeBody` window has a whole *run* of
zero-width instructions between the two swaps, so the transform emits
`(zrun.map (remapZeroWidth d))` — a run of remapped instructions.  Chaining the
per-window lemma across a run does not compose directly (the run is one window
with a multi-instruction interior, not many windows).

This module supplies the primitive that DOES compose: the *conjugation commuting
lemma*

    type? (remapZeroWidth d z) (remapShape d s) = (type? z s).map (remapShape d)

for every `RemapSafe` `z` (with the two swapped positions in range).  Because
`remapZeroWidth`/`remapShape` are conjugation by the `0 ↔ d+1` transposition and
conjugation is a homomorphism, this folds over a run, giving the whole-body
directional `type?`-preservation `normalizeBody_bodyType?` — the analogue of
`peepholeBody_bodyType?` for the Route-3 pass.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open TypedCfg (Instr Shape Slot)

/-! ## Involution facts -/

theorem remapDepth_involutive (d b : Nat) : remapDepth d (remapDepth d b) = b := by
  rcases eq_or_ne b 0 with h | h
  · subst h; simp [remapDepth]
  · rcases eq_or_ne b (d + 1) with h2 | h2
    · subst h2; simp [remapDepth]
    · simp [remapDepth, h, h2]

theorem remapShape_involutive (d : Nat) (s : Shape)
    (h0 : 0 < s.slots.length) (hd : d + 1 < s.slots.length) :
    remapShape d (remapShape d s) = s := by
  obtain ⟨sl, tl⟩ := s
  simp only [remapShape] at *
  rw [swapPos_involutive 0 (d + 1) sl h0 hd]

/-- A `RemapSafe` (hence zero-width) instruction's `type?` preserves the slot
count. -/
theorem type?_remapSafe_length {z : Instr} (hSafe : RemapSafe z = true)
    {s s' : Shape} (h : Instr.type? z s = some s') :
    s'.slots.length = s.slots.length := by
  cases z with
  | bindLocals offset names =>
      have := Instr.length_of_type?_bindLocals h; simpa [Shape.length] using this
  | bindScratch baseDepth name slot =>
      have := Instr.length_of_type?_bindScratch h; simpa [Shape.length] using this
  | relabel target =>
      have := Instr.length_of_type?_relabel h; simpa [Shape.length] using this
  | _ => simp [RemapSafe] at hSafe

/-! ## The conjugation commuting lemma (per constructor) -/

theorem type?_conj_bindScratch (d baseDepth : Nat) (name : String) (slot : Nat)
    (s : Shape) (h0 : 0 < s.slots.length) (hd : d + 1 < s.slots.length) :
    Instr.type? (.bindScratch (remapDepth d baseDepth) name slot) (remapShape d s)
      = (Instr.type? (.bindScratch baseDepth name slot) s).map (remapShape d) := by
  simp only [Instr.type?, Shape.bindScratch?, remapShape]
  have hcond : (swapPos 0 (d + 1) s.slots)[remapDepth d baseDepth]? = s.slots[baseDepth]? := by
    rw [getElem?_swapPos_remapDepth d s.slots (remapDepth d baseDepth) h0 hd,
      remapDepth_involutive]
  rw [hcond]
  cases hLook : s.slots[baseDepth]? with
  | none => simp
  | some existing =>
      simp only [Option.map_some]
      refine congrArg some ?_
      simp only [remapShape]
      congr 1
      rw [swapPos_set_comm 0 (d + 1) s.slots baseDepth .scratchBase h0 hd,
        ← remapDepth_eq_transpIdx]

/-- Slot-agreement is invariant (as a Bool) under simultaneously transposing two
in-range positions on both equal-length lists. -/
theorem slotsAgree_swapPos_eq (d : Nat) (a b : List Slot)
    (hlen : a.length = b.length) (h0 : 0 < a.length) (hd : d + 1 < a.length) :
    Shape.slotsAgree (swapPos 0 (d + 1) a) (swapPos 0 (d + 1) b)
      = Shape.slotsAgree a b := by
  have h0b : 0 < b.length := hlen ▸ h0
  have hdb : d + 1 < b.length := hlen ▸ hd
  by_cases h : Shape.slotsAgree a b = true
  · rw [h, slotsAgree_swapPos d a b hlen h0 hd h]
  · simp only [Bool.not_eq_true] at h
    rw [h]
    by_contra hne
    simp only [Bool.not_eq_false] at hne
    have hback := slotsAgree_swapPos d (swapPos 0 (d + 1) a) (swapPos 0 (d + 1) b)
      (by rw [swapPos_length, swapPos_length]; exact hlen)
      (by rw [swapPos_length]; exact h0) (by rw [swapPos_length]; exact hd) hne
    rw [swapPos_involutive 0 (d + 1) a h0 hd,
      swapPos_involutive 0 (d + 1) b h0b hdb] at hback
    rw [hback] at h; exact absurd h (by simp)

theorem type?_conj_relabel (d : Nat) (target s : Shape)
    (h0 : 0 < s.slots.length) (hd : d + 1 < s.slots.length) :
    Instr.type? (.relabel (remapShape d target)) (remapShape d s)
      = (Instr.type? (.relabel target) s).map (remapShape d) := by
  simp only [Instr.type?]
  have hCompatEq : (remapShape d s).relabelCompatible (remapShape d target)
      = s.relabelCompatible target := by
    unfold Shape.relabelCompatible remapShape
    simp only [Shape.length, Shape.tail, swapPos_length]
    by_cases hLen : s.slots.length = target.slots.length
    · rw [slotsAgree_swapPos_eq d s.slots target.slots hLen h0 hd]
    · simp [hLen]
  rw [hCompatEq]
  by_cases hCompat : s.relabelCompatible target = true
  · rw [hCompat]; simp
  · simp only [Bool.not_eq_true] at hCompat; rw [hCompat]; simp

theorem type?_conj_bindLocals_single (d offset : Nat) (name : String) (s : Shape)
    (h0 : 0 < s.slots.length) (hd : d + 1 < s.slots.length) :
    Instr.type? (.bindLocals (remapDepth d offset) [name]) (remapShape d s)
      = (Instr.type? (.bindLocals offset [name]) s).map (remapShape d) := by
  by_cases hOff : offset < s.slots.length
  · rw [type?_bindLocals_single offset name s hOff]
    have hOff' : remapDepth d offset < (remapShape d s).slots.length := by
      simp only [remapShape, swapPos_length]
      have hlt : offset < (swapPos 0 (d + 1) s.slots).length := by
        rw [swapPos_length]; exact hOff
      have heq := getElem?_swapPos_remapDepth d s.slots offset h0 hd
      rw [List.getElem?_eq_getElem hlt] at heq
      obtain ⟨hh, _⟩ := List.getElem?_eq_some_iff.mp heq.symm
      exact hh
    rw [type?_bindLocals_single (remapDepth d offset) name (remapShape d s) hOff']
    simp only [Option.map_some]
    refine congrArg some ?_
    simp only [remapShape]
    congr 1
    rw [swapPos_set_comm 0 (d + 1) s.slots offset (Shape.slotOfBinder name) h0 hd,
      ← remapDepth_eq_transpIdx]
  · push_neg at hOff
    have hL : Instr.type? (.bindLocals offset [name]) s = none := by
      simp only [Instr.type?, Shape.bindLocals?, Shape.length, List.length_cons,
        List.length_nil]
      rw [if_neg (by omega)]
    have hOff2 : ¬ remapDepth d offset < s.slots.length := by
      unfold remapDepth
      split_ifs <;> omega
    have hR : Instr.type? (.bindLocals (remapDepth d offset) [name]) (remapShape d s)
        = none := by
      simp only [Instr.type?, Shape.bindLocals?, Shape.length, List.length_cons,
        List.length_nil, remapShape, swapPos_length]
      rw [if_neg (by omega)]
    rw [hL, hR]; simp

/-- **The conjugation commuting lemma.** For every `RemapSafe` zero-width `z`,
`remapZeroWidth d` conjugates `type? z` by the shape transposition `remapShape d`
(given the two swapped positions are in range on `s`). -/
theorem type?_conj_remap {d : Nat} {z : Instr} (hSafe : RemapSafe z = true)
    (s : Shape) (h0 : 0 < s.slots.length) (hd : d + 1 < s.slots.length) :
    Instr.type? (remapZeroWidth d z) (remapShape d s)
      = (Instr.type? z s).map (remapShape d) := by
  cases z with
  | bindScratch baseDepth name slot =>
      exact type?_conj_bindScratch d baseDepth name slot s h0 hd
  | relabel target =>
      exact type?_conj_relabel d target s h0 hd
  | bindLocals offset names =>
      match names, hSafe with
      | [name], _ => exact type?_conj_bindLocals_single d offset name s h0 hd
  | _ => simp [RemapSafe] at hSafe

/-! ## `bodyType?` structural helpers -/

theorem bodyType?_cons (instr : Instr) (rest : List Instr) (s : Shape) :
    Block.bodyType? (instr :: rest) s
      = (instr.type? s).bind (fun s' => Block.bodyType? rest s') := rfl

theorem bodyType?_append (l1 l2 : List Instr) (s : Shape) :
    Block.bodyType? (l1 ++ l2) s
      = (Block.bodyType? l1 s).bind (fun s' => Block.bodyType? l2 s') := by
  induction l1 generalizing s with
  | nil => rfl
  | cons instr rest ih =>
      simp only [List.cons_append, bodyType?_cons]
      cases Instr.type? instr s with
      | none => rfl
      | some s' => simpa using ih s'

/-! ## The run-level conjugation fold -/

/-- **Run-level conjugation.** `remapZeroWidth d` conjugates a whole `RemapSafe`
run's `bodyType?` by the shape transposition `remapShape d`. -/
theorem bodyType?_map_remap_conj (d : Nat) (zrun : List Instr) :
    ∀ (s : Shape), (∀ z ∈ zrun, RemapSafe z = true) →
      0 < s.slots.length → d + 1 < s.slots.length →
      Block.bodyType? (zrun.map (remapZeroWidth d)) (remapShape d s)
        = (Block.bodyType? zrun s).map (remapShape d) := by
  induction zrun with
  | nil => intro s _ _ _; simp [Block.bodyType?]
  | cons z rest ih =>
      intro s hAll h0 hd
      simp only [List.map_cons, bodyType?_cons]
      have hzSafe : RemapSafe z = true := hAll z (List.mem_cons_self ..)
      rw [type?_conj_remap hzSafe s h0 hd]
      cases hz : Instr.type? z s with
      | none => simp
      | some s1 =>
          simp only [hz, Option.map_some, Option.bind_some]
          have hlen := type?_remapSafe_length hzSafe hz
          have h0' : 0 < s1.slots.length := by rw [hlen]; exact h0
          have hd' : d + 1 < s1.slots.length := by rw [hlen]; exact hd
          have hAll' : ∀ z' ∈ rest, RemapSafe z' = true :=
            fun z' hz' => hAll z' (List.mem_cons_of_mem z hz')
          exact ih s1 hAll' h0' hd'

/-! ## Whole-body directional `type?`-preservation -/

/-- **Directional `type?`-preservation** (analogue of `peepholeBody_bodyType?`).
If the ORIGINAL body types `input` to `output`, so does the `normalizeBody`
transform.  (One-way, exactly as the adjacent-inverse peephole: a shallow `input`
can make the original untypeable while the cancelled tail still types.) -/
theorem normalizeBody_bodyType? (body : List Instr) :
    ∀ input output, Block.bodyType? body input = some output →
      Block.bodyType? (normalizeBody body) input = some output := by
  induction body using normalizeBody.induct with
  | case1 => intro input output h; simpa [normalizeBody] using h
  | case2 d rest d' rest' hTail hGuard ih =>
      intro input output hType
      obtain ⟨hdd, hSafe⟩ := hGuard
      subst hdd
      have happ : (leadingZeroWidth rest).1 ++ Instr.swap d :: rest' = rest := by
        conv_rhs => rw [← leadingZeroWidth_append rest]
        rw [hTail]
      -- decompose the original typing: swap ; zrun ; swap ; rest'
      rw [bodyType?_cons, Option.bind_eq_some_iff] at hType
      obtain ⟨s1, h1, hType⟩ := hType
      obtain ⟨hi0, hid1⟩ := swap_bounds h1
      obtain ⟨hs1slots, hs1tail⟩ := type?_swap_eq h1
      have hs1len : s1.slots.length = input.slots.length := by
        rw [hs1slots, swapPos_length]
      have hs1eq : s1 = remapShape d input := by
        obtain ⟨sl1, tl1⟩ := s1
        simp only at hs1slots hs1tail
        simp only [remapShape, Shape.mk.injEq]; exact ⟨hs1slots, hs1tail⟩
      rw [← happ, bodyType?_append, Option.bind_eq_some_iff] at hType
      obtain ⟨sInner, hzt, hType⟩ := hType
      rw [bodyType?_cons, Option.bind_eq_some_iff] at hType
      obtain ⟨s3, h3, hType⟩ := hType
      obtain ⟨hs3slots, hs3tail⟩ := type?_swap_eq h3
      -- build the fire-result typing
      rw [normalizeBody_fire d rest rest' hTail hSafe, bodyType?_append,
        Option.bind_eq_some_iff]
      refine ⟨s3, ?_, ih s3 output hType⟩
      -- bodyType? (zrun.map (remap d)) input = some s3
      have hinput_eq : input = remapShape d s1 := by
        rw [hs1eq, remapShape_involutive d input hi0 hid1]
      have hAllSafe : ∀ z ∈ (leadingZeroWidth rest).1, RemapSafe z = true :=
        fun z hz => (List.all_eq_true.mp hSafe) z hz
      rw [hinput_eq, bodyType?_map_remap_conj d (leadingZeroWidth rest).1 s1 hAllSafe
        (by rw [hs1len]; exact hi0) (by rw [hs1len]; exact hid1), hzt, Option.map_some]
      refine congrArg some ?_
      obtain ⟨sl3, tl3⟩ := s3
      simp only at hs3slots hs3tail
      simp only [remapShape, Shape.mk.injEq]; exact ⟨hs3slots.symm, hs3tail.symm⟩
  | case3 d rest d' rest' hTail hGuard ih =>
      intro input output hType
      have hunfold : normalizeBody (Instr.swap d :: rest)
          = Instr.swap d :: normalizeBody rest := by
        by_cases hdd : d = d'
        · have hUnsafe : (leadingZeroWidth rest).1.all RemapSafe = false := by
            by_contra hne
            simp only [Bool.not_eq_false] at hne
            exact hGuard ⟨hdd, hne⟩
          exact normalizeBody_keep_unsafe d d' rest rest' hTail hUnsafe
        · exact normalizeBody_keep_swap d d' rest rest' hTail hdd
      rw [hunfold, bodyType?_cons, Option.bind_eq_some_iff] at *
      obtain ⟨mid, hHead, hTail2⟩ := hType
      exact ⟨mid, hHead, ih mid output hTail2⟩
  | case4 d rest hNoTail ih =>
      intro input output hType
      rw [normalizeBody_keep_noTail d rest (fun d' rest' h => hNoTail d' rest' h),
        bodyType?_cons, Option.bind_eq_some_iff] at *
      obtain ⟨mid, hHead, hTail2⟩ := hType
      exact ⟨mid, hHead, ih mid output hTail2⟩
  | case5 instr rest hNotSwap ih =>
      intro input output hType
      rw [normalizeBody_cons_generic instr rest (fun d h => hNotSwap d h),
        bodyType?_cons, Option.bind_eq_some_iff] at *
      obtain ⟨mid, hHead, hTail2⟩ := hType
      exact ⟨mid, hHead, ih mid output hTail2⟩

end Peephole
end TypedCfg
end EvmCompiler
