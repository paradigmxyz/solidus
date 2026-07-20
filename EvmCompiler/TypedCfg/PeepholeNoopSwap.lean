import EvmCompiler.TypedCfg.Typing

/-!
# Type-directed no-op-swap normalization (`swap d ; z* ; swap d → z'*`)

Session-57 milestone: the Route-3 (variant B) pre-normalization pass.  The
adjacent-inverse peephole (`Peephole.peepholeBody`) matches on *literal* list
adjacency, so it cancels `swap d ; swap d` only when the two swaps abut.  In the
emitted TypedCfg image the redundant swap pairs are separated by one or more
*zero-width* instructions — `bindLocals` / `bindScratch` / `relabel`, each of
which lowers to `[]` and runs as `.ok state` — so the literal-adjacency arm
never fires on them (see PEEPHOLE_PROGRESS §Session-55/56).

This module defines the type-directed normalization that cancels such a
`swap d ; z* ; swap d` window: the two swaps are dropped and each intervening
zero-width instruction `z` is replaced by `remapZeroWidth d z`, i.e. `z` with
its position parameters conjugated by the `0 ↔ d+1` transposition that `swap d`
performs on stack shapes (`Instr.type? (.swap d)`).  The residue is still
zero-width (lowers to `[]`, runs as `.ok state`) and — this is the point —
preserves the *output shape* fed to the block's remaining instructions, so the
transform is sound by construction while dropping the `swapN;swapN` two bytes.

Milestone split (this module):
* the transform (`remapZeroWidth`, `normalizeBody`) + its syntactic
  length/structure lemmas — this file;
* the `type?`-preservation transposition lemmas, the runtime congruence, and the
  `lower?`-shrink integration — follow-on modules.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open TypedCfg (Instr Shape)

/-- Transpose two list positions `i` and `j`.  If either index is out of range
the list is returned unchanged (so the operation is total and a no-op exactly
when it cannot exchange two genuine elements). -/
def swapPos {α : Type _} (i j : Nat) (l : List α) : List α :=
  match l[i]?, l[j]? with
  | some a, some b => (l.set i b).set j a
  | _, _ => l

/-- The `0 ↔ d+1` transposition on a single stack position (the permutation
`Instr.type? (.swap d)` induces on slot indices). -/
def remapDepth (d : Nat) (i : Nat) : Nat :=
  if i = 0 then d + 1 else if i = d + 1 then 0 else i

/-- The `0 ↔ d+1` transposition on a whole stack shape. -/
def remapShape (d : Nat) (s : Shape) : Shape :=
  { s with slots := swapPos 0 (d + 1) s.slots }

/-- Recognizer for the *zero-width* body instructions — the ones that lower to
`[]` and run as `.ok state`. -/
def isZeroWidth : Instr → Bool
  | .bindLocals _ _ => true
  | .bindScratch _ _ _ => true
  | .relabel _ => true
  | _ => false

/-- Conjugate a zero-width instruction's position parameters by the `0 ↔ d+1`
transposition.  Non-zero-width instructions are returned unchanged. -/
def remapZeroWidth (d : Nat) : Instr → Instr
  | .bindLocals offset names => .bindLocals (remapDepth d offset) names
  | .bindScratch baseDepth name slot => .bindScratch (remapDepth d baseDepth) name slot
  | .relabel target => .relabel (remapShape d target)
  | other => other

/-- The zero-width instructions whose `remapZeroWidth` residue is a single
shape-preserving instruction: `bindScratch`, `relabel`, and single-name
`bindLocals`.  Multi-name `bindLocals` (a straddling range) is excluded — its
transposition image is non-contiguous, so it cannot be a single `bindLocals` with
the same name list (see PEEPHOLE_PROGRESS §Session-57).  `normalizeBody` fires a
window only when EVERY intervening zero-width instruction is `RemapSafe`, which
makes the transform sound-by-construction. -/
def RemapSafe : Instr → Bool
  | .bindLocals _ names => names.length = 1
  | .bindScratch _ _ _ => true
  | .relabel _ => true
  | _ => false

theorem remapSafe_isZeroWidth {z : Instr} (h : RemapSafe z = true) :
    isZeroWidth z = true := by
  cases z <;> simp_all [RemapSafe, isZeroWidth]

/-- Split a body into its maximal leading run of zero-width instructions and the
remainder (which — when non-empty — begins with a non-zero-width instruction). -/
def leadingZeroWidth : List Instr → List Instr × List Instr
  | [] => ([], [])
  | instr :: rest =>
      if isZeroWidth instr then
        let split := leadingZeroWidth rest
        (instr :: split.1, split.2)
      else
        ([], instr :: rest)

theorem leadingZeroWidth_length (body : List Instr) :
    (leadingZeroWidth body).1.length + (leadingZeroWidth body).2.length =
      body.length := by
  induction body with
  | nil => rfl
  | cons instr rest ih =>
      unfold leadingZeroWidth
      by_cases h : isZeroWidth instr
      · simp only [h, if_true]
        simp only [List.length_cons]
        omega
      · simp only [h, if_false]
        simp [List.length_cons]

theorem leadingZeroWidth_snd_length_le (body : List Instr) :
    (leadingZeroWidth body).2.length ≤ body.length := by
  have h := leadingZeroWidth_length body
  omega

/-- Cancel `swap d ; z* ; swap d` windows in a straight-line body, remapping the
intervening zero-width instructions through the `0 ↔ d+1` transposition.

Recursion is well-founded on the body length: the firing branch continues on a
strict suffix `rest'` obtained after consuming `swap d`, the zero-width run, and
the closing `swap d`. -/
def normalizeBody : List Instr → List Instr
  | [] => []
  | .swap d :: rest =>
      match hTail : (leadingZeroWidth rest).2 with
      | .swap d' :: rest' =>
          if d = d' ∧ (leadingZeroWidth rest).1.all RemapSafe = true then
            (leadingZeroWidth rest).1.map (remapZeroWidth d) ++ normalizeBody rest'
          else
            .swap d :: normalizeBody rest
      | _ => .swap d :: normalizeBody rest
  | instr :: rest => instr :: normalizeBody rest
termination_by body => body.length
decreasing_by
  · -- firing branch: rest' is a strict suffix of `rest`, hence of `swap d :: rest`.
    have hlen := leadingZeroWidth_length rest
    have hsuf : (leadingZeroWidth rest).2.length = rest'.length + 1 := by
      rw [hTail]; simp
    simp only [List.length_cons]
    omega
  · simp only [List.length_cons]; omega
  · simp only [List.length_cons]; omega
  · simp only [List.length_cons]; omega

/-! ## Syntactic properties (step 2) -/

/-- `remapZeroWidth` never changes an instruction's zero-width classification. -/
@[simp] theorem isZeroWidth_remapZeroWidth (d : Nat) (instr : Instr) :
    isZeroWidth (remapZeroWidth d instr) = isZeroWidth instr := by
  cases instr <;> rfl

/-- `remapZeroWidth` fixes every non-zero-width instruction. -/
theorem remapZeroWidth_of_not_zeroWidth (d : Nat) {instr : Instr}
    (h : isZeroWidth instr = false) : remapZeroWidth d instr = instr := by
  cases instr <;> first | rfl | (simp [isZeroWidth] at h)

/-- Every instruction in a maximal zero-width prefix is zero-width. -/
theorem leadingZeroWidth_fst_all_zeroWidth (body : List Instr) :
    ∀ instr ∈ (leadingZeroWidth body).1, isZeroWidth instr = true := by
  induction body with
  | nil => intro instr h; simp [leadingZeroWidth] at h
  | cons head rest ih =>
      intro instr hMem
      unfold leadingZeroWidth at hMem
      by_cases h : isZeroWidth head
      · simp only [h, if_true] at hMem
        simp only [List.mem_cons] at hMem
        cases hMem with
        | inl hEq => exact hEq ▸ h
        | inr hTail => exact ih instr hTail
      · simp only [h, if_false] at hMem
        simp at hMem

/-- The remainder after the maximal zero-width prefix is a suffix of the body:
`leadingZeroWidth body = (pre, suf)` with `body = pre ++ suf`. -/
theorem leadingZeroWidth_append (body : List Instr) :
    (leadingZeroWidth body).1 ++ (leadingZeroWidth body).2 = body := by
  induction body with
  | nil => rfl
  | cons head rest ih =>
      unfold leadingZeroWidth
      cases h : isZeroWidth head with
      | true => simp only [h, if_true, List.cons_append, ih]
      | false => simp [h]

/-! ### Unfolding lemmas for the well-founded `normalizeBody` -/

/-- Firing arm: a `swap d ; z* ; swap d` window with an all-`RemapSafe` interior
run collapses to the remapped run. -/
theorem normalizeBody_fire (d : Nat) (rest rest' : List Instr)
    (hTail : (leadingZeroWidth rest).2 = Instr.swap d :: rest')
    (hSafe : (leadingZeroWidth rest).1.all RemapSafe = true) :
    normalizeBody (Instr.swap d :: rest)
      = (leadingZeroWidth rest).1.map (remapZeroWidth d) ++ normalizeBody rest' := by
  rw [normalizeBody, hTail]; simp [hSafe]

/-- Kept arm: the closing swap has a different depth. -/
theorem normalizeBody_keep_swap (d d' : Nat) (rest rest' : List Instr)
    (hTail : (leadingZeroWidth rest).2 = Instr.swap d' :: rest') (hNe : d ≠ d') :
    normalizeBody (Instr.swap d :: rest) = Instr.swap d :: normalizeBody rest := by
  rw [normalizeBody, hTail]; simp [hNe]

/-- Kept arm: the window closes on the same depth but the interior run contains a
non-`RemapSafe` instruction, so firing is suppressed. -/
theorem normalizeBody_keep_unsafe (d d' : Nat) (rest rest' : List Instr)
    (hTail : (leadingZeroWidth rest).2 = Instr.swap d' :: rest')
    (hUnsafe : (leadingZeroWidth rest).1.all RemapSafe = false) :
    normalizeBody (Instr.swap d :: rest) = Instr.swap d :: normalizeBody rest := by
  rw [normalizeBody, hTail]; simp [hUnsafe]

/-- Kept arm: no closing swap after the zero-width run. -/
theorem normalizeBody_keep_noTail (d : Nat) (rest : List Instr)
    (hNoTail : ∀ d' rest', (leadingZeroWidth rest).2 ≠ Instr.swap d' :: rest') :
    normalizeBody (Instr.swap d :: rest) = Instr.swap d :: normalizeBody rest := by
  rw [normalizeBody]
  split
  · rename_i d' rest' hEq; exact absurd hEq (hNoTail d' rest')
  · rfl

/-- Generic arm: a non-swap head is kept verbatim. -/
theorem normalizeBody_cons_generic (instr : Instr) (rest : List Instr)
    (hNotSwap : ∀ d, instr ≠ Instr.swap d) :
    normalizeBody (instr :: rest) = instr :: normalizeBody rest := by
  cases instr with
  | swap d => exact absurd rfl (hNotSwap d)
  | _ => simp only [normalizeBody]

/-- The normalization never grows a body. -/
theorem normalizeBody_length_le :
    ∀ body : List Instr, (normalizeBody body).length ≤ body.length := by
  intro body
  induction body using normalizeBody.induct with
  | case1 => simp [normalizeBody]
  | case2 d rest d' rest' hTail hGuard ih =>
      -- firing branch: `swap d ; z* ; swap d'` with `d = d'` and an all-safe run.
      obtain ⟨hdd, hSafe⟩ := hGuard
      subst hdd
      rw [normalizeBody_fire d rest rest' hTail hSafe]
      have hlen := leadingZeroWidth_length rest
      have hsuf : (leadingZeroWidth rest).2.length = rest'.length + 1 := by
        rw [hTail]; simp
      simp only [List.length_append, List.length_map, List.length_cons]
      omega
  | case3 d rest d' rest' hTail hGuard ih =>
      -- window opens with `swap d ; z* ; swap d'` but the guard fails — kept.
      have hkeep : normalizeBody (Instr.swap d :: rest)
          = Instr.swap d :: normalizeBody rest := by
        by_cases hdd : d = d'
        · have hUnsafe : (leadingZeroWidth rest).1.all RemapSafe = false := by
            by_contra hne
            simp only [Bool.not_eq_false] at hne
            exact hGuard ⟨hdd, hne⟩
          exact normalizeBody_keep_unsafe d d' rest rest' hTail hUnsafe
        · exact normalizeBody_keep_swap d d' rest rest' hTail hdd
      rw [hkeep, List.length_cons, List.length_cons]
      omega
  | case4 d rest hNoTail ih =>
      -- window opens with `swap d` but no closing swap — kept.
      rw [normalizeBody_keep_noTail d rest
        (fun d' rest' h => hNoTail d' rest' h), List.length_cons, List.length_cons]
      omega
  | case5 instr rest hNotSwap ih =>
      -- generic instruction: `instr :: normalizeBody rest`.
      rw [normalizeBody_cons_generic instr rest (fun d h => hNotSwap d h),
        List.length_cons, List.length_cons]
      omega

end Peephole
end TypedCfg
end EvmCompiler
