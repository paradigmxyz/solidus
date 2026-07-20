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
          if d = d' then
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

end Peephole
end TypedCfg
end EvmCompiler
