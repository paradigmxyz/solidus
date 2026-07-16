import EvmCompiler.Assembly.StackShufflePreservation
import EvmCompiler.Assembly.StateRelation

/-!
# Depth-guarded `swap n ; swap n → ε` involution kernel

Milestone (a-swap) of the adjacent-inverse-shuffle peephole, swap arm.

The `push v ; pop` cancellation is *unconditionally* stack-shape-neutral, so its
kernel lemma (`PeepholeKernel.pop_after_push_sameRuntimeData`) needs no side
condition.  The `swap n ; swap n` cancellation is different: `swap n` is a
*conditional* involution.  `EvmYul.swap n` reads the top `n + 1` stack elements;
on a stack shallower than `n + 1` it errors (`StackUnderflow`) where the empty
program `ε` would succeed, so unconditional cancellation is UNSOUND.  The
cancellation is sound exactly when the runtime stack is at least `n + 1` deep —
the depth the typing invariant (`Instr.type? (.swap depth)` requires
`depth + 2 ≤ shape.length`, i.e. `EvmYul.swap (depth+1)` sees `≥ depth + 2`
elements) guarantees at every program point of a well-typed body.

This module isolates the purely semantic fact under that explicit depth guard:
running `swap n` twice on a stack of depth `≥ n + 1` restores the stack exactly
and perturbs only the (unobserved) program counter, i.e. yields a state that is
`Assembly.SameRuntimeData` to the input.  Uniform in `n` (no 16-way case split),
phrased at the `EvmYul.swap` transformer level so a later wiring pass can bridge
it to `Instr.runState (.swap depth)` by the trivial `swap{depth+1}` dispatch
(cf. `Assembly.StackShuffle.swapInstr_step_eq_swap`).

Kept standalone from `PeepholeKernel.lean` / `Peephole.lean` so the landed,
green `push v ; pop` tower is untouched while the swap arm is developed.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState SameRuntimeData eraseRuntimeControl)

/-- A list of length `≥ m + 1` (with `m ≥ 1`) splits as
`top :: front ++ [last] ++ suffix` with `front.length + 1 = m`, i.e. `top` is the
stack head and `last` is the element `swap m` exchanges it with. -/
theorem exists_swap_decomp {α : Type _} (L : List α) (m : Nat)
    (hm : 1 ≤ m) (hlen : m + 1 ≤ L.length) :
    ∃ (top last : α) (front suffix : List α),
      L = top :: front ++ [last] ++ suffix ∧ front.length + 1 = m := by
  cases L with
  | nil => simp at hlen
  | cons top rest =>
      have hrest : m ≤ rest.length := by simpa using hlen
      have hdrop : 1 ≤ (rest.drop (m - 1)).length := by
        rw [List.length_drop]; omega
      obtain ⟨last, suffix, hls⟩ :
          ∃ last suffix, rest.drop (m - 1) = last :: suffix := by
        cases h : rest.drop (m - 1) with
        | nil => rw [h] at hdrop; simp at hdrop
        | cons a t => exact ⟨a, t, rfl⟩
      refine ⟨top, last, rest.take (m - 1), suffix, ?_, ?_⟩
      · have hsplit : rest = rest.take (m - 1) ++ rest.drop (m - 1) :=
          (List.take_append_drop (m - 1) rest).symm
        rw [hls] at hsplit
        conv_lhs => rw [hsplit]
        simp [List.append_assoc]
      · rw [List.length_take]; omega

/-- **Depth-guarded swap involution kernel (the swap-arm analogue of
`pop_after_push_sameRuntimeData`).**  On a stack of depth `≥ n + 1`, running
`EvmYul.swap n` twice succeeds both times and restores all runtime data: the
final state is `SameRuntimeData` to the input (only the program counter has
advanced).  This is exactly the semantic content that justifies cancelling an
adjacent `swap n ; swap n` pair — and it is FALSE without the depth guard, which
is why the swap arm requires the depth-typing invariant that `push v ; pop` did
not. -/
theorem swap_swap_sameRuntimeData (s : EVMState) (n : Nat)
    (hn : 1 ≤ n) (hDepth : n + 1 ≤ s.stack.length) :
    ∃ s1 s2, EvmYul.swap n s = .ok s1 ∧ EvmYul.swap n s1 = .ok s2 ∧
      SameRuntimeData s2 s := by
  obtain ⟨top, last, front, suffix, hStack, hfront⟩ :=
    exists_swap_decomp s.stack n hn hDepth
  -- First swap: exchanges `top` and `last`.
  have h1 : EvmYul.swap n s =
      .ok (s.replaceStackAndIncrPC (last :: front ++ [top] ++ suffix)) := by
    have hsn := Assembly.StackShuffle.swap_snoc
      (state := s) (front := front) (suffix := suffix) (top := top) (last := last)
    rw [hfront] at hsn
    rw [← hStack] at hsn
    exact hsn
  set s1 := s.replaceStackAndIncrPC (last :: front ++ [top] ++ suffix) with hs1
  -- `s1`'s stack is the swapped list.
  have hs1stack : s1.stack = last :: front ++ [top] ++ suffix := by
    simp [hs1, EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]
  -- Second swap on `s1`: exchanges `last` and `top` back, restoring `s.stack`.
  have h2 : EvmYul.swap n s1 =
      .ok (s1.replaceStackAndIncrPC (top :: front ++ [last] ++ suffix)) := by
    have hsn := Assembly.StackShuffle.swap_snoc
      (state := s1) (front := front) (suffix := suffix) (top := last) (last := top)
    rw [hfront] at hsn
    rw [← hs1stack] at hsn
    exact hsn
  refine ⟨s1, s1.replaceStackAndIncrPC (top :: front ++ [last] ++ suffix), h1, h2, ?_⟩
  -- The restored stack equals the original one, so only pc/execLength differ.
  have hrestore : top :: front ++ [last] ++ suffix = s.stack := hStack.symm
  rw [hrestore]
  -- `s1.replaceStackAndIncrPC s.stack` is `SameRuntimeData` to `s`.
  cases s with
  | mk shared pc stack execLength =>
      simp only [hs1, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, SameRuntimeData, eraseRuntimeControl]

end Peephole
end TypedCfg
end EvmCompiler
