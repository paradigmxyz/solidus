import EvmCompiler.TypedCfg.ShuffleCanonChain
import EvmCompiler.TypedCfg.PeepholeSeamCancelEffRuntime

/-!
# Runtime pending-permutation kernel for the chain transform (session-79)

Item 2 of the PEEPHOLE_PROGRESS §Session-74..78 campaign: the `PendingPerm σ`
runtime tower generalising the §62-67 `PendingSwap d` machinery from a single
`swap (d+1)` residual to a residual *permutation* accumulated across a fired
fallthrough chain.

The genuinely-new content — repeatedly deferred by §75-78 as "the bulk of the
next session" — is the **runtime net-permutation realisation**: a run of `.swap`
instructions realises the banked type-level `applySwaps` on the concrete stack,
and two runs with equal `netStack` land in `SameRuntimeData` (the "resync at chain
exit … the §76 P1/P2 algebra proves the states re-converge" crux).  This leaf
banks that crux and the `PendingPerm σ` invariant it feeds.

Imported by **nobody** in the spine ⟹ cannot affect the `compile_correct` axioms.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState SameRuntimeData eraseRuntimeControl)

/-! ## Part A — a single `EvmYul.swap` realises `applySwap` on the stack -/

/-- `applySwap` on a `swap`-decomposed list: exchanging positions `0` and
`front.length + 1` of `top :: front ++ [last] ++ suffix` gives
`last :: front ++ [top] ++ suffix`. -/
theorem applySwap_swap_decomp {α : Type _} (top last : α) (front suffix : List α) :
    ShuffleCanon.applySwap (front.length + 1)
        (top :: front ++ [last] ++ suffix)
      = last :: front ++ [top] ++ suffix := by
  have h0 : (top :: front ++ [last] ++ suffix)[0]? = some top := by simp
  have hn : (top :: front ++ [last] ++ suffix)[front.length + 1]? = some last := by
    have hrw : top :: front ++ [last] ++ suffix
        = top :: (front ++ (last :: suffix)) := by simp
    rw [hrw, List.getElem?_cons_succ]
    rw [List.getElem?_append_right (by omega)]
    simp
  unfold ShuffleCanon.applySwap
  rw [h0, hn]
  show ((top :: front ++ [last] ++ suffix).set 0 last).set (front.length + 1) top
      = last :: front ++ [top] ++ suffix
  have hset0 : (top :: front ++ [last] ++ suffix).set 0 last
      = last :: (front ++ (last :: suffix)) := by simp
  rw [hset0]
  rw [List.set_cons_succ]
  have hsetr : (front ++ (last :: suffix)).set front.length top
      = front ++ (top :: suffix) := by
    rw [List.set_append_right front.length top (Nat.le_refl _)]
    simp
  rw [hsetr]
  simp

/-- **A single `EvmYul.swap n` realises `applySwap n` on the stack.**  On a stack
of depth `≥ n + 1` (which the typing invariant guarantees), `swap n` succeeds and
its result is `s` with the stack replaced by `applySwap n s.stack` (and the pc
advanced — the only runtime-invisible change). -/
theorem swap_eq_of_depth {n : Nat} {s : EVMState} (hn : 1 ≤ n)
    (hlen : n + 1 ≤ s.stack.length) :
    EvmYul.swap n s
      = .ok (s.replaceStackAndIncrPC (ShuffleCanon.applySwap n s.stack)) := by
  obtain ⟨top, last, front, suffix, hStack, hfront⟩ :=
    exists_swap_decomp s.stack n hn hlen
  have hs : ({ s with stack := top :: front ++ [last] ++ suffix } : EVMState) = s := by
    rw [← hStack]
  have hswap := Assembly.StackShuffle.swap_snoc
    (state := s) (front := front) (suffix := suffix) (top := top) (last := last)
  rw [hfront, hs] at hswap
  rw [hswap]
  congr 1
  have hAp : ShuffleCanon.applySwap n s.stack
      = last :: front ++ [top] ++ suffix := by
    rw [← hfront, hStack]
    exact applySwap_swap_decomp top last front suffix
  rw [hAp]

/-! ## Part B — a run of `EvmYul.swap`s realises `applySwaps` on the stack -/

/-- Fold `EvmYul.swap` over a list of *positions* (`p = depth + 1`), left to right
— the runtime action of a cfg `.swap`-run, mirroring `applySwaps`/`netStack`. -/
def runSwaps : List Nat → EVMState → Except EVMException EVMState
  | [], s => .ok s
  | p :: rest, s =>
      match EvmYul.swap p s with
      | .ok s' => runSwaps rest s'
      | .error e => .error e

@[simp] theorem runSwaps_nil (s : EVMState) : runSwaps [] s = .ok s := rfl

theorem replaceStack_stack (s : EVMState) (st : List EvmYul.UInt256) (pcΔ : Nat) :
    (s.replaceStackAndIncrPC st pcΔ).stack = st := rfl

theorem replaceStack_shared (s : EVMState) (st : List EvmYul.UInt256) (pcΔ : Nat) :
    (s.replaceStackAndIncrPC st pcΔ).toSharedState = s.toSharedState := by
  simp [EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]

/-- **A depth-feasible swap run succeeds and realises `applySwaps` on the stack**,
preserving all shared runtime data (only pc/execLength — both SRD-erased — move).
The uniform depth guard `∀ p ∈ ps, p + 1 ≤ s.stack.length` is length-stable
because `applySwap` preserves length. -/
theorem runSwaps_ok :
    ∀ (ps : List Nat) (s : EVMState),
      (∀ p ∈ ps, 1 ≤ p) →
      (∀ p ∈ ps, p + 1 ≤ s.stack.length) →
      ∃ s', runSwaps ps s = .ok s' ∧
        s'.stack = ShuffleCanon.applySwaps ps s.stack ∧
        s'.toSharedState = s.toSharedState
  | [], s, _, _ => ⟨s, rfl, by simp, rfl⟩
  | p :: rest, s, hpos, hlen => by
      have hp1 : 1 ≤ p := hpos p (List.mem_cons_self)
      have hpl : p + 1 ≤ s.stack.length := hlen p (List.mem_cons_self)
      have hswap := swap_eq_of_depth hp1 hpl
      set s1 := s.replaceStackAndIncrPC (ShuffleCanon.applySwap p s.stack) with hs1
      have hs1stack : s1.stack = ShuffleCanon.applySwap p s.stack :=
        replaceStack_stack _ _ _
      have hs1len : s1.stack.length = s.stack.length := by
        rw [hs1stack, ShuffleCanon.length_applySwap]
      have hlen' : ∀ q ∈ rest, q + 1 ≤ s1.stack.length := by
        intro q hq; rw [hs1len]; exact hlen q (List.mem_cons_of_mem _ hq)
      have hpos' : ∀ q ∈ rest, 1 ≤ q := fun q hq => hpos q (List.mem_cons_of_mem _ hq)
      obtain ⟨s', hrun', hstk', hshared'⟩ := runSwaps_ok rest s1 hpos' hlen'
      refine ⟨s', ?_, ?_, ?_⟩
      · show (match EvmYul.swap p s with
              | .ok s'' => runSwaps rest s'' | .error e => .error e) = .ok s'
        rw [hswap]; exact hrun'
      · rw [hstk', hs1stack, ShuffleCanon.applySwaps_cons]
      · rw [hshared', hs1, replaceStack_shared]

/-! ## Part C — the resync crux: equal `netStack` runs land `SameRuntimeData` -/

/-- `SameRuntimeData` from equal shared state and equal stack (pc/execLength are
erased). -/
theorem sameRuntimeData_of {s1 s2 : EVMState}
    (hshared : s1.toSharedState = s2.toSharedState) (hstack : s1.stack = s2.stack) :
    SameRuntimeData s1 s2 := by
  cases s1 with
  | mk sh1 pc1 st1 el1 =>
    cases s2 with
    | mk sh2 pc2 st2 el2 =>
      simp_all [SameRuntimeData, eraseRuntimeControl]

/-- **The resync crux (the §76 P1/P2 algebra, at runtime).**  Two depth-feasible
`.swap`-runs `ps`, `qs` with the *same* `netStack` over the stack window, launched
from the same state, land in `SameRuntimeData` states.  This is exactly the fact
that "net permutations equal by construction ⟹ the states re-converge" (item 2
resync at chain exit): both realise the same `applySwaps` on the stack, and swaps
touch nothing else runtime-visible. -/
theorem runSwaps_resync {ps qs : List Nat} {s : EVMState}
    (hpos_p : ∀ p ∈ ps, 1 ≤ p) (hpos_q : ∀ q ∈ qs, 1 ≤ q)
    (hlen_p : ∀ p ∈ ps, p + 1 ≤ s.stack.length)
    (hlen_q : ∀ q ∈ qs, q + 1 ≤ s.stack.length)
    (hnet : ShuffleCanon.netStack ps s.stack.length
      = ShuffleCanon.netStack qs s.stack.length) :
    ∃ s1 s2, runSwaps ps s = .ok s1 ∧ runSwaps qs s = .ok s2 ∧
      SameRuntimeData s1 s2 := by
  obtain ⟨s1, hr1, hstk1, hsh1⟩ := runSwaps_ok ps s hpos_p hlen_p
  obtain ⟨s2, hr2, hstk2, hsh2⟩ := runSwaps_ok qs s hpos_q hlen_q
  refine ⟨s1, s2, hr1, hr2, ?_⟩
  apply sameRuntimeData_of
  · rw [hsh1, hsh2]
  · rw [hstk1, hstk2]
    exact ShuffleCanon.applySwaps_congr_of_netStack ps qs s.stack hnet
