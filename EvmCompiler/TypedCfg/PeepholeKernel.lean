import EvmCompiler.TypedCfg.Semantics
import EvmCompiler.Assembly.StateRelation

/-!
# Peephole semantic kernel

Milestone (a) of the adjacent-inverse-shuffle peephole: the purely semantic
facts that justify cancelling redundant instruction pairs, phrased over the
`Assembly.EVMState` transformer level so they are reusable by both the
`TypedCfg` block semantics (`runState` / `runBody`) and the assembly
refinement.

The observable relation is `Assembly.SameRuntimeData`, which erases only the
compiler-owned control counters (`pc`, `execLength`); it retains stack, memory,
storage, gas, logs and every other runtime datum.  Cancelling a
`push v ; pop` pair (or a `swap n ; swap n` / `dup n ; pop` pair) leaves the
runtime data untouched and only perturbs the (unobserved) program counter, so
each kernel lemma concludes with `SameRuntimeData`.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState SameRuntimeData)

/-- The state reached by pushing `v` and then popping it: the stack is restored
and only the program counter has advanced. -/
theorem pop_after_push_sameRuntimeData
    (s : EVMState) (v : Word) (k : Nat) :
    ∃ s',
      Assembly.PrimOp.pop.step
          (s.replaceStackAndIncrPC (s.stack.push v) k) = .ok s' ∧
        SameRuntimeData s' s := by
  refine
    ⟨(s.replaceStackAndIncrPC (s.stack.push v) k).replaceStackAndIncrPC
        s.stack, ?_, ?_⟩
  · -- `pop` sees a `cons` stack (the just-pushed value), so it succeeds.
    simp [Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
      Assembly.PrimStep.run, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, EvmYul.Stack.push, EvmYul.Stack.pop]
  · -- The resulting state differs from `s` only in `pc`.
    cases s with
    | mk shared pc stack execLength =>
        simp [SameRuntimeData, Assembly.eraseRuntimeControl,
          EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC,
          EvmYul.Stack.push, EvmYul.Stack.pop]

/-- **`push v ; push v → push v ; dup 0` kernel.**  On a state whose stack top
is `v`, `DUP1` succeeds and reaches exactly the runtime data of pushing `v` a
second time — the stacks are literally equal (`v :: v :: rest`), only the
(unobserved) program counter differs.  Unlike the swap involution this needs no
depth guard: a state with a `cons` stack is deep enough for `dup1` by
construction, and the rewrite's own `push v` always supplies one.

The rewrite is byte-profitable because `dup 0` lowers to the single byte
`DUP1` where the repeated `push v` lowers to `1 + width v` bytes. -/
theorem dup1_after_push_sameRuntimeData
    (s : EVMState) (v : Word) (rest : List Word)
    (hStack : s.stack = v :: rest) (k : Nat) :
    ∃ s',
      Assembly.PrimOp.dup1.step s = .ok s' ∧
        SameRuntimeData s' (s.replaceStackAndIncrPC (s.stack.push v) k) := by
  refine ⟨s.replaceStackAndIncrPC (v :: s.stack), ?_, ?_⟩
  · -- `dup1` reads `stack.take 1 = [v]` and re-pushes its last element.
    show EvmYul.dup 1 s = _
    simp [EvmYul.dup, hStack]
  · -- Same stack (`v :: v :: rest`); only `pc` differs.
    cases s with
    | mk shared pc stack execLength =>
        simp [SameRuntimeData, Assembly.eraseRuntimeControl,
          EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC,
          EvmYul.Stack.push]

end Peephole
end TypedCfg
end EvmCompiler
