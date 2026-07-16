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

end Peephole
end TypedCfg
end EvmCompiler
