import EvmCompiler.TypedCfg.PeepholeSemantics
import EvmCompiler.TypedCfg.InteractionCongruence

/-!
# Peephole preservation at the closed block level (`Block.run`)

Milestone (c-block): lift the closed `runBody` congruence
(`PeepholeSemantics.peepholeBody_runBody_erase`) through the block terminator up
to the whole `Block.run`.

The terminator half is *already available* as the pass-agnostic congruence
`InteractionCongruence.Block.runTermChecked_runtimeRel`: on `SameRuntimeData`
inputs the checked terminator interpreter produces
`Block.RuntimeOutcomeRel`-related results (equal control label, equal halt kind,
`SameRuntimeData` carried state).  The peephole only perturbs the (unobserved)
control counters of the body-end state, so it composes directly.

The new content here is the *different-body* congruence: whereas
`InteractionCongruence.Block.*_runtimeRel` relate the **same** program run from
two `SameRuntimeData` states, `Block.run_peephole_runtimeRel` relates the
**peepholed** body to the **original** body run from the *same* state.  This is
the block-boundary reconciliation the lowering wiring needs: the emitted
(peepholed) assembly's byte shift is internally consistent, and this lemma
supplies the `RuntimeRel` witness that `OpenOutcome.Simulates.runtime_left`
consumes to transfer a `Simulates` proof from the peepholed run to the original.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState SameRuntimeData eraseRuntimeControl)

/-- From the `map eraseFst` equality produced by the closed `runBody`
congruence, extract the case-split: both errors (equal), or both successes with
equal output shape and `SameRuntimeData` final states. -/
theorem runBody_erase_cases
    {A B : List Instr} {shape : Shape} {state : EVMState}
    (hEq :
      (Block.runBody A shape state).map eraseFst =
        (Block.runBody B shape state).map eraseFst) :
    (∃ e, Block.runBody A shape state = .error e ∧
        Block.runBody B shape state = .error e) ∨
      (∃ mA oA mB oB,
        Block.runBody A shape state = .ok (mA, oA) ∧
          Block.runBody B shape state = .ok (mB, oB) ∧
            oA = oB ∧ SameRuntimeData mA mB) := by
  cases hA : Block.runBody A shape state with
  | error eA =>
      cases hB : Block.runBody B shape state with
      | error eB =>
          simp only [hA, hB, Except.map] at hEq
          exact Or.inl ⟨eA, rfl, Except.error.inj hEq ▸ rfl⟩
      | ok rB => simp [hA, hB, Except.map] at hEq
  | ok rA =>
      cases hB : Block.runBody B shape state with
      | error eB => simp [hA, hB, Except.map] at hEq
      | ok rB =>
          rcases rA with ⟨mA, oA⟩
          rcases rB with ⟨mB, oB⟩
          simp only [hA, hB, Except.map, eraseFst] at hEq
          have hPair := Except.ok.inj hEq
          have hShape : oA = oB := (Prod.mk.inj hPair).2
          have hErase : eraseRuntimeControl mA = eraseRuntimeControl mB :=
            (Prod.mk.inj hPair).1
          exact Or.inr ⟨mA, oA, mB, oB, rfl, rfl, hShape, hErase⟩

/-- **Peephole preservation (closed block level).** On a block whose body is
peephole-safe, cancelling `push v ; pop` pairs preserves `Block.run` up to the
pass-agnostic `RuntimeRel`: same control labels, same halt kinds, and
`SameRuntimeData` carried states.  Reuses the existing terminator congruence
`InteractionCongruence.Block.runTermChecked_runtimeRel`. -/
theorem Block.run_peephole_runtimeRel
    (block : Block) (state : EVMState)
    (hSafe : BodySafe block.body) :
    InteractionCongruence.Block.RuntimeOutcomeRel
      (Block.run { block with body := peepholeBody block.body } state)
      (Block.run block state) := by
  have hErase :=
    peepholeBody_runBody_erase block.body block.input state hSafe
  simp only [Block.run]
  rcases runBody_erase_cases hErase with
    ⟨e, hP, hO⟩ | ⟨mP, oP, mO, oO, hP, hO, hShape, hRel⟩
  · simp only [hP, hO, Bind.bind, Except.bind]
    exact Simulation.Interaction.ExceptRel.error rfl
  · subst hShape
    simp only [hP, hO, Bind.bind, Except.bind]
    by_cases hOut : oP = block.output
    · simp only [hOut, if_pos]
      exact InteractionCongruence.Block.runTermChecked_runtimeRel hRel
    · simp only [hOut, if_neg, if_false]
      exact Simulation.Interaction.ExceptRel.error rfl

end Peephole
end TypedCfg
end EvmCompiler
