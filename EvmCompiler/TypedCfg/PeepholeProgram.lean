import EvmCompiler.TypedCfg.PeepholeOpen

/-!
# Peephole as a whole-program transform (`Program → Program`)

Milestone (e): package the block-body peephole as a `Program → Program`
transform `peepholeProgram` (labels / terminators / block CFG untouched; only
straight-line bodies are `push v ; pop`-cancelled), prove it preserves
`ProgramCounterIndependent`, and lift the open per-block congruence
(`Peephole.Block.openRun_peephole_runtimeRel`) to a WHOLE-PROGRAM congruence on
the fuel-bounded open runners `openStep` / `openRunN` / `openRunNPrefix`.

The whole-program congruence relates the ORIGINAL program run from `state1` to
the PEEPHOLED program run from any `SameRuntimeData`-equivalent `state2`
(original on the left).  This is the exact shape the public compile spine's
prefix-preservation consumes via `Rel.executes` and `OpenBlock.runtime_left`.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState SameRuntimeData)
open InteractionSemantics
open InteractionCongruence

/-- Peephole every block body of a program; the CFG (labels/terminators) is
untouched. -/
def peepholeProgram (program : Program) : Program :=
  { program with blocks := program.blocks.map peepholeBlock }

@[simp] theorem peepholeProgram_entry (program : Program) :
    (peepholeProgram program).entry = program.entry := rfl

@[simp] theorem peepholeProgram_blocks (program : Program) :
    (peepholeProgram program).blocks = program.blocks.map peepholeBlock := rfl

/-- Block lookup commutes with the peephole (labels are preserved). -/
theorem findBlock?_peepholeProgram (program : Program) (label : Label) :
    (peepholeProgram program).findBlock? label =
      (program.findBlock? label).map peepholeBlock := by
  simp only [peepholeProgram, Program.findBlock?]
  induction program.blocks with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.map_cons, List.find?_cons, peepholeBlock_label]
      by_cases h : (b.label == label) = true
      · simp [h]
      · simp only [h, Bool.false_eq_true, if_false]
        exact ih

/-- The peephole preserves whole-program `ProgramCounterIndependent`. -/
theorem peepholeProgram_programCounterIndependent {program : Program}
    (h : program.ProgramCounterIndependent) :
    (peepholeProgram program).ProgramCounterIndependent := by
  unfold Program.ProgramCounterIndependent at h ⊢
  rw [peepholeProgram_blocks]
  rw [List.forall_iff_forall_mem] at h ⊢
  intro b hb
  rw [List.mem_map] at hb
  obtain ⟨b0, hb0, rfl⟩ := hb
  have hb0Ind := h b0 hb0
  unfold Block.ProgramCounterIndependent at hb0Ind ⊢
  simpa only [peepholeBlock_body] using forall_pcIndependent_peephole hb0Ind

/-- `RuntimeOutcomeRel` is symmetric. -/
theorem runtimeOutcomeRel_symm
    {a b : Except EVMException TypedCfg.Outcome}
    (h : InteractionCongruence.Block.RuntimeOutcomeRel a b) :
    InteractionCongruence.Block.RuntimeOutcomeRel b a := by
  cases h with
  | error he => exact .error he.symm
  | ok ho => exact .ok ho.symm

/-- `RuntimeOutcomeRel` is transitive. -/
theorem runtimeOutcomeRel_trans
    {a b c : Except EVMException TypedCfg.Outcome}
    (h1 : InteractionCongruence.Block.RuntimeOutcomeRel a b)
    (h2 : InteractionCongruence.Block.RuntimeOutcomeRel b c) :
    InteractionCongruence.Block.RuntimeOutcomeRel a c := by
  cases h1 with
  | error he1 => cases h2 with | error he2 => exact .error (he1.trans he2)
  | ok ho1 => cases h2 with | ok ho2 => exact .ok (ho1.trans ho2)

/-- Flip a `Rel` over `RuntimeOutcomeRel`. -/
theorem rel_runtimeOutcomeRel_symm
    {X Y : InteractionSemantics.OpenOutcome}
    (h : Simulation.Interaction.Rel InteractionCongruence.Block.RuntimeOutcomeRel
      X Y) :
    Simulation.Interaction.Rel InteractionCongruence.Block.RuntimeOutcomeRel
      Y X :=
  (h.symm).mono (fun _ _ hab => runtimeOutcomeRel_symm hab)

/-- **One-step whole-program peephole congruence.** The original program stepped
from `state1` and the peepholed program stepped from any
`SameRuntimeData`-equivalent `state2` expose the same open interaction up to
`RuntimeOutcomeRel`. -/
theorem openStep_peephole_congr {program : Program} {label : Label}
    {state1 state2 : EVMState}
    (hTyped : program.WellTyped)
    (hIndependent : program.ProgramCounterIndependent)
    (hReal2 : ∀ block, program.findBlock? label = some block →
      StackRealizes block.input state2)
    (hRel : SameRuntimeData state1 state2) :
    Simulation.Interaction.Rel InteractionCongruence.Block.RuntimeOutcomeRel
      (InteractionSemantics.Program.openStep program label state1)
      (InteractionSemantics.Program.openStep (peepholeProgram program)
        label state2) := by
  unfold InteractionSemantics.Program.openStep Control.Program.step
  rw [findBlock?_peepholeProgram]
  cases hFind : program.findBlock? label with
  | none =>
      simp only [hFind, Option.map_none]
      exact .done (.ok (Outcome.RuntimeRel.invalid hRel))
  | some block =>
      simp only [hFind, Option.map_some]
      have hMem : block ∈ program.blocks := List.mem_of_find?_eq_some hFind
      have hBlockTyped : block.WellTyped program :=
        (List.forall_iff_forall_mem.mp hTyped.2.1) block hMem
      have hBlockIndep : block.ProgramCounterIndependent :=
        (List.forall_iff_forall_mem.mp hIndependent) block hMem
      have h1 :
          Simulation.Interaction.Rel
            InteractionCongruence.Block.RuntimeOutcomeRel
            (InteractionSemantics.Block.openRun block state1)
            (InteractionSemantics.Block.openRun block state2) :=
        InteractionCongruence.Block.openRun_runtimeRel
          hBlockTyped hBlockIndep hRel
      have h2 :
          Simulation.Interaction.Rel
            InteractionCongruence.Block.RuntimeOutcomeRel
            (InteractionSemantics.Block.openRun (peepholeBlock block) state2)
            (InteractionSemantics.Block.openRun block state2) :=
        Block.openRun_peephole_runtimeRel block state2 hBlockTyped hBlockIndep
          (hReal2 block hFind)
      refine Simulation.Interaction.Rel.mono
        (Simulation.Interaction.Rel.trans h1 (rel_runtimeOutcomeRel_symm h2)) ?_
      rintro l r ⟨m, ha, hb⟩
      exact runtimeOutcomeRel_trans ha hb

/-
**Fuel-bounded / prefix whole-program peephole congruences.**

The guard-free unconditional whole-program congruences (`openRunN_peephole_congr`,
`openRunNPrefix_peephole_congr`) can no longer be stated once the block-body
peephole carries the `swap d ; swap d → ε` arm: the per-block congruence acquires
a runtime depth guard (`StackRealizes block.input state`) that must be discharged
at EVERY reached block entry, which no static whole-program invariant supplies.
The source-threaded variants
(`Structured.…PeepholeSourceCongr.openRunN_peephole_congr_of_source`,
`openRunNPrefix_peephole_congr_of_source`) supersede them: they carry the
strengthened entry witness `realizedWitnessFC` and re-establish it at each jump
target, discharging the guard via `stackRealizes_of_realizedWitnessFC_total`.
Those are the variants the five OIC consumption sites use.  The one-step building
block `openStep_peephole_congr` (above) is retained with the per-found-block
`StackRealizes` guard hypothesis; the source-threaded step congruence supplies it.
-/

end Peephole
end TypedCfg
end EvmCompiler
