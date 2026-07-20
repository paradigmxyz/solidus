import EvmCompiler.Structured.PeepholeNoopSwapSourceCongr
import EvmCompiler.Structured.PeepholeSourceCongr
import EvmCompiler.TypedCfg.PeepholeNoopSwapSpine
import EvmCompiler.TypedCfg.PeepholeNoopSwapFuel
import EvmCompiler.TypedCfg.PeepholeFuel

/-!
# The COMBINED transform `peepholeProgram (normalizeProgram cfg)` (session-59, item 2)

The splice route (PEEPHOLE_PROGRESS §Session-58 frontier).  We cannot apply the
peephole source-threaded congruence with `cfg := normalizeProgram cfg` because the
`GeneratedContext source entryShapes (normalizeProgram cfg)` it needs is FALSE (the
context asserts `cfg` IS the exact compiled program).  Instead we prove the combined
transform's source-threaded congruence *relative to the real compiled `cfg`* by
`Rel.trans`-composing:

* `openStep_normalize_congr_of_source` : `openStep cfg` ~ `openStep (normalizeProgram cfg)`
  (source-threaded, carrying the successor witness — the LEFT tree is `cfg`);
* `openStep_peephole_congr` : `openStep (normalizeProgram cfg)` ~
  `openStep (peepholeProgram (normalizeProgram cfg))` (the pass-generic one-step
  congruence, instantiated with `program := normalizeProgram cfg`).

The peephole leg needs `(normalizeProgram cfg).WellTyped` (`normalizeProgram_wellTyped`),
`(normalizeProgram cfg).ProgramCounterIndependent`
(`normalizeProgram_programCounterIndependent`), and the per-found-block
`StackRealizes` at `state2` — which, since `normalizeBlock` preserves `.input`,
follows from `stackRealizes_of_realizedWitnessFC_total` on `cfg` transported along
`SameRuntimeData`.

These lemmas have the EXACT argument shape of the peephole `*_of_source` family, so
the OIC consumption sites swap `peephole` → `combined` names with no other change.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState SameRuntimeData)
open InteractionSemantics
open InteractionCongruence
open Structured.InteractionFrameConsistent (realizedWitnessFC)

/-! ## Combined `ProgramCounterIndependent` + fuel bound -/

/-- **Combined `ProgramCounterIndependent` preservation.**  Same argument shape as
`peepholeProgram_programCounterIndependent`. -/
theorem combined_programCounterIndependent {program : Program}
    (h : program.ProgramCounterIndependent) :
    (peepholeProgram (normalizeProgram program)).ProgramCounterIndependent :=
  peepholeProgram_programCounterIndependent
    (normalizeProgram_programCounterIndependent h)

/-- **Combined fuel bound.**  `peepholeProgram (normalizeProgram cfg)` lowers to at
most `cfg`'s whole-program fuel budget.  Same argument shape as
`fuelBudget_peepholeProgram_le`. -/
theorem fuelBudget_combined_le (program : Program) (hWT : program.WellTyped) :
    InteractionSemantics.CompiledProgram.fuelBudget
        (peepholeProgram (normalizeProgram program)) ≤
      InteractionSemantics.CompiledProgram.fuelBudget program :=
  le_trans
    (fuelBudget_peepholeProgram_le (normalizeProgram program)
      (normalizeProgram_wellTyped hWT))
    (fuelBudget_normalizeProgram_le program hWT)

/-! ## Combined source-threaded congruences -/

/-- **Source-threaded one-step combined congruence.**  `Rel.trans` of the normalize
step (source-threaded, LEFT tree `cfg`, carrying the successor witness) and the
peephole step (`program := normalizeProgram cfg`).  Same conclusion shape as
`openStep_peephole_congr_of_source`, with RHS
`openStep (peepholeProgram (normalizeProgram cfg))`. -/
theorem openStep_combined_congr_of_source
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped) (hIndependent : cfg.ProgramCounterIndependent)
    {label : Assembly.Label} {state1 state2 : EVMState}
    (hReal : realizedWitnessFC source cfg context.calls label state1)
    (hRel : SameRuntimeData state1 state2) :
    Simulation.Interaction.Rel
      (Simulation.Interaction.ExceptRel (fun a b : EVMException => a = b)
        (fun v1 v2 : TypedCfg.Outcome =>
          Outcome.RuntimeRel v1 v2 ∧
            (∀ lbl s1, v1 = TypedCfg.Outcome.jump lbl s1 →
              realizedWitnessFC source cfg context.calls lbl s1)))
      (InteractionSemantics.Program.openStep cfg label state1)
      (InteractionSemantics.Program.openStep
        (peepholeProgram (normalizeProgram cfg)) label state2) := by
  have hNorm :=
    openStep_normalize_congr_of_source context hSourceWF hTyped hIndependent hReal hRel
  have hTypedN : (normalizeProgram cfg).WellTyped := normalizeProgram_wellTyped hTyped
  have hIndepN : (normalizeProgram cfg).ProgramCounterIndependent :=
    normalizeProgram_programCounterIndependent hIndependent
  have hReal2N : ∀ block, (normalizeProgram cfg).findBlock? label = some block →
      StackRealizes block.input state2 := by
    intro block hFind
    rw [findBlock?_normalizeProgram] at hFind
    cases hf0 : cfg.findBlock? label with
    | none => rw [hf0] at hFind; simp at hFind
    | some b0 =>
        rw [hf0, Option.map_some] at hFind
        injection hFind with hFind
        subst hFind
        have hR1 :=
          Structured.TokenBottomThread.stackRealizes_of_realizedWitnessFC_total
            context hSourceWF hReal hf0
        simp only [normalizeBlock_input]
        unfold TypedCfg.StackRealizes at hR1 ⊢
        rw [← SameRuntimeData.stack_eq hRel]
        exact hR1
  have hPeep :=
    openStep_peephole_congr (program := normalizeProgram cfg) hTypedN hIndepN
      hReal2N (SameRuntimeData.refl state2) (label := label)
  refine Simulation.Interaction.Rel.mono
    (Simulation.Interaction.Rel.trans hNorm hPeep) ?_
  rintro x z ⟨y, hxy, hyz⟩
  cases hxy with
  | error he =>
      cases hyz with
      | error he2 => exact Simulation.Interaction.ExceptRel.error (he.trans he2)
  | ok hok =>
      obtain ⟨hrr, hP⟩ := hok
      cases hyz with
      | ok hrr2 => exact Simulation.Interaction.ExceptRel.ok ⟨hrr.trans hrr2, hP⟩

/-- **Source-threaded fuel-bounded combined congruence.**  Same conclusion shape as
`openRunN_peephole_congr_of_source`, with RHS
`openRunN (peepholeProgram (normalizeProgram cfg))`. -/
theorem openRunN_combined_congr_of_source
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped) (hIndependent : cfg.ProgramCounterIndependent) :
    ∀ (fuel : Nat) (label : Assembly.Label) (state1 state2 : EVMState),
      realizedWitnessFC source cfg context.calls label state1 →
      SameRuntimeData state1 state2 →
      Simulation.Interaction.Rel Block.RuntimeOutcomeRel
        (InteractionSemantics.Program.openRunN cfg fuel label state1)
        (InteractionSemantics.Program.openRunN
          (peepholeProgram (normalizeProgram cfg)) fuel label state2)
  | 0, label, state1, state2, _hReal, hRel => by
      simp only [InteractionSemantics.Program.openRunN_zero]
      exact .done (.ok (Outcome.RuntimeRel.jump label hRel))
  | fuel + 1, label, state1, state2, hReal, hRel => by
      rw [InteractionSemantics.Program.openRunN_succ,
        InteractionSemantics.Program.openRunN_succ]
      have hStep :=
        openStep_combined_congr_of_source context hSourceWF hTyped hIndependent hReal hRel
      apply Simulation.Interaction.Rel.bind hStep
      intro o1 o2 hOut
      obtain ⟨hRR, hWit⟩ := hOut
      cases hRR with
      | jump lbl hState =>
          exact openRunN_combined_congr_of_source context hSourceWF hTyped hIndependent
            fuel lbl _ _ (hWit lbl _ rfl) hState
      | fallthrough hState =>
          exact .done (.ok (Outcome.RuntimeRel.fallthrough hState))
      | returnDispatch hState =>
          exact .done (.ok (Outcome.RuntimeRel.returnDispatch hState))
      | halt kind hState =>
          exact .done (.ok (Outcome.RuntimeRel.halt kind hState))
      | invalid hState =>
          exact .done (.ok (Outcome.RuntimeRel.invalid hState))

/-- **Source-threaded prefix combined congruence.**  Same conclusion shape as
`openRunNPrefix_peephole_congr_of_source`, with RHS
`openRunNPrefix (peepholeProgram (normalizeProgram cfg))`. -/
theorem openRunNPrefix_combined_congr_of_source
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped) (hIndependent : cfg.ProgramCounterIndependent)
    (fuel : Nat) (label : Assembly.Label) (state1 state2 : EVMState)
    (hReal : realizedWitnessFC source cfg context.calls label state1)
    (hRel : SameRuntimeData state1 state2) :
    Simulation.Interaction.Rel Block.RuntimeOutcomeRel
      (InteractionSemantics.Program.openRunNPrefix cfg fuel label state1)
      (InteractionSemantics.Program.openRunNPrefix
        (peepholeProgram (normalizeProgram cfg)) fuel label state2) := by
  unfold InteractionSemantics.Program.openRunNPrefix
  have hRun :=
    openRunN_combined_congr_of_source context hSourceWF hTyped hIndependent
      fuel label state1 state2 hReal hRel
  apply Simulation.Interaction.Rel.bind hRun
  intro o1 o2 hOut
  cases hOut with
  | halt kind hState =>
      exact .done (.ok (Outcome.RuntimeRel.halt kind hState))
  | jump lbl hState =>
      exact .done (.error rfl)
  | fallthrough hState =>
      exact .done (.error rfl)
  | returnDispatch hState =>
      exact .done (.error rfl)
  | invalid hState =>
      exact .done (.error rfl)

end Peephole
end TypedCfg
end EvmCompiler
