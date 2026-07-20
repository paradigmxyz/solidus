import EvmCompiler.TypedCfg.PeepholeNoopSwapProgram
import EvmCompiler.Structured.PeepholeSourceCongr

/-!
# Source-threaded whole-program `normalizeProgram` congruences (session-58, step 3)

The Route-3 analogue of `PeepholeSourceCongr`.  The block-body `normalizeProgram`
transform carries the same runtime depth guard as the peephole swap arm (its
firing window is `swap d ; z* ; swap d`), discharged at each visited entry from
`TypedCfg.StackRealizes block.input state` via the source witness
`realizedWitnessFC`.

The witness machinery (`allDone_realizedWitnessFC_jump`,
`stackRealizes_of_realizedWitnessFC_total`, `realizedWitnessFC_entry_of_generated`)
is entirely about the compiled `cfg` (the LEFT tree) and pass-agnostic, so it is
reused verbatim from `PeepholeSourceCongr`; only the RIGHT tree's transform changes
from `peepholeProgram` to `normalizeProgram`, threaded through
`openStep_normalize_congr`.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState SameRuntimeData)
open InteractionSemantics
open InteractionCongruence
open Structured.InteractionFrameConsistent (realizedWitnessFC)

/-- **Source-threaded one-step whole-program normalize congruence.**  The step
congruence `openStep_normalize_congr`, strengthened so that each jump leaf of the
ORIGINAL `openStep` carries the successor entry witness alongside its
`RuntimeOutcomeRel` value. -/
theorem openStep_normalize_congr_of_source
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
      (InteractionSemantics.Program.openStep (normalizeProgram cfg) label state2) := by
  have hReal2 : ∀ block, cfg.findBlock? label = some block →
      TypedCfg.StackRealizes block.input state2 := by
    intro block hFind
    have hR1 :=
      Structured.TokenBottomThread.stackRealizes_of_realizedWitnessFC_total
        context hSourceWF hReal hFind
    unfold TypedCfg.StackRealizes at hR1 ⊢
    rw [← SameRuntimeData.stack_eq hRel]
    exact hR1
  have hStep :=
    openStep_normalize_congr (program := cfg) hTyped hIndependent hReal2 hRel
      (label := label)
  have hAll := allDone_realizedWitnessFC_jump context hSourceWF hReal
  have hStrong := Simulation.Interaction.Rel.strengthen_left hStep hAll
  refine Simulation.Interaction.Rel.mono hStrong ?_
  rintro o1 o2 ⟨hER, hProp⟩
  cases hER with
  | error he => exact Simulation.Interaction.ExceptRel.error he
  | ok hrr =>
      exact Simulation.Interaction.ExceptRel.ok
        ⟨hrr, fun lbl s1 hv => hProp lbl s1 (by rw [hv])⟩

/-- **Source-threaded fuel-bounded whole-program normalize congruence.** -/
theorem openRunN_normalize_congr_of_source
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
        (InteractionSemantics.Program.openRunN (normalizeProgram cfg) fuel label state2)
  | 0, label, state1, state2, _hReal, hRel => by
      simp only [InteractionSemantics.Program.openRunN_zero]
      exact .done (.ok (Outcome.RuntimeRel.jump label hRel))
  | fuel + 1, label, state1, state2, hReal, hRel => by
      rw [InteractionSemantics.Program.openRunN_succ,
        InteractionSemantics.Program.openRunN_succ]
      have hStep :=
        openStep_normalize_congr_of_source context hSourceWF hTyped hIndependent hReal hRel
      apply Simulation.Interaction.Rel.bind hStep
      intro o1 o2 hOut
      obtain ⟨hRR, hWit⟩ := hOut
      cases hRR with
      | jump lbl hState =>
          exact openRunN_normalize_congr_of_source context hSourceWF hTyped hIndependent
            fuel lbl _ _ (hWit lbl _ rfl) hState
      | fallthrough hState =>
          exact .done (.ok (Outcome.RuntimeRel.fallthrough hState))
      | returnDispatch hState =>
          exact .done (.ok (Outcome.RuntimeRel.returnDispatch hState))
      | halt kind hState =>
          exact .done (.ok (Outcome.RuntimeRel.halt kind hState))
      | invalid hState =>
          exact .done (.ok (Outcome.RuntimeRel.invalid hState))

/-- **Source-threaded whole-program prefix normalize congruence.** -/
theorem openRunNPrefix_normalize_congr_of_source
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
      (InteractionSemantics.Program.openRunNPrefix (normalizeProgram cfg)
        fuel label state2) := by
  unfold InteractionSemantics.Program.openRunNPrefix
  have hRun :=
    openRunN_normalize_congr_of_source context hSourceWF hTyped hIndependent
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
