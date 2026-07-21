import EvmCompiler.TypedCfg.ShuffleCanonChainResidual
import EvmCompiler.Structured.PeepholeSeamCombinedEff

/-!
# The combined-with-source layer for the chain canonicaliser (session-85)

Mirrors `EvmCompiler/Structured/PeepholeSeamCombinedEff.lean`, composing the live
source-threaded seam-combined congruence (`openStep_seamCombinedEff_congr_of_source`,
relating `cfg` to `Q := seamCancelProgramEff (peepholeProgram (normalizeProgram cfg))`)
with the banked chain-canonicalisation step congruence (`openStep_chainCanon_congr`,
relating `Q` to `chainCanonProgram Q`).  The chain leg is spliced AFTER the seam
canceller, so `chainCanonProgram` operates on `Q`'s (already seam-cancelled) output —
there is no shared editing window, so composition is purely sequential.

This module banks the **scaffold**: the 3-tuple invariant `ChainCombinedStepRelEff`,
its disjunctive outcome relation `ChainCombinedOutcomeRelEff`, the entry seed, and the
**core one-step composition** `openStep_chainCombinedEff_core` (stated over an EXPLICIT
intermediate state `s_mid` with the three per-entry feasibility facts as hypotheses).

The remaining frontier — a source-threaded `openStep_chainCombinedEff_congr_of_source`
that DERIVES those feasibility facts from the invariant (rather than taking `s_mid`
explicit) — reduces to the single **chain-runtime-feasibility invariant**
`∀ m ∈ growChain, m.input.length ≤ s_mid.stack.length` (needed at fired heads for
`hFeasO`, and at consumed members for the `finalOut`-shaped `hReal_c`).  See §85 note.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState SameRuntimeData)
open InteractionSemantics
open InteractionCongruence
open ShuffleCanon (editTable Edit chainCanonProgram applyEdit)
open Structured.InteractionFrameConsistent (realizedWitnessFC)

/-- Abbreviation for the pre-chain pipeline output: the seam-cancelled corrected
combined program the chain canonicaliser is spliced after. -/
abbrev preChainProgram (cfg : TypedCfg.Program) : TypedCfg.Program :=
  seamCancelProgramEff (peepholeProgram (normalizeProgram cfg))

/-! ## The carried 3-tuple invariant + disjunctive combined outcome relation -/

/-- The invariant carried at each reached block entry across the full
source→seam→chain bisimulation: the source-threaded seam-combined invariant relates
`s1` (the real `cfg` run) to an intermediate `s_mid` (the `Q := preChainProgram cfg`
run), and the chain-canon step invariant relates `s_mid` to `s_final` (the
`chainCanonProgram Q` run). -/
def ChainCombinedStepRelEff {source : Structured.Program}
    {cfg : TypedCfg.Program}
    (calls : List Structured.TypedCfgCompiler.DispatchSite)
    (label : Label) (s1 s_final : EVMState) : Prop :=
  ∃ s_mid, SeamCombinedStepRelEff (source := source) (cfg := cfg) calls label s1 s_mid ∧
    ChainStepRel (preChainProgram cfg) (residual (preChainProgram cfg)) label s_mid s_final

/-- The disjunctive one-step combined outcome relation for the full pipeline. -/
def ChainCombinedOutcomeRelEff {source : Structured.Program}
    {cfg : TypedCfg.Program}
    (calls : List Structured.TypedCfgCompiler.DispatchSite) :
    Except EVMException TypedCfg.Outcome →
      Except EVMException TypedCfg.Outcome → Prop :=
  fun a c =>
    (∃ (next : Label) (s1 s_final : EVMState),
      a = .ok (.jump next s1) ∧ c = .ok (.jump next s_final) ∧
        ChainCombinedStepRelEff (source := source) (cfg := cfg) calls next s1 s_final)
    ∨ (InteractionCongruence.Block.RuntimeOutcomeRel a c ∧
        ∀ (next : Label) (s : EVMState), a ≠ .ok (.jump next s))

/-! ## Entry seed for the whole-program chain-combined bisimulation -/

/-- **Entry seed (`ChainCombinedStepRelEff`).**  At the program entry, equal states
seed both legs: the seam-combined leg via `seamCombinedStepRelEff_entry_of_generated`,
the chain leg via `chainStepRel_entry` (the entry is never a consumed chain member). -/
theorem chainCombinedStepRelEff_entry_of_generated
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    {sourceState : Structured.RunState} {cfgState : EVMState}
    (hStateRel : Structured.TypedCfgPreservation.StateRel sourceState [] cfgState) :
    ChainCombinedStepRelEff (source := source) (cfg := cfg) context.calls
      cfg.entry cfgState cfgState := by
  refine ⟨cfgState, seamCombinedStepRelEff_entry_of_generated context hStateRel, ?_⟩
  have h := chainStepRel_entry (preChainProgram cfg) (residual (preChainProgram cfg)) cfgState
  simpa [preChainProgram] using h

/-! ## The core one-step composition (explicit intermediate state) -/

/-- **Core one-step chain-combined composition.**  `Rel.trans` of the source-threaded
seam-combined congruence (`cfg ~ Q := preChainProgram cfg`) with the chain-canon step
congruence (`Q ~ chainCanonProgram Q`), landing in the combined outcome relation.

Stated over an EXPLICIT intermediate state `s_mid` with the chain leg's three
per-entry feasibility facts as hypotheses.  Deriving `hReal_o`/`hReal_c`/`hFeasO` from
the invariant `hSeamComb` — `hReal_o` is the seam-style transported `StackRealizes`,
while `hFeasO` and the consumed-case `hReal_c` require the chain-runtime-feasibility
invariant (the §85 frontier) — is what the source-threaded wrapper adds. -/
theorem openStep_chainCombinedEff_core
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped) (hIndependent : cfg.ProgramCounterIndependent)
    {label : Label} {s1 s_mid s_final : EVMState}
    (hSeamComb : SeamCombinedStepRelEff (source := source) (cfg := cfg)
      context.calls label s1 s_mid)
    (hChainStep : ChainStepRel (preChainProgram cfg) (residual (preChainProgram cfg))
      label s_mid s_final)
    (hReal_o : ∀ b0, (preChainProgram cfg).findBlock? label = some b0 →
      StackRealizes b0.input s_mid)
    (hReal_c : ∀ b0, (preChainProgram cfg).findBlock? label = some b0 →
      StackRealizes (applyEdit (editTable (preChainProgram cfg)) b0).input s_final)
    (hFeasO : ∀ p ∈ residual (preChainProgram cfg) label, p + 1 ≤ s_mid.stack.length) :
    Simulation.Interaction.Rel
      (ChainCombinedOutcomeRelEff (source := source) (cfg := cfg) context.calls)
      (InteractionSemantics.Program.openStep cfg label s1)
      (InteractionSemantics.Program.openStep
        (chainCanonProgram (preChainProgram cfg)) label s_final) := by
  set Q := preChainProgram cfg with hQ
  have hTypedQ : Q.WellTyped :=
    seamCancelProgramEff_wellTyped
      (peepholeProgram_wellTyped (normalizeProgram_wellTyped hTyped))
  have hIndepQ : Q.ProgramCounterIndependent :=
    seamCancelProgramEff_programCounterIndependent
      (combined_programCounterIndependent hIndependent)
  have hSeam :=
    openStep_seamCombinedEff_congr_of_source context hSourceWF hTyped hIndependent hSeamComb
  have hChain :=
    openStep_chainCanon_congr hTypedQ.1 hTypedQ hIndepQ (chainResidualSpec hTypedQ.1)
      hReal_o hReal_c hFeasO hChainStep
  refine Simulation.Interaction.Rel.mono
    (Simulation.Interaction.Rel.trans hSeam hChain) ?_
  rintro x z ⟨y, hxy, hyz⟩
  rcases hxy with hjumpXY | ⟨hrrXY, hnjXY⟩
  · -- seam leg: synchronised jump  x = jump next sx, y = jump next sy
    obtain ⟨next, sx, sy, hx, hy, hSeamNext⟩ := hjumpXY
    rcases hyz with hjumpYZ | ⟨hrrYZ, hnjYZ⟩
    · obtain ⟨next2, sy2, sz, hy2, hz, hChainNext⟩ := hjumpYZ
      rw [hy] at hy2
      rw [Except.ok.injEq, Outcome.jump.injEq] at hy2
      obtain ⟨hnn, hss⟩ := hy2
      subst hnn; subst hss
      refine Or.inl ⟨next, sx, sz, hx, hz, sy, hSeamNext, hChainNext⟩
    · exact absurd hy (hnjYZ next sy)
  · -- seam leg: runtime non-jump  x is not a jump, RuntimeOutcomeRel x y
    rcases hyz with hjumpYZ | ⟨hrrYZ, hnjYZ⟩
    · -- y is a jump but x is not — impossible under RuntimeOutcomeRel x y
      obtain ⟨next2, sy2, sz, hy2, _, _⟩ := hjumpYZ
      exfalso
      cases hrrXY with
      | error he => exact absurd hy2 (by simp)
      | ok hrr =>
          cases hrr with
          | jump lbl hSt => exact hnjXY _ _ rfl
          | fallthrough hSt => exact absurd hy2 (by simp)
          | returnDispatch hSt => exact absurd hy2 (by simp)
          | halt kind hSt => exact absurd hy2 (by simp)
          | invalid hSt => exact absurd hy2 (by simp)
    · -- both runtime non-jump: compose the two `RuntimeOutcomeRel`s at the Except level
      refine Or.inr ⟨?_, hnjXY⟩
      cases hrrXY with
      | error he =>
          cases hrrYZ with
          | error he2 => exact .error (he.trans he2)
      | ok hrr =>
          cases hrrYZ with
          | ok hrrz => exact .ok (Outcome.RuntimeRel.trans hrr hrrz)

end Peephole
end TypedCfg
end EvmCompiler
