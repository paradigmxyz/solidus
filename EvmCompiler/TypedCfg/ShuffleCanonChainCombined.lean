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

/-! ## Frontier 1: the seam-transported per-entry `StackRealizes` at `s_mid` (free) -/

/-- **`hReal_o` for the pre-chain program (source-derived).**  At any reached label,
the `Q := preChainProgram cfg` block's input is realized by the intermediate seam
state `s_mid`.  This is exactly the seam layer's `hReal_cP` derivation
(`PeepholeSeamCombinedEff.lean:118-148`): `stackRealizes_of_realizedWitnessFC_total`
on `cfg` at `s1`, transported through `SameRuntimeData.stack_eq` and the
`SeamStepRelEff` length-preservation (`pendingSwap_stack_length` / `remapShape_length`),
since `Q`'s block `= seamBlockEff P (·)` preserves input length.  Lifted from `P`'s
block to `Q`'s via `findBlock?_seamCancelProgramEff`. -/
theorem stackRealizes_preChain_of_seamCombined
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    {label : Label} {s1 s_mid : EVMState}
    (hStep : SeamCombinedStepRelEff (source := source) (cfg := cfg)
      context.calls label s1 s_mid) :
    ∀ b0, (preChainProgram cfg).findBlock? label = some b0 → StackRealizes b0.input s_mid := by
  obtain ⟨state2, hReal, hRel, hStepP⟩ := hStep
  set P := peepholeProgram (normalizeProgram cfg) with hP
  intro bQ hFindQ
  rw [preChainProgram, ← hP, findBlock?_seamCancelProgramEff] at hFindQ
  cases hfP : P.findBlock? label with
  | none => rw [hfP] at hFindQ; simp at hFindQ
  | some b0 =>
      rw [hfP] at hFindQ
      simp only [Option.map_some, Option.some.injEq] at hFindQ
      subst hFindQ
      have hFindP' := hfP
      rw [hP, findBlock?_peepholeProgram, findBlock?_normalizeProgram] at hFindP'
      cases hf0 : cfg.findBlock? label with
      | none => rw [hf0] at hFindP'; simp at hFindP'
      | some bcfg =>
          rw [hf0] at hFindP'
          simp only [Option.map_some, Option.some.injEq] at hFindP'
          have hInputEq : b0.input = bcfg.input := by rw [← hFindP']; simp
          have hRcfg : bcfg.input.length ≤ s1.stack.length :=
            Structured.TokenBottomThread.stackRealizes_of_realizedWitnessFC_total
              context hSourceWF hReal hf0
          have hLen12 : s1.stack.length = state2.stack.length :=
            congrArg List.length (SameRuntimeData.stack_eq hRel)
          rw [seamBlockEff_input_cleanTgt]
          unfold StackRealizes
          cases htf : cleanTgt? P b0 with
          | none =>
              simp only [htf, hInputEq]
              simp only [SeamStepRelEff, hfP, htf] at hStepP
              have h3 : state2.stack.length = s_mid.stack.length :=
                congrArg List.length (SameRuntimeData.stack_eq hStepP)
              omega
          | some d =>
              simp only [htf, remapShape_length, hInputEq]
              simp only [SeamStepRelEff, hfP, htf] at hStepP
              have h3 : state2.stack.length = s_mid.stack.length :=
                pendingSwap_stack_length hStepP
              omega

/-! ## Part (B): length-constancy — chain-member bodies preserve stack length

The chain-runtime-feasibility invariant needs, at every reached chain member `m`,
that the runtime stack length at `m`'s entry equals the head-entry length.  This
section supplies the per-step half: a chain body (`.swap`/`.bindLocals`-only, the
`ChainInstr` shape) runs through `Block.runBody` preserving the stack length exactly,
because `Block.runBody` of such a body is `runSwaps` of its swap positions (§79
`runBody_chain_state`) and each `EvmYul.swap` preserves length. -/

/-- Every runtime swap position produced by a chain body is `≥ 1` (each is `d + 1`). -/
theorem bodyRunPositions_pos (body : List Instr) :
    ∀ p ∈ bodyRunPositions body, 1 ≤ p := by
  induction body with
  | nil => intro p hp; simp [bodyRunPositions] at hp
  | cons i rest ih =>
      intro p hp
      cases i <;>
        first
          | (simp only [bodyRunPositions, List.mem_cons] at hp
             rcases hp with h | h
             · omega
             · exact ih p h)
          | exact ih p (by simpa only [bodyRunPositions] using hp)

/-- **A depth-positive `runSwaps` run preserves stack length.**  Each `EvmYul.swap p`
with `p ≥ 1` that succeeds keeps the stack length fixed (`swap_ok_stack_length`), so a
whole successful run does too. -/
theorem runSwaps_stack_length : ∀ (ps : List Nat) {s s' : EVMState},
    (∀ p ∈ ps, 1 ≤ p) → runSwaps ps s = .ok s' → s'.stack.length = s.stack.length
  | [], s, s', _, hrun => by
      simp only [runSwaps_nil, Except.ok.injEq] at hrun; rw [hrun]
  | p :: rest, s, s', hpos, hrun => by
      have hp1 : 1 ≤ p := hpos p List.mem_cons_self
      simp only [runSwaps] at hrun
      cases hsw : EvmYul.swap p s with
      | error e => rw [hsw] at hrun; simp at hrun
      | ok s1 =>
          rw [hsw] at hrun
          have hlen1 : s1.stack.length = s.stack.length := swap_ok_stack_length hp1 hsw
          have hposR : ∀ q ∈ rest, 1 ≤ q := fun q hq => hpos q (List.mem_cons_of_mem _ hq)
          rw [runSwaps_stack_length rest hposR hrun, hlen1]

/-- **Part (B): a chain-eligible block body preserves stack length exactly.**  A body
made of `ChainInstr`s (`.swap`/`.bindLocals`/`.bindScratch`/`.relabel`) with every swap
depth `< 16` runs through `Block.runBody` leaving the stack length unchanged.  This is
the per-member length-constancy step the feasibility invariant threads across the run. -/
theorem runBody_chain_stack_length (body : List Instr) {input out : Shape} {s s' : EVMState}
    (hChain : ∀ i ∈ body, ChainInstr i) (hsw16 : ∀ d, Instr.swap d ∈ body → d < 16)
    (hrun : Block.runBody body input s = .ok (s', out)) :
    s'.stack.length = s.stack.length :=
  runSwaps_stack_length _ (bodyRunPositions_pos body)
    (runBody_chain_state body hChain hsw16 hrun)

/-- **Part (B), member form.**  A chain-eligible block (`chainBodyOk = true`, i.e.
its body has `chainBodyDepths? = some`) whose swap depths are all `< 16` runs through
`Block.runBody` preserving stack length.  Discharges the `ChainInstr` hypothesis of
`runBody_chain_stack_length` from `chainBodyOk` via `chainInstr_of_chainBodyDepths`, so
the length-constancy step applies directly to real `growChain` members. -/
theorem runBody_chainBodyOk_stack_length {b : Block} {s s' : EVMState} {out : Shape}
    (hOk : ShuffleCanon.chainBodyOk b = true)
    (hsw16 : ∀ d, Instr.swap d ∈ b.body → d < 16)
    (hrun : Block.runBody b.body b.input s = .ok (s', out)) :
    s'.stack.length = s.stack.length := by
  unfold ShuffleCanon.chainBodyOk at hOk
  rw [Option.isSome_iff_exists] at hOk
  obtain ⟨ds, hds⟩ := hOk
  exact runBody_chain_stack_length b.body (chainInstr_of_chainBodyDepths hds) hsw16 hrun

/-! ## Part (A) static scaffolding: chain adjacency supplies the run's jump targets

Part (A) — "the run visits each `growChain` member in order" — rests on the static
fact that consecutive members are `chainStep`-linked, so each non-last member's
terminator is exactly a `jump` to the next member's label.  This is the jump-target
spine the eventual run-forward induction walks; it follows from `growChain_chain'`
(consecutive members are `chainStep`-linked) and `chainStep_spec` (a `chainStep` forces
the predecessor's `jump`). -/
theorem growChain_member_term_jump (prog : Program) (b : Block) (bs : List Block)
    (i : Nat) (hi : i + 1 < (ShuffleCanon.growChain prog b bs).length) :
    ((ShuffleCanon.growChain prog b bs)[i]'(by omega)).term
      = Terminator.jump ((ShuffleCanon.growChain prog b bs)[i + 1]'hi).label :=
  (ShuffleCanon.chainStep_spec
    (List.IsChain.getElem (ShuffleCanon.growChain_chain' prog b bs) i hi)).1

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
