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
    (hReal_c : ∀ b0 body out, (preChainProgram cfg).findBlock? label = some b0 →
      (editTable (preChainProgram cfg)).lookup label = some (Edit.head body out) →
      StackRealizes b0.input s_final)
    (hFeasO : ∀ body out, (editTable (preChainProgram cfg)).lookup label = some (Edit.head body out) →
      ∀ p ∈ residual (preChainProgram cfg) label, p + 1 ≤ s_mid.stack.length) :
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

/-! ## Part (A) inductive step: jump-propagation of the seam-combined invariant

The run-forward induction of part (A) walks the fired chain one member at a time,
re-establishing `SeamCombinedStepRelEff` at each successor's entry.  This is that
single step, extracted from the source-threaded seam congruence: whenever the two
bisimilar runs both take a synchronised `jump` to the same successor `nxt` (which the
actual `openRunN` run supplies at each `growChain` member via the
`growChain_member_term_jump` adjacency), the invariant re-seeds at `nxt`.  The proof
inverts `Simulation.Interaction.Rel` on the two `.done` jump outcomes and reads off the
`jump` disjunct of `SeamCombinedOutcomeRelEff` (the runtime non-jump disjunct is refuted
by the `cfg`-side jump). -/
theorem seamCombinedStepRelEff_propagate_jump
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped) (hIndependent : cfg.ProgramCounterIndependent)
    {label nxt : Label} {s1 s_mid s1' s_nxt : EVMState}
    (hStep : SeamCombinedStepRelEff (source := source) (cfg := cfg)
      context.calls label s1 s_mid)
    (hcfg : InteractionSemantics.Program.openStep cfg label s1
      = Simulation.Interaction.done (Except.ok (TypedCfg.Outcome.jump nxt s1')))
    (hQ : InteractionSemantics.Program.openStep (preChainProgram cfg) label s_mid
      = Simulation.Interaction.done (Except.ok (TypedCfg.Outcome.jump nxt s_nxt))) :
    SeamCombinedStepRelEff (source := source) (cfg := cfg) context.calls nxt s1' s_nxt := by
  have hRel :=
    openStep_seamCombinedEff_congr_of_source context hSourceWF hTyped hIndependent hStep
  rw [preChainProgram] at hQ
  rw [hcfg, hQ] at hRel
  cases hRel with
  | done hdone =>
      rcases hdone with ⟨n, sa, sc, ha, hc, hnext⟩ | ⟨_, hnj⟩
      · rw [Except.ok.injEq, Outcome.jump.injEq] at ha hc
        obtain ⟨rfl, rfl⟩ := ha
        obtain ⟨_, rfl⟩ := hc
        exact hnext
      · exact absurd rfl (hnj nxt s1')

/-- **Jump-propagation from the `Q`-side jump alone.**  The run-forward induction only
observes the `Q := preChainProgram cfg` run stepping to a `.done` jump (via
`member_openStep_done_jump`); the `cfg`-side jump is *derived* here from the bisimulation.
Since `openStep cfg _ s1` and `openStep Q _ s_mid` are `Rel`-related and the `Q` side is a
`.done`, the `cfg` side is a `.done` too (`Rel` pairs `done` with `done`, `request` with
`request`), and reading the `jump` disjunct of `SeamCombinedOutcomeRelEff` re-seeds the
invariant at `nxt`.  This drops the explicit `cfg`-jump hypothesis of
`seamCombinedStepRelEff_propagate_jump`. -/
theorem seamCombinedStepRelEff_propagate_jump_of_Q
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped) (hIndependent : cfg.ProgramCounterIndependent)
    {label nxt : Label} {s1 s_mid s_nxt : EVMState}
    (hStep : SeamCombinedStepRelEff (source := source) (cfg := cfg)
      context.calls label s1 s_mid)
    (hQ : InteractionSemantics.Program.openStep (preChainProgram cfg) label s_mid
      = Simulation.Interaction.done (Except.ok (TypedCfg.Outcome.jump nxt s_nxt))) :
    ∃ s1', SeamCombinedStepRelEff (source := source) (cfg := cfg)
      context.calls nxt s1' s_nxt := by
  have hRel :=
    openStep_seamCombinedEff_congr_of_source context hSourceWF hTyped hIndependent hStep
  rw [preChainProgram] at hQ
  cases hcfgStep : InteractionSemantics.Program.openStep cfg label s1 with
  | request q k => rw [hcfgStep, hQ] at hRel; cases hRel
  | done c =>
      rw [hcfgStep, hQ] at hRel
      cases hRel with
      | done hdone =>
          rcases hdone with ⟨n, sa, sc, ha, hc, hnext⟩ | ⟨hrr, hnj⟩
          · rw [Except.ok.injEq, Outcome.jump.injEq] at hc
            obtain ⟨rfl, rfl⟩ := hc
            exact ⟨sa, hnext⟩
          · exfalso
            cases hrr with
            | ok hok => cases hok; exact hnj _ _ rfl

/-! ## Part (A) step (i): a chain member's `openStep` is a `.done` jump

The single Interaction-monad evaluation the run-forward induction needs.  A chain-eligible
member `m` — body only `ChainInstr` (`chainBodyDepths? m.body = some ds`), typing
`m.input → m.output`, terminator a bare `jump nxt` — entered with a stack realizing
`m.input`, steps in the OPEN interaction semantics (`Control.Program.step Instr.openRunState`)
to `.done (.ok (.jump nxt s'))` with the stack length preserved.

This is the ONE place the Interaction-monad `Control.Block.run`/`openRunBody` must be
evaluated (distinct from the closed `Block.runBody` parts (B)/(C) use).  The bridge:
`openRunBody_chain_done` (§80) collapses the interaction body to `.done (Block.runBody …)`;
`runBody_chain_ok` (§81) evaluates that closed body to `.ok (s', m.output)` under typing +
`StackRealizes`; the output-check passes (`m.output = m.output`); the `jump` terminator runs
through `runTermChecked_jump` to `.ok (.jump nxt s')`; `runBody_chain_stack_length` (§87
part B) supplies the length preservation. -/
theorem member_openStep_done_jump {Q : Program} {m : Block} {ds : List Nat}
    {nxt : Label} {s : EVMState}
    (hFind : Q.findBlock? m.label = some m)
    (helig : ShuffleCanon.chainBodyDepths? m.body = some ds)
    (hbt : Block.bodyType? m.body m.input = some m.output)
    (hReal : StackRealizes m.input s)
    (hterm : m.term = Terminator.jump nxt) :
    ∃ s', InteractionSemantics.Program.openStep Q m.label s
        = Simulation.Interaction.done (Except.ok (TypedCfg.Outcome.jump nxt s'))
      ∧ s'.stack.length = s.stack.length := by
  have hChain : ∀ i ∈ m.body, ChainInstr i := chainInstr_of_chainBodyDepths helig
  have hsw16 : ∀ d, Instr.swap d ∈ m.body → d < 16 := chain_swap_lt16 m.body hbt
  obtain ⟨s', hrun⟩ := runBody_chain_ok m.body hChain hbt hReal
  have hlen : s'.stack.length = s.stack.length :=
    runBody_chain_stack_length m.body hChain hsw16 hrun
  refine ⟨s', ?_, hlen⟩
  unfold InteractionSemantics.Program.openStep Control.Program.step
  rw [hFind]
  show Simulation.Interaction.bind
      (InteractionSemantics.Block.openRunBody m.body m.input s) _ = _
  rw [openRunBody_chain_done hChain, hrun]
  simp only [Simulation.Interaction.bind_done_ok, if_pos, hterm,
    Block.runTermChecked_jump, Block.runTerm]
  rfl

/-! ## Part (A) assembled: the chain-runtime-feasibility walk

Stitches the parts together.  Entering a grown chain's head with a source-threaded
`SeamCombinedStepRelEff` relating the real `cfg` run `s1` to the `Q := preChainProgram cfg`
run `s_mid`, the `Q`-run deterministically jumps head → member₂ → member₃ → … (each member
is a bare-jump-terminated chain body, `member_openStep_done_jump`).  Each hop preserves the
stack length (part B, inside the bridge) and re-seeds the seam-combined invariant
(`seamCombinedStepRelEff_propagate_jump_of_Q`), whose per-member witness
(`stackRealizes_preChain_of_seamCombined`) bounds that member's input length by the
(constant) stack length.  Hence every member `m` of the grown chain satisfies
`m.input.length ≤ s_mid.stack.length` — the chain-runtime-feasibility invariant §84–§87
pinned as the transform's soundness core. -/
theorem chain_feasibility_walk
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped) (hIndependent : cfg.ProgramCounterIndependent) :
    ∀ (bs : List Block) (b : Block) {s1 s_mid : EVMState},
      (∀ m ∈ ShuffleCanon.growChain (preChainProgram cfg) b bs,
        (preChainProgram cfg).findBlock? m.label = some m) →
      SeamCombinedStepRelEff (source := source) (cfg := cfg) context.calls b.label s1 s_mid →
      ∀ m ∈ ShuffleCanon.growChain (preChainProgram cfg) b bs,
        m.input.length ≤ s_mid.stack.length := by
  have hTypedQ : (preChainProgram cfg).WellTyped :=
    seamCancelProgramEff_wellTyped
      (peepholeProgram_wellTyped (normalizeProgram_wellTyped hTyped))
  set Q := preChainProgram cfg with hQdef
  intro bs
  induction bs with
  | nil =>
      intro b s1 s_mid hfind hStep m hm
      have hgc : ShuffleCanon.growChain Q b [] = [b] := rfl
      rw [hgc, List.mem_singleton] at hm
      subst hm
      have hbmem : m ∈ ShuffleCanon.growChain Q m [] := by rw [hgc]; exact List.mem_singleton.2 rfl
      exact stackRealizes_preChain_of_seamCombined context hSourceWF hStep m (hfind m hbmem)
  | cons nxt rest ih =>
      intro b s1 s_mid hfind hStep m hm
      have hbmem : b ∈ ShuffleCanon.growChain Q b (nxt :: rest) := by
        obtain ⟨t, ht⟩ := ShuffleCanon.growChain_head Q b (nxt :: rest)
        rw [ht]; exact List.mem_cons_self
      have hReal_b : StackRealizes b.input s_mid :=
        stackRealizes_preChain_of_seamCombined context hSourceWF hStep b (hfind b hbmem)
      by_cases hstep : ShuffleCanon.chainStep Q b nxt = true
      · unfold ShuffleCanon.growChain at hm
        rw [if_pos hstep] at hm
        rcases List.mem_cons.1 hm with rfl | hmtail
        · exact hReal_b
        · -- Step forward across `b → nxt`.
          have hterm : b.term = Terminator.jump nxt.label := (ShuffleCanon.chainStep_spec hstep).1
          obtain ⟨ds, helig⟩ := Option.isSome_iff_exists.1 (chainStep_chainBodyOk_a hstep)
          have hbBlocks : b ∈ Q.blocks := by
            have hfb := hfind b hbmem
            unfold TypedCfg.Program.findBlock? at hfb
            exact List.mem_of_find?_eq_some hfb
          have hbtyped : b.WellTyped Q := (List.forall_iff_forall_mem.mp hTypedQ.2.1) b hbBlocks
          obtain ⟨s_mid', hopen, hlen⟩ :=
            member_openStep_done_jump (hFind := hfind b hbmem) (helig := helig)
              (hbt := hbtyped.1) (hReal := hReal_b) (hterm := hterm)
          obtain ⟨s1', hStepNxt⟩ :=
            seamCombinedStepRelEff_propagate_jump_of_Q context hSourceWF hTyped hIndependent
              hStep hopen
          have hfindTail : ∀ m' ∈ ShuffleCanon.growChain Q nxt rest,
              Q.findBlock? m'.label = some m' := by
            intro m' hm'
            refine hfind m' ?_
            unfold ShuffleCanon.growChain; rw [if_pos hstep]; exact List.mem_cons_of_mem b hm'
          have hIHtail := ih nxt hfindTail hStepNxt m hmtail
          rw [hlen] at hIHtail
          exact hIHtail
      · unfold ShuffleCanon.growChain at hm
        rw [if_neg hstep, List.mem_singleton] at hm
        subst hm
        exact hReal_b

/-! ## The residual-arithmetic bridge (head case): `hFeasO` from the feasibility walk

The head-case discharge of `hFeasO` from the chain-runtime-feasibility invariant
(`chain_feasibility_walk`).  A fired chain head `b0`'s residual is the whole chain's
concatenated `bodyRunPositions` (`residual_flatMap_of_run`, since the fired chain is a
residual run through its consumed successors).  Every residual position `p` therefore
lies in some member `m`'s `bodyRunPositions`; by `bodyRunPositions_bound` (member
typing) `p + 1 ≤ m.input.length`, and by `chain_feasibility_walk`
`m.input.length ≤ s_mid.stack.length` — so `p + 1 ≤ s_mid.stack.length`. -/
theorem residual_head_feasO
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped) (hIndependent : cfg.ProgramCounterIndependent)
    {b0 : Block} {hbody : List Instr} {hout : Shape} {s1 s_mid : EVMState}
    (hb0mem : b0 ∈ (preChainProgram cfg).blocks)
    (hlk : (editTable (preChainProgram cfg)).lookup b0.label = some (Edit.head hbody hout))
    (hStep : SeamCombinedStepRelEff (source := source) (cfg := cfg)
      context.calls b0.label s1 s_mid) :
    ∀ p ∈ residual (preChainProgram cfg) b0.label, p + 1 ≤ s_mid.stack.length := by
  set Q := preChainProgram cfg with hQdef
  have hTypedQ : Q.WellTyped :=
    seamCancelProgramEff_wellTyped
      (peepholeProgram_wellTyped (normalizeProgram_wellTyped hTyped))
  have hUnique : Q.LabelsUnique := hTypedQ.1
  -- Fired-chain context for the head edit.
  obtain ⟨ordered, b, rest, hord, hsuf, hlen, hmem, hsub⟩ :=
    firedChainCtx (ShuffleCanon.lookup_mem hlk)
  obtain ⟨hd, tl, hchain, _hbodyT, hcases⟩ := ShuffleCanon.chainEdits_fired hmem
  -- The entry edit is the head edit ⟹ `b0 = hd` (the chain head).
  have hb0label : b0.label = hd.label := by
    rcases hcases with heq | ⟨C, _hC, hCeq⟩
    · rw [Prod.mk.injEq] at heq; exact heq.1
    · rw [Prod.mk.injEq] at hCeq; exact absurd hCeq.2 (by simp)
  have hhdmem : hd ∈ Q.blocks :=
    ShuffleCanon.growChain_mem_blocks hord hsuf (hchain ▸ List.mem_cons_self)
  have hb0hd : b0 = hd := by
    have h1 : Q.findBlock? b0.label = some b0 :=
      Program.findBlock?_eq_some_of_mem hUnique hb0mem
    rw [hb0label, Program.findBlock?_eq_some_of_mem hUnique hhdmem] at h1
    exact ((Option.some.injEq _ _).mp h1).symm
  have hgrowhead : ShuffleCanon.growChain Q b rest = b0 :: tl := by rw [hb0hd]; exact hchain
  have hfired : ShuffleCanon.chainEdits (ShuffleCanon.growChain Q b rest) ≠ [] := by
    intro he; rw [he] at hmem; exact absurd hmem (by simp)
  -- `b0 = b` (both are the growChain head).
  have hb0b : b0 = b := by
    obtain ⟨tl0, hgh⟩ := ShuffleCanon.growChain_head Q b rest
    rw [hgrowhead] at hgh; exact (List.cons.injEq .. ▸ hgh).1
  -- `tl = B :: tl'`.
  obtain ⟨B, tl', htleq⟩ : ∃ B tl', tl = B :: tl' := by
    cases tl with
    | nil => rw [hchain] at hlen; simp at hlen
    | cons B tl' => exact ⟨B, tl', rfl⟩
  subst htleq
  -- `b0.term = jump B.label`, `B` consumed, last-block existence.
  have hgc := ShuffleCanon.growChain_chain' Q b rest
  rw [hgrowhead] at hgc
  obtain ⟨hstepB, _⟩ := List.isChain_cons_cons.mp hgc
  obtain ⟨htermB, _, _⟩ := ShuffleCanon.chainStep_spec hstepB
  have hZlast : ∃ Z, (ShuffleCanon.growChain Q b rest).getLast? = some Z := by
    cases hgl : (ShuffleCanon.growChain Q b rest).getLast? with
    | none => rw [List.getLast?_eq_none_iff] at hgl; rw [hgl] at hgrowhead; simp at hgrowhead
    | some Z => exact ⟨Z, rfl⟩
  obtain ⟨Z, hZlast⟩ := hZlast
  have hBconsumed : (editTable Q).lookup B.label
      = some (Edit.consumed ((ShuffleCanon.growChain Q b rest).getLastD b0).output) :=
    chain_tail_consumed hUnique hgrowhead hfired hsub List.mem_cons_self
  have hRunTl : IsResidualRun Q (B :: tl') :=
    isResidualRun_tail_suffix hUnique hord hsuf hgrowhead hfired hsub hZlast
      (B :: tl') (List.suffix_refl _) (by simp)
  have hRunFull : IsResidualRun Q (b0 :: B :: tl') :=
    ⟨Program.findBlock?_eq_some_of_mem hUnique hb0mem, htermB, ⟨_, hBconsumed⟩, hRunTl⟩
  have hlenFull : (b0 :: B :: tl').length ≤ Q.blocks.length := by
    have h := chain_length_le_blocks hord hsuf
    rw [hgrowhead] at h; exact h
  have hresFull : residual Q b0.label = (b0 :: B :: tl').flatMap (fun b => bodyRunPositions b.body) :=
    residual_flatMap_of_run hlenFull hRunFull
  -- The chain-runtime-feasibility invariant over the whole chain.
  have hfindcov : ∀ m ∈ ShuffleCanon.growChain Q b rest, Q.findBlock? m.label = some m :=
    fun m hm => Program.findBlock?_eq_some_of_mem hUnique (ShuffleCanon.growChain_mem_blocks hord hsuf hm)
  have hStepB : SeamCombinedStepRelEff (source := source) (cfg := cfg)
      context.calls b.label s1 s_mid := by rw [← hb0b]; exact hStep
  have hwalk := chain_feasibility_walk context hSourceWF hTyped hIndependent rest b hfindcov hStepB
  -- Combine, position by position.
  intro p hp
  rw [hresFull, ← hgrowhead] at hp
  obtain ⟨m, hmg, hpm⟩ := List.mem_flatMap.1 hp
  have hmmem : m ∈ Q.blocks := ShuffleCanon.growChain_mem_blocks hord hsuf hmg
  obtain ⟨ds, hds⟩ := Option.isSome_iff_exists.1 (chain_all_eligible hlen m hmg)
  have hChain : ∀ i ∈ m.body, ChainInstr i := chainInstr_of_chainBodyDepths hds
  have hmType : Block.bodyType? m.body m.input = some m.output :=
    (blockWellTyped_of_mem hTypedQ.2.1 hmmem).1
  have hbound := (bodyRunPositions_bound m.body hChain hmType p hpm).2
  have hwbound := hwalk m hmg
  omega

/-! ## The source-threaded one-step combined congruence (`_of_source`)

The fuel-composable one-step congruence that DROPS the explicit `s_mid` and the three
per-entry feasibility facts of `openStep_chainCombinedEff_core`, deriving them from the
combined invariant `ChainCombinedStepRelEff`:

* `hReal_o` — `stackRealizes_preChain_of_seamCombined` (§86).
* `hReal_c` — needed only at fired heads (`headBlock_rel_discharged`), where the chain
  leg is `SameRuntimeData` (a head is never consumed), so `s_mid.stack = s_final.stack`
  transports `hReal_o`'s `StackRealizes b0.input` from `s_mid` to `s_final`.
* `hFeasO` — needed only at fired heads (`hmergedBd`), discharged by the just-banked
  residual-arithmetic bridge `residual_head_feasO`.

The head-gating of `hReal_c`/`hFeasO` (in `openStep_chainCanon_congr`) is what makes the
consumed/ordinary cases vanish: both facts are consumed *only* in the head branch of
`openRun_chainCanon_congr`, so they need never be proven at non-head labels (where the
residual is not a length-preserving chain permutation and feasibility can genuinely
fail). -/
theorem openStep_chainCombinedEff_congr_of_source
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped) (hIndependent : cfg.ProgramCounterIndependent)
    {label : Label} {s1 s_final : EVMState}
    (hStep : ChainCombinedStepRelEff (source := source) (cfg := cfg)
      context.calls label s1 s_final) :
    Simulation.Interaction.Rel
      (ChainCombinedOutcomeRelEff (source := source) (cfg := cfg) context.calls)
      (InteractionSemantics.Program.openStep cfg label s1)
      (InteractionSemantics.Program.openStep
        (chainCanonProgram (preChainProgram cfg)) label s_final) := by
  obtain ⟨s_mid, hSeamComb, hChainStep⟩ := hStep
  set Q := preChainProgram cfg with hQ
  have hTypedQ : Q.WellTyped :=
    seamCancelProgramEff_wellTyped
      (peepholeProgram_wellTyped (normalizeProgram_wellTyped hTyped))
  -- hReal_o : the seam-transported per-entry `StackRealizes` at `s_mid` (§86).
  have hReal_o : ∀ b0, Q.findBlock? label = some b0 → StackRealizes b0.input s_mid :=
    fun b0 hFind => stackRealizes_preChain_of_seamCombined context hSourceWF hSeamComb b0 hFind
  -- hReal_c : needed only at heads; there the chain leg is SRD, transporting hReal_o.
  have hReal_c : ∀ b0 body out, Q.findBlock? label = some b0 →
      (editTable Q).lookup label = some (Edit.head body out) →
      StackRealizes b0.input s_final := by
    intro b0 body out hFind hlk
    have hSRD : SameRuntimeData s_mid s_final := by
      have h := hChainStep
      simp only [ChainStepRel, hlk] at h
      exact h
    have hro := hReal_o b0 hFind
    unfold StackRealizes at hro ⊢
    rw [← SameRuntimeData.stack_eq hSRD]; exact hro
  -- hFeasO : needed only at heads; the residual-arithmetic bridge.
  have hFeasO : ∀ body out, (editTable Q).lookup label = some (Edit.head body out) →
      ∀ p ∈ residual Q label, p + 1 ≤ s_mid.stack.length := by
    intro body out hlk
    cases hFind : Q.findBlock? label with
    | none => exact absurd hFind (findBlock?_ne_none_of_editTable_lookup hTypedQ.1 hlk)
    | some b0 =>
        have hb0label : b0.label = label := by
          unfold TypedCfg.Program.findBlock? at hFind
          have := List.find?_some hFind; simpa using this
        have hb0mem : b0 ∈ Q.blocks := by
          unfold TypedCfg.Program.findBlock? at hFind; exact List.mem_of_find?_eq_some hFind
        subst hb0label
        exact residual_head_feasO context hSourceWF hTyped hIndependent hb0mem hlk hSeamComb
  exact openStep_chainCombinedEff_core context hSourceWF hTyped hIndependent
    hSeamComb hChainStep hReal_o hReal_c hFeasO

/-! ## Source-threaded fuel + prefix combined congruences (mirror the seam layer) -/

/-- **Source-threaded fuel-bounded chain-combined congruence.** -/
theorem openRunN_chainCombinedEff_congr_of_source
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped) (hIndependent : cfg.ProgramCounterIndependent) :
    ∀ (fuel : Nat) (label : Label) (s1 s_final : EVMState),
      ChainCombinedStepRelEff (source := source) (cfg := cfg) context.calls label s1 s_final →
      Simulation.Interaction.Rel
        (ChainCombinedOutcomeRelEff (source := source) (cfg := cfg) context.calls)
        (InteractionSemantics.Program.openRunN cfg fuel label s1)
        (InteractionSemantics.Program.openRunN
          (chainCanonProgram (preChainProgram cfg)) fuel label s_final)
  | 0, label, s1, s_final, hStep => by
      simp only [InteractionSemantics.Program.openRunN_zero]
      exact .done (Or.inl ⟨label, s1, s_final, rfl, rfl, hStep⟩)
  | fuel + 1, label, s1, s_final, hStep => by
      rw [InteractionSemantics.Program.openRunN_succ,
        InteractionSemantics.Program.openRunN_succ]
      have hStepOne :=
        openStep_chainCombinedEff_congr_of_source context hSourceWF hTyped hIndependent hStep
      apply Simulation.Interaction.Rel.bind_custom hStepOne
      intro leftDone rightDone hOut
      rcases hOut with hjump | hterm
      · obtain ⟨next, s1', sf', h1, h2, hstep'⟩ := hjump
        subst h1; subst h2
        exact openRunN_chainCombinedEff_congr_of_source context hSourceWF hTyped hIndependent
          fuel next s1' sf' hstep'
      · obtain ⟨hrr, hnj⟩ := hterm
        cases hrr with
        | error he => exact .done (Or.inr ⟨.error he, by simp⟩)
        | ok hrrr =>
            cases hrrr with
            | jump lbl hSt => exact absurd rfl (hnj _ _)
            | fallthrough hSt => exact .done (Or.inr ⟨.ok (.fallthrough hSt), by simp⟩)
            | returnDispatch hSt => exact .done (Or.inr ⟨.ok (.returnDispatch hSt), by simp⟩)
            | halt kind hSt => exact .done (Or.inr ⟨.ok (.halt kind hSt), by simp⟩)
            | invalid hSt => exact .done (Or.inr ⟨.ok (.invalid hSt), by simp⟩)

/-- **Source-threaded prefix chain-combined congruence.** -/
theorem openRunNPrefix_chainCombinedEff_congr_of_source
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped) (hIndependent : cfg.ProgramCounterIndependent)
    (fuel : Nat) (label : Label) (s1 s_final : EVMState)
    (hStep : ChainCombinedStepRelEff (source := source) (cfg := cfg)
      context.calls label s1 s_final) :
    Simulation.Interaction.Rel InteractionCongruence.Block.RuntimeOutcomeRel
      (InteractionSemantics.Program.openRunNPrefix cfg fuel label s1)
      (InteractionSemantics.Program.openRunNPrefix
        (chainCanonProgram (preChainProgram cfg)) fuel label s_final) := by
  unfold InteractionSemantics.Program.openRunNPrefix
  have hRun :=
    openRunN_chainCombinedEff_congr_of_source context hSourceWF hTyped hIndependent
      fuel label s1 s_final hStep
  apply Simulation.Interaction.Rel.bind_custom hRun
  intro leftDone rightDone hOut
  rcases hOut with hjump | hterm
  · obtain ⟨next, s1', sf', h1, h2, _⟩ := hjump
    subst h1; subst h2
    exact .done (.error rfl)
  · obtain ⟨hrr, hnj⟩ := hterm
    cases hrr with
    | error he => exact .done (.error he)
    | ok hrrr =>
        cases hrrr with
        | jump lbl hSt => exact absurd rfl (hnj _ _)
        | fallthrough hSt => exact .done (.error rfl)
        | returnDispatch hSt => exact .done (.error rfl)
        | halt kind hSt => exact .done (.ok (Outcome.RuntimeRel.halt kind hSt))
        | invalid hSt => exact .done (.error rfl)

/-! ## Halted-path bridges for the openRunN splice sites -/

/-- On a non-jump left outcome, `ChainCombinedOutcomeRelEff` collapses to the plain
`RuntimeOutcomeRel` disjunct. -/
theorem runtimeOutcomeRel_of_chainCombinedOutcomeRelEff_of_not_jump
    {source : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List Structured.TypedCfgCompiler.DispatchSite}
    {a b : Except EVMException TypedCfg.Outcome}
    (h : ChainCombinedOutcomeRelEff (source := source) (cfg := cfg) calls a b)
    (hnj : ∀ (next : Label) (s : EVMState), a ≠ .ok (.jump next s)) :
    InteractionCongruence.Block.RuntimeOutcomeRel a b := by
  rcases h with hjump | hterm
  · obtain ⟨next, s1, sf, ha, _, _⟩ := hjump
    exact absurd ha (hnj next s1)
  · exact hterm.1

/-- **Halted-path bridge (a).** -/
theorem assemblySafeHalted_of_chainCombinedOutcomeRelEff
    {source : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List Structured.TypedCfgCompiler.DispatchSite}
    {a b : Except EVMException TypedCfg.Outcome}
    (h : ChainCombinedOutcomeRelEff (source := source) (cfg := cfg) calls a b)
    (hSafe : InteractionSemantics.Program.AssemblySafeHalted a) :
    InteractionSemantics.Program.AssemblySafeHalted b :=
  assemblySafeHalted_of_runtimeRel
    (runtimeOutcomeRel_of_chainCombinedOutcomeRelEff_of_not_jump h
      (assemblySafeHalted_not_jump hSafe))
    hSafe

/-- **Halted-path bridge (b).** -/
theorem runSimulates_of_chainCombinedOutcomeRelEff_halted
    {source : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List Structured.TypedCfgCompiler.DispatchSite}
    {target : Assembly.Program}
    {a m : Except EVMException TypedCfg.Outcome}
    {r : Assembly.Source.ExecutionOutcome}
    (h : ChainCombinedOutcomeRelEff (source := source) (cfg := cfg) calls a m)
    (hSim : TypedCfg.InteractionPreservation.OpenBlock.RunSimulates target m r)
    (hSafe : InteractionSemantics.Program.AssemblySafeHalted a) :
    TypedCfg.InteractionPreservation.OpenBlock.RunSimulates target a r :=
  TypedCfg.InteractionPreservation.OpenBlock.runtime_left
    (runtimeOutcomeRel_of_chainCombinedOutcomeRelEff_of_not_jump h
      (assemblySafeHalted_not_jump hSafe))
    hSim

/-- **Halted-path bridge (a), finished variant.** -/
theorem assemblySafeFinished_of_chainCombinedOutcomeRelEff
    {source : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List Structured.TypedCfgCompiler.DispatchSite}
    {a b : Except EVMException TypedCfg.Outcome}
    (h : ChainCombinedOutcomeRelEff (source := source) (cfg := cfg) calls a b)
    (hSafe : InteractionSemantics.Program.AssemblySafeFinished a) :
    InteractionSemantics.Program.AssemblySafeFinished b :=
  assemblySafeFinished_of_runtimeRel
    (runtimeOutcomeRel_of_chainCombinedOutcomeRelEff_of_not_jump h
      (assemblySafeFinished_not_jump hSafe))
    hSafe

/-- **Halted-path bridge (b), finished variant.** -/
theorem runSimulates_of_chainCombinedOutcomeRelEff_finished
    {source : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List Structured.TypedCfgCompiler.DispatchSite}
    {target : Assembly.Program}
    {a m : Except EVMException TypedCfg.Outcome}
    {r : Assembly.Source.ExecutionOutcome}
    (h : ChainCombinedOutcomeRelEff (source := source) (cfg := cfg) calls a m)
    (hSim : TypedCfg.InteractionPreservation.OpenBlock.RunSimulates target m r)
    (hSafe : InteractionSemantics.Program.AssemblySafeFinished a) :
    TypedCfg.InteractionPreservation.OpenBlock.RunSimulates target a r :=
  TypedCfg.InteractionPreservation.OpenBlock.runtime_left
    (runtimeOutcomeRel_of_chainCombinedOutcomeRelEff_of_not_jump h
      (assemblySafeFinished_not_jump hSafe))
    hSim

end Peephole
end TypedCfg
end EvmCompiler
