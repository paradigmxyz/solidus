import EvmCompiler.Structured.PeepholeNoopSwapCombined
import EvmCompiler.TypedCfg.PeepholeSeamCancel

/-!
# The seam-cancelled combined transform `seamCancelProgram (peepholeProgram (normalizeProgram cfg))`
(session-66)

The splice route (PEEPHOLE_PROGRESS §Session-65 frontier).  We compose the
already-banked source-threaded combined congruence
(`openStep_combined_congr_of_source`, relating `cfg` to
`P := peepholeProgram (normalizeProgram cfg)`) with the banked whole-program
one-step seam-cancel congruence (`openStep_seamCancel_congr`, relating `P` to
`seamCancelProgram P`) via `Rel.trans`.

The seam leg's per-entry `StackRealizes (seamBlock P b0).input s_c` guard is
DERIVABLE, not axiomatic: `stackRealizes_of_realizedWitnessFC_total` on `cfg`,
transported through `findBlock?_{peephole,normalize}Program` +
`{peephole,normalize}Block_input`, then along `SameRuntimeData` stack equality
and the pending-swap / `remapShape` stack-**length** preservation carried by
`SeamStepRel`.

These lemmas have the argument shape of the combined `*_of_source` family, so the
OIC consumption sites swap `combined` → `seamCombined` names and supply the seam
guards.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState SameRuntimeData)
open InteractionSemantics
open InteractionCongruence
open Structured.InteractionFrameConsistent (realizedWitnessFC)

/-! ## Stack-length preservation support lemmas -/

/-- `remapShape` (the `0 ↔ d+1` transposition) preserves shape length. -/
@[simp] theorem remapShape_length (d : Nat) (s : Shape) :
    (remapShape d s).length = s.length := by
  simp [remapShape, Shape.length]

/-- `EvmYul.swap n` (when it succeeds) preserves the runtime stack length. -/
theorem swap_ok_stack_length {n : Nat} {s next : EVMState} (hn : 1 ≤ n)
    (h : EvmYul.swap n s = .ok next) : next.stack.length = s.stack.length := by
  have hlen : n + 1 ≤ s.stack.length := by
    unfold EvmYul.swap at h
    by_cases hc : (List.take (n + 1) s.stack).length = n + 1
    · rw [List.length_take] at hc; omega
    · rw [if_neg hc] at h; simp at h
  obtain ⟨top, last, front, suffix, hStack, hfront⟩ :=
    exists_swap_decomp s.stack n hn hlen
  have h1 : EvmYul.swap n s =
      .ok (s.replaceStackAndIncrPC (last :: front ++ [top] ++ suffix)) := by
    have hsn := Assembly.StackShuffle.swap_snoc
      (state := s) (front := front) (suffix := suffix) (top := top) (last := last)
    rw [hfront] at hsn
    rw [← hStack] at hsn
    exact hsn
  rw [h1] at h
  injection h with h
  subst h
  have hstack :
      (s.replaceStackAndIncrPC (last :: front ++ [top] ++ suffix)).stack =
        last :: front ++ [top] ++ suffix := by
    simp [EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]
  rw [hstack, hStack]
  simp [List.length_append, Nat.add_comm, Nat.add_left_comm]

/-- A `PendingSwap` relates two states of equal runtime stack length. -/
theorem pendingSwap_stack_length {d : Nat} {s_c s_o : EVMState}
    (h : PendingSwap d s_c s_o) :
    s_o.stack.length = s_c.stack.length := by
  obtain ⟨next, hswap, hsync⟩ := h
  have h1 := swap_ok_stack_length (n := d + 1) (by omega) hswap
  have h2 := SameRuntimeData.stack_eq hsync
  rw [← h1, h2]

/-! ## The carried 3-tuple invariant + disjunctive combined outcome relation -/

/-- The 3-tuple invariant carried at each reached block entry across the combined
seam-cancel bisimulation: the ORIGINAL `cfg` state `s1` realizes the source
witness, is `SameRuntimeData` to an intermediate `P`-state `s2`, and that `P`-state
stands in the `SeamStepRel` (SRD unless the block tails a fired seam) to the
seam-cancelled state `s_c`. -/
def SeamCombinedStepRel {source : Structured.Program}
    {cfg : TypedCfg.Program}
    (calls : List Structured.TypedCfgCompiler.DispatchSite)
    (label : Label) (s1 s_c : EVMState) : Prop :=
  ∃ s2, realizedWitnessFC source cfg calls label s1 ∧
    SameRuntimeData s1 s2 ∧
    SeamStepRel (peepholeProgram (normalizeProgram cfg)) label s2 s_c

/-- The disjunctive one-step combined outcome relation.  Either both outcomes are
a `.jump` to the same successor carrying `SeamCombinedStepRel` there, or they are
plain `RuntimeOutcomeRel` (halts / fallthroughs / errors — always from re-synced,
witness-carrying states). -/
def SeamCombinedOutcomeRel {source : Structured.Program}
    {cfg : TypedCfg.Program}
    (calls : List Structured.TypedCfgCompiler.DispatchSite) :
    Except EVMException TypedCfg.Outcome →
      Except EVMException TypedCfg.Outcome → Prop :=
  fun a b =>
    (∃ (next : Label) (s1 s_c : EVMState),
      a = .ok (.jump next s1) ∧ b = .ok (.jump next s_c) ∧
        SeamCombinedStepRel (source := source) (cfg := cfg) calls next s1 s_c)
    ∨ InteractionCongruence.Block.RuntimeOutcomeRel a b

/-! ## Source-threaded one-step seam-combined congruence -/

/-- **Source-threaded one-step seam-combined congruence.**  `Rel.trans` of the
combined step (source-threaded, LEFT tree `cfg`, carrying the successor witness)
and the seam-cancel step (`program := peepholeProgram (normalizeProgram cfg)`).
The seam leg's per-entry `StackRealizes` guard is derived from the source witness
transported through the pass block-input equalities and `SeamStepRel`'s
stack-length preservation. -/
theorem openStep_seamCombined_congr_of_source
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped) (hIndependent : cfg.ProgramCounterIndependent)
    {label : Label} {state1 s_c : EVMState}
    (hStep : SeamCombinedStepRel (source := source) (cfg := cfg)
      context.calls label state1 s_c) :
    Simulation.Interaction.Rel
      (SeamCombinedOutcomeRel (source := source) (cfg := cfg) context.calls)
      (InteractionSemantics.Program.openStep cfg label state1)
      (InteractionSemantics.Program.openStep
        (seamCancelProgram (peepholeProgram (normalizeProgram cfg))) label s_c) := by
  obtain ⟨state2, hReal, hRel, hStepP⟩ := hStep
  set P := peepholeProgram (normalizeProgram cfg) with hP
  have hTypedP : P.WellTyped :=
    peepholeProgram_wellTyped (normalizeProgram_wellTyped hTyped)
  have hIndepP : P.ProgramCounterIndependent :=
    combined_programCounterIndependent hIndependent
  have hCombined :=
    openStep_combined_congr_of_source context hSourceWF hTyped hIndependent hReal hRel
  -- Derive the seam leg's per-entry `StackRealizes` guard.
  have hReal_cP : ∀ b0, P.findBlock? label = some b0 →
      StackRealizes (seamBlock P b0).input s_c := by
    intro b0 hFindP
    have hFindP' := hFindP
    rw [hP, findBlock?_peepholeProgram, findBlock?_normalizeProgram] at hFindP'
    cases hf0 : cfg.findBlock? label with
    | none => rw [hf0] at hFindP'; simp at hFindP'
    | some bcfg =>
        rw [hf0] at hFindP'
        simp only [Option.map_some, Option.some.injEq] at hFindP'
        have hInputEq : b0.input = bcfg.input := by rw [← hFindP']; simp
        have hRcfg : bcfg.input.length ≤ state1.stack.length :=
          Structured.TokenBottomThread.stackRealizes_of_realizedWitnessFC_total
            context hSourceWF hReal hf0
        have hLen12 : state1.stack.length = state2.stack.length :=
          congrArg List.length (SameRuntimeData.stack_eq hRel)
        rw [seamBlock_input]
        unfold StackRealizes
        cases htf : targetFire? P b0 with
        | none =>
            simp only [htf, hInputEq]
            simp only [SeamStepRel, hFindP, htf] at hStepP
            have h3 : state2.stack.length = s_c.stack.length :=
              congrArg List.length (SameRuntimeData.stack_eq hStepP)
            omega
        | some d =>
            simp only [htf, remapShape_length, hInputEq]
            simp only [SeamStepRel, hFindP, htf] at hStepP
            have h3 : state2.stack.length = s_c.stack.length :=
              pendingSwap_stack_length hStepP
            omega
  have hSeam :=
    openStep_seamCancel_congr (program := P) hTypedP.1 hTypedP hIndepP hReal_cP hStepP
  refine Simulation.Interaction.Rel.mono
    (Simulation.Interaction.Rel.trans hCombined hSeam) ?_
  rintro x z ⟨y, hxy, hyz⟩
  cases hxy with
  | error he =>
      rcases hyz with hjump | hrr
      · obtain ⟨next, so, sc, hy, _, _⟩ := hjump
        exact absurd hy (by simp)
      · cases hrr with
        | error he2 => exact Or.inr (.error (he.trans he2))
  | ok hok =>
      obtain ⟨hrr, hwit⟩ := hok
      rcases hyz with hjump | hrr2
      · obtain ⟨next, so, sc, hy, hz, hstepP⟩ := hjump
        rw [Except.ok.injEq] at hy
        subst hy
        cases hrr with
        | jump lbl hSt =>
            refine Or.inl ⟨next, _, sc, rfl, hz, ?_⟩
            exact ⟨so, hwit next _ rfl, hSt, hstepP⟩
      · cases hrr2 with
        | ok hrrz => exact Or.inr (.ok (Outcome.RuntimeRel.trans hrr hrrz))

end Peephole
end TypedCfg
end EvmCompiler
