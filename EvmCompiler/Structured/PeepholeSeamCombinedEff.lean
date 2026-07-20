import EvmCompiler.Structured.PeepholeSeamCombined
import EvmCompiler.TypedCfg.PeepholeSeamCancelEffRuntime

/-!
# The corrected (clean-seam) combined transform `seamCancelProgramEff (peepholeProgram (normalizeProgram cfg))` (session-72)

Ports `PeepholeSeamCombined` to the corrected conjugating clean-seam canceller
`seamCancelProgramEff`.  Structurally mechanical over the shipped combined tower
with `SeamStepRel → SeamStepRelEff`, `targetFire? → cleanTgt?`, `seamBlock →
seamBlockEff`, `openStep_seamCancel_congr → openStep_seamCancelEff_congr`,
`seamStepRel_entry → seamStepRelEff_entry`.  The stack-length support
(`pendingSwap_stack_length`, `remapShape_length`) and the source-threaded combined
leg (`openStep_combined_congr_of_source`) are reused verbatim from the shipped
tower.  These lemmas have the argument shape of the combined `*_of_source` family,
so the OIC consumption sites swap `seamCombined` → `seamCombinedEff` names.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState SameRuntimeData)
open InteractionSemantics
open InteractionCongruence
open Structured.InteractionFrameConsistent (realizedWitnessFC)

/-! ## `seamBlockEff` input as a clean `cleanTgt?` branch (disjointness collapse) -/

/-- The corrected seam edit moves the input by `remapShape d` exactly when the block
is a clean target; otherwise it is untouched.  (In the clean-source case `cleanTgt?
= none` by disjointness, and the source edit leaves `input` fixed.) -/
theorem seamBlockEff_input_cleanTgt (program : Program) (block : Block) :
    (seamBlockEff program block).input =
      match cleanTgt? program block with
      | some d => remapShape d block.input
      | none => block.input := by
  rw [seamBlockEff_input]
  cases hct : cleanTgt? program block with
  | none => cases cleanSrc? program block <;> rfl
  | some d =>
      have hcs : cleanSrc? program block = none := by
        rcases cleanSrc?_cleanTgt?_disjoint program block with h | h
        · exact h
        · rw [h] at hct; exact absurd hct (by simp)
      rw [hcs]

/-! ## The carried 3-tuple invariant + disjunctive combined outcome relation -/

/-- The 3-tuple invariant carried at each reached block entry across the corrected
combined seam-cancel bisimulation. -/
def SeamCombinedStepRelEff {source : Structured.Program}
    {cfg : TypedCfg.Program}
    (calls : List Structured.TypedCfgCompiler.DispatchSite)
    (label : Label) (s1 s_c : EVMState) : Prop :=
  ∃ s2, realizedWitnessFC source cfg calls label s1 ∧
    SameRuntimeData s1 s2 ∧
    SeamStepRelEff (peepholeProgram (normalizeProgram cfg)) label s2 s_c

/-- The disjunctive one-step combined outcome relation for the corrected canceller. -/
def SeamCombinedOutcomeRelEff {source : Structured.Program}
    {cfg : TypedCfg.Program}
    (calls : List Structured.TypedCfgCompiler.DispatchSite) :
    Except EVMException TypedCfg.Outcome →
      Except EVMException TypedCfg.Outcome → Prop :=
  fun a b =>
    (∃ (next : Label) (s1 s_c : EVMState),
      a = .ok (.jump next s1) ∧ b = .ok (.jump next s_c) ∧
        SeamCombinedStepRelEff (source := source) (cfg := cfg) calls next s1 s_c)
    ∨ (InteractionCongruence.Block.RuntimeOutcomeRel a b ∧
        ∀ (next : Label) (s : EVMState), a ≠ .ok (.jump next s))

/-! ## Entry seed for the whole-program seam-combined bisimulation -/

/-- **Entry seed (`SeamCombinedStepRelEff`).** -/
theorem seamCombinedStepRelEff_entry_of_generated
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    {sourceState : Structured.RunState} {cfgState : EVMState}
    (hStateRel : Structured.TypedCfgPreservation.StateRel sourceState [] cfgState) :
    SeamCombinedStepRelEff (source := source) (cfg := cfg) context.calls
      cfg.entry cfgState cfgState := by
  refine ⟨cfgState, realizedWitnessFC_entry_of_generated context hStateRel,
    SameRuntimeData.refl cfgState, ?_⟩
  have h := seamStepRelEff_entry (peepholeProgram (normalizeProgram cfg)) cfgState
  simpa using h

/-! ## Source-threaded one-step seam-combined congruence -/

/-- **Source-threaded one-step corrected seam-combined congruence.** -/
theorem openStep_seamCombinedEff_congr_of_source
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped) (hIndependent : cfg.ProgramCounterIndependent)
    {label : Label} {state1 s_c : EVMState}
    (hStep : SeamCombinedStepRelEff (source := source) (cfg := cfg)
      context.calls label state1 s_c) :
    Simulation.Interaction.Rel
      (SeamCombinedOutcomeRelEff (source := source) (cfg := cfg) context.calls)
      (InteractionSemantics.Program.openStep cfg label state1)
      (InteractionSemantics.Program.openStep
        (seamCancelProgramEff (peepholeProgram (normalizeProgram cfg))) label s_c) := by
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
      StackRealizes (seamBlockEff P b0).input s_c := by
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
        rw [seamBlockEff_input_cleanTgt]
        unfold StackRealizes
        cases htf : cleanTgt? P b0 with
        | none =>
            simp only [htf, hInputEq]
            simp only [SeamStepRelEff, hFindP, htf] at hStepP
            have h3 : state2.stack.length = s_c.stack.length :=
              congrArg List.length (SameRuntimeData.stack_eq hStepP)
            omega
        | some d =>
            simp only [htf, remapShape_length, hInputEq]
            simp only [SeamStepRelEff, hFindP, htf] at hStepP
            have h3 : state2.stack.length = s_c.stack.length :=
              pendingSwap_stack_length hStepP
            omega
  have hSeam :=
    openStep_seamCancelEff_congr (program := P) hTypedP.1 hTypedP hIndepP hReal_cP hStepP
  refine Simulation.Interaction.Rel.mono
    (Simulation.Interaction.Rel.trans hCombined hSeam) ?_
  rintro x z ⟨y, hxy, hyz⟩
  cases hxy with
  | error he =>
      rcases hyz with hjump | hrr
      · obtain ⟨next, so, sc, hy, _, _⟩ := hjump
        exact absurd hy (by simp)
      · obtain ⟨hrrr, _⟩ := hrr
        cases hrrr with
        | error he2 => exact Or.inr ⟨.error (he.trans he2), by simp⟩
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
      · obtain ⟨hrrz0, hnj⟩ := hrr2
        cases hrrz0 with
        | ok hrrz =>
            refine Or.inr ⟨.ok (Outcome.RuntimeRel.trans hrr hrrz), ?_⟩
            rintro n s hEq
            rw [Except.ok.injEq] at hEq
            subst hEq
            cases hrr with
            | jump lbl hSt => exact hnj _ _ rfl

/-! ## Source-threaded fuel + prefix seam-combined congruences -/

/-- **Source-threaded fuel-bounded corrected seam-combined congruence.** -/
theorem openRunN_seamCombinedEff_congr_of_source
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped) (hIndependent : cfg.ProgramCounterIndependent) :
    ∀ (fuel : Nat) (label : Label) (state1 s_c : EVMState),
      SeamCombinedStepRelEff (source := source) (cfg := cfg) context.calls label state1 s_c →
      Simulation.Interaction.Rel
        (SeamCombinedOutcomeRelEff (source := source) (cfg := cfg) context.calls)
        (InteractionSemantics.Program.openRunN cfg fuel label state1)
        (InteractionSemantics.Program.openRunN
          (seamCancelProgramEff (peepholeProgram (normalizeProgram cfg))) fuel label s_c)
  | 0, label, state1, s_c, hStep => by
      simp only [InteractionSemantics.Program.openRunN_zero]
      exact .done (Or.inl ⟨label, state1, s_c, rfl, rfl, hStep⟩)
  | fuel + 1, label, state1, s_c, hStep => by
      rw [InteractionSemantics.Program.openRunN_succ,
        InteractionSemantics.Program.openRunN_succ]
      have hStepOne :=
        openStep_seamCombinedEff_congr_of_source context hSourceWF hTyped hIndependent hStep
      apply Simulation.Interaction.Rel.bind_custom hStepOne
      intro leftDone rightDone hOut
      rcases hOut with hjump | hterm
      · obtain ⟨next, s1', sc', h1, h2, hstep'⟩ := hjump
        subst h1; subst h2
        exact openRunN_seamCombinedEff_congr_of_source context hSourceWF hTyped hIndependent
          fuel next s1' sc' hstep'
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

/-- **Source-threaded prefix corrected seam-combined congruence.** -/
theorem openRunNPrefix_seamCombinedEff_congr_of_source
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped) (hIndependent : cfg.ProgramCounterIndependent)
    (fuel : Nat) (label : Label) (state1 s_c : EVMState)
    (hStep : SeamCombinedStepRelEff (source := source) (cfg := cfg)
      context.calls label state1 s_c) :
    Simulation.Interaction.Rel InteractionCongruence.Block.RuntimeOutcomeRel
      (InteractionSemantics.Program.openRunNPrefix cfg fuel label state1)
      (InteractionSemantics.Program.openRunNPrefix
        (seamCancelProgramEff (peepholeProgram (normalizeProgram cfg))) fuel label s_c) := by
  unfold InteractionSemantics.Program.openRunNPrefix
  have hRun :=
    openRunN_seamCombinedEff_congr_of_source context hSourceWF hTyped hIndependent
      fuel label state1 s_c hStep
  apply Simulation.Interaction.Rel.bind_custom hRun
  intro leftDone rightDone hOut
  rcases hOut with hjump | hterm
  · obtain ⟨next, s1', sc', h1, h2, _⟩ := hjump
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

/-- On a non-jump left outcome, `SeamCombinedOutcomeRelEff` collapses to the plain
`RuntimeOutcomeRel` disjunct. -/
theorem runtimeOutcomeRel_of_seamCombinedOutcomeRelEff_of_not_jump
    {source : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List Structured.TypedCfgCompiler.DispatchSite}
    {a b : Except EVMException TypedCfg.Outcome}
    (h : SeamCombinedOutcomeRelEff (source := source) (cfg := cfg) calls a b)
    (hnj : ∀ (next : Label) (s : EVMState), a ≠ .ok (.jump next s)) :
    InteractionCongruence.Block.RuntimeOutcomeRel a b := by
  rcases h with hjump | hterm
  · obtain ⟨next, s1, s_c, ha, _, _⟩ := hjump
    exact absurd ha (hnj next s1)
  · exact hterm.1

/-- **Halted-path bridge (a).** -/
theorem assemblySafeHalted_of_seamCombinedOutcomeRelEff
    {source : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List Structured.TypedCfgCompiler.DispatchSite}
    {a b : Except EVMException TypedCfg.Outcome}
    (h : SeamCombinedOutcomeRelEff (source := source) (cfg := cfg) calls a b)
    (hSafe : InteractionSemantics.Program.AssemblySafeHalted a) :
    InteractionSemantics.Program.AssemblySafeHalted b :=
  assemblySafeHalted_of_runtimeRel
    (runtimeOutcomeRel_of_seamCombinedOutcomeRelEff_of_not_jump h
      (assemblySafeHalted_not_jump hSafe))
    hSafe

/-- **Halted-path bridge (b).** -/
theorem runSimulates_of_seamCombinedOutcomeRelEff_halted
    {source : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List Structured.TypedCfgCompiler.DispatchSite}
    {target : Assembly.Program}
    {a m : Except EVMException TypedCfg.Outcome}
    {r : Assembly.Source.ExecutionOutcome}
    (h : SeamCombinedOutcomeRelEff (source := source) (cfg := cfg) calls a m)
    (hSim : TypedCfg.InteractionPreservation.OpenBlock.RunSimulates target m r)
    (hSafe : InteractionSemantics.Program.AssemblySafeHalted a) :
    TypedCfg.InteractionPreservation.OpenBlock.RunSimulates target a r :=
  TypedCfg.InteractionPreservation.OpenBlock.runtime_left
    (runtimeOutcomeRel_of_seamCombinedOutcomeRelEff_of_not_jump h
      (assemblySafeHalted_not_jump hSafe))
    hSim

/-- **Halted-path bridge (a), finished variant.** -/
theorem assemblySafeFinished_of_seamCombinedOutcomeRelEff
    {source : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List Structured.TypedCfgCompiler.DispatchSite}
    {a b : Except EVMException TypedCfg.Outcome}
    (h : SeamCombinedOutcomeRelEff (source := source) (cfg := cfg) calls a b)
    (hSafe : InteractionSemantics.Program.AssemblySafeFinished a) :
    InteractionSemantics.Program.AssemblySafeFinished b :=
  assemblySafeFinished_of_runtimeRel
    (runtimeOutcomeRel_of_seamCombinedOutcomeRelEff_of_not_jump h
      (assemblySafeFinished_not_jump hSafe))
    hSafe

/-- **Halted-path bridge (b), finished variant.** -/
theorem runSimulates_of_seamCombinedOutcomeRelEff_finished
    {source : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List Structured.TypedCfgCompiler.DispatchSite}
    {target : Assembly.Program}
    {a m : Except EVMException TypedCfg.Outcome}
    {r : Assembly.Source.ExecutionOutcome}
    (h : SeamCombinedOutcomeRelEff (source := source) (cfg := cfg) calls a m)
    (hSim : TypedCfg.InteractionPreservation.OpenBlock.RunSimulates target m r)
    (hSafe : InteractionSemantics.Program.AssemblySafeFinished a) :
    TypedCfg.InteractionPreservation.OpenBlock.RunSimulates target a r :=
  TypedCfg.InteractionPreservation.OpenBlock.runtime_left
    (runtimeOutcomeRel_of_seamCombinedOutcomeRelEff_of_not_jump h
      (assemblySafeFinished_not_jump hSafe))
    hSim

/-! ## The corrected seam-cancel fuel bound -/

/-- `lowerBodyFrom?` of a single well-typed `bindLocals` (lowers to no bytes). -/
theorem lowerBodyFrom?_singleton_bindLocals {off : Nat} {names : List String}
    {input output : Shape}
    (hType : Instr.type? (.bindLocals off names) input = some output) :
    Block.lowerBodyFrom? [Instr.bindLocals off names] input = some ([], output) := by
  have hla : Instr.lowerAt? (.bindLocals off names) input = some ([], output) := by
    simp [Instr.lowerAt?, hType, Instr.lower?]
  rw [lowerBodyFrom?_cons, hla]
  simp [Block.lowerBodyFrom?]

/-- **Per-block corrected seam fuel bound.** -/
theorem compiledBlock_fuelBudget_seamBlockEff_le {program : Program} {b0 : Block}
    (hUnique : program.LabelsUnique) (hAll : program.AllBlocksTyped)
    (hmem : b0 ∈ program.blocks) :
    InteractionSemantics.CompiledBlock.fuelBudget (seamBlockEff program b0) ≤
      InteractionSemantics.CompiledBlock.fuelBudget b0 := by
  have hTyped := blockWellTyped_of_mem hAll hmem
  have hBodyEq := seamBlockEff_body program b0
  have hInEq := seamBlockEff_input program b0
  have hOutEq := seamBlockEff_output program b0
  have hTermEq := seamBlockEff_term program b0
  cases hs : cleanSrc? program b0 with
  | some d =>
      -- Source: edited body = [bindLocals names'] (lowers to []); original adds a swap.
      obtain ⟨names, hbody, hswapT, hbindO, hbindC⟩ := cleanSrc_body_facts hTyped hs
      obtain ⟨hsr, _, bLabel, B, hterm, _, _⟩ := cleanSrc?_spec hs
      have hct : cleanTgt? program b0 = none := by
        rcases cleanSrc?_cleanTgt?_disjoint program b0 with h | h
        · rw [h] at hs; exact absurd hs (by simp)
        · exact h
      have hTermJump : ∀ s : Shape, b0.term.lowerAt? s = some [Assembly.Instr.jump bLabel] := by
        intro s; rw [hterm]; rfl
      unfold InteractionSemantics.CompiledBlock.fuelBudget
      simp only [hBodyEq, hInEq, hOutEq, hTermEq, hs]
      simp only [hbody, List.tail_cons, List.map_cons, List.map_nil, conjBind]
      -- edited: lowerBodyFrom? [bindLocals names'] b0.input = some ([], remapShape d b0.output)
      rw [lowerBodyFrom?_singleton_bindLocals hbindC]
      simp only [↓reduceIte, hTermJump, List.length_nil]
      -- original: lowerBodyFrom? [swap d, bindLocals names] b0.input
      obtain ⟨sc, hsc⟩ := lowerAt?_swap_of_type? hswapT
      have hLowOrig : Block.lowerBodyFrom? [Instr.swap d, Instr.bindLocals 0 names] b0.input
          = some (sc ++ [], b0.output) := by
        rw [lowerBodyFrom?_cons, hsc]
        simp only [Option.bind]
        rw [lowerBodyFrom?_singleton_bindLocals hbindO]
      simp only [hLowOrig, ↓reduceIte, hTermJump, List.length_append, List.length_nil]
      omega
  | none =>
      cases ht : cleanTgt? program b0 with
      | none =>
          have : seamBlockEff program b0 = b0 := by
            unfold seamBlockEff; rw [hs, ht]
          rw [this]
      | some d =>
          -- Target only: drop the head swap, re-type the input.
          have hhd := cleanTgt_head_swap hUnique hmem ht
          have hdecomp : b0.body = Instr.swap d :: b0.body.tail := head_tail_decomp hhd
          have hbodyT := hTyped.1
          rw [hdecomp, bodyType?_cons, Option.bind_eq_some_iff] at hbodyT
          obtain ⟨m, htype, hrest⟩ := hbodyT
          have hmid : m = remapShape d b0.input := type?_swap_eq_remapShape htype
          subst hmid
          unfold InteractionSemantics.CompiledBlock.fuelBudget
          simp only [hBodyEq, hInEq, hOutEq, hTermEq, hs, ht]
          cases hLowEdit : Block.lowerBodyFrom? b0.body.tail (remapShape d b0.input) with
          | none => simp
          | some pair =>
              obtain ⟨bc, o⟩ := pair
              have hoEq : o = b0.output := by
                have := bodyType?_of_lowerBodyFrom? b0.body.tail hLowEdit
                rw [hrest] at this; exact (Option.some.inj this).symm
              subst hoEq
              obtain ⟨hc, hhc⟩ := lowerAt?_swap_of_type? htype
              have hLowOrig : Block.lowerBodyFrom? b0.body b0.input
                  = some (hc ++ bc, b0.output) := by
                conv_lhs => rw [hdecomp]
                rw [lowerBodyFrom?_cons, hhc]
                simp [Option.bind, hLowEdit]
              simp only [hLowOrig, ↓reduceIte]
              cases hTerm : b0.term.lowerAt? b0.output with
              | none => simp
              | some tc => simp only [List.length_append]; omega

/-- Whole-block-list corrected seam fuel-budget monotonicity. -/
theorem fuelBudget_seamBlocksEff_le {program : Program}
    (hUnique : program.LabelsUnique) (hAll : program.AllBlocksTyped) :
    ∀ (blocks : List Block), (∀ b ∈ blocks, b ∈ program.blocks) →
      (blocks.map fun b =>
          InteractionSemantics.CompiledBlock.fuelBudget (seamBlockEff program b)).sum ≤
        (blocks.map InteractionSemantics.CompiledBlock.fuelBudget).sum
  | [], _ => by simp
  | b :: bs, hAllMem => by
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (compiledBlock_fuelBudget_seamBlockEff_le hUnique hAll
          (hAllMem b (List.mem_cons_self ..)))
        (fuelBudget_seamBlocksEff_le hUnique hAll bs
          (fun b' hb' => hAllMem b' (List.mem_cons_of_mem _ hb')))

/-- **The corrected seam cancellation does not increase the whole-program fuel budget.** -/
theorem fuelBudget_seamCancelProgramEff_le {program : Program}
    (hWT : program.WellTyped) :
    InteractionSemantics.CompiledProgram.fuelBudget (seamCancelProgramEff program) ≤
      InteractionSemantics.CompiledProgram.fuelBudget program := by
  unfold InteractionSemantics.CompiledProgram.fuelBudget
  rw [seamCancelProgramEff_blocks, List.map_map]
  obtain ⟨hUnique, hAll, _, _⟩ := hWT
  exact fuelBudget_seamBlocksEff_le hUnique hAll program.blocks (fun b hb => hb)

/-- **Combined corrected seam fuel bound.** -/
theorem fuelBudget_seamCombinedEff_le (program : Program) (hWT : program.WellTyped) :
    InteractionSemantics.CompiledProgram.fuelBudget
        (seamCancelProgramEff (peepholeProgram (normalizeProgram program))) ≤
      InteractionSemantics.CompiledProgram.fuelBudget program :=
  le_trans
    (fuelBudget_seamCancelProgramEff_le
      (peepholeProgram_wellTyped (normalizeProgram_wellTyped hWT)))
    (fuelBudget_combined_le program hWT)

end Peephole
end TypedCfg
end EvmCompiler
