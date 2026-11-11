import EvmCompiler.TypedCfg.VirtualStackPairPreservation
import EvmCompiler.TypedCfg.ShuffleCanonChainCombined
import EvmCompiler.TypedCfg.BlockReorderCanon
import EvmCompiler.TypedCfg.ConstTrueBranch

/-!
# Source-threaded composition for virtual-stack canonicalisation

This module composes the existing source-to-chain proof with the pure block
reorder and the certified two-block virtual-stack scheduler.  The scheduler is
allowed to fire only on a block that still contains a runtime event.  A
chain-canonicalised head or consumed block contains only shuffles/metadata, so
that guard also supplies the runtime stack-realisation fact required by the
pair proof.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState SameRuntimeData)
open InteractionCongruence

abbrev virtualBase (cfg : Program) : Program :=
  ConstTrueBranch.optimizedProgram
    (ShuffleCanon.chainCanonProgram (preChainProgram cfg))

abbrev virtualProgram (cfg : Program) : Program :=
  VirtualStack.canonProgram (virtualBase cfg)

@[simp] theorem virtualBase_entry (cfg : Program) :
    (virtualBase cfg).entry = cfg.entry := by
  simp [virtualBase, ConstTrueBranch.optimizedProgram,
    preChainProgram]

@[simp] theorem virtualProgram_entry (cfg : Program) :
    (virtualProgram cfg).entry = cfg.entry := by
  simp [virtualProgram]

theorem VirtualStack.hasRuntimeEvent_eq_false_of_chainInstr
    {block : Block}
    (hChain : ∀ instr ∈ block.body, ChainInstr instr) :
    VirtualStack.hasRuntimeEvent block = false := by
  unfold VirtualStack.hasRuntimeEvent
  rw [List.any_eq_false]
  intro instr hInstr
  have h := hChain instr hInstr
  cases instr <;> simp [ChainInstr] at h ⊢

theorem VirtualStack.hasRuntimeEvent_chainHead_false
    {program : Program} (hUnique : program.LabelsUnique)
    {block : Block} (hBlock : block ∈ program.blocks)
    {body : List Instr} {out : Shape}
    (hLookup :
      (ShuffleCanon.editTable program).lookup block.label =
        some (.head body out)) :
    VirtualStack.hasRuntimeEvent
        (ShuffleCanon.applyEdit
          (ShuffleCanon.editTable program) block) =
      false := by
  obtain ⟨next, merged, depths, hDepths, hTerm, hNext,
      hBody, hPositions, hResidual⟩ :=
    (chainResidualSpec hUnique).head hBlock hLookup
  apply VirtualStack.hasRuntimeEvent_eq_false_of_chainInstr
  intro instr hInstr
  rw [ShuffleCanon.applyEdit_body_eq, hLookup, hBody] at hInstr
  exact chainInstr_canonBody _ _ instr hInstr

theorem VirtualStack.hasRuntimeEvent_chainConsumed_false
    {program : Program} {block : Block} {out : Shape}
    (hLookup :
      (ShuffleCanon.editTable program).lookup block.label =
        some (.consumed out)) :
    VirtualStack.hasRuntimeEvent
        (ShuffleCanon.applyEdit
          (ShuffleCanon.editTable program) block) =
      false := by
  unfold VirtualStack.hasRuntimeEvent
  rw [ShuffleCanon.applyEdit_body_eq, hLookup]
  rfl

theorem VirtualStack.hasRuntimeEvent_constTrueBlock_false
    {block : Block}
    (hFalse : VirtualStack.hasRuntimeEvent block = false) :
    VirtualStack.hasRuntimeEvent
        (ConstTrueBranch.constTrueBlock block) = false := by
  unfold ConstTrueBranch.constTrueBlock
  split
  next value target fallthrough hLast hTerm =>
    split
    next hValue =>
      unfold VirtualStack.hasRuntimeEvent at hFalse ⊢
      rw [List.any_eq_false] at hFalse ⊢
      intro instr hInstr
      exact hFalse instr (List.mem_of_mem_dropLast hInstr)
    next => exact hFalse
  next => exact hFalse

/--
A virtual-stack eligible block can only come from a chain block that was left
untouched by chain canonicalisation.  Therefore its entry shape is realised by
the source-threaded chain state.
-/
theorem stackRealizes_virtualEligible_of_chainCombined
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext
        source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped)
    {label : Label} {sourceState chainState constState : EVMState}
    (hCombined :
      ChainCombinedStepRelEff (source := source) (cfg := cfg)
        context.calls label sourceState chainState)
    (hConst : SameRuntimeData chainState constState)
    {block : Block}
    (hFind :
      (virtualBase cfg).findBlock? label = some block)
    (hEvent :
      VirtualStack.hasRuntimeEvent block = true) :
    StackRealizes block.input constState := by
  let Q := preChainProgram cfg
  let C := ShuffleCanon.chainCanonProgram Q
  let T := ConstTrueBranch.constTrueProgram C
  have hTypedQ : Q.WellTyped :=
    seamCancelProgramEff_wellTyped
      (peepholeProgram_wellTyped
        (normalizeProgram_wellTyped hTyped))
  have hUniqueQ : Q.LabelsUnique := hTypedQ.1
  have hTypedC : C.WellTyped :=
    ShuffleCanon.chainCanonProgram_WellTyped hTypedQ
  have hTypedT : T.WellTyped :=
    ConstTrueBranch.wellTyped_constTrueProgram hTypedC
  have hBlockR : block ∈ (virtualBase cfg).blocks := by
    unfold Program.findBlock? at hFind
    exact List.mem_of_find?_eq_some hFind
  have hUniqueR : (virtualBase cfg).LabelsUnique := by
    exact BlockReorder.reorderProgram_labelsUnique T
  have hBlockLabel : block.label = label := by
    unfold Program.findBlock? at hFind
    have hFound := List.find?_some hFind
    simpa using hFound
  have hBlockT : block ∈ T.blocks := by
    exact BlockReorder.reorderProgram_blocks_mem T hBlockR
  rw [ConstTrueBranch.constTrueProgram_blocks,
    List.mem_map] at hBlockT
  obtain ⟨chainBlock, hBlockC, hConstApplied⟩ := hBlockT
  rw [ShuffleCanon.chainCanonProgram_blocks,
    List.mem_map] at hBlockC
  obtain ⟨original, hOriginal, hChainApplied⟩ := hBlockC
  have hChainBlockLabel : chainBlock.label = label := by
    rw [← ConstTrueBranch.constTrueBlock_label chainBlock,
      hConstApplied]
    exact hBlockLabel
  cases hChainLookup :
      (ShuffleCanon.editTable Q).lookup original.label with
  | none =>
      have hOriginalEq : original = chainBlock := by
        simpa [ShuffleCanon.applyEdit, hChainLookup] using hChainApplied
      obtain ⟨seamState, hSeam, hChain⟩ := hCombined
      have hOriginalLabel : original.label = label := by
        rw [hOriginalEq]
        exact hChainBlockLabel
      have hFindQ : Q.findBlock? label = some original := by
        rw [← hOriginalLabel]
        exact Program.findBlock?_eq_some_of_mem hUniqueQ hOriginal
      have hRealMid :=
        stackRealizes_preChain_of_seamCombined
          context hSourceWF hSeam original hFindQ
      have hState : SameRuntimeData seamState chainState := by
        unfold ChainStepRel at hChain
        rw [← hOriginalLabel, hChainLookup] at hChain
        exact hChain
      have hFinalState : SameRuntimeData seamState constState :=
        SameRuntimeData.trans hState hConst
      unfold StackRealizes at hRealMid ⊢
      rw [← SameRuntimeData.stack_eq hFinalState]
      simpa [hOriginalEq, ← hConstApplied] using hRealMid
  | some edit =>
      cases edit with
      | head body out =>
          have hFalse :=
            VirtualStack.hasRuntimeEvent_chainHead_false
              hUniqueQ hOriginal hChainLookup
          have hConstFalse :=
            VirtualStack.hasRuntimeEvent_constTrueBlock_false hFalse
          rw [hChainApplied, hConstApplied, hEvent] at hConstFalse
          contradiction
      | consumed out =>
          have hFalse :=
            VirtualStack.hasRuntimeEvent_chainConsumed_false
              hChainLookup
          have hConstFalse :=
            VirtualStack.hasRuntimeEvent_constTrueBlock_false hFalse
          rw [hChainApplied, hConstApplied, hEvent] at hConstFalse
          contradiction

/--
Compatibility wrapper for callers that obtain eligibility from a certified
left edit rather than carrying it explicitly.
-/
theorem stackRealizes_virtualLeft_of_chainCombined
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext
        source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped)
    {label : Label} {sourceState chainState constState : EVMState}
    (hCombined :
      ChainCombinedStepRelEff (source := source) (cfg := cfg)
        context.calls label sourceState chainState)
    (hConst : SameRuntimeData chainState constState)
    {block : Block} {choice : VirtualStack.PairChoice}
    (hFind :
      (virtualBase cfg).findBlock? label = some block)
    (hVirtual :
      (VirtualStack.editTable (virtualBase cfg)).lookup block.label =
        some (.left choice)) :
    StackRealizes block.input constState := by
  have hBlock : block ∈ (virtualBase cfg).blocks := by
    unfold Program.findBlock? at hFind
    exact List.mem_of_find?_eq_some hFind
  have hUnique : (virtualBase cfg).LabelsUnique := by
    let Q := preChainProgram cfg
    let C := ShuffleCanon.chainCanonProgram Q
    let T := ConstTrueBranch.constTrueProgram C
    exact BlockReorder.reorderProgram_labelsUnique T
  obtain ⟨hBlockEq, hValid, _⟩ :=
    VirtualStack.block_eq_sourceLeft_of_lookup
      hUnique hBlock hVirtual
  apply stackRealizes_virtualEligible_of_chainCombined
    context hSourceWF hTyped hCombined hConst hFind
  rw [hBlockEq]
  exact hValid.leftHasEvent

/-- Source-to-virtual invariant carried at every reached block entry. -/
def VirtualCombinedStepRelEff {source : Structured.Program}
    {cfg : Program}
    (calls : List Structured.TypedCfgCompiler.DispatchSite)
    (label : Label) (sourceState finalState : EVMState) : Prop :=
  ∃ chainState constState,
    ChainCombinedStepRelEff (source := source) (cfg := cfg)
        calls label sourceState chainState ∧
      SameRuntimeData chainState constState ∧
      VirtualStack.CanonStepRel
        (virtualBase cfg) label constState finalState

/-- One-step outcome relation for the complete source-to-virtual pipeline. -/
def VirtualCombinedOutcomeRelEff {source : Structured.Program}
    {cfg : Program}
    (calls : List Structured.TypedCfgCompiler.DispatchSite) :
    Except EVMException Outcome → Except EVMException Outcome → Prop :=
  fun sourceOutcome finalOutcome =>
    (∃ (next : Label) (sourceState finalState : EVMState),
      sourceOutcome = .ok (.jump next sourceState) ∧
        finalOutcome = .ok (.jump next finalState) ∧
        VirtualCombinedStepRelEff
          (source := source) (cfg := cfg)
          calls next sourceState finalState)
    ∨ (InteractionCongruence.Block.RuntimeOutcomeRel
          sourceOutcome finalOutcome ∧
        ∀ (next : Label) (state : EVMState),
          sourceOutcome ≠ .ok (.jump next state))

theorem virtualCombinedStepRelEff_entry_of_generated
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext
        source entryShapes cfg)
    {sourceState : Structured.RunState} {cfgState : EVMState}
    (hStateRel :
      Structured.TypedCfgPreservation.StateRel
        sourceState [] cfgState) :
    VirtualCombinedStepRelEff
      (source := source) (cfg := cfg) context.calls
      cfg.entry cfgState cfgState := by
  refine
    ⟨cfgState, cfgState,
      chainCombinedStepRelEff_entry_of_generated context hStateRel,
      SameRuntimeData.refl cfgState,
      ?_⟩
  simpa [virtualBase, preChainProgram] using
    VirtualStack.canonStepRel_entry (virtualBase cfg) cfgState

/-- Exact one-step composition of the chain/reorder pipeline and the certified
virtual-stack pair scheduler. -/
theorem openStep_virtualCombinedEff_congr_of_source
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext
        source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped)
    (hIndependent : cfg.ProgramCounterIndependent)
    (hVirtualTyped : (virtualProgram cfg).WellTyped)
    {label : Label} {sourceState finalState : EVMState}
    (hStep :
      VirtualCombinedStepRelEff
        (source := source) (cfg := cfg)
        context.calls label sourceState finalState) :
    Simulation.Interaction.Rel
      (VirtualCombinedOutcomeRelEff
        (source := source) (cfg := cfg) context.calls)
      (InteractionSemantics.Program.openStep
        cfg label sourceState)
      (InteractionSemantics.Program.openStep
        (virtualProgram cfg) label finalState) := by
  obtain
    ⟨chainState, constState, hChainStep,
      hConstState, hVirtualStep⟩ := hStep
  let Q := preChainProgram cfg
  let C := ShuffleCanon.chainCanonProgram Q
  let T := ConstTrueBranch.constTrueProgram C
  let R := BlockReorder.reorderProgram T
  have hTypedQ : Q.WellTyped :=
    seamCancelProgramEff_wellTyped
      (peepholeProgram_wellTyped
        (normalizeProgram_wellTyped hTyped))
  have hTypedC : C.WellTyped :=
    ShuffleCanon.chainCanonProgram_WellTyped hTypedQ
  have hTypedT : T.WellTyped :=
    ConstTrueBranch.wellTyped_constTrueProgram hTypedC
  have hTypedR : R.WellTyped :=
    BlockReorder.wellTyped_reorderProgram T hTypedT
  have hIndependentQ : Q.ProgramCounterIndependent :=
    seamCancelProgramEff_programCounterIndependent
      (combined_programCounterIndependent hIndependent)
  have hIndependentC : C.ProgramCounterIndependent :=
    ShuffleCanon.chainCanonProgram_programCounterIndependent
      hIndependentQ
  have hIndependentT : T.ProgramCounterIndependent :=
    ConstTrueBranch.programCounterIndependent_constTrueProgram
      hIndependentC
  have hIndependentR : R.ProgramCounterIndependent :=
    BlockReorder.programCounterIndependent_reorderProgram
      T hIndependentT
  have hChain :=
    openStep_chainCombinedEff_congr_of_source
      context hSourceWF hTyped hIndependent hChainStep
  have hConst :=
    ConstTrueBranch.openStep_constTrueProgram_congr
      hTypedC hIndependentC hConstState (label := label)
  have hRealizesFirst :
      ∀ block choice,
        R.findBlock? label = some block →
          (VirtualStack.editTable R).lookup block.label =
              some (.left choice) →
            StackRealizes block.input constState := by
    intro block choice hFind hLookup
    have hBlock : block ∈ R.blocks := by
      unfold Program.findBlock? at hFind
      exact List.mem_of_find?_eq_some hFind
    obtain ⟨hBlockEq, hValid, hRightBlock⟩ :=
      VirtualStack.block_eq_sourceLeft_of_lookup
        hTypedR.1 hBlock hLookup
    have hEvent :
        VirtualStack.hasRuntimeEvent block = true := by
      rw [hBlockEq]
      simpa [VirtualStack.pairEligible] using
        hValid.leftEligible
    exact stackRealizes_virtualEligible_of_chainCombined
      context hSourceWF hTyped hChainStep hConstState
        (by simpa [virtualBase, R, T, C, Q] using hFind)
        hEvent
  have hRealizesSecond :
      ∀ (hMiddleTyped :
          (VirtualStack.canonProgramOnce R).WellTyped)
          middle block choice,
        VirtualStack.PairStepRel R label constState middle →
          (VirtualStack.canonProgramOnce R).findBlock? label =
              some block →
            (VirtualStack.editTable
                (VirtualStack.canonProgramOnce R)).lookup
                  block.label =
                some (.left choice) →
              StackRealizes block.input middle := by
    intro hMiddleTyped middle block choice
      hFirstStep hFind hSecondLookup
    apply
      VirtualStack.stackRealizes_canonProgramOnce_of_pairStepRel
        hTypedR.1 hMiddleTyped
    · intro original hOriginalFind hNoRight
      have hOriginalMem : original ∈ R.blocks := by
        unfold Program.findBlock? at hOriginalFind
        exact List.mem_of_find?_eq_some hOriginalFind
      have hOriginalLabel : original.label = label := by
        unfold Program.findBlock? at hOriginalFind
        have hFound := List.find?_some hOriginalFind
        simpa using hFound
      have hBlockMem :
          block ∈ (VirtualStack.canonProgramOnce R).blocks := by
        unfold Program.findBlock? at hFind
        exact List.mem_of_find?_eq_some hFind
      obtain ⟨hBlockEq, hSecondValid, hSecondRight⟩ :=
        VirtualStack.block_eq_sourceLeft_of_lookup
          hMiddleTyped.1 hBlockMem hSecondLookup
      have hSecondEvent :
          VirtualStack.hasRuntimeEvent block = true := by
        rw [hBlockEq]
        simpa [VirtualStack.pairEligible] using
          hSecondValid.leftEligible
      have hAppliedEq :
          VirtualStack.applyEdit
              (VirtualStack.editTable R) original = block := by
        rw [VirtualStack.findBlock?_canonProgram,
          hOriginalFind] at hFind
        simpa using hFind
      cases hFirstLookup :
          (VirtualStack.editTable R).lookup original.label with
      | none =>
          have hOriginalEq : original = block := by
            simpa [VirtualStack.applyEdit, hFirstLookup] using
              hAppliedEq
          have hEvent :
              VirtualStack.hasRuntimeEvent original = true := by
            rw [hOriginalEq]
            exact hSecondEvent
          exact stackRealizes_virtualEligible_of_chainCombined
            context hSourceWF hTyped hChainStep hConstState
              (by simpa [virtualBase, R, T, C, Q] using
                hOriginalFind)
              hEvent
      | some firstEdit =>
          cases firstEdit with
          | left firstChoice =>
              obtain ⟨hOriginalEq, hFirstValid, hFirstRight⟩ :=
                VirtualStack.block_eq_sourceLeft_of_lookup
                  hTypedR.1 hOriginalMem hFirstLookup
              have hEvent :
                  VirtualStack.hasRuntimeEvent original = true := by
                rw [hOriginalEq]
                simpa [VirtualStack.pairEligible] using
                  hFirstValid.leftEligible
              exact stackRealizes_virtualEligible_of_chainCombined
                context hSourceWF hTyped hChainStep hConstState
                  (by simpa [virtualBase, R, T, C, Q] using
                    hOriginalFind)
                  hEvent
          | right firstChoice =>
              exact absurd hFirstLookup
                (hNoRight firstChoice)
    · exact hFirstStep
    · exact hFind
  have hVirtual :=
    VirtualStack.openStep_canonProgram_congr
      (program := R) hTypedR.1 hTypedR
      (by simpa [virtualProgram, virtualBase, R, T, C, Q] using
        hVirtualTyped)
      hIndependentR hRealizesFirst hRealizesSecond
      (by simpa [virtualBase, R, T, C, Q] using hVirtualStep)
  rw [BlockReorder.openStep_reorderProgram T hTypedT.1] at hVirtual
  refine Simulation.Interaction.Rel.mono
    (Simulation.Interaction.Rel.trans
      (Simulation.Interaction.Rel.trans hChain hConst)
      hVirtual) ?_
  rintro sourceOutcome finalOutcome
    ⟨constOutcome,
      ⟨chainOutcome, hSourceChain, hChainConst⟩,
      hConstVirtual⟩
  rcases hSourceChain with
    hSourceJump | ⟨hSourceRuntime, hSourceNotJump⟩
  · obtain ⟨next, sourceNext, chainNext,
        hSourceEq, hChainEq, hChainNext⟩ :=
      hSourceJump
    rw [hChainEq] at hChainConst
    cases hChainConst with
    | ok hConstRuntime =>
        cases hConstRuntime with
        | jump _ hConstNext =>
            rename_i constNext
            rcases hConstVirtual with
              hVirtualJump |
                ⟨hVirtualRuntime, hConstNotJump⟩
            · obtain ⟨next₂, constNext₂, finalNext,
                  hConstEq, hFinalEq, hVirtualNext⟩ :=
                hVirtualJump
              rw [Except.ok.injEq,
                Outcome.jump.injEq] at hConstEq
              obtain ⟨hNext, hState⟩ := hConstEq
              subst next₂
              subst constNext₂
              exact Or.inl
                ⟨next, sourceNext, finalNext,
                  hSourceEq, hFinalEq,
                  chainNext, constNext,
                  hChainNext, hConstNext,
                  hVirtualNext⟩
            · exact absurd rfl
                (hConstNotJump next constNext)
  · have hSourceConst :=
      runtimeOutcomeRel_trans hSourceRuntime hChainConst
    rcases hConstVirtual with
      hVirtualJump | ⟨hVirtualRuntime, hChainNotJump⟩
    · obtain ⟨next, chainNext, finalNext,
          hChainEq, hFinalEq, hVirtualNext⟩ :=
        hVirtualJump
      exfalso
      cases hSourceConst with
      | error hError =>
          exact absurd hChainEq (by simp)
      | ok hRuntime =>
          cases hRuntime with
          | jump label hState =>
              exact hSourceNotJump label _ rfl
          | fallthrough hState =>
              exact absurd hChainEq (by simp)
          | returnDispatch hState =>
              exact absurd hChainEq (by simp)
          | halt kind hState =>
              exact absurd hChainEq (by simp)
          | invalid hState =>
              exact absurd hChainEq (by simp)
    · refine Or.inr ⟨?_, hSourceNotJump⟩
      cases hSourceConst with
      | error hSourceError =>
          cases hVirtualRuntime with
          | error hVirtualError =>
              exact .error (hSourceError.trans hVirtualError)
      | ok hSourceResult =>
          cases hVirtualRuntime with
          | ok hVirtualResult =>
              exact .ok
                (Outcome.RuntimeRel.trans
                  hSourceResult hVirtualResult)

/-- Fuel-bounded source-to-virtual congruence. -/
theorem openRunN_virtualCombinedEff_congr_of_source
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext
        source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped)
    (hIndependent : cfg.ProgramCounterIndependent)
    (hVirtualTyped : (virtualProgram cfg).WellTyped) :
    ∀ (fuel : Nat) (label : Label)
        (sourceState finalState : EVMState),
      VirtualCombinedStepRelEff
          (source := source) (cfg := cfg)
          context.calls label sourceState finalState →
      Simulation.Interaction.Rel
        (VirtualCombinedOutcomeRelEff
          (source := source) (cfg := cfg) context.calls)
        (InteractionSemantics.Program.openRunN
          cfg fuel label sourceState)
        (InteractionSemantics.Program.openRunN
          (virtualProgram cfg) fuel label finalState)
  | 0, label, sourceState, finalState, hStep => by
      simp only [InteractionSemantics.Program.openRunN_zero]
      exact .done
        (Or.inl
          ⟨label, sourceState, finalState,
            rfl, rfl, hStep⟩)
  | fuel + 1, label, sourceState, finalState, hStep => by
      rw [InteractionSemantics.Program.openRunN_succ,
        InteractionSemantics.Program.openRunN_succ]
      have hOne :=
        openStep_virtualCombinedEff_congr_of_source
          context hSourceWF hTyped hIndependent
          hVirtualTyped hStep
      apply Simulation.Interaction.Rel.bind_custom hOne
      intro sourceDone finalDone hOutcome
      rcases hOutcome with hJump | hTerminal
      · obtain ⟨next, sourceNext, finalNext,
          hSource, hFinal, hNext⟩ := hJump
        subst hSource
        subst hFinal
        exact
          openRunN_virtualCombinedEff_congr_of_source
            context hSourceWF hTyped hIndependent
            hVirtualTyped fuel next sourceNext finalNext hNext
      · obtain ⟨hRuntime, hNotJump⟩ := hTerminal
        cases hRuntime with
        | error hError =>
            exact .done
              (Or.inr ⟨.error hError, by simp⟩)
        | ok hResult =>
            cases hResult with
            | jump next hState =>
                exact absurd rfl (hNotJump next _)
            | fallthrough hState =>
                exact .done
                  (Or.inr
                    ⟨.ok (.fallthrough hState), by simp⟩)
            | returnDispatch hState =>
                exact .done
                  (Or.inr
                    ⟨.ok (.returnDispatch hState), by simp⟩)
            | halt kind hState =>
                exact .done
                  (Or.inr
                    ⟨.ok (.halt kind hState), by simp⟩)
            | invalid hState =>
                exact .done
                  (Or.inr
                    ⟨.ok (.invalid hState), by simp⟩)

/-- Canonical finite-prefix source-to-virtual congruence. -/
theorem openRunNPrefix_virtualCombinedEff_congr_of_source
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext
        source entryShapes cfg)
    (hSourceWF : source.WF)
    (hTyped : cfg.WellTyped)
    (hIndependent : cfg.ProgramCounterIndependent)
    (hVirtualTyped : (virtualProgram cfg).WellTyped)
    (fuel : Nat) (label : Label)
    (sourceState finalState : EVMState)
    (hStep :
      VirtualCombinedStepRelEff
        (source := source) (cfg := cfg)
        context.calls label sourceState finalState) :
    Simulation.Interaction.Rel
      InteractionCongruence.Block.RuntimeOutcomeRel
      (InteractionSemantics.Program.openRunNPrefix
        cfg fuel label sourceState)
      (InteractionSemantics.Program.openRunNPrefix
        (virtualProgram cfg) fuel label finalState) := by
  unfold InteractionSemantics.Program.openRunNPrefix
  have hRun :=
    openRunN_virtualCombinedEff_congr_of_source
      context hSourceWF hTyped hIndependent hVirtualTyped
      fuel label sourceState finalState hStep
  apply Simulation.Interaction.Rel.bind_custom hRun
  intro sourceDone finalDone hOutcome
  rcases hOutcome with hJump | hTerminal
  · obtain ⟨next, sourceNext, finalNext,
      hSource, hFinal, hNext⟩ := hJump
    subst hSource
    subst hFinal
    exact .done (.error rfl)
  · obtain ⟨hRuntime, hNotJump⟩ := hTerminal
    cases hRuntime with
    | error hError =>
        exact .done (.error hError)
    | ok hResult =>
        cases hResult with
        | jump next hState =>
            exact absurd rfl (hNotJump next _)
        | fallthrough hState =>
            exact .done (.error rfl)
        | returnDispatch hState =>
            exact .done (.error rfl)
        | halt kind hState =>
            exact .done (.ok (.halt kind hState))
        | invalid hState =>
            exact .done (.error rfl)

theorem runtimeOutcomeRel_of_virtualCombinedOutcomeRelEff_of_not_jump
    {source : Structured.Program} {cfg : Program}
    {calls : List Structured.TypedCfgCompiler.DispatchSite}
    {sourceOutcome finalOutcome : Except EVMException Outcome}
    (hOutcome :
      VirtualCombinedOutcomeRelEff
        (source := source) (cfg := cfg)
        calls sourceOutcome finalOutcome)
    (hNotJump :
      ∀ (next : Label) (state : EVMState),
        sourceOutcome ≠ .ok (.jump next state)) :
    InteractionCongruence.Block.RuntimeOutcomeRel
      sourceOutcome finalOutcome := by
  rcases hOutcome with hJump | hTerminal
  · obtain ⟨next, sourceState, finalState,
      hSource, hFinal, hStep⟩ := hJump
    exact absurd hSource (hNotJump next sourceState)
  · exact hTerminal.1

theorem assemblySafeHalted_of_virtualCombinedOutcomeRelEff
    {source : Structured.Program} {cfg : Program}
    {calls : List Structured.TypedCfgCompiler.DispatchSite}
    {sourceOutcome finalOutcome : Except EVMException Outcome}
    (hOutcome :
      VirtualCombinedOutcomeRelEff
        (source := source) (cfg := cfg)
        calls sourceOutcome finalOutcome)
    (hSafe :
      InteractionSemantics.Program.AssemblySafeHalted sourceOutcome) :
    InteractionSemantics.Program.AssemblySafeHalted finalOutcome :=
  assemblySafeHalted_of_runtimeRel
    (runtimeOutcomeRel_of_virtualCombinedOutcomeRelEff_of_not_jump
      hOutcome (assemblySafeHalted_not_jump hSafe))
    hSafe

theorem runSimulates_of_virtualCombinedOutcomeRelEff_halted
    {source : Structured.Program} {cfg : Program}
    {calls : List Structured.TypedCfgCompiler.DispatchSite}
    {target : Assembly.Program}
    {sourceOutcome finalOutcome :
      Except EVMException Outcome}
    {assemblyOutcome : Assembly.Source.ExecutionOutcome}
    (hOutcome :
      VirtualCombinedOutcomeRelEff
        (source := source) (cfg := cfg)
        calls sourceOutcome finalOutcome)
    (hSimulates :
      InteractionPreservation.OpenBlock.RunSimulates
        target finalOutcome assemblyOutcome)
    (hSafe :
      InteractionSemantics.Program.AssemblySafeHalted sourceOutcome) :
    InteractionPreservation.OpenBlock.RunSimulates
      target sourceOutcome assemblyOutcome :=
  InteractionPreservation.OpenBlock.runtime_left
    (runtimeOutcomeRel_of_virtualCombinedOutcomeRelEff_of_not_jump
      hOutcome (assemblySafeHalted_not_jump hSafe))
    hSimulates

theorem assemblySafeFinished_of_virtualCombinedOutcomeRelEff
    {source : Structured.Program} {cfg : Program}
    {calls : List Structured.TypedCfgCompiler.DispatchSite}
    {sourceOutcome finalOutcome : Except EVMException Outcome}
    (hOutcome :
      VirtualCombinedOutcomeRelEff
        (source := source) (cfg := cfg)
        calls sourceOutcome finalOutcome)
    (hSafe :
      InteractionSemantics.Program.AssemblySafeFinished sourceOutcome) :
    InteractionSemantics.Program.AssemblySafeFinished finalOutcome :=
  assemblySafeFinished_of_runtimeRel
    (runtimeOutcomeRel_of_virtualCombinedOutcomeRelEff_of_not_jump
      hOutcome (assemblySafeFinished_not_jump hSafe))
    hSafe

theorem runSimulates_of_virtualCombinedOutcomeRelEff_finished
    {source : Structured.Program} {cfg : Program}
    {calls : List Structured.TypedCfgCompiler.DispatchSite}
    {target : Assembly.Program}
    {sourceOutcome finalOutcome :
      Except EVMException Outcome}
    {assemblyOutcome : Assembly.Source.ExecutionOutcome}
    (hOutcome :
      VirtualCombinedOutcomeRelEff
        (source := source) (cfg := cfg)
        calls sourceOutcome finalOutcome)
    (hSimulates :
      InteractionPreservation.OpenBlock.RunSimulates
        target finalOutcome assemblyOutcome)
    (hSafe :
      InteractionSemantics.Program.AssemblySafeFinished sourceOutcome) :
    InteractionPreservation.OpenBlock.RunSimulates
      target sourceOutcome assemblyOutcome :=
  InteractionPreservation.OpenBlock.runtime_left
    (runtimeOutcomeRel_of_virtualCombinedOutcomeRelEff_of_not_jump
      hOutcome (assemblySafeFinished_not_jump hSafe))
    hSimulates

end Peephole
end TypedCfg
end EvmCompiler
