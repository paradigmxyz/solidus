import EvmCompiler.Structured.ObserverPreservation

namespace EvmCompiler
namespace Structured
namespace ObserverAdequacy

/-!
Backward adequacy for the adjacent Structured-to-TypedCfg pass.

This module consumes only the existing Structured compiler, its TypedCfg
typing facts, the shared observer semantics, and the pass-owned state relation.
It does not reason about Assembly or bytecode execution.
-/

abbrev Trace := Assembly.ResourceTrace

namespace OutcomeSimulation

abbrev Continuations :=
  TypedCfgPreservation.OutcomeSimulation.Continuations

/--
A target outcome has reached one of the Structured fragment's semantic
continuations or has halted. Fallthrough, return dispatch, and invalid target
outcomes are internal to lower control machinery and are not Structured
statement outcomes.
-/
def TargetBoundary (continuations : Continuations) :
    TypedCfg.Outcome → Prop
  | .jump label _ =>
      label = continuations.regular ∨
        continuations.breakLabel? = some label ∨
        continuations.continueLabel? = some label ∨
        continuations.leaveLabel? = some label
  | .halt _ _ => True
  | .fallthrough _ | .returnDispatch _ | .invalid _ => False

/--
Execution to the first target outcome owned by the Structured fragment.

This is stated entirely with the existing TypedCfg observer interpreter.
Minimality supplies the compositional stopping rule needed by backward
adequacy; it is not a replay trace or a second control interpreter.
-/
structure ReachesBoundary
    (program : TypedCfg.Program) (continuations : Continuations)
    (fuel : Nat) (entry : Assembly.Label)
    (initial : EVMState) (initialTrace : Trace)
    (outcome : TypedCfg.Outcome) (finalTrace : Trace) : Prop where
  run :
    TypedCfg.ObserverSemantics.Program.runN
        program fuel entry initial initialTrace =
      .ok (outcome, finalTrace)
  boundary : TargetBoundary continuations outcome
  minimal :
    ∀ prefixFuel, prefixFuel < fuel →
      ∀ prefixOutcome prefixTrace,
        TypedCfg.ObserverSemantics.Program.runN
            program prefixFuel entry initial initialTrace =
          .ok (prefixOutcome, prefixTrace) →
        ¬ TargetBoundary continuations prefixOutcome

namespace ReachesBoundary

theorem fuel_pos_of_entry_not_boundary
    {program : TypedCfg.Program} {continuations : Continuations}
    {fuel : Nat} {entry : Assembly.Label}
    {initial : EVMState} {initialTrace finalTrace : Trace}
    {outcome : TypedCfg.Outcome}
    (hReach :
      ReachesBoundary program continuations fuel
        entry initial initialTrace outcome finalTrace)
    (hEntry :
      ¬ TargetBoundary continuations (.jump entry initial)) :
    0 < fuel := by
  cases fuel with
  | zero =>
      have hRun := hReach.run
      simp only
        [TypedCfg.ObserverSemantics.Program.runN_zero] at hRun
      cases hRun
      exact False.elim (hEntry hReach.boundary)
  | succ fuel =>
      omega

theorem tail_of_step_jump
    {program : TypedCfg.Program} {continuations : Continuations}
    {fuel : Nat} {entry next : Assembly.Label}
    {initial middle : EVMState}
    {initialTrace middleTrace finalTrace : Trace}
    {outcome : TypedCfg.Outcome}
    (hReach :
      ReachesBoundary program continuations (fuel + 1)
        entry initial initialTrace outcome finalTrace)
    (hStep :
      TypedCfg.ObserverSemantics.Program.step
          program entry initial initialTrace =
        .ok (.jump next middle, middleTrace)) :
    ReachesBoundary program continuations fuel
      next middle middleTrace outcome finalTrace := by
  refine ⟨?_, hReach.boundary, ?_⟩
  · have hRun := hReach.run
    rw [TypedCfg.ObserverSemantics.Program.runN_succ,
      hStep] at hRun
    exact hRun
  · intro prefixFuel hPrefix prefixOutcome prefixTrace
      hPrefixRun hPrefixBoundary
    have hOriginalPrefix :
        TypedCfg.ObserverSemantics.Program.runN
            program (prefixFuel + 1) entry initial initialTrace =
          .ok (prefixOutcome, prefixTrace) := by
      rw [TypedCfg.ObserverSemantics.Program.runN_succ, hStep]
      exact hPrefixRun
    exact
      hReach.minimal (prefixFuel + 1) (by omega)
        prefixOutcome prefixTrace hOriginalPrefix hPrefixBoundary

theorem fuel_eq_one_of_step_boundary
    {program : TypedCfg.Program} {continuations : Continuations}
    {fuel : Nat} {entry : Assembly.Label}
    {initial : EVMState} {initialTrace finalTrace firstTrace : Trace}
    {outcome firstOutcome : TypedCfg.Outcome}
    (hReach :
      ReachesBoundary program continuations (fuel + 1)
        entry initial initialTrace outcome finalTrace)
    (hStep :
      TypedCfg.ObserverSemantics.Program.step
          program entry initial initialTrace =
        .ok (firstOutcome, firstTrace))
    (hBoundary : TargetBoundary continuations firstOutcome) :
    fuel = 0 := by
  by_contra hFuel
  have hOneLt : 1 < fuel + 1 := by omega
  exact
    hReach.minimal 1 hOneLt firstOutcome firstTrace
      (TypedCfg.ObserverSemantics.Program.runN_one_of_step hStep)
      hBoundary

theorem outcome_eq_of_step_boundary
    {program : TypedCfg.Program} {continuations : Continuations}
    {fuel : Nat} {entry : Assembly.Label}
    {initial : EVMState} {initialTrace finalTrace firstTrace : Trace}
    {outcome firstOutcome : TypedCfg.Outcome}
    (hReach :
      ReachesBoundary program continuations (fuel + 1)
        entry initial initialTrace outcome finalTrace)
    (hStep :
      TypedCfg.ObserverSemantics.Program.step
          program entry initial initialTrace =
        .ok (firstOutcome, firstTrace))
    (hBoundary : TargetBoundary continuations firstOutcome) :
    outcome = firstOutcome ∧ finalTrace = firstTrace := by
  have hFuel :=
    fuel_eq_one_of_step_boundary hReach hStep hBoundary
  subst fuel
  have hOne :=
    TypedCfg.ObserverSemantics.Program.runN_one_of_step hStep
  have hRun := hReach.run
  rw [hOne] at hRun
  simpa only [Prod.mk.injEq] using Except.ok.inj hRun.symm

end ReachesBoundary

/--
Stable backward-adequacy interface for a source evaluation relation at a typed
Structured-to-TypedCfg boundary.
-/
def AdequateAt {transcript : Trace}
    (eval :
      Nat →
        ObserverSemantics.Outcome (transcript := transcript) → Prop)
    (program : TypedCfg.Program) (continuations : Continuations)
    (entry : Assembly.Label) (input : TypedCfg.Shape)
    (source : ObserverSemantics.State transcript)
    (tokens : List Word) : Prop :=
  ∀ {targetFuel : Nat} {target : EVMState}
    {trace traceFinal : Trace} {targetOutcome : TypedCfg.Outcome},
    ObserverPreservation.StateRel.At
        input source tokens target trace →
      ReachesBoundary
          program continuations (targetFuel + 1)
          entry target trace targetOutcome traceFinal →
        ∃ sourceFuel sourceOutcome,
          eval sourceFuel sourceOutcome ∧
            ObserverPreservation.OutcomeSimulation.Rel
              continuations tokens sourceOutcome
              targetOutcome traceFinal

end OutcomeSimulation

namespace BasicInstr

theorem output_length_pos_of_observer
    {instr : Structured.BasicInstr}
    {input output : TypedCfg.Shape}
    {kind : Assembly.ResourceObserver}
    (hType :
      TypedCfg.Instr.type?
          (TypedCfgCompiler.BasicInstr.toCfg instr) input =
        some output)
    (hObserver :
      (match instr with
       | .op op => ObserverSemantics.basicOpObserver? op
       | _ => none) = some kind) :
    1 ≤ output.length := by
  cases instr with
  | push value | bindLocals value names
  | bindScratch value name slot =>
      simp at hObserver
  | op op =>
      obtain
          ⟨inputArity, outputArity, hArity,
            _hInputBound, hOutputLength⟩ :=
        TypedCfgPreservation.BasicOp.type_length_toCfg hType
      have hCases : op = .gas ∨ op = .msize := by
        cases op <;>
          simp [ObserverSemantics.basicOpObserver?,
            Assembly.ResourceObserver.ofPrimOp?,
            Structured.BasicOp.toPrimOp] at hObserver ⊢
      rcases hCases with rfl | rfl <;>
        simp [Structured.BasicOp.toPrimOp,
          Assembly.PrimOp.stackArity?,
          Assembly.PrimOp.toEVM,
          EvmYul.EVM.δ, EvmYul.EVM.α] at hArity <;>
        omega

end BasicInstr

namespace Code

/--
Typed observer execution respects the symbolic stack lower bound.

This pass-owned semantic interface is discharged structurally by `shapeSound`;
callers supply no layout, replay, emitted-code, or stack-shape evidence.
-/
def ShapeSound (code : Structured.Code) : Prop :=
  ∀ {transcript : Trace} {input output : TypedCfg.Shape}
      {source final : ObserverSemantics.State transcript},
    TypedCfgCompiler.Code.type? code input = some output →
      input.length ≤ source.source.evm.stack.length →
      ObserverSemantics.Code.run code source = .ok final →
      output.length ≤ final.source.evm.stack.length

/--
Every straight-line fragment accepted by the existing Structured-to-TypedCfg
body typer is shape-sound under observer replay.
-/
theorem shapeSound (code : Structured.Code) : ShapeSound code := by
  intro transcript input output source final hType hBound hRun
  induction code generalizing input output source final with
  | nil =>
      simp [TypedCfgCompiler.Code.type?,
        TypedCfgCompiler.Code.toCfg,
        TypedCfg.Block.bodyType?,
        ObserverSemantics.Code.run,
        EffectSemantics.Code.run] at hType hRun
      cases hType
      cases hRun
      exact hBound
  | cons instr rest ih =>
      unfold TypedCfgCompiler.Code.type? at hType
      simp only [TypedCfgCompiler.Code.toCfg, List.map_cons,
        TypedCfg.Block.bodyType?] at hType
      cases hHeadType :
          TypedCfg.Instr.type?
            (TypedCfgCompiler.BasicInstr.toCfg instr) input with
      | none =>
          simp [hHeadType] at hType
      | some middle =>
          simp [hHeadType] at hType
          have hTailType :
              TypedCfgCompiler.Code.type? rest middle = some output := by
            simpa [TypedCfgCompiler.Code.type?,
              TypedCfgCompiler.Code.toCfg] using hType
          unfold ObserverSemantics.Code.run
            EffectSemantics.Code.run at hRun
          simp only [ObserverSemantics.stateModel_evm,
            ObserverSemantics.stateModel_withEVM] at hRun
          cases hStep : instr.step source.source.evm with
          | error err =>
              simp [hStep, Bind.bind, Except.bind] at hRun
          | ok evm =>
              simp only [hStep, Bind.bind, Except.bind] at hRun
              cases hAfter :
                  (ObserverSemantics.handler transcript).afterInstr instr
                    (source.withSource
                      (source.source.withEVM evm)) with
              | error err =>
                  rw [hAfter] at hRun
                  contradiction
              | ok middleState =>
                  rw [hAfter] at hRun
                  have hStepBound :
                      middle.length ≤ evm.stack.length :=
                    TypedCfgPreservation.BasicInstr.step_stack_bound_of_type
                      hHeadType hBound hStep
                  have hAfterLength :=
                    ObserverSemantics.handler_stack_length hAfter
                  have hMiddleBound :
                      middle.length ≤
                        middleState.source.evm.stack.length := by
                    have hLength :
                        middleState.source.evm.stack.length =
                          evm.stack.length := by
                      simpa [RunState.withEVM] using hAfterLength
                    omega
                  exact ih hTailType hMiddleBound hRun

/--
Backward frame adequacy indexed by the checked input shape.

Unlike the former unindexed source predicate, this interface quantifies only
over states whose visible stack satisfies the actual compiler typing judgment.
The conclusion uses the pass's existing replay relation, which intentionally
forgets compiler-owned control counters.
-/
def FrameReflectingAt (code : Structured.Code)
    (input : TypedCfg.Shape) : Prop :=
  ∀ {transcript : Trace} {output : TypedCfg.Shape}
      {state framedFinal : ObserverSemantics.State transcript}
      {hidden : EvmYul.Stack Word},
    TypedCfgCompiler.Code.type? code input = some output →
      input.length ≤ state.source.evm.stack.length →
      ObserverSemantics.Code.run code
          (ObserverSemantics.Code.withHidden state hidden) =
        .ok framedFinal →
      ∃ final,
        ObserverSemantics.Code.run code state = .ok final ∧
          ObserverPreservation.ReplayStateRel
            framedFinal
            (ObserverSemantics.Code.withHidden final hidden)

/--
Every straight-line fragment accepted by the existing pass typer reflects
execution through compiler-owned frame suffixes at its checked input shape.
-/
theorem frameReflectingAt
    (code : Structured.Code) (input : TypedCfg.Shape) :
    FrameReflectingAt code input := by
  intro transcript output state framedFinal hidden
    hType hBound hFramed
  induction code generalizing input output state framedFinal with
  | nil =>
      simp [TypedCfgCompiler.Code.type?,
        TypedCfgCompiler.Code.toCfg,
        TypedCfg.Block.bodyType?,
        ObserverSemantics.Code.run,
        EffectSemantics.Code.run] at hType hFramed
      cases hType
      cases hFramed
      exact
        ⟨state, rfl,
          ObserverPreservation.ReplayStateRel.refl
            (ObserverSemantics.Code.withHidden state hidden)⟩
  | cons instr rest ih =>
      unfold TypedCfgCompiler.Code.type? at hType
      simp only [TypedCfgCompiler.Code.toCfg, List.map_cons,
        TypedCfg.Block.bodyType?] at hType
      cases hHeadType :
          TypedCfg.Instr.type?
            (TypedCfgCompiler.BasicInstr.toCfg instr) input with
      | none =>
          simp [hHeadType] at hType
      | some middle =>
          simp [hHeadType] at hType
          have hTailType :
              TypedCfgCompiler.Code.type? rest middle = some output := by
            simpa [TypedCfgCompiler.Code.type?,
              TypedCfgCompiler.Code.toCfg] using hType
          unfold ObserverSemantics.Code.run
            EffectSemantics.Code.run at hFramed
          simp only [ObserverSemantics.stateModel_evm,
            ObserverSemantics.stateModel_withEVM] at hFramed
          simp only [ObserverSemantics.Code.withHidden_source,
            RunState.withEVM_evm] at hFramed
          cases hFramedStep :
              instr.step
                { state.source.evm with
                  stack := state.source.evm.stack ++ hidden } with
          | error err =>
              simp [hFramedStep, Bind.bind, Except.bind] at hFramed
          | ok framedEVM =>
              simp only [hFramedStep,
                Bind.bind, Except.bind] at hFramed
              obtain ⟨sourceEVM, hSourceStep⟩ :=
                TypedCfgPreservation.BasicInstr.exists_step_of_type_bound_append
                  hHeadType hBound hFramedStep
              have hStepRel :
                  Assembly.SameRuntimeData
                    framedEVM
                    { sourceEVM with
                      stack := sourceEVM.stack ++ hidden } :=
                TypedCfgPreservation.BasicInstr.step_append_stack_rel_of_type
                  hHeadType hBound hSourceStep hFramedStep
              let sourceMiddle : ObserverSemantics.State transcript :=
                state.withSource
                  (state.source.withEVM sourceEVM)
              let framedMiddle : ObserverSemantics.State transcript :=
                (ObserverSemantics.Code.withHidden state hidden).withSource
                  ((ObserverSemantics.Code.withHidden state hidden).source.withEVM
                    framedEVM)
              let expectedMiddle : ObserverSemantics.State transcript :=
                ObserverSemantics.Code.withHidden sourceMiddle hidden
              have hNormalizeFramedMiddle :
                  (ObserverSemantics.Code.withHidden state hidden).withSource
                      ((state.source.withEVM
                        { state.source.evm with
                          stack := state.source.evm.stack ++ hidden }).withEVM
                        framedEVM) =
                    framedMiddle := by
                simp [framedMiddle,
                  ObserverSemantics.Code.withHidden,
                  RunState.withEVM]
              rw [hNormalizeFramedMiddle] at hFramed
              have hMiddleRel :
                  ObserverPreservation.ReplayStateRel
                    framedMiddle expectedMiddle := by
                refine ⟨rfl, ?_, ?_⟩
                · simp [framedMiddle, expectedMiddle, sourceMiddle,
                    ObserverSemantics.Code.withHidden, RunState.withEVM]
                · simpa [framedMiddle, expectedMiddle, sourceMiddle,
                    ObserverSemantics.Code.withHidden, RunState.withEVM]
                    using hStepRel
              cases hFramedAfter :
                  (ObserverSemantics.handler transcript).afterInstr
                    instr framedMiddle with
              | error err =>
                  rw [hFramedAfter] at hFramed
                  contradiction
              | ok framedAfter =>
                  rw [hFramedAfter] at hFramed
                  obtain
                      ⟨expectedAfter, hExpectedAfter, hAfterRel⟩ :=
                    ObserverPreservation.handler_of_rel
                      hMiddleRel hFramedAfter
                  have hSourceStepBound :
                      middle.length ≤ sourceEVM.stack.length :=
                    TypedCfgPreservation.BasicInstr.step_stack_bound_of_type
                      hHeadType hBound hSourceStep
                  have hObserverTop :
                      ∀ op kind,
                        instr = .op op →
                        ObserverSemantics.basicOpObserver? op = some kind →
                        sourceMiddle.source.evm.stack ≠ [] := by
                    intro op kind hInstr hObserver
                    subst instr
                    have hOutputPos :
                        1 ≤ middle.length :=
                      BasicInstr.output_length_pos_of_observer
                        hHeadType hObserver
                    have hStackPos :
                        1 ≤ sourceEVM.stack.length :=
                      Nat.le_trans hOutputPos hSourceStepBound
                    intro hNil
                    have hSourceNil : sourceEVM.stack = [] := by
                      simpa [sourceMiddle] using hNil
                    simp [hSourceNil] at hStackPos
                  obtain
                      ⟨sourceAfter, hSourceAfter, hExpectedEq⟩ :=
                    ObserverSemantics.Code.handler_frameReflecting
                      hObserverTop
                      (by simpa [expectedMiddle] using hExpectedAfter)
                  subst expectedAfter
                  have hAfterBound :
                      middle.length ≤
                        sourceAfter.source.evm.stack.length := by
                    have hLength :=
                      ObserverSemantics.handler_stack_length hSourceAfter
                    have hSourceLength :
                        sourceMiddle.source.evm.stack.length =
                          sourceEVM.stack.length := by
                      simp [sourceMiddle]
                    omega
                  obtain
                      ⟨expectedFinal, hExpectedTail, hTailRel⟩ :=
                    ObserverPreservation.Code.run_of_rel
                      hAfterRel hFramed
                  obtain
                      ⟨final, hSourceTail, hExpectedFinalRel⟩ :=
                    ih middle hTailType hAfterBound hExpectedTail
                  refine ⟨final, ?_, ?_⟩
                  · unfold ObserverSemantics.Code.run
                      EffectSemantics.Code.run
                    simp only [ObserverSemantics.stateModel_evm,
                      ObserverSemantics.stateModel_withEVM]
                    rw [hSourceStep]
                    simp only [Bind.bind, Except.bind]
                    change
                      (ObserverSemantics.handler transcript).afterInstr
                          instr sourceMiddle =
                        .ok sourceAfter at hSourceAfter
                    rw [hSourceAfter]
                    exact hSourceTail
                  · exact
                      ObserverPreservation.ReplayStateRel.trans
                        hTailRel hExpectedFinalRel

/--
Backward straight-line adequacy across realized procedure frames.

The target run is transported to the source state with its concrete hidden
suffix, then the checked input shape derives reflection through only that
compiler-owned suffix. Return-frame representation remains inside the adjacent
pass proof.
-/
theorem run_of_runBody_toCfg
    {transcript : Trace} {code : Structured.Code}
    {input output : TypedCfg.Shape}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    {target targetFinal : EVMState}
    {trace traceFinal : Trace}
    (hType : TypedCfgCompiler.Code.type? code input = some output)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace)
    (hRun :
      TypedCfg.ObserverSemantics.Block.runBody
          (TypedCfgCompiler.Code.toCfg code) input target trace =
        .ok ((targetFinal, output), traceFinal)) :
    ∃ final : ObserverSemantics.State transcript,
      ObserverSemantics.Code.run code source = .ok final ∧
        ObserverPreservation.StateRel
          final tokens targetFinal traceFinal := by
  rcases hRel.rel.1 with ⟨realized, hRealize, hSame⟩
  have hAppend :=
    TypedCfgPreservation.realizeStack_append_prefix
      source.source.evm.stack [] source.source.returns tokens
  cases hHidden :
      TypedCfgPreservation.realizeStack
        [] source.source.returns tokens with
  | none =>
      simp [hHidden] at hAppend
      rw [hAppend] at hRealize
      cases hRealize
  | some hidden =>
      simp [hHidden] at hAppend
      rw [hAppend] at hRealize
      cases hRealize
      let targetState : ObserverSemantics.State transcript :=
        source.withSource (source.source.withEVM target)
      let framedSource :=
        ObserverSemantics.Code.withHidden source hidden
      have hReplay :
          ObserverPreservation.ReplayStateRel targetState framedSource := by
        exact
          ⟨rfl, by simp [targetState, framedSource],
            by simpa [targetState, framedSource,
                ObserverSemantics.Code.withHidden,
                RunState.withEVM] using hSame⟩
      have hTargetBody :
          TypedCfg.ObserverSemantics.Block.runBody
              (TypedCfgCompiler.Code.toCfg code) input
              targetState.source.evm targetState.remaining =
            .ok ((targetFinal, output), traceFinal) := by
        simpa [targetState, hRel.rel.2] using hRun
      obtain
          ⟨targetFinalState, hTargetCode, hTargetEVM, hTargetTrace⟩ :=
        ObserverPreservation.Code.run_of_runBody_toCfg
          hType hTargetBody
      obtain ⟨framedFinal, hFramedRun, hFinalReplay⟩ :=
        ObserverPreservation.Code.run_of_rel hReplay hTargetCode
      obtain ⟨final, hSourceRun, hFrameReplay⟩ :=
        frameReflectingAt code input hType hRel.sourceStack
          (by simpa [framedSource] using hFramedRun)
      have hFinalReplay' :
          ObserverPreservation.ReplayStateRel
            targetFinalState
            (ObserverSemantics.Code.withHidden final hidden) :=
        ObserverPreservation.ReplayStateRel.trans
          hFinalReplay hFrameReplay
      have hFinalReturns :
          final.source.returns = source.source.returns :=
        ObserverSemantics.Code.run_returns_eq hSourceRun
      refine ⟨final, hSourceRun, ?_⟩
      refine ⟨?_, ?_⟩
      · refine ⟨final.source.evm.stack ++ hidden, ?_, ?_⟩
        · have hFinalAppend :=
            TypedCfgPreservation.realizeStack_append_prefix
              final.source.evm.stack [] final.source.returns tokens
          simpa [hFinalReturns, hHidden] using hFinalAppend
        · rw [← hTargetEVM]
          simpa [ObserverSemantics.Code.withHidden,
              RunState.withEVM] using hFinalReplay'.source.2
      · rw [← hTargetTrace]
        exact
          (ObserverPreservation.ReplayStateRel.remaining_eq
            hFinalReplay').symm

/--
Backward adequacy for a compiled condition across active procedure frames.

The shape-soundness fact prevents the condition pop from consuming a hidden
return token or caller-stack value.
-/
theorem runCondition_of_runBody_toCfg
    {transcript : Trace} {code : Structured.Code}
    {input output : TypedCfg.Shape}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    {target targetAfter targetFinal : EVMState}
    {trace traceFinal : Trace} {cond : Bool}
    {condition : TypedCfg.Slot}
    (hType : TypedCfgCompiler.Code.type? code input = some output)
    (hHead : output.slots.head? = some condition)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace)
    (hBody :
      TypedCfg.ObserverSemantics.Block.runBody
          (TypedCfgCompiler.Code.toCfg code) input target trace =
        .ok ((targetAfter, output), traceFinal))
    (hPop :
      Structured.Code.popCondition targetAfter =
        .ok (targetFinal, cond)) :
    ∃ final : ObserverSemantics.State transcript,
      ObserverSemantics.Code.runCondition code source =
          .ok (final, cond) ∧
        ObserverPreservation.StateRel.At
          { output with slots := output.slots.tail }
          final tokens targetFinal traceFinal := by
  obtain ⟨after, hSourceCode, hAfterRel⟩ :=
    run_of_runBody_toCfg
      hType hRel hBody
  have hOutputBound :
      output.length ≤ after.source.evm.stack.length :=
    shapeSound code hType hRel.sourceStack hSourceCode
  have hOutputPos : 1 ≤ output.length := by
    cases hSlots : output.slots with
    | nil =>
        simp [hSlots] at hHead
    | cons slot rest =>
        simp [TypedCfg.Shape.length, hSlots]
  have hAfterPos : 1 ≤ after.source.evm.stack.length :=
    Nat.le_trans hOutputPos hOutputBound
  cases hAfterStack : after.source.evm.stack with
  | nil =>
      simp [hAfterStack] at hAfterPos
  | cons value stack =>
      let final : ObserverSemantics.State transcript :=
        after.withSource
          (after.source.withEVM
            { after.source.evm with stack := stack })
      have hSourcePop :
          EffectSemantics.Code.popCondition
              (ObserverSemantics.stateModel transcript) after =
            .ok
              (final,
                value != EvmYul.UInt256.ofNat 0) := by
        unfold EffectSemantics.Code.popCondition
        simp only [ObserverSemantics.stateModel_evm,
          ObserverSemantics.stateModel_withEVM]
        rw [hAfterStack]
        rfl
      obtain ⟨producedTarget, hProducedPop, hFinalRel⟩ :=
        ObserverPreservation.StateRel.popCondition
          hSourcePop hAfterRel
      rw [hPop] at hProducedPop
      cases hProducedPop
      refine ⟨final, ?_, hFinalRel, ?_⟩
      · unfold ObserverSemantics.Code.runCondition
          EffectSemantics.Code.runCondition
        have hEffectRun :
            EffectSemantics.Code.run
                (ObserverSemantics.stateModel transcript)
                (ObserverSemantics.handler transcript)
                code source =
              .ok after :=
          hSourceCode
        rw [hEffectRun]
        exact hSourcePop
      · cases hSlots : output.slots with
        | nil =>
            simp [hSlots] at hHead
        | cons slot rest =>
            simpa [TypedCfg.Shape.length, hSlots, final, hAfterStack]
              using hOutputBound

/--
Backward straight-line adequacy at a source boundary with no active ghost
return frames. This is the top-level case used by the first closed-program
theorem; recursive procedure frames require the stronger shape-indexed
induction still under construction.
-/
theorem run_of_runBody_toCfg_noFrames
    {transcript : Trace} {code : Structured.Code}
    {input output : TypedCfg.Shape}
    {source : ObserverSemantics.State transcript}
    {target targetFinal : EVMState}
    {trace traceFinal : Trace}
    (hType : TypedCfgCompiler.Code.type? code input = some output)
    (hReturns : source.source.returns = [])
    (hRel :
      ObserverPreservation.StateRel
        source [] target trace)
    (hRun :
      TypedCfg.ObserverSemantics.Block.runBody
          (TypedCfgCompiler.Code.toCfg code) input target trace =
        .ok ((targetFinal, output), traceFinal)) :
    ∃ final : ObserverSemantics.State transcript,
      ObserverSemantics.Code.run code source = .ok final ∧
        ObserverPreservation.StateRel
          final [] targetFinal traceFinal := by
  rcases hRel.1 with ⟨realized, hRealize, hSame⟩
  simp [hReturns, TypedCfgPreservation.realizeStack] at hRealize
  subst realized
  let targetState : ObserverSemantics.State transcript :=
    source.withSource (source.source.withEVM target)
  have hReplay :
      ObserverPreservation.ReplayStateRel targetState source := by
    exact
      ⟨rfl, by simp [targetState], by simpa [targetState] using hSame⟩
  have hTargetBody :
      TypedCfg.ObserverSemantics.Block.runBody
          (TypedCfgCompiler.Code.toCfg code) input
          targetState.source.evm targetState.remaining =
        .ok ((targetFinal, output), traceFinal) := by
    simpa [targetState, hRel.2] using hRun
  obtain
      ⟨targetFinalState, hTargetCode, hTargetEVM, hTargetTrace⟩ :=
    ObserverPreservation.Code.run_of_runBody_toCfg
      hType hTargetBody
  obtain ⟨final, hSourceCode, hFinalReplay⟩ :=
    ObserverPreservation.Code.run_of_rel hReplay hTargetCode
  have hFinalReturns : final.source.returns = [] := by
    rw [ObserverSemantics.Code.run_returns_eq hSourceCode, hReturns]
  refine ⟨final, hSourceCode, ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨final.source.evm.stack, ?_, ?_⟩
    · simp [hFinalReturns, TypedCfgPreservation.realizeStack]
    · rw [← hTargetEVM]
      simpa using hFinalReplay.source.2
  · rw [← hTargetTrace]
    exact
      (ObserverPreservation.ReplayStateRel.remaining_eq
        hFinalReplay).symm

/--
Backward adequacy for a compiled condition at a no-frame boundary.
-/
theorem runCondition_of_runBody_toCfg_noFrames
    {transcript : Trace} {code : Structured.Code}
    {input output : TypedCfg.Shape}
    {source : ObserverSemantics.State transcript}
    {target targetAfter targetFinal : EVMState}
    {trace traceFinal : Trace} {cond : Bool}
    (hType : TypedCfgCompiler.Code.type? code input = some output)
    (hReturns : source.source.returns = [])
    (hRel :
      ObserverPreservation.StateRel
        source [] target trace)
    (hBody :
      TypedCfg.ObserverSemantics.Block.runBody
          (TypedCfgCompiler.Code.toCfg code) input target trace =
        .ok ((targetAfter, output), traceFinal))
    (hPop :
      Structured.Code.popCondition targetAfter =
        .ok (targetFinal, cond)) :
    ∃ final : ObserverSemantics.State transcript,
      ObserverSemantics.Code.runCondition code source =
          .ok (final, cond) ∧
        ObserverPreservation.StateRel
          final [] targetFinal traceFinal := by
  obtain ⟨after, hSourceCode, hAfterRel⟩ :=
    run_of_runBody_toCfg_noFrames
      hType hReturns hRel hBody
  have hAfterReturns : after.source.returns = [] := by
    rw [ObserverSemantics.Code.run_returns_eq hSourceCode, hReturns]
  rcases hAfterRel.1 with ⟨realized, hRealize, hSame⟩
  simp [hAfterReturns, TypedCfgPreservation.realizeStack] at hRealize
  subst realized
  have hStack :
      targetAfter.stack = after.source.evm.stack :=
    Assembly.SameRuntimeData.stack_eq hSame
  unfold Structured.Code.popCondition
    EffectSemantics.Code.popCondition at hPop
  cases hTargetStack : targetAfter.stack with
  | nil =>
      simp [hTargetStack, EvmYul.Stack.pop] at hPop
  | cons value stack =>
      simp [hTargetStack, EvmYul.Stack.pop] at hPop
      rcases hPop with ⟨rfl, rfl⟩
      have hSourceStack :
          after.source.evm.stack = value :: stack := by
        rw [← hStack, hTargetStack]
      let final : ObserverSemantics.State transcript :=
        after.withSource
          (after.source.withEVM
            { after.source.evm with stack := stack })
      refine ⟨final, ?_, ?_⟩
      · unfold ObserverSemantics.Code.runCondition
          EffectSemantics.Code.runCondition
        have hEffectRun :
            EffectSemantics.Code.run
                (ObserverSemantics.stateModel transcript)
                (ObserverSemantics.handler transcript)
                code source =
              .ok after :=
          hSourceCode
        rw [hEffectRun]
        simp only [Bind.bind, Except.bind]
        unfold EffectSemantics.Code.popCondition
        simp only [ObserverSemantics.stateModel_evm,
          ObserverSemantics.stateModel_withEVM]
        rw [hSourceStack]
        rfl
      · refine ⟨?_, ?_⟩
        · refine ⟨stack, ?_, ?_⟩
          · simp [final, hAfterReturns,
              TypedCfgPreservation.realizeStack]
          · simpa [final] using
              Assembly.SameRuntimeData.replaceStack hSame
                (targetStack := stack)
                (sourceStack := stack) rfl
        · simpa [final] using hAfterRel.2

end Code

namespace Block

/--
Backward adequacy for the empty Structured block up to its first semantic
continuation. The generated jump block and its one-step execution are
constructed from the existing compiler result.
-/
theorem outcome_nil_of_compileBlockFuel?_and_reachesBoundary
    {transcript : Trace} {compilerFuel targetFuel : Nat}
    {program : Structured.Program}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState}
    {trace traceFinal : Trace}
    {targetOutcome : TypedCfg.Outcome}
    (hCompile :
      TypedCfgCompiler.compileBlockFuel? (compilerFuel + 2)
          { stmts := [] } ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hRegular : continuations.regular = regular)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace)
    (hReach :
      OutcomeSimulation.ReachesBoundary
        cfg continuations (targetFuel + 1)
        entry target trace targetOutcome traceFinal) :
    ∃ sourceFuel sourceOutcome,
      ObserverSemantics.Block.Eval
          program sourceFuel { stmts := [] } source sourceOutcome ∧
        ObserverPreservation.OutcomeSimulation.Rel
          continuations tokens sourceOutcome
          targetOutcome traceFinal := by
  unfold TypedCfgCompiler.compileBlockFuel? at hCompile
  unfold TypedCfgCompiler.compileStmtListFuel? at hCompile
  simp [TypedCfgCompiler.mkBlock?] at hCompile
  cases hCompile
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .jump regular }
  have hFind :
      cfg.findBlock? entry = some generated :=
    hBlocks generated (by simp [generated])
  have hStep :
      TypedCfg.ObserverSemantics.Program.step
          cfg entry target trace =
        .ok (.jump regular target, trace) := by
    unfold TypedCfg.ObserverSemantics.Program.step
    rw [hFind]
    change
      TypedCfg.ObserverSemantics.Block.run
          generated target trace =
        .ok (.jump regular target, trace)
    unfold TypedCfg.ObserverSemantics.Block.run
    rw [TypedCfg.ObserverSemantics.Block.runBody_nil]
    simp [generated, TypedCfg.Block.runTerm,
      Bind.bind, Except.bind]
  have hFirstBoundary :
      OutcomeSimulation.TargetBoundary continuations
        (.jump regular target) :=
    Or.inl hRegular.symm
  obtain ⟨hTargetOutcome, hTraceFinal⟩ :=
    OutcomeSimulation.ReachesBoundary.outcome_eq_of_step_boundary
      hReach hStep hFirstBoundary
  subst targetOutcome
  subst traceFinal
  exact
    ⟨1, Structured.OutcomeT.regular source,
      Structured.EffectSemantics.Block.Eval.nil,
      ObserverPreservation.OutcomeSimulation.Rel.regular_iff.mpr
        ⟨hRegular.symm, hRel.rel⟩⟩

theorem adequate_nil_of_compileBlockFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {program : Structured.Program}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileBlockFuel? (compilerFuel + 2)
          { stmts := [] } ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hRegular : continuations.regular = regular) :
    OutcomeSimulation.AdequateAt
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Block.Eval
          program sourceFuel { stmts := [] } source sourceOutcome)
      cfg continuations entry input source tokens := by
  intro targetFuel target trace traceFinal targetOutcome hRel hReach
  exact
    outcome_nil_of_compileBlockFuel?_and_reachesBoundary
      hCompile hBlocks hRegular hRel hReach

end Block

namespace Stmt

/--
Compiler-facing backward adequacy for a straight-line statement across active
procedure frames.
-/
theorem outcome_code_of_compileStmtFuel?_and_step
    {transcript : Trace} {fuel : Nat}
    {program : Structured.Program} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target targetFinal : EVMState}
    {trace traceFinal : Trace}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1)
          (.code code) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace)
    (hStep :
      TypedCfg.ObserverSemantics.Program.step
          cfg entry target trace =
        .ok (.jump regular targetFinal, traceFinal)) :
    ∃ final : ObserverSemantics.State transcript,
      ObserverSemantics.Stmt.Eval program fuel
          (.code code) source
          (Structured.OutcomeT.regular final) ∧
        ObserverPreservation.StateRel
          final tokens targetFinal traceFinal := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg code) input with
  | none =>
      simp [TypedCfgCompiler.mkBlock?, hType] at hCompile
  | some output =>
      simp [TypedCfgCompiler.mkBlock?, hType] at hCompile
      cases hCompile
      let generated : TypedCfg.Block :=
        { label := entry
          input := input
          body := TypedCfgCompiler.Code.toCfg code
          output := output
          term := .jump regular }
      have hFind :
          cfg.findBlock? entry = some generated :=
        hBlocks generated (by simp [generated])
      unfold TypedCfg.ObserverSemantics.Program.step at hStep
      rw [hFind] at hStep
      change
        TypedCfg.ObserverSemantics.Block.run generated target trace =
          .ok (.jump regular targetFinal, traceFinal) at hStep
      unfold TypedCfg.ObserverSemantics.Block.run at hStep
      dsimp [generated] at hStep
      cases hBody :
          TypedCfg.ObserverSemantics.Block.runBody
            (TypedCfgCompiler.Code.toCfg code) input target trace with
      | error err =>
          rw [hBody] at hStep
          simp [generated, Bind.bind, Except.bind] at hStep
      | ok bodyResult =>
          rcases bodyResult with ⟨⟨bodyFinal, bodyOutput⟩, bodyTrace⟩
          rw [hBody] at hStep
          simp only [Bind.bind, Except.bind] at hStep
          by_cases hOutput : bodyOutput = output
          · simp [generated, hOutput] at hStep
            rcases hStep with ⟨hFinal, hTrace⟩
            subst bodyOutput
            simp [TypedCfg.Block.runTerm] at hFinal
            subst targetFinal
            subst traceFinal
            obtain ⟨final, hSourceRun, hFinalRel⟩ :=
              Code.run_of_runBody_toCfg
                (by simpa [TypedCfgCompiler.Code.type?] using hType)
                hRel hBody
            exact
              ⟨final,
                Structured.EffectSemantics.Stmt.Eval.code hSourceRun,
                hFinalRel⟩
          · simp [generated, hOutput] at hStep

/--
First-boundary backward adequacy for a straight-line statement.
-/
theorem outcome_code_of_compileStmtFuel?_and_reachesBoundary
    {transcript : Trace} {compilerFuel targetFuel : Nat}
    {program : Structured.Program} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState}
    {trace traceFinal : Trace}
    {targetOutcome : TypedCfg.Outcome}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.code code) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hRegular : continuations.regular = regular)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace)
    (hReach :
      OutcomeSimulation.ReachesBoundary
        cfg continuations (targetFuel + 1)
        entry target trace targetOutcome traceFinal) :
    ∃ sourceFuel sourceOutcome,
      ObserverSemantics.Stmt.Eval
          program sourceFuel (.code code) source sourceOutcome ∧
        ObserverPreservation.OutcomeSimulation.Rel
          continuations tokens sourceOutcome
          targetOutcome traceFinal := by
  obtain ⟨firstOutcome, firstTrace, hStep, _hAfterStep⟩ :=
    TypedCfg.ObserverSemantics.Program.runN_succ_elim hReach.run
  have hHeadStep := hStep
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg code) input with
  | none =>
      simp [TypedCfgCompiler.mkBlock?, hType] at hCompile
  | some output =>
      simp [TypedCfgCompiler.mkBlock?, hType] at hCompile
      cases hCompile
      let generated : TypedCfg.Block :=
        { label := entry
          input := input
          body := TypedCfgCompiler.Code.toCfg code
          output := output
          term := .jump regular }
      have hFind :
          cfg.findBlock? entry = some generated :=
        hBlocks generated (by simp [generated])
      unfold TypedCfg.ObserverSemantics.Program.step at hStep
      rw [hFind] at hStep
      change
        TypedCfg.ObserverSemantics.Block.run generated target trace =
          .ok (firstOutcome, firstTrace) at hStep
      unfold TypedCfg.ObserverSemantics.Block.run at hStep
      dsimp [generated] at hStep
      cases hBody :
          TypedCfg.ObserverSemantics.Block.runBody
            (TypedCfgCompiler.Code.toCfg code) input target trace with
      | error err =>
          rw [hBody] at hStep
          simp [generated, Bind.bind, Except.bind] at hStep
      | ok bodyResult =>
          rcases bodyResult with
            ⟨⟨targetFinal, bodyOutput⟩, bodyTrace⟩
          rw [hBody] at hStep
          simp only [Bind.bind, Except.bind] at hStep
          by_cases hOutput : bodyOutput = output
          · simp [generated, hOutput] at hStep
            subst bodyOutput
            rcases hStep with ⟨hFirst, hFirstTrace⟩
            subst firstOutcome
            subst firstTrace
            obtain ⟨final, hSourceRun, hFinalRel⟩ :=
              Code.run_of_runBody_toCfg
                (by simpa [TypedCfgCompiler.Code.type?] using hType)
                hRel hBody
            have hFirstBoundary :
                OutcomeSimulation.TargetBoundary continuations
                  (.jump regular targetFinal) :=
              Or.inl hRegular.symm
            obtain ⟨hTargetOutcome, hTraceFinal⟩ :=
              OutcomeSimulation.ReachesBoundary.outcome_eq_of_step_boundary
                hReach hHeadStep hFirstBoundary
            subst targetOutcome
            subst traceFinal
            exact
              ⟨compilerFuel,
                Structured.OutcomeT.regular final,
                Structured.EffectSemantics.Stmt.Eval.code hSourceRun,
                ObserverPreservation.OutcomeSimulation.Rel.regular_iff.mpr
                  ⟨hRegular.symm, hFinalRel⟩⟩
          · simp [generated, hOutput] at hStep

theorem adequate_code_of_compileStmtFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {program : Structured.Program} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.code code) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hRegular : continuations.regular = regular) :
    OutcomeSimulation.AdequateAt
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Stmt.Eval
          program sourceFuel (.code code) source sourceOutcome)
      cfg continuations entry input source tokens := by
  intro targetFuel target trace traceFinal targetOutcome hRel hReach
  exact
    outcome_code_of_compileStmtFuel?_and_reachesBoundary
      hCompile hBlocks hRegular hRel hReach

/--
Compiler-facing backward adequacy for a straight-line statement at a boundary
with no active procedure frames.
-/
theorem outcome_code_of_compileStmtFuel?_and_step_noFrames
    {transcript : Trace} {fuel : Nat}
    {program : Structured.Program} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {target targetFinal : EVMState}
    {trace traceFinal : Trace}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1)
          (.code code) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hReturns : source.source.returns = [])
    (hRel :
      ObserverPreservation.StateRel.At
        input source [] target trace)
    (hStep :
      TypedCfg.ObserverSemantics.Program.step
          cfg entry target trace =
        .ok (.jump regular targetFinal, traceFinal)) :
    ∃ final : ObserverSemantics.State transcript,
      ObserverSemantics.Stmt.Eval program fuel
          (.code code) source
          (Structured.OutcomeT.regular final) ∧
        ObserverPreservation.StateRel
          final [] targetFinal traceFinal := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg code) input with
  | none =>
      simp [TypedCfgCompiler.mkBlock?, hType] at hCompile
  | some output =>
      simp [TypedCfgCompiler.mkBlock?, hType] at hCompile
      cases hCompile
      let generated : TypedCfg.Block :=
        { label := entry
          input := input
          body := TypedCfgCompiler.Code.toCfg code
          output := output
          term := .jump regular }
      have hFind :
          cfg.findBlock? entry = some generated :=
        hBlocks generated (by simp [generated])
      unfold TypedCfg.ObserverSemantics.Program.step at hStep
      rw [hFind] at hStep
      change
        TypedCfg.ObserverSemantics.Block.run generated target trace =
          .ok (.jump regular targetFinal, traceFinal) at hStep
      unfold TypedCfg.ObserverSemantics.Block.run at hStep
      dsimp [generated] at hStep
      cases hBody :
          TypedCfg.ObserverSemantics.Block.runBody
            (TypedCfgCompiler.Code.toCfg code) input target trace with
      | error err =>
          rw [hBody] at hStep
          simp [generated, Bind.bind, Except.bind] at hStep
      | ok bodyResult =>
          rcases bodyResult with ⟨⟨bodyFinal, bodyOutput⟩, bodyTrace⟩
          rw [hBody] at hStep
          simp only [Bind.bind, Except.bind] at hStep
          by_cases hOutput : bodyOutput = output
          · simp [generated, hOutput] at hStep
            rcases hStep with ⟨hFinal, hTrace⟩
            subst bodyOutput
            simp [TypedCfg.Block.runTerm] at hFinal
            subst targetFinal
            subst traceFinal
            obtain ⟨final, hSourceRun, hFinalRel⟩ :=
              Code.run_of_runBody_toCfg_noFrames
                (by simpa [TypedCfgCompiler.Code.type?] using hType)
                hReturns hRel.rel hBody
            exact
              ⟨final,
                Structured.EffectSemantics.Stmt.Eval.code hSourceRun,
                hFinalRel⟩
          · simp [generated, hOutput] at hStep

/--
Backward adequacy for the false branch of a compiled conditional across active
procedure frames.
-/
theorem outcome_if_false_of_compileStmtFuel?_and_step
    {transcript : Trace} {fuel : Nat}
    {program : Structured.Program}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target targetFinal : EVMState}
    {trace traceFinal : Trace}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1)
          (.if_ cond body) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hDistinct : LabelSupply.label supply 0 ≠ regular)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace)
    (hStep :
      TypedCfg.ObserverSemantics.Program.step
          cfg entry target trace =
        .ok (.jump regular targetFinal, traceFinal)) :
    ∃ final : ObserverSemantics.State transcript,
      ObserverSemantics.Stmt.Eval program (fuel + 1)
          (.if_ cond body) source
          (Structured.OutcomeT.regular final) ∧
        ObserverPreservation.StateRel
          final tokens targetFinal traceFinal := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg cond) input with
  | none =>
      simp [hType] at hCompile
  | some output =>
      cases hHead : output.slots.head? with
      | none =>
          simp [hType, hHead] at hCompile
      | some condition =>
          cases hBody :
              TypedCfgCompiler.compileBlockFuel? fuel body ctx
                (supply + 1) (LabelSupply.label supply 0)
                { output with slots := output.slots.tail } regular with
          | none =>
              simp [hType, hHead,
                TypedCfgCompiler.mkBlock?, hBody] at hCompile
          | some bodyResult =>
              simp [hType, hHead,
                TypedCfgCompiler.mkBlock?, hBody] at hCompile
              cases hCompile
              let generated : TypedCfg.Block :=
                { label := entry
                  input := input
                  body := TypedCfgCompiler.Code.toCfg cond
                  output := output
                  term :=
                    .jumpi (LabelSupply.label supply 0) regular }
              have hFind :
                  cfg.findBlock? entry = some generated :=
                hBlocks generated (by simp [generated])
              unfold TypedCfg.ObserverSemantics.Program.step at hStep
              rw [hFind] at hStep
              change
                TypedCfg.ObserverSemantics.Block.run
                    generated target trace =
                  .ok (.jump regular targetFinal, traceFinal) at hStep
              unfold TypedCfg.ObserverSemantics.Block.run at hStep
              dsimp [generated] at hStep
              cases hCondBody :
                  TypedCfg.ObserverSemantics.Block.runBody
                    (TypedCfgCompiler.Code.toCfg cond)
                    input target trace with
              | error err =>
                  simp [hCondBody, Bind.bind, Except.bind] at hStep
              | ok bodyRun =>
                  rcases bodyRun with
                    ⟨⟨targetAfter, targetOutput⟩, targetTrace⟩
                  rw [hCondBody] at hStep
                  simp only [Bind.bind, Except.bind] at hStep
                  by_cases hOutput : targetOutput = output
                  · simp [hOutput] at hStep
                    subst targetOutput
                    rcases hStep with ⟨hTerm, hTrace⟩
                    unfold TypedCfg.Block.runTerm at hTerm
                    cases hStack : targetAfter.stack with
                    | nil =>
                        simp [hStack, EvmYul.Stack.pop] at hTerm
                    | cons value stack =>
                        by_cases hZero :
                            value = EvmYul.UInt256.ofNat 0
                        · simp [hStack, EvmYul.Stack.pop, hZero] at hTerm
                          subst targetFinal
                          subst traceFinal
                          have hBne :
                              (value != EvmYul.UInt256.ofNat 0) =
                                false := by
                            rw [hZero]
                            exact
                              TypedCfg.Preservation.uint256_bne_zero_self
                          have hPop :
                              Structured.Code.popCondition targetAfter =
                                .ok
                                  ({ targetAfter with stack := stack },
                                    false) := by
                            unfold Structured.Code.popCondition
                              EffectSemantics.Code.popCondition
                            simp [hStack, EvmYul.Stack.pop, hBne]
                          obtain ⟨final, hCond, hFinalRel⟩ :=
                            Code.runCondition_of_runBody_toCfg
                              (by simpa [TypedCfgCompiler.Code.type?]
                                using hType)
                              hHead hRel
                              hCondBody hPop
                          exact
                            ⟨final,
                              Structured.EffectSemantics.Stmt.Eval.if_false
                                hCond,
                              hFinalRel.rel⟩
                        · simp [hStack, EvmYul.Stack.pop, hZero] at hTerm
                          exact False.elim (hDistinct hTerm.1)
                  · simp [hOutput] at hStep

/--
Backward inversion for the taken head of a compiled conditional.

The generated `jumpi` block, its recursively generated body artifact, and the
post-pop body-entry shape are all reconstructed from the existing compiler
result. No body-preservation witness is accepted here.
-/
theorem condition_if_true_of_compileStmtFuel?_and_step
    {transcript : Trace} {fuel : Nat}
    {program : Structured.Program}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target targetFinal : EVMState}
    {trace traceFinal : Trace}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1)
          (.if_ cond body) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hDistinct : LabelSupply.label supply 0 ≠ regular)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace)
    (hStep :
      TypedCfg.ObserverSemantics.Program.step
          cfg entry target trace =
        .ok
          (.jump (LabelSupply.label supply 0) targetFinal,
            traceFinal)) :
    ∃ output condition bodyResult final,
      TypedCfgCompiler.Code.type? cond input = some output ∧
        output.slots.head? = some condition ∧
        TypedCfgCompiler.compileBlockFuel? fuel body ctx
            (supply + 1) (LabelSupply.label supply 0)
            { output with slots := output.slots.tail } regular =
          some bodyResult ∧
        TypedCfgPreservation.BlocksInProgram bodyResult cfg ∧
        ObserverSemantics.Code.runCondition cond source =
          .ok (final, true) ∧
        ObserverPreservation.StateRel.At
          { output with slots := output.slots.tail }
          final tokens targetFinal traceFinal := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg cond) input with
  | none =>
      simp [hType] at hCompile
  | some output =>
      cases hHead : output.slots.head? with
      | none =>
          simp [hType, hHead] at hCompile
      | some condition =>
          cases hBody :
              TypedCfgCompiler.compileBlockFuel? fuel body ctx
                (supply + 1) (LabelSupply.label supply 0)
                { output with slots := output.slots.tail } regular with
          | none =>
              simp [hType, hHead,
                TypedCfgCompiler.mkBlock?, hBody] at hCompile
          | some bodyResult =>
              simp [hType, hHead,
                TypedCfgCompiler.mkBlock?, hBody] at hCompile
              cases hCompile
              have hBodyBlocks :
                  TypedCfgPreservation.BlocksInProgram
                    bodyResult cfg := by
                intro block hMem
                apply hBlocks block
                simp [hMem]
              let generated : TypedCfg.Block :=
                { label := entry
                  input := input
                  body := TypedCfgCompiler.Code.toCfg cond
                  output := output
                  term :=
                    .jumpi (LabelSupply.label supply 0) regular }
              have hFind :
                  cfg.findBlock? entry = some generated :=
                hBlocks generated (by simp [generated])
              unfold TypedCfg.ObserverSemantics.Program.step at hStep
              rw [hFind] at hStep
              change
                TypedCfg.ObserverSemantics.Block.run
                    generated target trace =
                  .ok
                    (.jump (LabelSupply.label supply 0)
                      targetFinal, traceFinal) at hStep
              unfold TypedCfg.ObserverSemantics.Block.run at hStep
              dsimp [generated] at hStep
              cases hCondBody :
                  TypedCfg.ObserverSemantics.Block.runBody
                    (TypedCfgCompiler.Code.toCfg cond)
                    input target trace with
              | error err =>
                  simp [hCondBody, Bind.bind, Except.bind] at hStep
              | ok bodyRun =>
                  rcases bodyRun with
                    ⟨⟨targetAfter, targetOutput⟩, targetTrace⟩
                  rw [hCondBody] at hStep
                  simp only [Bind.bind, Except.bind] at hStep
                  by_cases hOutput : targetOutput = output
                  · simp [hOutput] at hStep
                    subst targetOutput
                    rcases hStep with ⟨hTerm, hTrace⟩
                    unfold TypedCfg.Block.runTerm at hTerm
                    cases hStack : targetAfter.stack with
                    | nil =>
                        simp [hStack, EvmYul.Stack.pop] at hTerm
                    | cons value stack =>
                        by_cases hZero :
                            value = EvmYul.UInt256.ofNat 0
                        · simp [hStack, EvmYul.Stack.pop, hZero] at hTerm
                          exact
                            False.elim (hDistinct hTerm.1.symm)
                        · simp [hStack, EvmYul.Stack.pop, hZero] at hTerm
                          subst targetFinal
                          subst traceFinal
                          have hBne :
                              (value != EvmYul.UInt256.ofNat 0) =
                                true := by
                            exact
                              TypedCfg.Preservation.uint256_bne_zero_of_ne
                                value hZero
                          have hPop :
                              Structured.Code.popCondition targetAfter =
                                .ok
                                  ({ targetAfter with stack := stack },
                                    true) := by
                            unfold Structured.Code.popCondition
                              EffectSemantics.Code.popCondition
                            simp [hStack, EvmYul.Stack.pop, hBne]
                          obtain ⟨final, hCond, hFinalRel⟩ :=
                            Code.runCondition_of_runBody_toCfg
                              (by simpa [TypedCfgCompiler.Code.type?]
                                using hType)
                              hHead hRel hCondBody hPop
                          exact
                            ⟨output, condition, bodyResult, final,
                              by simpa [TypedCfgCompiler.Code.type?]
                                using hType,
                              hHead, hBody, hBodyBlocks,
                              hCond, hFinalRel⟩
                  · simp [hOutput] at hStep

/--
Classify one successful generated conditional-head step and reconstruct the
corresponding source condition. The body compilation evidence is returned
existentially only in the taken branch.
-/
theorem condition_if_of_compileStmtFuel?_and_step
    {transcript : Trace} {fuel : Nat}
    {program : Structured.Program}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState}
    {trace firstTrace : Trace} {firstOutcome : TypedCfg.Outcome}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1)
          (.if_ cond body) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace)
    (hStep :
      TypedCfg.ObserverSemantics.Program.step
          cfg entry target trace =
        .ok (firstOutcome, firstTrace)) :
    (∃ final targetFinal,
        firstOutcome = .jump regular targetFinal ∧
          ObserverSemantics.Code.runCondition cond source =
            .ok (final, false) ∧
          ObserverPreservation.StateRel
            final tokens targetFinal firstTrace) ∨
      ∃ output condition bodyResult final targetFinal,
        firstOutcome =
            .jump (LabelSupply.label supply 0) targetFinal ∧
          TypedCfgCompiler.Code.type? cond input = some output ∧
          output.slots.head? = some condition ∧
          TypedCfgCompiler.compileBlockFuel? fuel body ctx
              (supply + 1) (LabelSupply.label supply 0)
              { output with slots := output.slots.tail } regular =
            some bodyResult ∧
          TypedCfgPreservation.BlocksInProgram bodyResult cfg ∧
          ObserverSemantics.Code.runCondition cond source =
            .ok (final, true) ∧
          ObserverPreservation.StateRel.At
            { output with slots := output.slots.tail }
            final tokens targetFinal firstTrace := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg cond) input with
  | none =>
      simp [hType] at hCompile
  | some output =>
      cases hHead : output.slots.head? with
      | none =>
          simp [hType, hHead] at hCompile
      | some condition =>
          cases hBody :
              TypedCfgCompiler.compileBlockFuel? fuel body ctx
                (supply + 1) (LabelSupply.label supply 0)
                { output with slots := output.slots.tail } regular with
          | none =>
              simp [hType, hHead,
                TypedCfgCompiler.mkBlock?, hBody] at hCompile
          | some bodyResult =>
              simp [hType, hHead,
                TypedCfgCompiler.mkBlock?, hBody] at hCompile
              cases hCompile
              have hBodyBlocks :
                  TypedCfgPreservation.BlocksInProgram
                    bodyResult cfg := by
                intro block hMem
                apply hBlocks block
                simp [hMem]
              let generated : TypedCfg.Block :=
                { label := entry
                  input := input
                  body := TypedCfgCompiler.Code.toCfg cond
                  output := output
                  term :=
                    .jumpi (LabelSupply.label supply 0) regular }
              have hFind :
                  cfg.findBlock? entry = some generated :=
                hBlocks generated (by simp [generated])
              unfold TypedCfg.ObserverSemantics.Program.step at hStep
              rw [hFind] at hStep
              change
                TypedCfg.ObserverSemantics.Block.run
                    generated target trace =
                  .ok (firstOutcome, firstTrace) at hStep
              unfold TypedCfg.ObserverSemantics.Block.run at hStep
              dsimp [generated] at hStep
              cases hCondBody :
                  TypedCfg.ObserverSemantics.Block.runBody
                    (TypedCfgCompiler.Code.toCfg cond)
                    input target trace with
              | error err =>
                  simp [hCondBody, Bind.bind, Except.bind] at hStep
              | ok bodyRun =>
                  rcases bodyRun with
                    ⟨⟨targetAfter, targetOutput⟩, targetTrace⟩
                  rw [hCondBody] at hStep
                  simp only [Bind.bind, Except.bind] at hStep
                  by_cases hOutput : targetOutput = output
                  · simp [hOutput] at hStep
                    subst targetOutput
                    rcases hStep with ⟨hTerm, hTrace⟩
                    subst firstTrace
                    unfold TypedCfg.Block.runTerm at hTerm
                    obtain
                        ⟨afterCode, hSourceCode, hAfterCodeRel⟩ :=
                      Code.run_of_runBody_toCfg
                        (by simpa [TypedCfgCompiler.Code.type?]
                          using hType)
                        hRel hCondBody
                    have hOutputBound :
                        output.length ≤
                          afterCode.source.evm.stack.length :=
                      Code.shapeSound cond
                        (by simpa [TypedCfgCompiler.Code.type?]
                          using hType)
                        hRel.sourceStack hSourceCode
                    have hAfterCodeAt :
                        ObserverPreservation.StateRel.At
                          output afterCode tokens
                          targetAfter targetTrace :=
                      ⟨hAfterCodeRel, hOutputBound⟩
                    obtain ⟨hidden, hTargetStack⟩ :=
                      ObserverPreservation.StateRel.targetStack_eq_source_append_hidden
                        hAfterCodeAt
                    cases hStack : targetAfter.stack with
                    | nil =>
                        rw [hStack] at hTargetStack
                        simp at hTargetStack
                        have hOutputPos : 1 ≤ output.length := by
                          cases hSlots : output.slots with
                          | nil =>
                              simp [hSlots] at hHead
                          | cons slot rest =>
                              simp [TypedCfg.Shape.length, hSlots]
                        have hSourcePos :
                            1 ≤ afterCode.source.evm.stack.length :=
                          Nat.le_trans hOutputPos hOutputBound
                        simp [hTargetStack.1] at hSourcePos
                    | cons value stack =>
                        by_cases hZero :
                            value = EvmYul.UInt256.ofNat 0
                        · simp [hStack, EvmYul.Stack.pop, hZero] at hTerm
                          have hBne :
                              (value != EvmYul.UInt256.ofNat 0) =
                                false := by
                            rw [hZero]
                            exact
                              TypedCfg.Preservation.uint256_bne_zero_self
                          have hPop :
                              Structured.Code.popCondition targetAfter =
                                .ok
                                  ({ targetAfter with stack := stack },
                                    false) := by
                            unfold Structured.Code.popCondition
                              EffectSemantics.Code.popCondition
                            simp [hStack, EvmYul.Stack.pop, hBne]
                          obtain ⟨final, hCond, hFinalRel⟩ :=
                            Code.runCondition_of_runBody_toCfg
                              (by simpa [TypedCfgCompiler.Code.type?]
                                using hType)
                              hHead hRel hCondBody hPop
                          exact
                            Or.inl
                              ⟨final,
                                { targetAfter with stack := stack },
                                hTerm.symm, hCond, hFinalRel.rel⟩
                        · simp [hStack, EvmYul.Stack.pop, hZero] at hTerm
                          have hBne :
                              (value != EvmYul.UInt256.ofNat 0) =
                                true := by
                            exact
                              TypedCfg.Preservation.uint256_bne_zero_of_ne
                                value hZero
                          have hPop :
                              Structured.Code.popCondition targetAfter =
                                .ok
                                  ({ targetAfter with stack := stack },
                                    true) := by
                            unfold Structured.Code.popCondition
                              EffectSemantics.Code.popCondition
                            simp [hStack, EvmYul.Stack.pop, hBne]
                          obtain ⟨final, hCond, hFinalRel⟩ :=
                            Code.runCondition_of_runBody_toCfg
                              (by simpa [TypedCfgCompiler.Code.type?]
                                using hType)
                              hHead hRel hCondBody hPop
                          exact
                            Or.inr
                              ⟨output, condition, bodyResult, final,
                                { targetAfter with stack := stack },
                                hTerm.symm,
                                by simpa [TypedCfgCompiler.Code.type?]
                                  using hType,
                                hHead, hBody, hBodyBlocks,
                                hCond, hFinalRel⟩
                  · simp [hOutput] at hStep

/--
Private structural composition for a taken conditional.

The eventual public recursive theorem supplies `hBodyAdequate` by induction;
the adjacent-pass API does not expose this callback.
-/
private theorem outcome_if_true_of_compileStmtFuel?_and_step
    {transcript : Trace} {fuel : Nat}
    {program : Structured.Program}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations :
      TypedCfgPreservation.OutcomeSimulation.Continuations}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target targetAfter : EVMState}
    {trace traceAfter traceFinal : Trace}
    {targetOutcome : TypedCfg.Outcome}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1)
          (.if_ cond body) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hDistinct : LabelSupply.label supply 0 ≠ regular)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace)
    (hStep :
      TypedCfg.ObserverSemantics.Program.step
          cfg entry target trace =
        .ok
          (.jump (LabelSupply.label supply 0) targetAfter,
            traceAfter))
    (hBodyEventually :
      TypedCfg.ObserverSemantics.Program.Eventually
        cfg (LabelSupply.label supply 0) targetAfter traceAfter
        targetOutcome traceFinal)
    (hBodyAdequate :
      ∀ {bodyInput : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result}
        {afterCond : ObserverSemantics.State transcript}
        {bodyTarget : EVMState} {bodyTrace : Trace},
        TypedCfgCompiler.compileBlockFuel? fuel body ctx
            (supply + 1) (LabelSupply.label supply 0)
            bodyInput regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        ObserverPreservation.StateRel.At
          bodyInput afterCond tokens bodyTarget bodyTrace →
        TypedCfg.ObserverSemantics.Program.Eventually
          cfg (LabelSupply.label supply 0) bodyTarget bodyTrace
          targetOutcome traceFinal →
        ∃ bodyFuel bodyOutcome,
          ObserverSemantics.Block.Eval
              program bodyFuel body afterCond bodyOutcome ∧
            ObserverPreservation.OutcomeSimulation.Rel
              continuations tokens bodyOutcome
              targetOutcome traceFinal) :
    ∃ sourceFuel sourceOutcome,
      ObserverSemantics.Stmt.Eval
          program sourceFuel (.if_ cond body) source sourceOutcome ∧
        ObserverPreservation.OutcomeSimulation.Rel
          continuations tokens sourceOutcome
          targetOutcome traceFinal := by
  obtain
      ⟨output, condition, bodyResult, afterCond,
        _hType, _hHead, hBodyCompile, hBodyBlocks,
        hCond, hAfterCondRel⟩ :=
    condition_if_true_of_compileStmtFuel?_and_step
      (program := program)
      hCompile hBlocks hDistinct hRel hStep
  obtain ⟨bodyFuel, bodyOutcome, hBodyEval, hOutcomeRel⟩ :=
    hBodyAdequate hBodyCompile hBodyBlocks
      hAfterCondRel hBodyEventually
  exact
    ⟨bodyFuel + 1, bodyOutcome,
      Structured.EffectSemantics.Stmt.Eval.if_true
        hCond hBodyEval,
      hOutcomeRel⟩

/--
Fuel-decreasing backward adequacy for a compiled conditional up to the first
Structured continuation or halt. The recursive body premise is private proof
machinery and is discharged by the mutual block theorem.
-/
private theorem outcome_if_of_compileStmtFuel?_and_reachesBoundary
    {transcript : Trace} {compilerFuel targetFuel : Nat}
    {program : Structured.Program}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState}
    {trace traceFinal : Trace}
    {targetOutcome : TypedCfg.Outcome}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.if_ cond body) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hRegular : continuations.regular = regular)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace)
    (hReach :
      OutcomeSimulation.ReachesBoundary
        cfg continuations (targetFuel + 1)
        entry target trace targetOutcome traceFinal)
    (hBodyAdequate :
      ∀ {bodyInput : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result}
        {afterCond : ObserverSemantics.State transcript}
        {bodyTarget : EVMState} {bodyTrace : Trace}
        {bodyTargetFuel : Nat},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            (supply + 1) (LabelSupply.label supply 0)
            bodyInput regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        ObserverPreservation.StateRel.At
          bodyInput afterCond tokens bodyTarget bodyTrace →
        OutcomeSimulation.ReachesBoundary
          cfg continuations bodyTargetFuel
          (LabelSupply.label supply 0)
          bodyTarget bodyTrace targetOutcome traceFinal →
        ∃ bodySourceFuel bodyOutcome,
          ObserverSemantics.Block.Eval
              program bodySourceFuel body afterCond bodyOutcome ∧
            ObserverPreservation.OutcomeSimulation.Rel
              continuations tokens bodyOutcome
              targetOutcome traceFinal) :
    ∃ sourceFuel sourceOutcome,
      ObserverSemantics.Stmt.Eval
          program sourceFuel (.if_ cond body) source sourceOutcome ∧
        ObserverPreservation.OutcomeSimulation.Rel
          continuations tokens sourceOutcome
          targetOutcome traceFinal := by
  obtain ⟨firstOutcome, firstTrace, hStep, _hAfterStep⟩ :=
    TypedCfg.ObserverSemantics.Program.runN_succ_elim
      hReach.run
  rcases
      condition_if_of_compileStmtFuel?_and_step
        (program := program)
        hCompile hBlocks hRel hStep with
    hFalse | hTrue
  · rcases hFalse with
      ⟨final, targetFinal, hFirst, hCond, hFinalRel⟩
    subst firstOutcome
    have hFirstBoundary :
        OutcomeSimulation.TargetBoundary continuations
          (.jump regular targetFinal) :=
      Or.inl hRegular.symm
    obtain ⟨hTargetOutcome, hTraceFinal⟩ :=
      OutcomeSimulation.ReachesBoundary.outcome_eq_of_step_boundary
        hReach hStep hFirstBoundary
    subst targetOutcome
    subst traceFinal
    exact
      ⟨1, Structured.OutcomeT.regular final,
        Structured.EffectSemantics.Stmt.Eval.if_false
          (fuel := 0) hCond,
        ObserverPreservation.OutcomeSimulation.Rel.regular_iff.mpr
          ⟨hRegular.symm, hFinalRel⟩⟩
  · rcases hTrue with
      ⟨output, condition, bodyResult, afterCond, bodyTarget,
        hFirst, _hType, _hHead, hBodyCompile, hBodyBlocks,
        hCond, hAfterCondRel⟩
    subst firstOutcome
    have hBodyReach :
        OutcomeSimulation.ReachesBoundary
          cfg continuations targetFuel
          (LabelSupply.label supply 0)
          bodyTarget firstTrace targetOutcome traceFinal :=
      OutcomeSimulation.ReachesBoundary.tail_of_step_jump
        hReach hStep
    obtain
        ⟨bodySourceFuel, bodyOutcome,
          hBodyEval, hOutcomeRel⟩ :=
      hBodyAdequate hBodyCompile hBodyBlocks
        hAfterCondRel hBodyReach
    exact
      ⟨bodySourceFuel + 1, bodyOutcome,
        Structured.EffectSemantics.Stmt.Eval.if_true
          hCond hBodyEval,
        hOutcomeRel⟩

/--
Private `AdequateAt` composition rule for conditionals. The mutual recursive
statement/block theorem supplies the body instance.
-/
private theorem adequate_if_of_compileStmtFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {program : Structured.Program}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {continuations : OutcomeSimulation.Continuations}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.if_ cond body) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hRegular : continuations.regular = regular)
    (hBodyEntry :
      ∀ targetState,
        ¬ OutcomeSimulation.TargetBoundary continuations
            (.jump (LabelSupply.label supply 0) targetState))
    (hBodyAdequate :
      ∀ {bodyInput : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result}
        {afterCond : ObserverSemantics.State transcript},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            (supply + 1) (LabelSupply.label supply 0)
            bodyInput regular =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        OutcomeSimulation.AdequateAt
          (fun sourceFuel sourceOutcome =>
            ObserverSemantics.Block.Eval
              program sourceFuel body afterCond sourceOutcome)
          cfg continuations (LabelSupply.label supply 0)
          bodyInput afterCond tokens) :
    OutcomeSimulation.AdequateAt
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Stmt.Eval
          program sourceFuel (.if_ cond body) source sourceOutcome)
      cfg continuations entry input source tokens := by
  intro targetFuel target trace traceFinal targetOutcome hRel hReach
  exact
    outcome_if_of_compileStmtFuel?_and_reachesBoundary
      hCompile hBlocks hRegular hRel hReach
      (by
        intro bodyInput bodyResult afterCond bodyTarget bodyTrace
          bodyTargetFuel hBodyCompile hBodyBlocks hAfterCondRel
          hBodyReach
        have hPositive :
            0 < bodyTargetFuel :=
          OutcomeSimulation.ReachesBoundary.fuel_pos_of_entry_not_boundary
            hBodyReach (hBodyEntry bodyTarget)
        cases bodyTargetFuel with
        | zero =>
            omega
        | succ bodyTargetFuel =>
            exact
              hBodyAdequate hBodyCompile hBodyBlocks
                hAfterCondRel hBodyReach)

/--
Backward adequacy for the false branch of a compiled conditional at a no-frame
boundary. Label distinctness is the local compiler-freshness fact; whole-program
generation will discharge it internally.
-/
theorem outcome_if_false_of_compileStmtFuel?_and_step_noFrames
    {transcript : Trace} {fuel : Nat}
    {program : Structured.Program}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {target targetFinal : EVMState}
    {trace traceFinal : Trace}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1)
          (.if_ cond body) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hDistinct : LabelSupply.label supply 0 ≠ regular)
    (hReturns : source.source.returns = [])
    (hRel :
      ObserverPreservation.StateRel.At
        input source [] target trace)
    (hStep :
      TypedCfg.ObserverSemantics.Program.step
          cfg entry target trace =
        .ok (.jump regular targetFinal, traceFinal)) :
    ∃ final : ObserverSemantics.State transcript,
      ObserverSemantics.Stmt.Eval program (fuel + 1)
          (.if_ cond body) source
          (Structured.OutcomeT.regular final) ∧
        ObserverPreservation.StateRel
          final [] targetFinal traceFinal := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg cond) input with
  | none =>
      simp [hType] at hCompile
  | some output =>
      cases hHead : output.slots.head? with
      | none =>
          simp [hType, hHead] at hCompile
      | some condition =>
          cases hBody :
              TypedCfgCompiler.compileBlockFuel? fuel body ctx
                (supply + 1) (LabelSupply.label supply 0)
                { output with slots := output.slots.tail } regular with
          | none =>
              simp [hType, hHead,
                TypedCfgCompiler.mkBlock?, hBody] at hCompile
          | some bodyResult =>
              simp [hType, hHead,
                TypedCfgCompiler.mkBlock?, hBody] at hCompile
              cases hCompile
              let generated : TypedCfg.Block :=
                { label := entry
                  input := input
                  body := TypedCfgCompiler.Code.toCfg cond
                  output := output
                  term :=
                    .jumpi (LabelSupply.label supply 0) regular }
              have hFind :
                  cfg.findBlock? entry = some generated :=
                hBlocks generated (by simp [generated])
              unfold TypedCfg.ObserverSemantics.Program.step at hStep
              rw [hFind] at hStep
              change
                TypedCfg.ObserverSemantics.Block.run
                    generated target trace =
                  .ok (.jump regular targetFinal, traceFinal) at hStep
              unfold TypedCfg.ObserverSemantics.Block.run at hStep
              dsimp [generated] at hStep
              cases hCondBody :
                  TypedCfg.ObserverSemantics.Block.runBody
                    (TypedCfgCompiler.Code.toCfg cond)
                    input target trace with
              | error err =>
                  simp [hCondBody, Bind.bind, Except.bind] at hStep
              | ok bodyRun =>
                  rcases bodyRun with
                    ⟨⟨targetAfter, targetOutput⟩, targetTrace⟩
                  rw [hCondBody] at hStep
                  simp only [Bind.bind, Except.bind] at hStep
                  by_cases hOutput : targetOutput = output
                  · simp [hOutput] at hStep
                    subst targetOutput
                    rcases hStep with ⟨hTerm, hTrace⟩
                    unfold TypedCfg.Block.runTerm at hTerm
                    cases hStack : targetAfter.stack with
                    | nil =>
                        simp [hStack, EvmYul.Stack.pop] at hTerm
                    | cons value stack =>
                        by_cases hZero :
                            value = EvmYul.UInt256.ofNat 0
                        · simp [hStack, EvmYul.Stack.pop, hZero] at hTerm
                          subst targetFinal
                          subst traceFinal
                          have hBne :
                              (value != EvmYul.UInt256.ofNat 0) =
                                false := by
                            rw [hZero]
                            exact
                              TypedCfg.Preservation.uint256_bne_zero_self
                          have hPop :
                              Structured.Code.popCondition targetAfter =
                                .ok
                                  ({ targetAfter with stack := stack },
                                    false) := by
                            unfold Structured.Code.popCondition
                              EffectSemantics.Code.popCondition
                            simp [hStack, EvmYul.Stack.pop, hBne]
                          obtain ⟨final, hCond, hFinalRel⟩ :=
                            Code.runCondition_of_runBody_toCfg_noFrames
                              (by simpa [TypedCfgCompiler.Code.type?]
                                using hType)
                              hReturns hRel.rel hCondBody hPop
                          exact
                            ⟨final,
                              Structured.EffectSemantics.Stmt.Eval.if_false
                                hCond,
                              hFinalRel⟩
                        · simp [hStack, EvmYul.Stack.pop, hZero] at hTerm
                          exact False.elim (hDistinct hTerm.1)
                  · simp [hOutput] at hStep

/--
A well-typed TypedCfg halt cannot obtain missing operands from compiler-owned
return data. The shape-indexed relation therefore reconstructs the
corresponding observer-aware Structured terminal evaluation.
-/
theorem terminal_of_wellTyped_halt
    {transcript : Trace} {program : Structured.Program}
    {cfg : TypedCfg.Program} {block : TypedCfg.Block}
    {kind : Assembly.HaltKind}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState} {trace : Trace}
    {fuel : Nat}
    (hTyped : block.WellTyped cfg)
    (hTerm : block.term = .halt kind)
    (hRel :
      ObserverPreservation.StateRel.At
        block.output source tokens target trace) :
    ∃ finalEVM,
      Structured.Terminal.step kind source.source.evm =
          .ok finalEVM ∧
        ObserverSemantics.Stmt.Eval program fuel
          (.terminal kind) source
          (Structured.OutcomeT.halt kind
            (source.withSource
              (source.source.withEVM finalEVM))) := by
  have hArityShape :
      kind.argCount ≤ block.output.length :=
    TypedCfg.Block.halt_argCount_le_of_wellTyped hTyped hTerm
  have hAritySource :
      kind.argCount ≤ source.source.evm.stack.length :=
    Nat.le_trans hArityShape hRel.sourceStack
  obtain ⟨finalEVM, hStep⟩ :=
    Structured.Terminal.exists_step_of_argCount_le
      kind source.source.evm hAritySource
  exact
    ⟨finalEVM, hStep,
      Structured.EffectSemantics.Stmt.Eval.terminal hStep⟩

/--
The terminal backward leaf also reconstructs the post-terminal target relation.
This is the outcome-indexed fact needed by the recursive statement adequacy
proof; no terminal-safety premise remains at the boundary.
-/
theorem terminal_outcome_of_wellTyped_halt
    {transcript : Trace} {program : Structured.Program}
    {cfg : TypedCfg.Program} {block : TypedCfg.Block}
    {kind : Assembly.HaltKind}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState} {trace : Trace}
    {fuel : Nat}
    (hTyped : block.WellTyped cfg)
    (hTerm : block.term = .halt kind)
    (hRel :
      ObserverPreservation.StateRel.At
        block.output source tokens target trace) :
    ∃ sourceFinal targetFinal,
      Structured.Terminal.step kind source.source.evm =
          .ok sourceFinal ∧
        Structured.Terminal.step kind target =
          .ok targetFinal ∧
        ObserverSemantics.Stmt.Eval program fuel
          (.terminal kind) source
          (Structured.OutcomeT.halt kind
            (source.withSource
              (source.source.withEVM sourceFinal))) ∧
        ObserverPreservation.StateRel
          (source.withSource
            (source.source.withEVM sourceFinal))
          tokens targetFinal trace := by
  obtain ⟨sourceFinal, hSourceStep, hEval⟩ :=
    terminal_of_wellTyped_halt hTyped hTerm hRel
  obtain ⟨targetFinal, hTargetStep, hFinalRel⟩ :=
    ObserverPreservation.StateRel.terminal hRel.rel hSourceStep
  exact
    ⟨sourceFinal, targetFinal, hSourceStep, hTargetStep,
      hEval, hFinalRel⟩

/--
Compiler-facing backward adequacy for a terminal statement.

The checked compiler block and ambient CFG typing construct all target evidence
internally. The public inputs are the existing compiler result, its generated
block inclusion, and the adjacent shape-indexed state relation.
-/
theorem outcome_terminal_of_compileStmtFuel?
    {transcript : Trace} {fuel : Nat}
    {program : Structured.Program} {kind : Assembly.HaltKind}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState} {trace : Trace}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1)
          (.terminal kind) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hWellTyped : cfg.WellTyped)
    (hRel :
      ObserverPreservation.StateRel.At
        input source tokens target trace) :
    ∃ sourceFinal targetFinal,
      ObserverSemantics.Stmt.Eval program fuel
          (.terminal kind) source
          (Structured.OutcomeT.halt kind
            (source.withSource
              (source.source.withEVM sourceFinal))) ∧
        TypedCfg.ObserverSemantics.Program.Eventually
          cfg entry target trace (.halt kind target) trace ∧
        Structured.Terminal.step kind target =
          .ok targetFinal ∧
        ObserverPreservation.StateRel
          (source.withSource
            (source.source.withEVM sourceFinal))
          tokens targetFinal trace := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  simp [TypedCfgCompiler.mkBlock?] at hCompile
  cases hCompile
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .halt kind }
  have hFind :
      cfg.findBlock? entry = some generated :=
    hBlocks generated (by simp [generated])
  have hMem : generated ∈ cfg.blocks := by
    unfold TypedCfg.Program.findBlock? at hFind
    exact List.mem_of_find?_eq_some hFind
  have hTyped : generated.WellTyped cfg :=
    (List.forall_iff_forall_mem.mp hWellTyped.2.1) generated hMem
  obtain
      ⟨sourceFinal, targetFinal, _hSourceStep,
        hTargetStep, hEval, hFinalRel⟩ :=
    terminal_outcome_of_wellTyped_halt
      (fuel := fuel) hTyped (by rfl) hRel
  have hRun :
      TypedCfg.ObserverSemantics.Block.run
          generated target trace =
        .ok (.halt kind target, trace) := by
    unfold TypedCfg.ObserverSemantics.Block.run
    rw [TypedCfg.ObserverSemantics.Block.runBody_nil]
    simp [generated, TypedCfg.Block.runTerm,
      Bind.bind, Except.bind]
  have hEventually :=
    ObserverPreservation.BlocksInProgram.eventually_of_run
      hBlocks (block := generated) (by simp [generated]) hRun
  exact
    ⟨sourceFinal, targetFinal, hEval, hEventually,
      hTargetStep, hFinalRel⟩

end Stmt

end ObserverAdequacy
end Structured
end EvmCompiler
