import EvmCompiler.Structured.ObserverAdequacy

namespace EvmCompiler
namespace Structured
namespace ObserverAdequacy
namespace Loop

abbrev bodyContinuations :=
  TypedCfgPreservation.OutcomeSimulation.Loop.bodyContinuations

abbrev postContinuations :=
  TypedCfgPreservation.OutcomeSimulation.Loop.postContinuations

private theorem jumpOr_of_accept
    {next : Assembly.Label}
    {accept : TypedCfg.Outcome → Prop}
    {outcome : TypedCfg.Outcome}
    (hAccept : accept outcome) :
    OutcomeSimulation.JumpOr next accept outcome := by
  cases outcome <;> simp [OutcomeSimulation.JumpOr, hAccept]

private theorem bodyBoundary
    {endLabel postLabel : Assembly.Label}
    {outer : OutcomeSimulation.Continuations}
    {accept : TypedCfg.Outcome → Prop}
    {outcome : TypedCfg.Outcome}
    (hOuter :
      ∀ targetOutcome,
        OutcomeSimulation.TargetBoundary outer targetOutcome →
          accept targetOutcome)
    (hOuterRegular : outer.regular = endLabel)
    (hBoundary :
      OutcomeSimulation.TargetBoundary
        (bodyContinuations endLabel postLabel outer) outcome) :
    OutcomeSimulation.JumpOr postLabel accept outcome := by
  cases outcome with
  | jump label target =>
      change
        label = postLabel ∨
          some endLabel = some label ∨
          some postLabel = some label ∨
          outer.leaveLabel? = some label at hBoundary
      change label = postLabel ∨ accept (.jump label target)
      rcases hBoundary with hPost | hBreak | hContinue | hLeave
      · exact Or.inl hPost
      · exact Or.inr (hOuter _ (by
          have hLabel : label = outer.regular := by
            exact (Option.some.inj hBreak).symm.trans hOuterRegular.symm
          simp [OutcomeSimulation.TargetBoundary, hLabel]))
      · exact Or.inl (Option.some.inj hContinue).symm
      · exact Or.inr (hOuter _ (by
          simp [OutcomeSimulation.TargetBoundary, hLeave]))
  | halt kind target =>
      exact jumpOr_of_accept (hOuter _ (by
        simp [OutcomeSimulation.TargetBoundary]))
  | fallthrough target | returnDispatch target | invalid target =>
      simp [OutcomeSimulation.TargetBoundary] at hBoundary

private theorem postBoundary
    {loopLabel : Assembly.Label}
    {outer : OutcomeSimulation.Continuations}
    {accept : TypedCfg.Outcome → Prop}
    {outcome : TypedCfg.Outcome}
    (hOuter :
      ∀ targetOutcome,
        OutcomeSimulation.TargetBoundary outer targetOutcome →
          accept targetOutcome)
    (hBoundary :
      OutcomeSimulation.TargetBoundary
        (postContinuations loopLabel outer) outcome) :
    OutcomeSimulation.JumpOr loopLabel accept outcome := by
  cases outcome with
  | jump label target =>
      change
        label = loopLabel ∨
          none = some label ∨
          none = some label ∨
          outer.leaveLabel? = some label at hBoundary
      change label = loopLabel ∨ accept (.jump label target)
      rcases hBoundary with hLoop | hBreak | hContinue | hLeave
      · exact Or.inl hLoop
      · cases hBreak
      · cases hContinue
      · exact Or.inr (hOuter _ (by
          simp [OutcomeSimulation.TargetBoundary, hLeave]))
  | halt kind target =>
      exact jumpOr_of_accept (hOuter _ (by
        simp [OutcomeSimulation.TargetBoundary]))
  | fallthrough target | returnDispatch target | invalid target =>
      simp [OutcomeSimulation.TargetBoundary] at hBoundary

private theorem bodyLeaveRel
    {transcript : Trace}
    {endLabel postLabel : Assembly.Label}
    {outer : OutcomeSimulation.Continuations}
    {tokens : List Word}
    {source : ObserverSemantics.State transcript}
    {targetOutcome : TypedCfg.Outcome} {trace : Trace}
    (hRel :
      ObserverPreservation.OutcomeSimulation.Rel
        (bodyContinuations endLabel postLabel outer)
        tokens (Structured.OutcomeT.leave source)
        targetOutcome trace) :
    ObserverPreservation.OutcomeSimulation.Rel
      outer tokens (Structured.OutcomeT.leave source)
      targetOutcome trace := by
  cases targetOutcome <;>
    simpa [
      ObserverPreservation.OutcomeSimulation.Rel,
      TypedCfgPreservation.OutcomeSimulation.Loop.bodyContinuations] using
      hRel

private theorem bodyHaltRel
    {transcript : Trace}
    {endLabel postLabel : Assembly.Label}
    {outer : OutcomeSimulation.Continuations}
    {tokens : List Word}
    {source : ObserverSemantics.State transcript}
    {kind : Assembly.HaltKind}
    {targetOutcome : TypedCfg.Outcome} {trace : Trace}
    (hRel :
      ObserverPreservation.OutcomeSimulation.Rel
        (bodyContinuations endLabel postLabel outer)
        tokens (Structured.OutcomeT.halt kind source)
        targetOutcome trace) :
    ObserverPreservation.OutcomeSimulation.Rel
      outer tokens (Structured.OutcomeT.halt kind source)
      targetOutcome trace := by
  cases targetOutcome <;>
    simpa [
      ObserverPreservation.OutcomeSimulation.Rel,
      TypedCfgPreservation.OutcomeSimulation.Loop.bodyContinuations] using
      hRel

private theorem postLeaveRel
    {transcript : Trace}
    {loopLabel : Assembly.Label}
    {outer : OutcomeSimulation.Continuations}
    {tokens : List Word}
    {source : ObserverSemantics.State transcript}
    {targetOutcome : TypedCfg.Outcome} {trace : Trace}
    (hRel :
      ObserverPreservation.OutcomeSimulation.Rel
        (postContinuations loopLabel outer)
        tokens (Structured.OutcomeT.leave source)
        targetOutcome trace) :
    ObserverPreservation.OutcomeSimulation.Rel
      outer tokens (Structured.OutcomeT.leave source)
      targetOutcome trace := by
  cases targetOutcome <;>
    simpa [
      ObserverPreservation.OutcomeSimulation.Rel,
      TypedCfgPreservation.OutcomeSimulation.Loop.postContinuations] using
      hRel

private theorem postHaltRel
    {transcript : Trace}
    {loopLabel : Assembly.Label}
    {outer : OutcomeSimulation.Continuations}
    {tokens : List Word}
    {source : ObserverSemantics.State transcript}
    {kind : Assembly.HaltKind}
    {targetOutcome : TypedCfg.Outcome} {trace : Trace}
    (hRel :
      ObserverPreservation.OutcomeSimulation.Rel
        (postContinuations loopLabel outer)
        tokens (Structured.OutcomeT.halt kind source)
        targetOutcome trace) :
    ObserverPreservation.OutcomeSimulation.Rel
      outer tokens (Structured.OutcomeT.halt kind source)
      targetOutcome trace := by
  cases targetOutcome <;>
    simpa [
      ObserverPreservation.OutcomeSimulation.Rel,
      TypedCfgPreservation.OutcomeSimulation.Loop.postContinuations] using
      hRel

/--
Invert one generated loop-condition step and reconstruct the corresponding
Structured condition evaluation. The target block is the existing compiler
block; no alternate interpreter or generated-code premise crosses the adjacent
pass boundary.
-/
theorem condition_of_step
    {transcript : Trace}
    {cond : Structured.Code}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {loopLabel bodyLabel endLabel : Assembly.Label}
    {loopInput condOutput : TypedCfg.Shape}
    {condition : TypedCfg.Slot}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState}
    {trace firstTrace : Trace} {firstOutcome : TypedCfg.Outcome}
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hMem :
      { label := loopLabel
        input := loopInput
        body := TypedCfgCompiler.Code.toCfg cond
        output := condOutput
        term := .jumpi bodyLabel endLabel } ∈ result.blocks)
    (hType :
      TypedCfgCompiler.Code.type? cond loopInput =
        some condOutput)
    (hSource :
      TypedCfgCompiler.Shape.requireSourceWords? 1 condOutput =
        some ())
    (hHead : condOutput.slots.head? = some condition)
    (hRel :
      ObserverPreservation.StateRel.At
        loopInput source tokens target trace)
    (hStep :
      TypedCfg.ObserverSemantics.Program.step
          cfg loopLabel target trace =
        .ok (firstOutcome, firstTrace)) :
    (∃ final targetFinal,
        firstOutcome = .jump endLabel targetFinal ∧
          ObserverSemantics.Code.runCondition cond source =
            .ok (final, false) ∧
          ObserverPreservation.StateRel.At
            { condOutput with slots := condOutput.slots.tail }
            final tokens targetFinal firstTrace) ∨
      ∃ final targetFinal,
        firstOutcome = .jump bodyLabel targetFinal ∧
          ObserverSemantics.Code.runCondition cond source =
            .ok (final, true) ∧
          ObserverPreservation.StateRel.At
            { condOutput with slots := condOutput.slots.tail }
            final tokens targetFinal firstTrace := by
  let generated : TypedCfg.Block :=
    { label := loopLabel
      input := loopInput
      body := TypedCfgCompiler.Code.toCfg cond
      output := condOutput
      term := .jumpi bodyLabel endLabel }
  have hFind :
      cfg.findBlock? loopLabel = some generated :=
    hBlocks generated (by simpa [generated] using hMem)
  unfold TypedCfg.ObserverSemantics.Program.step at hStep
  rw [hFind] at hStep
  change
    TypedCfg.ObserverSemantics.Block.run generated target trace =
      .ok (firstOutcome, firstTrace) at hStep
  unfold TypedCfg.ObserverSemantics.Block.run at hStep
  dsimp [generated] at hStep
  cases hCondBody :
      TypedCfg.ObserverSemantics.Block.runBody
        (TypedCfgCompiler.Code.toCfg cond)
        loopInput target trace with
  | error err =>
      simp [hCondBody, Bind.bind, Except.bind] at hStep
  | ok bodyRun =>
      rcases bodyRun with
        ⟨⟨targetAfter, targetOutput⟩, targetTrace⟩
      rw [hCondBody] at hStep
      simp only [Bind.bind, Except.bind] at hStep
      by_cases hOutput : targetOutput = condOutput
      · simp [hOutput] at hStep
        subst targetOutput
        rcases hStep with ⟨hTerm, hTrace⟩
        subst firstTrace
        unfold TypedCfg.Block.runTerm at hTerm
        obtain
            ⟨afterCode, hSourceCode, hAfterCodeRel⟩ :=
          Code.run_of_runBody_toCfg hType hRel hCondBody
        have hOutputBound :
            TypedCfgCompiler.Shape.sourceLength condOutput ≤
              afterCode.source.evm.stack.length :=
          Code.shapeSound cond hType
            hRel.sourceStack hSourceCode
        have hAfterCodeAt :
            ObserverPreservation.StateRel.At
              condOutput afterCode tokens
              targetAfter targetTrace :=
          ObserverPreservation.StateRel.At.ofFits hAfterCodeRel
            (Code.sourceFrameFits cond hType
              hRel.sourceFrameFits hSourceCode)
        obtain ⟨hidden, hTargetStack⟩ :=
          ObserverPreservation.StateRel.targetStack_eq_source_append_hidden
            hAfterCodeAt
        cases hStack : targetAfter.stack with
        | nil =>
            rw [hStack] at hTargetStack
            simp at hTargetStack
            have hOutputPos :
                1 ≤ TypedCfgCompiler.Shape.sourceLength condOutput :=
              TypedCfgCompilerFacts.Shape.requireSourceWords?_eq_some_iff.mp
                hSource
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
                  hType hSource hHead hRel hCondBody hPop
              exact
                Or.inl
                  ⟨final, { targetAfter with stack := stack },
                    hTerm.symm, hCond, hFinalRel⟩
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
                  hType hSource hHead hRel hCondBody hPop
              exact
                Or.inr
                  ⟨final, { targetAfter with stack := stack },
                    hTerm.symm, hCond, hFinalRel⟩
      · simp [hOutput] at hStep

/--
Backward adequacy for the recursive loop core, beginning at the generated
condition block. Recursive body and post proofs are supplied only through the
adjacent block interface; recursion itself decreases the concrete residual
target fuel.
-/
private theorem outcome_for_step_of_firstReaches
    {transcript : Trace} {targetFuel : Nat}
    {program : Structured.Program}
    {cond : Structured.Code} {post body : Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {cfg : TypedCfg.Program}
    {loopLabel bodyLabel postLabel endLabel : Assembly.Label}
    {loopInput condOutput : TypedCfg.Shape}
    {condition : TypedCfg.Slot}
    {result bodyResult postResult : TypedCfgCompiler.Result}
    {outer : OutcomeSimulation.Continuations}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState}
    {trace traceFinal : Trace} {targetOutcome : TypedCfg.Outcome}
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hLoopMem :
      { label := loopLabel
        input := loopInput
        body := TypedCfgCompiler.Code.toCfg cond
        output := condOutput
        term := .jumpi bodyLabel endLabel } ∈ result.blocks)
    (hType :
      TypedCfgCompiler.Code.type? cond loopInput = some condOutput)
    (hSource :
      TypedCfgCompiler.Shape.requireSourceWords? 1 condOutput =
        some ())
    (hHead : condOutput.slots.head? = some condition)
    (hBodyRequire :
      bodyResult.requireFallthrough?
          { condOutput with slots := condOutput.slots.tail } =
        some ())
    (hPostRequire :
      postResult.requireFallthrough? loopInput = some ())
    (hOuterRegular : outer.regular = endLabel)
    (hAccept :
      ∀ acceptedOutcome,
        OutcomeSimulation.TargetBoundary outer acceptedOutcome →
          accept acceptedOutcome)
    (hBodyEntryNotAccepted :
      ∀ targetState,
        ¬ OutcomeSimulation.JumpOr postLabel accept
          (.jump bodyLabel targetState))
    (hPostEntryNotAccepted :
      ∀ targetState,
        ¬ OutcomeSimulation.JumpOr loopLabel accept
          (.jump postLabel targetState))
    (hLoopEntryNotAccepted :
      ∀ targetState, ¬ accept (.jump loopLabel targetState))
    (hRel :
      ObserverPreservation.StateRel.At
        loopInput source tokens target trace)
    (hReach :
      OutcomeSimulation.FirstReaches cfg accept (targetFuel + 1)
        loopLabel target trace targetOutcome traceFinal)
    (hBodyAdequate :
      ∀ {bodySource : ObserverSemantics.State transcript},
        OutcomeSimulation.AdequateWithin
          (fun sourceFuel sourceOutcome =>
            ObserverSemantics.Block.Eval
              program sourceFuel body bodySource sourceOutcome)
          bodyResult
          { ctx with
            breakLabel? := some endLabel
            breakShape? :=
              some { condOutput with slots := condOutput.slots.tail }
            continueLabel? := some postLabel
            continueShape? :=
              some { condOutput with slots := condOutput.slots.tail } }
          cfg (bodyContinuations endLabel postLabel outer)
          (OutcomeSimulation.JumpOr postLabel accept)
          bodyLabel
          { condOutput with slots := condOutput.slots.tail }
          bodySource tokens)
    (hPostAdequate :
      ∀ {postSource : ObserverSemantics.State transcript},
        OutcomeSimulation.AdequateWithin
          (fun sourceFuel sourceOutcome =>
            ObserverSemantics.Block.Eval
              program sourceFuel post postSource sourceOutcome)
          postResult
          { ctx with
            breakLabel? := none
            breakShape? := none
            continueLabel? := none
            continueShape? := none }
          cfg (postContinuations loopLabel outer)
          (OutcomeSimulation.JumpOr loopLabel accept)
          postLabel
          { condOutput with slots := condOutput.slots.tail }
          postSource tokens)
    (hRecurse :
      ∀ {smallerFuel : Nat}
        {loopSource : ObserverSemantics.State transcript}
        {loopTarget : EVMState} {loopTrace : Trace},
        smallerFuel < targetFuel →
        ObserverPreservation.StateRel.At
            loopInput loopSource tokens loopTarget loopTrace →
        OutcomeSimulation.FirstReaches cfg accept (smallerFuel + 1)
            loopLabel loopTarget loopTrace targetOutcome traceFinal →
        ∃ sourceFuel sourceOutcome,
          ObserverSemantics.For.Eval program sourceFuel
              cond post body loopSource sourceOutcome ∧
            ObserverPreservation.OutcomeSimulation.Rel
              outer tokens sourceOutcome targetOutcome traceFinal ∧
            OutcomeSimulation.JoinArtifact ctx
              { condOutput with slots := condOutput.slots.tail }
              sourceOutcome) :
    ∃ sourceFuel sourceOutcome,
      ObserverSemantics.For.Eval program sourceFuel
          cond post body source sourceOutcome ∧
        ObserverPreservation.OutcomeSimulation.Rel
          outer tokens sourceOutcome targetOutcome traceFinal ∧
        OutcomeSimulation.JoinArtifact ctx
          { condOutput with slots := condOutput.slots.tail }
          sourceOutcome := by
  obtain ⟨firstOutcome, firstTrace, hStep, _hAfterStep⟩ :=
    TypedCfg.ObserverSemantics.Program.runN_succ_elim hReach.run
  rcases
      condition_of_step hBlocks hLoopMem hType hSource hHead hRel hStep with
    hFalse | hTrue
  · rcases hFalse with
      ⟨afterCond, targetAfterCond, rfl, hCond, hAfterCondRel⟩
    have hBoundary :
        OutcomeSimulation.TargetBoundary outer
          (.jump endLabel targetAfterCond) := by
      simp [OutcomeSimulation.TargetBoundary, hOuterRegular]
    obtain ⟨hOutcomeEq, hTraceEq⟩ :=
      OutcomeSimulation.FirstReaches.outcome_eq_of_step_accepted
        hReach hStep (hAccept _ hBoundary)
    subst targetOutcome
    subst traceFinal
    exact
      ⟨1, Structured.OutcomeT.regular afterCond,
        Structured.EffectSemantics.For.Eval.false
          (fuel := 0) hCond,
        ObserverPreservation.OutcomeSimulation.Rel.regular_iff.mpr
          ⟨hOuterRegular.symm, hAfterCondRel.rel⟩,
        hAfterCondRel.sourceFrameFits⟩
  · rcases hTrue with
      ⟨afterCond, targetAfterCond, rfl, hCond, hAfterCondRel⟩
    have hTailReach :
        OutcomeSimulation.FirstReaches cfg accept targetFuel
          bodyLabel targetAfterCond firstTrace
          targetOutcome traceFinal :=
      OutcomeSimulation.FirstReaches.tail_of_step_jump hReach hStep
    obtain
        ⟨bodyPrefixFuel, bodyTargetOutcome, bodyTrace,
          hBodyLe, hBodyReach⟩ :=
      OutcomeSimulation.FirstReaches.exists_of_run
        hTailReach.run (jumpOr_of_accept hTailReach.boundary)
    have hBodyPositive : 0 < bodyPrefixFuel :=
      OutcomeSimulation.FirstReaches.fuel_pos_of_entry_not_accepted
        hBodyReach (hBodyEntryNotAccepted targetAfterCond)
    cases bodyPrefixFuel with
    | zero =>
        omega
    | succ bodyPrefixFuel =>
        obtain
            ⟨bodySourceFuel, bodyOutcome,
              hBodyEval, hBodyOutcomeRel, hBodyArtifact⟩ :=
          hBodyAdequate
            (fun targetOutcome hBoundary =>
              bodyBoundary (postLabel := postLabel)
                hAccept hOuterRegular hBoundary)
            hAfterCondRel hBodyReach
        have hBodyJoin :
            OutcomeSimulation.JoinArtifact
              { ctx with
                breakLabel? := some endLabel
                breakShape? :=
                  some { condOutput with slots := condOutput.slots.tail }
                continueLabel? := some postLabel
                continueShape? :=
                  some { condOutput with slots := condOutput.slots.tail } }
              { condOutput with slots := condOutput.slots.tail }
              bodyOutcome :=
          OutcomeSimulation.OutcomeArtifact.toJoin_of_requireFallthrough
            hBodyRequire hBodyArtifact
        rcases bodyOutcome with ⟨bodyState, bodyMode⟩
        cases bodyMode with
        | brk =>
            obtain
                ⟨label, bodyTarget, hLabel,
                  hTargetOutcome, hBodyStateRel⟩ :=
              ObserverPreservation.OutcomeSimulation.Rel.brk_elim
                hBodyOutcomeRel
            have hLabelEq : label = endLabel := by
              change some endLabel = some label at hLabel
              exact (Option.some.inj hLabel).symm
            subst label
            subst bodyTargetOutcome
            have hOuterRel :
                ObserverPreservation.OutcomeSimulation.Rel
                  outer tokens (Structured.OutcomeT.regular bodyState)
                  (.jump endLabel bodyTarget) bodyTrace :=
              ObserverPreservation.OutcomeSimulation.Rel.regular_iff.mpr
                ⟨hOuterRegular.symm, hBodyStateRel⟩
            obtain ⟨_hFuelEq, hOutcomeEq, hTraceEq⟩ :=
              OutcomeSimulation.FirstReaches.outcome_eq_of_prefix_accepted
                hTailReach hBodyReach hBodyLe
                (hAccept _
                  (OutcomeSimulation.targetBoundary_of_rel hOuterRel))
            subst targetOutcome
            subst traceFinal
            change
              ∃ output,
                (some { condOutput with
                    slots := condOutput.slots.tail } :
                  Option TypedCfg.Shape) = some output ∧
                TypedCfgCompiler.Shape.SourceFrameFits output
                  bodyState.source.evm.stack.length
              at hBodyJoin
            obtain ⟨output, hOutput, hBound⟩ := hBodyJoin
            have hOutputEq :
                output =
                  { condOutput with slots := condOutput.slots.tail } :=
              Option.some.inj hOutput.symm
            subst output
            exact
              ⟨bodySourceFuel + 1,
                Structured.OutcomeT.regular bodyState,
                Structured.EffectSemantics.For.Eval.body_brk
                  hCond hBodyEval,
                hOuterRel, hBound⟩
        | leave =>
            have hOuterRel :
                ObserverPreservation.OutcomeSimulation.Rel
                  outer tokens (Structured.OutcomeT.leave bodyState)
                  bodyTargetOutcome bodyTrace := by
              exact bodyLeaveRel hBodyOutcomeRel
            obtain ⟨_hFuelEq, hOutcomeEq, hTraceEq⟩ :=
              OutcomeSimulation.FirstReaches.outcome_eq_of_prefix_accepted
                hTailReach hBodyReach hBodyLe
                (hAccept _
                  (OutcomeSimulation.targetBoundary_of_rel hOuterRel))
            subst targetOutcome
            subst traceFinal
            exact
              ⟨bodySourceFuel + 1,
                Structured.OutcomeT.leave bodyState,
                Structured.EffectSemantics.For.Eval.body_leave
                  hCond hBodyEval,
                hOuterRel,
                by
                  simpa [OutcomeSimulation.JoinArtifact] using
                    hBodyJoin⟩
        | halt kind =>
            have hOuterRel :
                ObserverPreservation.OutcomeSimulation.Rel
                  outer tokens (Structured.OutcomeT.halt kind bodyState)
                  bodyTargetOutcome bodyTrace := by
              exact bodyHaltRel hBodyOutcomeRel
            obtain ⟨_hFuelEq, hOutcomeEq, hTraceEq⟩ :=
              OutcomeSimulation.FirstReaches.outcome_eq_of_prefix_accepted
                hTailReach hBodyReach hBodyLe
                (hAccept _
                  (OutcomeSimulation.targetBoundary_of_rel hOuterRel))
            subst targetOutcome
            subst traceFinal
            exact
              ⟨bodySourceFuel + 1,
                Structured.OutcomeT.halt kind bodyState,
                Structured.EffectSemantics.For.Eval.body_halt
                  hCond hBodyEval,
                hOuterRel, by trivial⟩
        | regular =>
            obtain ⟨bodyTarget, hTargetOutcome, hBodyStateRel⟩ :=
              ObserverPreservation.OutcomeSimulation.Rel.regular_elim
                hBodyOutcomeRel
            subst bodyTargetOutcome
            change
              TypedCfgCompiler.Shape.SourceFrameFits
                  { condOutput with slots := condOutput.slots.tail }
                bodyState.source.evm.stack.length at hBodyJoin
            have hBodyAt :
                ObserverPreservation.StateRel.At
                  { condOutput with slots := condOutput.slots.tail }
                  bodyState tokens bodyTarget bodyTrace :=
              ObserverPreservation.StateRel.At.ofFits
                hBodyStateRel hBodyJoin
            have hAfterBodyReach :=
              OutcomeSimulation.FirstReaches.tail_of_prefix_jump
                hTailReach hBodyReach hBodyLe
            obtain
                ⟨postPrefixFuel, postTargetOutcome, postTrace,
                  hPostLe, hPostReach⟩ :=
              OutcomeSimulation.FirstReaches.exists_of_run
                hAfterBodyReach.run
                (jumpOr_of_accept hAfterBodyReach.boundary)
            have hPostPositive : 0 < postPrefixFuel :=
              OutcomeSimulation.FirstReaches.fuel_pos_of_entry_not_accepted
                hPostReach (hPostEntryNotAccepted bodyTarget)
            cases postPrefixFuel with
            | zero =>
                omega
            | succ postPrefixFuel =>
                obtain
                    ⟨postSourceFuel, postOutcome,
                      hPostEval, hPostOutcomeRel, hPostArtifact⟩ :=
                  hPostAdequate
                    (fun targetOutcome hBoundary =>
                      postBoundary (loopLabel := loopLabel)
                        hAccept hBoundary)
                    hBodyAt hPostReach
                have hPostJoin :
                    OutcomeSimulation.JoinArtifact
                      { ctx with
                        breakLabel? := none
                        breakShape? := none
                        continueLabel? := none
                        continueShape? := none }
                      loopInput postOutcome :=
                  OutcomeSimulation.OutcomeArtifact.toJoin_of_requireFallthrough
                    hPostRequire hPostArtifact
                rcases postOutcome with ⟨postState, postMode⟩
                cases postMode with
                | regular =>
                    obtain
                        ⟨postTarget, hPostTargetOutcome,
                          hPostStateRel⟩ :=
                      ObserverPreservation.OutcomeSimulation.Rel.regular_elim
                        hPostOutcomeRel
                    subst postTargetOutcome
                    change
                      TypedCfgCompiler.Shape.SourceFrameFits loopInput
                        postState.source.evm.stack.length at hPostJoin
                    have hPostAt :
                        ObserverPreservation.StateRel.At
                          loopInput postState tokens postTarget postTrace :=
                      ObserverPreservation.StateRel.At.ofFits
                        hPostStateRel hPostJoin
                    have hAfterPostReach :=
                      OutcomeSimulation.FirstReaches.tail_of_prefix_jump
                        hAfterBodyReach hPostReach hPostLe
                    have hLoopPositive :
                        0 <
                          (targetFuel - (bodyPrefixFuel + 1)) -
                            (postPrefixFuel + 1) :=
                      OutcomeSimulation.FirstReaches.fuel_pos_of_entry_not_accepted
                        hAfterPostReach (hLoopEntryNotAccepted postTarget)
                    cases hResidual :
                        (targetFuel - (bodyPrefixFuel + 1)) -
                          (postPrefixFuel + 1) with
                    | zero =>
                        omega
                    | succ loopTargetFuel =>
                        have hDecrease :
                            loopTargetFuel < targetFuel := by
                          omega
                        obtain
                            ⟨loopSourceFuel, sourceOutcome,
                              hLoopEval, hLoopOutcomeRel, hLoopArtifact⟩ :=
                          hRecurse hDecrease hPostAt
                            (by simpa [hResidual] using hAfterPostReach)
                        let sourceFuel :=
                          Nat.max bodySourceFuel
                            (Nat.max postSourceFuel loopSourceFuel)
                        exact
                          ⟨sourceFuel + 1, sourceOutcome,
                            Structured.EffectSemantics.For.Eval.regular_post_regular
                              hCond
                              (Structured.EffectSemantics.Block.Eval.mono
                                hBodyEval (by
                                  simp [sourceFuel]))
                              (Structured.EffectSemantics.Block.Eval.mono
                                hPostEval (by
                                  simp [sourceFuel]))
                              (Structured.EffectSemantics.For.Eval.mono
                                hLoopEval (by
                                  simp [sourceFuel])),
                            hLoopOutcomeRel, hLoopArtifact⟩
                | leave =>
                    have hOuterRel :
                        ObserverPreservation.OutcomeSimulation.Rel
                          outer tokens
                          (Structured.OutcomeT.leave postState)
                          postTargetOutcome postTrace := by
                      exact postLeaveRel hPostOutcomeRel
                    obtain ⟨_hFuelEq, hOutcomeEq, hTraceEq⟩ :=
                      OutcomeSimulation.FirstReaches.outcome_eq_of_prefix_accepted
                        hAfterBodyReach hPostReach hPostLe
                        (hAccept _
                          (OutcomeSimulation.targetBoundary_of_rel hOuterRel))
                    subst targetOutcome
                    subst traceFinal
                    let sourceFuel :=
                      Nat.max bodySourceFuel postSourceFuel
                    exact
                      ⟨sourceFuel + 1,
                        Structured.OutcomeT.leave postState,
                        Structured.EffectSemantics.For.Eval.regular_post_leave
                          hCond
                          (Structured.EffectSemantics.Block.Eval.mono
                            hBodyEval (by simp [sourceFuel]))
                          (Structured.EffectSemantics.Block.Eval.mono
                            hPostEval (by simp [sourceFuel])),
                        hOuterRel,
                        by
                          simpa [OutcomeSimulation.JoinArtifact] using
                            hPostJoin⟩
                | halt kind =>
                    have hOuterRel :
                        ObserverPreservation.OutcomeSimulation.Rel
                          outer tokens
                          (Structured.OutcomeT.halt kind postState)
                          postTargetOutcome postTrace := by
                      exact postHaltRel hPostOutcomeRel
                    obtain ⟨_hFuelEq, hOutcomeEq, hTraceEq⟩ :=
                      OutcomeSimulation.FirstReaches.outcome_eq_of_prefix_accepted
                        hAfterBodyReach hPostReach hPostLe
                        (hAccept _
                          (OutcomeSimulation.targetBoundary_of_rel hOuterRel))
                    subst targetOutcome
                    subst traceFinal
                    let sourceFuel :=
                      Nat.max bodySourceFuel postSourceFuel
                    exact
                      ⟨sourceFuel + 1,
                        Structured.OutcomeT.halt kind postState,
                        Structured.EffectSemantics.For.Eval.regular_post_halt
                          hCond
                          (Structured.EffectSemantics.Block.Eval.mono
                            hBodyEval (by simp [sourceFuel]))
                          (Structured.EffectSemantics.Block.Eval.mono
                            hPostEval (by simp [sourceFuel])),
                        hOuterRel, by trivial⟩
                | brk =>
                    change
                      ∃ output,
                        (none : Option TypedCfg.Shape) = some output ∧
                          TypedCfgCompiler.Shape.SourceFrameFits output
                            postState.source.evm.stack.length at hPostJoin
                    obtain ⟨output, hNone, _hBound⟩ := hPostJoin
                    cases hNone
                | cont =>
                    change
                      ∃ output,
                        (none : Option TypedCfg.Shape) = some output ∧
                          TypedCfgCompiler.Shape.SourceFrameFits output
                            postState.source.evm.stack.length at hPostJoin
                    obtain ⟨output, hNone, _hBound⟩ := hPostJoin
                    cases hNone
        | cont =>
            obtain
                ⟨label, bodyTarget, hLabel,
                  hTargetOutcome, hBodyStateRel⟩ :=
              ObserverPreservation.OutcomeSimulation.Rel.cont_elim
                hBodyOutcomeRel
            have hLabelEq : label = postLabel := by
              change some postLabel = some label at hLabel
              exact (Option.some.inj hLabel).symm
            subst label
            subst bodyTargetOutcome
            change
              ∃ output,
                (some { condOutput with
                    slots := condOutput.slots.tail } :
                  Option TypedCfg.Shape) = some output ∧
                TypedCfgCompiler.Shape.SourceFrameFits output
                  bodyState.source.evm.stack.length
              at hBodyJoin
            obtain ⟨output, hOutput, hBodyFits⟩ := hBodyJoin
            have hOutputEq :
                output =
                  { condOutput with slots := condOutput.slots.tail } :=
              Option.some.inj hOutput.symm
            subst output
            have hBodyAt :
                ObserverPreservation.StateRel.At
                  { condOutput with slots := condOutput.slots.tail }
                  bodyState tokens bodyTarget bodyTrace :=
              ObserverPreservation.StateRel.At.ofFits
                hBodyStateRel hBodyFits
            have hAfterBodyReach :=
              OutcomeSimulation.FirstReaches.tail_of_prefix_jump
                hTailReach hBodyReach hBodyLe
            obtain
                ⟨postPrefixFuel, postTargetOutcome, postTrace,
                  hPostLe, hPostReach⟩ :=
              OutcomeSimulation.FirstReaches.exists_of_run
                hAfterBodyReach.run
                (jumpOr_of_accept hAfterBodyReach.boundary)
            have hPostPositive : 0 < postPrefixFuel :=
              OutcomeSimulation.FirstReaches.fuel_pos_of_entry_not_accepted
                hPostReach (hPostEntryNotAccepted bodyTarget)
            cases postPrefixFuel with
            | zero =>
                omega
            | succ postPrefixFuel =>
                obtain
                    ⟨postSourceFuel, postOutcome,
                      hPostEval, hPostOutcomeRel, hPostArtifact⟩ :=
                  hPostAdequate
                    (fun targetOutcome hBoundary =>
                      postBoundary (loopLabel := loopLabel)
                        hAccept hBoundary)
                    hBodyAt hPostReach
                have hPostJoin :
                    OutcomeSimulation.JoinArtifact
                      { ctx with
                        breakLabel? := none
                        breakShape? := none
                        continueLabel? := none
                        continueShape? := none }
                      loopInput postOutcome :=
                  OutcomeSimulation.OutcomeArtifact.toJoin_of_requireFallthrough
                    hPostRequire hPostArtifact
                rcases postOutcome with ⟨postState, postMode⟩
                cases postMode with
                | regular =>
                    obtain
                        ⟨postTarget, hPostTargetOutcome,
                          hPostStateRel⟩ :=
                      ObserverPreservation.OutcomeSimulation.Rel.regular_elim
                        hPostOutcomeRel
                    subst postTargetOutcome
                    change
                      TypedCfgCompiler.Shape.SourceFrameFits loopInput
                        postState.source.evm.stack.length at hPostJoin
                    have hPostAt :
                        ObserverPreservation.StateRel.At
                          loopInput postState tokens postTarget postTrace :=
                      ObserverPreservation.StateRel.At.ofFits
                        hPostStateRel hPostJoin
                    have hAfterPostReach :=
                      OutcomeSimulation.FirstReaches.tail_of_prefix_jump
                        hAfterBodyReach hPostReach hPostLe
                    have hLoopPositive :
                        0 <
                          (targetFuel - (bodyPrefixFuel + 1)) -
                            (postPrefixFuel + 1) :=
                      OutcomeSimulation.FirstReaches.fuel_pos_of_entry_not_accepted
                        hAfterPostReach (hLoopEntryNotAccepted postTarget)
                    cases hResidual :
                        (targetFuel - (bodyPrefixFuel + 1)) -
                          (postPrefixFuel + 1) with
                    | zero =>
                        omega
                    | succ loopTargetFuel =>
                        have hDecrease :
                            loopTargetFuel < targetFuel := by
                          omega
                        obtain
                            ⟨loopSourceFuel, sourceOutcome,
                              hLoopEval, hLoopOutcomeRel, hLoopArtifact⟩ :=
                          hRecurse hDecrease hPostAt
                            (by simpa [hResidual] using hAfterPostReach)
                        let sourceFuel :=
                          Nat.max bodySourceFuel
                            (Nat.max postSourceFuel loopSourceFuel)
                        exact
                          ⟨sourceFuel + 1, sourceOutcome,
                            Structured.EffectSemantics.For.Eval.cont_post_regular
                              hCond
                              (Structured.EffectSemantics.Block.Eval.mono
                                hBodyEval (by
                                  simp [sourceFuel]))
                              (Structured.EffectSemantics.Block.Eval.mono
                                hPostEval (by
                                  simp [sourceFuel]))
                              (Structured.EffectSemantics.For.Eval.mono
                                hLoopEval (by
                                  simp [sourceFuel])),
                            hLoopOutcomeRel, hLoopArtifact⟩
                | leave =>
                    have hOuterRel :
                        ObserverPreservation.OutcomeSimulation.Rel
                          outer tokens
                          (Structured.OutcomeT.leave postState)
                          postTargetOutcome postTrace := by
                      exact postLeaveRel hPostOutcomeRel
                    obtain ⟨_hFuelEq, hOutcomeEq, hTraceEq⟩ :=
                      OutcomeSimulation.FirstReaches.outcome_eq_of_prefix_accepted
                        hAfterBodyReach hPostReach hPostLe
                        (hAccept _
                          (OutcomeSimulation.targetBoundary_of_rel hOuterRel))
                    subst targetOutcome
                    subst traceFinal
                    let sourceFuel :=
                      Nat.max bodySourceFuel postSourceFuel
                    exact
                      ⟨sourceFuel + 1,
                        Structured.OutcomeT.leave postState,
                        Structured.EffectSemantics.For.Eval.cont_post_leave
                          hCond
                          (Structured.EffectSemantics.Block.Eval.mono
                            hBodyEval (by simp [sourceFuel]))
                          (Structured.EffectSemantics.Block.Eval.mono
                            hPostEval (by simp [sourceFuel])),
                        hOuterRel,
                        by
                          simpa [OutcomeSimulation.JoinArtifact] using
                            hPostJoin⟩
                | halt kind =>
                    have hOuterRel :
                        ObserverPreservation.OutcomeSimulation.Rel
                          outer tokens
                          (Structured.OutcomeT.halt kind postState)
                          postTargetOutcome postTrace := by
                      exact postHaltRel hPostOutcomeRel
                    obtain ⟨_hFuelEq, hOutcomeEq, hTraceEq⟩ :=
                      OutcomeSimulation.FirstReaches.outcome_eq_of_prefix_accepted
                        hAfterBodyReach hPostReach hPostLe
                        (hAccept _
                          (OutcomeSimulation.targetBoundary_of_rel hOuterRel))
                    subst targetOutcome
                    subst traceFinal
                    let sourceFuel :=
                      Nat.max bodySourceFuel postSourceFuel
                    exact
                      ⟨sourceFuel + 1,
                        Structured.OutcomeT.halt kind postState,
                        Structured.EffectSemantics.For.Eval.cont_post_halt
                          hCond
                          (Structured.EffectSemantics.Block.Eval.mono
                            hBodyEval (by simp [sourceFuel]))
                          (Structured.EffectSemantics.Block.Eval.mono
                            hPostEval (by simp [sourceFuel])),
                        hOuterRel, by trivial⟩
                | brk =>
                    change
                      ∃ output,
                        (none : Option TypedCfg.Shape) = some output ∧
                          TypedCfgCompiler.Shape.SourceFrameFits output
                            postState.source.evm.stack.length at hPostJoin
                    obtain ⟨output, hNone, _hBound⟩ := hPostJoin
                    cases hNone
                | cont =>
                    change
                      ∃ output,
                        (none : Option TypedCfg.Shape) = some output ∧
                          TypedCfgCompiler.Shape.SourceFrameFits output
                            postState.source.evm.stack.length at hPostJoin
                    obtain ⟨output, hNone, _hBound⟩ := hPostJoin
                    cases hNone

private theorem outcome_for_of_firstReaches
    {transcript : Trace} {targetFuel : Nat}
    {program : Structured.Program}
    {cond : Structured.Code} {post body : Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {cfg : TypedCfg.Program}
    {loopLabel bodyLabel postLabel endLabel : Assembly.Label}
    {loopInput condOutput : TypedCfg.Shape}
    {condition : TypedCfg.Slot}
    {result bodyResult postResult : TypedCfgCompiler.Result}
    {outer : OutcomeSimulation.Continuations}
    {accept : TypedCfg.Outcome → Prop}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState}
    {trace traceFinal : Trace} {targetOutcome : TypedCfg.Outcome}
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hLoopMem :
      { label := loopLabel
        input := loopInput
        body := TypedCfgCompiler.Code.toCfg cond
        output := condOutput
        term := .jumpi bodyLabel endLabel } ∈ result.blocks)
    (hType :
      TypedCfgCompiler.Code.type? cond loopInput = some condOutput)
    (hSource :
      TypedCfgCompiler.Shape.requireSourceWords? 1 condOutput =
        some ())
    (hHead : condOutput.slots.head? = some condition)
    (hBodyRequire :
      bodyResult.requireFallthrough?
          { condOutput with slots := condOutput.slots.tail } =
        some ())
    (hPostRequire :
      postResult.requireFallthrough? loopInput = some ())
    (hOuterRegular : outer.regular = endLabel)
    (hAccept :
      ∀ acceptedOutcome,
        OutcomeSimulation.TargetBoundary outer acceptedOutcome →
          accept acceptedOutcome)
    (hBodyEntryNotAccepted :
      ∀ targetState,
        ¬ OutcomeSimulation.JumpOr postLabel accept
          (.jump bodyLabel targetState))
    (hPostEntryNotAccepted :
      ∀ targetState,
        ¬ OutcomeSimulation.JumpOr loopLabel accept
          (.jump postLabel targetState))
    (hLoopEntryNotAccepted :
      ∀ targetState, ¬ accept (.jump loopLabel targetState))
    (hRel :
      ObserverPreservation.StateRel.At
        loopInput source tokens target trace)
    (hReach :
      OutcomeSimulation.FirstReaches cfg accept (targetFuel + 1)
        loopLabel target trace targetOutcome traceFinal)
    (hBodyAdequate :
      ∀ {bodySource : ObserverSemantics.State transcript},
        OutcomeSimulation.AdequateWithin
          (fun sourceFuel sourceOutcome =>
            ObserverSemantics.Block.Eval
              program sourceFuel body bodySource sourceOutcome)
          bodyResult
          { ctx with
            breakLabel? := some endLabel
            breakShape? :=
              some { condOutput with slots := condOutput.slots.tail }
            continueLabel? := some postLabel
            continueShape? :=
              some { condOutput with slots := condOutput.slots.tail } }
          cfg (bodyContinuations endLabel postLabel outer)
          (OutcomeSimulation.JumpOr postLabel accept)
          bodyLabel
          { condOutput with slots := condOutput.slots.tail }
          bodySource tokens)
    (hPostAdequate :
      ∀ {postSource : ObserverSemantics.State transcript},
        OutcomeSimulation.AdequateWithin
          (fun sourceFuel sourceOutcome =>
            ObserverSemantics.Block.Eval
              program sourceFuel post postSource sourceOutcome)
          postResult
          { ctx with
            breakLabel? := none
            breakShape? := none
            continueLabel? := none
            continueShape? := none }
          cfg (postContinuations loopLabel outer)
          (OutcomeSimulation.JumpOr loopLabel accept)
          postLabel
          { condOutput with slots := condOutput.slots.tail }
          postSource tokens) :
    ∃ sourceFuel sourceOutcome,
      ObserverSemantics.For.Eval program sourceFuel
          cond post body source sourceOutcome ∧
        ObserverPreservation.OutcomeSimulation.Rel
          outer tokens sourceOutcome targetOutcome traceFinal ∧
        OutcomeSimulation.JoinArtifact ctx
          { condOutput with slots := condOutput.slots.tail }
          sourceOutcome := by
  induction targetFuel using Nat.strong_induction_on
      generalizing source target trace with
  | h targetFuel ih =>
      exact
        outcome_for_step_of_firstReaches
          hBlocks hLoopMem hType hSource hHead hBodyRequire hPostRequire
          hOuterRegular hAccept hBodyEntryNotAccepted
          hPostEntryNotAccepted hLoopEntryNotAccepted
          hRel hReach hBodyAdequate hPostAdequate
          (by
            intro smallerFuel loopSource loopTarget loopTrace
              hSmaller hLoopRel hLoopReach
            exact
              ih smallerFuel hSmaller
                hLoopRel hLoopReach)

/--
Compiler-facing backward adequacy for a checked Structured `for` statement.
All generated shapes and labels are recovered from the existing compiler
result; recursive blocks cross only the shared adjacent block interface.
-/
private theorem adequateWithin_for_of_compileStmtFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {program : Structured.Program}
    {init : Structured.Block} {cond : Structured.Code}
    {post body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.for_ init cond post body) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hInitEntryNotAccepted :
      ∀ {accept : TypedCfg.Outcome → Prop} targetState,
        ¬ OutcomeSimulation.JumpOr (LabelSupply.label supply 0) accept
          (.jump entry targetState))
    (hGeneratedEntryNotAccepted :
      ∀ {accept : TypedCfg.Outcome → Prop}
        generatedOffset targetState,
        ¬ accept
          (.jump (LabelSupply.label supply generatedOffset) targetState))
    (hInitAdequate :
      ∀ {initResult : TypedCfgCompiler.Result}
        {loopInput : TypedCfg.Shape},
        TypedCfgCompiler.compileBlockFuel? compilerFuel init
            { ctx with
              breakLabel? := none
              breakShape? := none
              continueLabel? := none
              continueShape? := none }
            (supply + 1) entry input (LabelSupply.label supply 0) =
          some initResult →
        initResult.fallthrough? = some loopInput →
        TypedCfgPreservation.BlocksInProgram initResult cfg →
        ∀ {initSource : ObserverSemantics.State transcript}
          {outer : OutcomeSimulation.Continuations}
          {accept : TypedCfg.Outcome → Prop},
          OutcomeSimulation.AdequateWithin
            (fun sourceFuel sourceOutcome =>
              ObserverSemantics.Block.Eval
                program sourceFuel init initSource sourceOutcome)
            initResult
            { ctx with
              breakLabel? := none
              breakShape? := none
              continueLabel? := none
              continueShape? := none }
            cfg
            (postContinuations (LabelSupply.label supply 0) outer)
            (OutcomeSimulation.JumpOr
              (LabelSupply.label supply 0) accept)
            entry input initSource tokens)
    (hBodyAdequate :
      ∀ {initResult bodyResult : TypedCfgCompiler.Result}
        {condOutput : TypedCfg.Shape},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body
            { ctx with
              breakLabel? := some regular
              breakShape? :=
                some { condOutput with slots := condOutput.slots.tail }
              continueLabel? := some (LabelSupply.label supply 2)
              continueShape? :=
                some { condOutput with slots := condOutput.slots.tail } }
            initResult.next (LabelSupply.label supply 1)
            { condOutput with slots := condOutput.slots.tail }
            (LabelSupply.label supply 2) =
          some bodyResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        ∀ {bodySource : ObserverSemantics.State transcript}
          {outer : OutcomeSimulation.Continuations}
          {accept : TypedCfg.Outcome → Prop},
          OutcomeSimulation.AdequateWithin
            (fun sourceFuel sourceOutcome =>
              ObserverSemantics.Block.Eval
                program sourceFuel body bodySource sourceOutcome)
            bodyResult
            { ctx with
              breakLabel? := some regular
              breakShape? :=
                some { condOutput with slots := condOutput.slots.tail }
              continueLabel? := some (LabelSupply.label supply 2)
              continueShape? :=
                some { condOutput with slots := condOutput.slots.tail } }
            cfg
            (bodyContinuations regular (LabelSupply.label supply 2) outer)
            (OutcomeSimulation.JumpOr
              (LabelSupply.label supply 2) accept)
            (LabelSupply.label supply 1)
            { condOutput with slots := condOutput.slots.tail }
            bodySource tokens)
    (hPostAdequate :
      ∀ {bodyResult postResult : TypedCfgCompiler.Result}
        {condOutput : TypedCfg.Shape},
        TypedCfgCompiler.compileBlockFuel? compilerFuel post
            { ctx with
              breakLabel? := none
              breakShape? := none
              continueLabel? := none
              continueShape? := none }
            bodyResult.next (LabelSupply.label supply 2)
            { condOutput with slots := condOutput.slots.tail }
            (LabelSupply.label supply 0) =
          some postResult →
        TypedCfgPreservation.BlocksInProgram postResult cfg →
        ∀ {postSource : ObserverSemantics.State transcript}
          {outer : OutcomeSimulation.Continuations}
          {accept : TypedCfg.Outcome → Prop},
          OutcomeSimulation.AdequateWithin
            (fun sourceFuel sourceOutcome =>
              ObserverSemantics.Block.Eval
                program sourceFuel post postSource sourceOutcome)
            postResult
            { ctx with
              breakLabel? := none
              breakShape? := none
              continueLabel? := none
              continueShape? := none }
            cfg
            (postContinuations (LabelSupply.label supply 0) outer)
            (OutcomeSimulation.JumpOr
              (LabelSupply.label supply 0) accept)
            (LabelSupply.label supply 2)
            { condOutput with slots := condOutput.slots.tail }
            postSource tokens) :
    OutcomeSimulation.AdequateWithin
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Stmt.Eval program sourceFuel
          (.for_ init cond post body) source sourceOutcome)
      result ctx cfg
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      (OutcomeSimulation.TargetBoundary
        (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
          ctx regular))
      entry input source tokens := by
  intro hAccept targetFuel target trace traceFinal
    targetOutcome hRel hReach
  rcases
      TypedCfgCompilerFacts.Loop.components_of_compileStmtFuel?_for
        hCompile with
    ⟨initResult, loopInput, condOutput, condition,
      bodyResult, postResult, hInitCompile, hInitFallthrough,
      hType, hSource, hHead, hBodyCompile, hBodyRequire,
      hPostCompile, hPostRequire, hResult⟩
  subst result
  let outer :=
    TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
      ctx regular
  have hInitBlocks :
      TypedCfgPreservation.BlocksInProgram initResult cfg := by
    intro block hMem
    apply hBlocks block
    simp [hMem]
  have hBodyBlocks :
      TypedCfgPreservation.BlocksInProgram bodyResult cfg := by
    intro block hMem
    apply hBlocks block
    simp [hMem]
  have hPostBlocks :
      TypedCfgPreservation.BlocksInProgram postResult cfg := by
    intro block hMem
    apply hBlocks block
    simp [hMem]
  have hLoopMem :
      { label := LabelSupply.label supply 0
        input := loopInput
        body := TypedCfgCompiler.Code.toCfg cond
        output := condOutput
        term := .jumpi (LabelSupply.label supply 1) regular } ∈
        initResult.blocks ++
          [{ label := LabelSupply.label supply 0
             input := loopInput
             body := TypedCfgCompiler.Code.toCfg cond
             output := condOutput
             term := .jumpi (LabelSupply.label supply 1) regular }] ++
          bodyResult.blocks ++ postResult.blocks := by
    simp
  obtain
      ⟨initPrefixFuel, initTargetOutcome, initTrace,
        hInitLe, hInitReach⟩ :=
    OutcomeSimulation.FirstReaches.exists_of_run
      hReach.run (jumpOr_of_accept hReach.boundary)
  have hInitPositive : 0 < initPrefixFuel :=
    OutcomeSimulation.FirstReaches.fuel_pos_of_entry_not_accepted
      hInitReach (hInitEntryNotAccepted target)
  cases initPrefixFuel with
  | zero =>
      omega
  | succ initPrefixFuel =>
      obtain
          ⟨initSourceFuel, initOutcome,
            hInitEval, hInitOutcomeRel, hInitArtifact⟩ :=
        hInitAdequate hInitCompile hInitFallthrough hInitBlocks
          (fun targetOutcome hBoundary =>
            postBoundary (loopLabel := LabelSupply.label supply 0)
              hAccept hBoundary)
          hRel hInitReach
      have hInitJoin :
          OutcomeSimulation.JoinArtifact
            { ctx with
              breakLabel? := none
              breakShape? := none
              continueLabel? := none
              continueShape? := none }
            loopInput initOutcome :=
        OutcomeSimulation.OutcomeArtifact.toJoin
          hInitFallthrough hInitArtifact
      rcases initOutcome with ⟨initState, initMode⟩
      cases initMode with
      | regular =>
          obtain ⟨loopTarget, hTargetOutcome, hInitStateRel⟩ :=
            ObserverPreservation.OutcomeSimulation.Rel.regular_elim
              hInitOutcomeRel
          subst initTargetOutcome
          change
            TypedCfgCompiler.Shape.SourceFrameFits loopInput
              initState.source.evm.stack.length
            at hInitJoin
          have hLoopAt :
              ObserverPreservation.StateRel.At
                loopInput initState tokens loopTarget initTrace :=
            ObserverPreservation.StateRel.At.ofFits
              hInitStateRel hInitJoin
          have hAfterInitReach :=
            OutcomeSimulation.FirstReaches.tail_of_prefix_jump
              hReach hInitReach hInitLe
          have hLoopPositive :
              0 < targetFuel + 1 - (initPrefixFuel + 1) :=
            OutcomeSimulation.FirstReaches.fuel_pos_of_entry_not_accepted
              hAfterInitReach
              (hGeneratedEntryNotAccepted 0 loopTarget)
          cases hResidual :
              targetFuel + 1 - (initPrefixFuel + 1) with
          | zero =>
              omega
          | succ loopTargetFuel =>
              obtain
                  ⟨loopSourceFuel, sourceOutcome,
                    hLoopEval, hLoopOutcomeRel, hLoopJoin⟩ :=
                outcome_for_of_firstReaches
                  hBlocks hLoopMem hType hSource hHead hBodyRequire
                  hPostRequire
                  rfl hAccept
                  (by
                    intro targetState
                    simp [OutcomeSimulation.JumpOr]
                    exact
                      ⟨by simp [LabelSupply.label],
                        hGeneratedEntryNotAccepted 1 targetState⟩)
                  (by
                    intro targetState
                    simp [OutcomeSimulation.JumpOr]
                    exact
                      ⟨by simp [LabelSupply.label],
                        hGeneratedEntryNotAccepted 2 targetState⟩)
                  (hGeneratedEntryNotAccepted 0)
                  hLoopAt
                  (by simpa [hResidual] using hAfterInitReach)
                  (hBodyAdequate hBodyCompile hBodyBlocks)
                  (hPostAdequate hPostCompile hPostBlocks)
              let sourceFuel :=
                Nat.max initSourceFuel loopSourceFuel
              exact
                ⟨sourceFuel + 1, sourceOutcome,
                  Structured.EffectSemantics.Stmt.Eval.for_init_regular
                    (Structured.EffectSemantics.Block.Eval.mono
                      hInitEval (by simp [sourceFuel]))
                    (Structured.EffectSemantics.For.Eval.mono
                      hLoopEval (by simp [sourceFuel])),
                  hLoopOutcomeRel,
                  OutcomeSimulation.OutcomeArtifact.ofJoin
                    rfl hLoopJoin⟩
      | leave =>
          have hOuterRel :
              ObserverPreservation.OutcomeSimulation.Rel
                outer tokens (Structured.OutcomeT.leave initState)
                initTargetOutcome initTrace :=
            postLeaveRel hInitOutcomeRel
          obtain ⟨_hFuelEq, hOutcomeEq, hTraceEq⟩ :=
            OutcomeSimulation.FirstReaches.outcome_eq_of_prefix_accepted
              hReach hInitReach hInitLe
              (hAccept _
                (OutcomeSimulation.targetBoundary_of_rel hOuterRel))
          subst targetOutcome
          subst traceFinal
          exact
            ⟨initSourceFuel + 1,
              Structured.OutcomeT.leave initState,
              Structured.EffectSemantics.Stmt.Eval.for_init_leave
                hInitEval,
              hOuterRel,
              by
                simpa [OutcomeSimulation.OutcomeArtifact,
                  OutcomeSimulation.JoinArtifact] using hInitJoin⟩
      | halt kind =>
          have hOuterRel :
              ObserverPreservation.OutcomeSimulation.Rel
                outer tokens (Structured.OutcomeT.halt kind initState)
                initTargetOutcome initTrace :=
            postHaltRel hInitOutcomeRel
          obtain ⟨_hFuelEq, hOutcomeEq, hTraceEq⟩ :=
            OutcomeSimulation.FirstReaches.outcome_eq_of_prefix_accepted
              hReach hInitReach hInitLe
              (hAccept _
                (OutcomeSimulation.targetBoundary_of_rel hOuterRel))
          subst targetOutcome
          subst traceFinal
          exact
            ⟨initSourceFuel + 1,
              Structured.OutcomeT.halt kind initState,
              Structured.EffectSemantics.Stmt.Eval.for_init_halt
                hInitEval,
              hOuterRel, by trivial⟩
      | brk =>
          change
            ∃ output,
              (none : Option TypedCfg.Shape) = some output ∧
                TypedCfgCompiler.Shape.SourceFrameFits output
                  initState.source.evm.stack.length
            at hInitJoin
          obtain ⟨output, hNone, _hBound⟩ := hInitJoin
          cases hNone
      | cont =>
          change
            ∃ output,
              (none : Option TypedCfg.Shape) = some output ∧
                TypedCfgCompiler.Shape.SourceFrameFits output
                  initState.source.evm.stack.length
            at hInitJoin
          obtain ⟨output, hNone, _hBound⟩ := hInitJoin
          cases hNone

end Loop
end ObserverAdequacy
end Structured
end EvmCompiler
