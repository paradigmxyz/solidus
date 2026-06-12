import EvmCompiler.Structured.ObserverAdequacy

namespace EvmCompiler
namespace Structured
namespace ObserverAdequacy
namespace Loop

abbrev bodyContinuations :=
  TypedCfgPreservation.OutcomeSimulation.Loop.bodyContinuations

abbrev postContinuations :=
  TypedCfgPreservation.OutcomeSimulation.Loop.postContinuations

private theorem bodyActivationBoundary
    {transcript : Trace} {program : Structured.Program}
    {cond : Structured.Code} {post body : Structured.Block}
    {endLabel postLabel : Assembly.Label}
    {outer : OutcomeSimulation.Continuations}
    {accept : TypedCfg.Outcome → Prop}
    {bodyShape : TypedCfg.Shape}
    {bodyResult : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {loopSource initial : ObserverSemantics.State transcript}
    {tokens : List Word}
    {sourceFuel : Nat}
    {sourceOutcome : ObserverSemantics.Outcome}
    {targetOutcome : TypedCfg.Outcome} {trace : Trace}
    (hClose :
      ∀ forFuel forOutcome forTarget forTrace,
        ObserverSemantics.For.Eval program forFuel
            cond post body loopSource forOutcome →
          ObserverPreservation.OutcomeSimulation.Rel
            outer tokens forOutcome forTarget forTrace →
          OutcomeSimulation.JoinArtifact ctx bodyShape forOutcome →
          accept forTarget)
    (hCond :
      ObserverSemantics.Code.runCondition cond loopSource =
        .ok (initial, true))
    (hOuterRegular : outer.regular = endLabel)
    (hRequire :
      bodyResult.requireFallthrough? bodyShape = some ())
    (hEval :
      ObserverSemantics.Block.Eval
        program sourceFuel body initial sourceOutcome)
    (hRel :
      ObserverPreservation.OutcomeSimulation.Rel
        (bodyContinuations endLabel postLabel outer)
        tokens sourceOutcome targetOutcome trace)
    (hArtifact :
      OutcomeSimulation.OutcomeArtifact
        bodyResult
        { ctx with
          breakLabel? := some endLabel
          breakShape? := some bodyShape
          continueLabel? := some postLabel
          continueShape? := some bodyShape }
        sourceOutcome) :
    OutcomeSimulation.JumpAt initial tokens postLabel bodyShape
      accept targetOutcome := by
  have hJoin :
      OutcomeSimulation.JoinArtifact
        { ctx with
          breakLabel? := some endLabel
          breakShape? := some bodyShape
          continueLabel? := some postLabel
          continueShape? := some bodyShape }
        bodyShape sourceOutcome :=
    OutcomeSimulation.OutcomeArtifact.toJoin_of_requireFallthrough
      hRequire hArtifact
  rcases sourceOutcome with ⟨source, mode⟩
  cases mode with
  | regular =>
      obtain ⟨target, rfl, hStateRel⟩ :=
        ObserverPreservation.OutcomeSimulation.Rel.regular_elim hRel
      exact
        OutcomeSimulation.JumpAt.of_rel
          (ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
            hEval (by simp [ObserverSemantics.Outcome.Nonhalting]))
          hStateRel hJoin
  | brk =>
      obtain ⟨label, target, hLabel, rfl, _hStateRel⟩ :=
        ObserverPreservation.OutcomeSimulation.Rel.brk_elim hRel
      apply OutcomeSimulation.JumpAt.of_accept
      have hLabelEq : label = endLabel := by
        change some endLabel = some label at hLabel
        exact (Option.some.inj hLabel).symm
      subst label
      have hOuterRel :
          ObserverPreservation.OutcomeSimulation.Rel
            outer tokens (Structured.OutcomeT.regular source)
            (.jump endLabel target) trace := by
        exact
          ObserverPreservation.OutcomeSimulation.Rel.regular_iff.mpr
            ⟨hOuterRegular.symm, _hStateRel⟩
      have hOuterJoin :
          OutcomeSimulation.JoinArtifact ctx bodyShape
            (Structured.OutcomeT.regular source) := by
        change
          TypedCfgCompiler.Shape.SourceFrameFits bodyShape
            source.source.evm.stack.length
        change
          ∃ output,
            some bodyShape = some output ∧
              TypedCfgCompiler.Shape.SourceFrameFits output
                source.source.evm.stack.length at hJoin
        obtain ⟨output, hOutput, hFits⟩ := hJoin
        have hOutputEq : output = bodyShape :=
          Option.some.inj hOutput.symm
        simpa [hOutputEq] using hFits
      exact
        hClose (sourceFuel + 1) (Structured.OutcomeT.regular source)
          (.jump endLabel target) trace
          (Structured.EffectSemantics.For.Eval.body_brk hCond hEval)
          hOuterRel hOuterJoin
  | cont =>
      obtain ⟨label, target, hLabel, rfl, hStateRel⟩ :=
        ObserverPreservation.OutcomeSimulation.Rel.cont_elim hRel
      have hLabelEq : label = postLabel := by
        change some postLabel = some label at hLabel
        exact (Option.some.inj hLabel).symm
      subst label
      have hFits :
          TypedCfgCompiler.Shape.SourceFrameFits bodyShape
            source.source.evm.stack.length := by
        simpa [OutcomeSimulation.JoinArtifact] using hJoin
      exact
        OutcomeSimulation.JumpAt.of_rel
          (ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
            hEval (by simp [ObserverSemantics.Outcome.Nonhalting]))
          hStateRel hFits
  | leave =>
      apply OutcomeSimulation.JumpAt.of_accept
      have hOuterRel :
          ObserverPreservation.OutcomeSimulation.Rel
            outer tokens (Structured.OutcomeT.leave source)
            targetOutcome trace := by
        cases targetOutcome <;>
          simpa [
            ObserverPreservation.OutcomeSimulation.Rel,
            TypedCfgPreservation.OutcomeSimulation.Loop.bodyContinuations] using
            hRel
      exact
        hClose (sourceFuel + 1) (Structured.OutcomeT.leave source)
          targetOutcome trace
          (Structured.EffectSemantics.For.Eval.body_leave hCond hEval)
          hOuterRel
          (by simpa [OutcomeSimulation.JoinArtifact] using hJoin)
  | halt kind =>
      apply OutcomeSimulation.JumpAt.of_accept
      have hOuterRel :
          ObserverPreservation.OutcomeSimulation.Rel
            outer tokens (Structured.OutcomeT.halt kind source)
            targetOutcome trace := by
        cases targetOutcome <;>
          simpa [
            ObserverPreservation.OutcomeSimulation.Rel,
            TypedCfgPreservation.OutcomeSimulation.Loop.bodyContinuations] using
            hRel
      exact
        hClose (sourceFuel + 1) (Structured.OutcomeT.halt kind source)
          targetOutcome trace
          (Structured.EffectSemantics.For.Eval.body_halt hCond hEval)
          hOuterRel (by trivial)

private theorem postActivationBoundary
    {transcript : Trace} {program : Structured.Program}
    {post : Structured.Block} {loopLabel : Assembly.Label}
    {outer : OutcomeSimulation.Continuations}
    {accept : TypedCfg.Outcome → Prop}
    {loopShape : TypedCfg.Shape}
    {postResult : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {initial : ObserverSemantics.State transcript}
    {tokens : List Word}
    {sourceFuel : Nat}
    {sourceOutcome : ObserverSemantics.Outcome}
    {targetOutcome : TypedCfg.Outcome} {trace : Trace}
    (hLeave :
      ∀ {postFuel : Nat}
        {postState : ObserverSemantics.State transcript}
        {postTarget : TypedCfg.Outcome} {postTrace : Trace},
        ObserverSemantics.Block.Eval program postFuel post initial
            (Structured.OutcomeT.leave postState) →
          ObserverPreservation.OutcomeSimulation.Rel
            (postContinuations loopLabel outer)
            tokens (Structured.OutcomeT.leave postState)
            postTarget postTrace →
          OutcomeSimulation.JoinArtifact
            { ctx with
              breakLabel? := none
              breakShape? := none
              continueLabel? := none
              continueShape? := none }
            loopShape (Structured.OutcomeT.leave postState) →
          accept postTarget)
    (hHalt :
      ∀ {postFuel : Nat}
        {postState : ObserverSemantics.State transcript}
        {kind : Assembly.HaltKind}
        {postTarget : TypedCfg.Outcome} {postTrace : Trace},
        ObserverSemantics.Block.Eval program postFuel post initial
            (Structured.OutcomeT.halt kind postState) →
          ObserverPreservation.OutcomeSimulation.Rel
            (postContinuations loopLabel outer)
            tokens (Structured.OutcomeT.halt kind postState)
            postTarget postTrace →
          OutcomeSimulation.JoinArtifact
            { ctx with
              breakLabel? := none
              breakShape? := none
              continueLabel? := none
              continueShape? := none }
            loopShape (Structured.OutcomeT.halt kind postState) →
          accept postTarget)
    (hRequire :
      postResult.requireFallthrough? loopShape = some ())
    (hEval :
      ObserverSemantics.Block.Eval
        program sourceFuel post initial sourceOutcome)
    (hRel :
      ObserverPreservation.OutcomeSimulation.Rel
        (postContinuations loopLabel outer)
        tokens sourceOutcome targetOutcome trace)
    (hArtifact :
      OutcomeSimulation.OutcomeArtifact
        postResult
        { ctx with
          breakLabel? := none
          breakShape? := none
          continueLabel? := none
          continueShape? := none }
        sourceOutcome) :
    OutcomeSimulation.JumpAt initial tokens loopLabel loopShape
      accept targetOutcome := by
  have hJoin :
      OutcomeSimulation.JoinArtifact
        { ctx with
          breakLabel? := none
          breakShape? := none
          continueLabel? := none
          continueShape? := none }
        loopShape sourceOutcome :=
    OutcomeSimulation.OutcomeArtifact.toJoin_of_requireFallthrough
      hRequire hArtifact
  rcases sourceOutcome with ⟨source, mode⟩
  cases mode with
  | regular =>
      obtain ⟨target, rfl, hStateRel⟩ :=
        ObserverPreservation.OutcomeSimulation.Rel.regular_elim hRel
      exact
        OutcomeSimulation.JumpAt.of_rel
          (ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
            hEval (by simp [ObserverSemantics.Outcome.Nonhalting]))
          hStateRel hJoin
  | brk =>
      change
        ∃ output,
          (none : Option TypedCfg.Shape) = some output ∧
            TypedCfgCompiler.Shape.SourceFrameFits output
              source.source.evm.stack.length at hJoin
      obtain ⟨output, hNone, _hFits⟩ := hJoin
      cases hNone
  | cont =>
      change
        ∃ output,
          (none : Option TypedCfg.Shape) = some output ∧
            TypedCfgCompiler.Shape.SourceFrameFits output
              source.source.evm.stack.length at hJoin
      obtain ⟨output, hNone, _hFits⟩ := hJoin
      cases hNone
  | leave =>
      apply OutcomeSimulation.JumpAt.of_accept
      exact hLeave hEval hRel hJoin
  | halt kind =>
      apply OutcomeSimulation.JumpAt.of_accept
      exact hHalt hEval hRel hJoin

private theorem initActivationBoundary
    {transcript : Trace} {program : Structured.Program}
    {init post body : Structured.Block} {cond : Structured.Code}
    {loopLabel regular : Assembly.Label}
    {accept : TypedCfg.Outcome → Prop}
    {loopShape : TypedCfg.Shape}
    {result initResult : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {initial : ObserverSemantics.State transcript}
    {tokens : List Word}
    {sourceFuel : Nat}
    {sourceOutcome : ObserverSemantics.Outcome}
    {targetOutcome : TypedCfg.Outcome} {trace : Trace}
    (hAccept :
      ∀ parentFuel parentOutcome parentTarget parentTrace,
        ObserverSemantics.Stmt.Eval program parentFuel
            (.for_ init cond post body) initial parentOutcome →
          ObserverPreservation.OutcomeSimulation.Rel
            (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
              ctx regular)
            tokens parentOutcome parentTarget parentTrace →
          OutcomeSimulation.OutcomeArtifact result ctx parentOutcome →
          accept parentTarget)
    (hFallthrough :
      initResult.fallthrough? = some loopShape)
    (hEval :
      ObserverSemantics.Block.Eval
        program sourceFuel init initial sourceOutcome)
    (hRel :
      ObserverPreservation.OutcomeSimulation.Rel
        (postContinuations loopLabel
          (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
            ctx regular))
        tokens sourceOutcome targetOutcome trace)
    (hArtifact :
      OutcomeSimulation.OutcomeArtifact
        initResult
        { ctx with
          breakLabel? := none
          breakShape? := none
          continueLabel? := none
          continueShape? := none }
        sourceOutcome) :
    OutcomeSimulation.JumpAt initial tokens loopLabel loopShape
      accept targetOutcome := by
  have hJoin :
      OutcomeSimulation.JoinArtifact
        { ctx with
          breakLabel? := none
          breakShape? := none
          continueLabel? := none
          continueShape? := none }
        loopShape sourceOutcome :=
    OutcomeSimulation.OutcomeArtifact.toJoin hFallthrough hArtifact
  rcases sourceOutcome with ⟨source, mode⟩
  cases mode with
  | regular =>
      obtain ⟨target, rfl, hStateRel⟩ :=
        ObserverPreservation.OutcomeSimulation.Rel.regular_elim hRel
      exact
        OutcomeSimulation.JumpAt.of_rel
          (ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
            hEval (by simp [ObserverSemantics.Outcome.Nonhalting]))
          hStateRel hJoin
  | brk =>
      change
        ∃ output,
          (none : Option TypedCfg.Shape) = some output ∧
            TypedCfgCompiler.Shape.SourceFrameFits output
              source.source.evm.stack.length at hJoin
      obtain ⟨output, hNone, _hFits⟩ := hJoin
      cases hNone
  | cont =>
      change
        ∃ output,
          (none : Option TypedCfg.Shape) = some output ∧
            TypedCfgCompiler.Shape.SourceFrameFits output
              source.source.evm.stack.length at hJoin
      obtain ⟨output, hNone, _hFits⟩ := hJoin
      cases hNone
  | leave =>
      apply OutcomeSimulation.JumpAt.of_accept
      have hOuterRel :
          ObserverPreservation.OutcomeSimulation.Rel
            (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
              ctx regular)
            tokens (Structured.OutcomeT.leave source)
            targetOutcome trace := by
        cases targetOutcome <;>
          simpa [
            ObserverPreservation.OutcomeSimulation.Rel,
            TypedCfgPreservation.OutcomeSimulation.Loop.postContinuations] using
            hRel
      exact
        hAccept (sourceFuel + 1) (Structured.OutcomeT.leave source)
          targetOutcome trace
          (Structured.EffectSemantics.Stmt.Eval.for_init_leave hEval)
          hOuterRel
          (by
            simpa [OutcomeSimulation.OutcomeArtifact] using hArtifact)
  | halt kind =>
      apply OutcomeSimulation.JumpAt.of_accept
      have hOuterRel :
          ObserverPreservation.OutcomeSimulation.Rel
            (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
              ctx regular)
            tokens (Structured.OutcomeT.halt kind source)
            targetOutcome trace := by
        cases targetOutcome <;>
          simpa [
            ObserverPreservation.OutcomeSimulation.Rel,
            TypedCfgPreservation.OutcomeSimulation.Loop.postContinuations] using
            hRel
      exact
        hAccept (sourceFuel + 1) (Structured.OutcomeT.halt kind source)
          targetOutcome trace
          (Structured.EffectSemantics.Stmt.Eval.for_init_halt hEval)
          hOuterRel (by trivial)

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
    (hClose :
      ∀ forFuel forOutcome forTarget forTrace,
        ObserverSemantics.For.Eval program forFuel
            cond post body source forOutcome →
          ObserverPreservation.OutcomeSimulation.Rel
            outer tokens forOutcome forTarget forTrace →
          OutcomeSimulation.JoinArtifact ctx
            { condOutput with slots := condOutput.slots.tail }
            forOutcome →
          accept forTarget)
    (hBodyEntryNotAccepted :
      ∀ (bodySource : ObserverSemantics.State transcript) targetState,
        ¬ OutcomeSimulation.JumpAt bodySource tokens postLabel
          { condOutput with slots := condOutput.slots.tail } accept
          (.jump bodyLabel targetState))
    (hPostEntryNotAccepted :
      ∀ (postSource : ObserverSemantics.State transcript) targetState,
        ¬ OutcomeSimulation.JumpAt postSource tokens loopLabel
          loopInput accept
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
      ∀ bodyTargetFuel, bodyTargetFuel < targetFuel →
        ∀ {bodySource : ObserverSemantics.State transcript},
        OutcomeSimulation.AdequateWithinFuel
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
          (OutcomeSimulation.JumpAt bodySource tokens postLabel
            { condOutput with slots := condOutput.slots.tail } accept)
          bodyLabel
          { condOutput with slots := condOutput.slots.tail }
          bodySource tokens bodyTargetFuel)
    (hPostAdequate :
      ∀ postTargetFuel, postTargetFuel < targetFuel →
        ∀ {postSource : ObserverSemantics.State transcript},
        OutcomeSimulation.AdequateWithinFuel
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
          (OutcomeSimulation.JumpAt postSource tokens loopLabel
            loopInput accept)
          postLabel
          { condOutput with slots := condOutput.slots.tail }
          postSource tokens postTargetFuel)
    (hRecurse :
      ∀ {smallerFuel : Nat}
        {loopSource : ObserverSemantics.State transcript}
        {loopTarget : EVMState} {loopTrace : Trace},
        smallerFuel < targetFuel →
        (∀ loopFuel loopOutcome loopTargetOutcome loopFinalTrace,
          ObserverSemantics.For.Eval program loopFuel
              cond post body loopSource loopOutcome →
            ObserverPreservation.OutcomeSimulation.Rel
              outer tokens loopOutcome loopTargetOutcome loopFinalTrace →
            OutcomeSimulation.JoinArtifact ctx
              { condOutput with slots := condOutput.slots.tail }
              loopOutcome →
            accept loopTargetOutcome) →
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
    have hForEval :
        ObserverSemantics.For.Eval program 1
          cond post body source
          (Structured.OutcomeT.regular afterCond) :=
      Structured.EffectSemantics.For.Eval.false
        (fuel := 0) hCond
    have hOuterRel :
        ObserverPreservation.OutcomeSimulation.Rel
          outer tokens (Structured.OutcomeT.regular afterCond)
          (.jump endLabel targetAfterCond) firstTrace :=
      ObserverPreservation.OutcomeSimulation.Rel.regular_iff.mpr
        ⟨hOuterRegular.symm, hAfterCondRel.rel⟩
    have hJoin :
        OutcomeSimulation.JoinArtifact ctx
          { condOutput with slots := condOutput.slots.tail }
          (Structured.OutcomeT.regular afterCond) :=
      hAfterCondRel.sourceFrameFits
    obtain ⟨hOutcomeEq, hTraceEq⟩ :=
      OutcomeSimulation.FirstReaches.outcome_eq_of_step_accepted
        hReach hStep
          (hClose 1 (Structured.OutcomeT.regular afterCond)
            (.jump endLabel targetAfterCond) firstTrace
            hForEval hOuterRel hJoin)
    subst targetOutcome
    subst traceFinal
    exact
      ⟨1, Structured.OutcomeT.regular afterCond,
        hForEval, hOuterRel, hJoin⟩
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
        hTailReach.run
          (OutcomeSimulation.JumpAt.of_accept hTailReach.boundary)
    have hBodyPositive : 0 < bodyPrefixFuel :=
      OutcomeSimulation.FirstReaches.fuel_pos_of_entry_not_accepted
        hBodyReach (hBodyEntryNotAccepted afterCond targetAfterCond)
    cases bodyPrefixFuel with
    | zero =>
        omega
    | succ bodyPrefixFuel =>
        obtain
            ⟨bodySourceFuel, bodyOutcome,
              hBodyEval, hBodyOutcomeRel, hBodyArtifact⟩ :=
          hBodyAdequate bodyPrefixFuel (by omega)
            (fun _sourceFuel _sourceOutcome _targetOutcome _trace
                hEval hOutcomeRel hArtifact =>
              bodyActivationBoundary hClose hCond hOuterRegular
                hBodyRequire hEval hOutcomeRel hArtifact)
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
            have hForEval :
                ObserverSemantics.For.Eval program (bodySourceFuel + 1)
                  cond post body source
                  (Structured.OutcomeT.regular bodyState) :=
              Structured.EffectSemantics.For.Eval.body_brk
                hCond hBodyEval
            obtain ⟨_hFuelEq, hOutcomeEq, hTraceEq⟩ :=
              OutcomeSimulation.FirstReaches.outcome_eq_of_prefix_accepted
                hTailReach hBodyReach hBodyLe
                (hClose (bodySourceFuel + 1)
                  (Structured.OutcomeT.regular bodyState)
                  (.jump endLabel bodyTarget) bodyTrace
                  hForEval hOuterRel hBound)
            subst targetOutcome
            subst traceFinal
            exact
              ⟨bodySourceFuel + 1,
                Structured.OutcomeT.regular bodyState,
                hForEval,
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
                (hClose (bodySourceFuel + 1)
                  (Structured.OutcomeT.leave bodyState)
                  bodyTargetOutcome bodyTrace
                  (Structured.EffectSemantics.For.Eval.body_leave
                    hCond hBodyEval)
                  hOuterRel
                  (by
                    simpa [OutcomeSimulation.JoinArtifact] using
                      hBodyJoin))
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
                (hClose (bodySourceFuel + 1)
                  (Structured.OutcomeT.halt kind bodyState)
                  bodyTargetOutcome bodyTrace
                  (Structured.EffectSemantics.For.Eval.body_halt
                    hCond hBodyEval)
                  hOuterRel (by trivial))
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
                (OutcomeSimulation.JumpAt.of_accept
                  hAfterBodyReach.boundary)
            have hPostPositive : 0 < postPrefixFuel :=
              OutcomeSimulation.FirstReaches.fuel_pos_of_entry_not_accepted
                hPostReach
                  (hPostEntryNotAccepted bodyState bodyTarget)
            cases postPrefixFuel with
            | zero =>
                omega
            | succ postPrefixFuel =>
                obtain
                    ⟨postSourceFuel, postOutcome,
                      hPostEval, hPostOutcomeRel, hPostArtifact⟩ :=
                  hPostAdequate postPrefixFuel (by omega)
                    (fun _sourceFuel _sourceOutcome _targetOutcome _trace
                        hEval hOutcomeRel hArtifact =>
                      postActivationBoundary
                        (hLeave := fun {postFuel} {postState}
                            {postTarget} {postTrace}
                            hPostEval hPostRel hPostJoin => by
                          let sourceFuel :=
                            Nat.max bodySourceFuel postFuel
                          exact
                            hClose (sourceFuel + 1)
                              (Structured.OutcomeT.leave postState)
                              postTarget postTrace
                              (Structured.EffectSemantics.For.Eval.regular_post_leave
                                hCond
                                (Structured.EffectSemantics.Block.Eval.mono
                                  hBodyEval (by simp [sourceFuel]))
                                (Structured.EffectSemantics.Block.Eval.mono
                                  hPostEval (by simp [sourceFuel])))
                              (postLeaveRel hPostRel)
                              (by
                                simpa [OutcomeSimulation.JoinArtifact] using
                                  hPostJoin))
                        (hHalt := fun {postFuel} {postState} {kind}
                            {postTarget} {postTrace}
                            hPostEval hPostRel _hPostJoin => by
                          let sourceFuel :=
                            Nat.max bodySourceFuel postFuel
                          exact
                            hClose (sourceFuel + 1)
                              (Structured.OutcomeT.halt kind postState)
                              postTarget postTrace
                              (Structured.EffectSemantics.For.Eval.regular_post_halt
                                hCond
                                (Structured.EffectSemantics.Block.Eval.mono
                                  hBodyEval (by simp [sourceFuel]))
                                (Structured.EffectSemantics.Block.Eval.mono
                                  hPostEval (by simp [sourceFuel])))
                              (postHaltRel hPostRel) (by trivial))
                        hPostRequire hEval hOutcomeRel hArtifact)
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
                          hRecurse hDecrease
                            (fun loopFuel loopOutcome loopTargetOutcome
                                loopFinalTrace hLoopEval hLoopRel
                                hLoopArtifact => by
                              let sourceFuel :=
                                Nat.max bodySourceFuel
                                  (Nat.max postSourceFuel loopFuel)
                              exact
                                hClose (sourceFuel + 1) loopOutcome
                                  loopTargetOutcome loopFinalTrace
                                  (Structured.EffectSemantics.For.Eval.regular_post_regular
                                    hCond
                                    (Structured.EffectSemantics.Block.Eval.mono
                                      hBodyEval (by simp [sourceFuel]))
                                    (Structured.EffectSemantics.Block.Eval.mono
                                      hPostEval (by simp [sourceFuel]))
                                    (Structured.EffectSemantics.For.Eval.mono
                                      hLoopEval (by simp [sourceFuel])))
                                  hLoopRel hLoopArtifact)
                            hPostAt
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
                    let sourceFuel :=
                      Nat.max bodySourceFuel postSourceFuel
                    have hForEval :
                        ObserverSemantics.For.Eval program (sourceFuel + 1)
                          cond post body source
                          (Structured.OutcomeT.leave postState) :=
                      Structured.EffectSemantics.For.Eval.regular_post_leave
                        hCond
                        (Structured.EffectSemantics.Block.Eval.mono
                          hBodyEval (by simp [sourceFuel]))
                        (Structured.EffectSemantics.Block.Eval.mono
                          hPostEval (by simp [sourceFuel]))
                    obtain ⟨_hFuelEq, hOutcomeEq, hTraceEq⟩ :=
                      OutcomeSimulation.FirstReaches.outcome_eq_of_prefix_accepted
                        hAfterBodyReach hPostReach hPostLe
                        (hClose (sourceFuel + 1)
                          (Structured.OutcomeT.leave postState)
                          postTargetOutcome postTrace hForEval hOuterRel
                          (by
                            simpa [OutcomeSimulation.JoinArtifact] using
                              hPostJoin))
                    subst targetOutcome
                    subst traceFinal
                    exact
                      ⟨sourceFuel + 1,
                        Structured.OutcomeT.leave postState,
                        hForEval,
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
                    let sourceFuel :=
                      Nat.max bodySourceFuel postSourceFuel
                    have hForEval :
                        ObserverSemantics.For.Eval program (sourceFuel + 1)
                          cond post body source
                          (Structured.OutcomeT.halt kind postState) :=
                      Structured.EffectSemantics.For.Eval.regular_post_halt
                        hCond
                        (Structured.EffectSemantics.Block.Eval.mono
                          hBodyEval (by simp [sourceFuel]))
                        (Structured.EffectSemantics.Block.Eval.mono
                          hPostEval (by simp [sourceFuel]))
                    obtain ⟨_hFuelEq, hOutcomeEq, hTraceEq⟩ :=
                      OutcomeSimulation.FirstReaches.outcome_eq_of_prefix_accepted
                        hAfterBodyReach hPostReach hPostLe
                        (hClose (sourceFuel + 1)
                          (Structured.OutcomeT.halt kind postState)
                          postTargetOutcome postTrace hForEval hOuterRel
                          (by trivial))
                    subst targetOutcome
                    subst traceFinal
                    exact
                      ⟨sourceFuel + 1,
                        Structured.OutcomeT.halt kind postState,
                        hForEval,
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
                (OutcomeSimulation.JumpAt.of_accept
                  hAfterBodyReach.boundary)
            have hPostPositive : 0 < postPrefixFuel :=
              OutcomeSimulation.FirstReaches.fuel_pos_of_entry_not_accepted
                hPostReach
                  (hPostEntryNotAccepted bodyState bodyTarget)
            cases postPrefixFuel with
            | zero =>
                omega
            | succ postPrefixFuel =>
                obtain
                    ⟨postSourceFuel, postOutcome,
                      hPostEval, hPostOutcomeRel, hPostArtifact⟩ :=
                  hPostAdequate postPrefixFuel (by omega)
                    (fun _sourceFuel _sourceOutcome _targetOutcome _trace
                        hEval hOutcomeRel hArtifact =>
                      postActivationBoundary
                        (hLeave := fun {postFuel} {postState}
                            {postTarget} {postTrace}
                            hPostEval hPostRel hPostJoin => by
                          let sourceFuel :=
                            Nat.max bodySourceFuel postFuel
                          exact
                            hClose (sourceFuel + 1)
                              (Structured.OutcomeT.leave postState)
                              postTarget postTrace
                              (Structured.EffectSemantics.For.Eval.cont_post_leave
                                hCond
                                (Structured.EffectSemantics.Block.Eval.mono
                                  hBodyEval (by simp [sourceFuel]))
                                (Structured.EffectSemantics.Block.Eval.mono
                                  hPostEval (by simp [sourceFuel])))
                              (postLeaveRel hPostRel)
                              (by
                                simpa [OutcomeSimulation.JoinArtifact] using
                                  hPostJoin))
                        (hHalt := fun {postFuel} {postState} {kind}
                            {postTarget} {postTrace}
                            hPostEval hPostRel _hPostJoin => by
                          let sourceFuel :=
                            Nat.max bodySourceFuel postFuel
                          exact
                            hClose (sourceFuel + 1)
                              (Structured.OutcomeT.halt kind postState)
                              postTarget postTrace
                              (Structured.EffectSemantics.For.Eval.cont_post_halt
                                hCond
                                (Structured.EffectSemantics.Block.Eval.mono
                                  hBodyEval (by simp [sourceFuel]))
                                (Structured.EffectSemantics.Block.Eval.mono
                                  hPostEval (by simp [sourceFuel])))
                              (postHaltRel hPostRel) (by trivial))
                        hPostRequire hEval hOutcomeRel hArtifact)
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
                          hRecurse hDecrease
                            (fun loopFuel loopOutcome loopTargetOutcome
                                loopFinalTrace hLoopEval hLoopRel
                                hLoopArtifact => by
                              let sourceFuel :=
                                Nat.max bodySourceFuel
                                  (Nat.max postSourceFuel loopFuel)
                              exact
                                hClose (sourceFuel + 1) loopOutcome
                                  loopTargetOutcome loopFinalTrace
                                  (Structured.EffectSemantics.For.Eval.cont_post_regular
                                    hCond
                                    (Structured.EffectSemantics.Block.Eval.mono
                                      hBodyEval (by simp [sourceFuel]))
                                    (Structured.EffectSemantics.Block.Eval.mono
                                      hPostEval (by simp [sourceFuel]))
                                    (Structured.EffectSemantics.For.Eval.mono
                                      hLoopEval (by simp [sourceFuel])))
                                  hLoopRel hLoopArtifact)
                            hPostAt
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
                    let sourceFuel :=
                      Nat.max bodySourceFuel postSourceFuel
                    have hForEval :
                        ObserverSemantics.For.Eval program (sourceFuel + 1)
                          cond post body source
                          (Structured.OutcomeT.leave postState) :=
                      Structured.EffectSemantics.For.Eval.cont_post_leave
                        hCond
                        (Structured.EffectSemantics.Block.Eval.mono
                          hBodyEval (by simp [sourceFuel]))
                        (Structured.EffectSemantics.Block.Eval.mono
                          hPostEval (by simp [sourceFuel]))
                    obtain ⟨_hFuelEq, hOutcomeEq, hTraceEq⟩ :=
                      OutcomeSimulation.FirstReaches.outcome_eq_of_prefix_accepted
                        hAfterBodyReach hPostReach hPostLe
                        (hClose (sourceFuel + 1)
                          (Structured.OutcomeT.leave postState)
                          postTargetOutcome postTrace hForEval hOuterRel
                          (by
                            simpa [OutcomeSimulation.JoinArtifact] using
                              hPostJoin))
                    subst targetOutcome
                    subst traceFinal
                    exact
                      ⟨sourceFuel + 1,
                        Structured.OutcomeT.leave postState,
                        hForEval,
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
                    let sourceFuel :=
                      Nat.max bodySourceFuel postSourceFuel
                    have hForEval :
                        ObserverSemantics.For.Eval program (sourceFuel + 1)
                          cond post body source
                          (Structured.OutcomeT.halt kind postState) :=
                      Structured.EffectSemantics.For.Eval.cont_post_halt
                        hCond
                        (Structured.EffectSemantics.Block.Eval.mono
                          hBodyEval (by simp [sourceFuel]))
                        (Structured.EffectSemantics.Block.Eval.mono
                          hPostEval (by simp [sourceFuel]))
                    obtain ⟨_hFuelEq, hOutcomeEq, hTraceEq⟩ :=
                      OutcomeSimulation.FirstReaches.outcome_eq_of_prefix_accepted
                        hAfterBodyReach hPostReach hPostLe
                        (hClose (sourceFuel + 1)
                          (Structured.OutcomeT.halt kind postState)
                          postTargetOutcome postTrace hForEval hOuterRel
                          (by trivial))
                    subst targetOutcome
                    subst traceFinal
                    exact
                      ⟨sourceFuel + 1,
                        Structured.OutcomeT.halt kind postState,
                        hForEval,
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
    (hClose :
      ∀ forFuel forOutcome forTarget forTrace,
        ObserverSemantics.For.Eval program forFuel
            cond post body source forOutcome →
          ObserverPreservation.OutcomeSimulation.Rel
            outer tokens forOutcome forTarget forTrace →
          OutcomeSimulation.JoinArtifact ctx
            { condOutput with slots := condOutput.slots.tail }
            forOutcome →
          accept forTarget)
    (hBodyEntryNotAccepted :
      ∀ (bodySource : ObserverSemantics.State transcript) targetState,
        ¬ OutcomeSimulation.JumpAt bodySource tokens postLabel
          { condOutput with slots := condOutput.slots.tail } accept
          (.jump bodyLabel targetState))
    (hPostEntryNotAccepted :
      ∀ (postSource : ObserverSemantics.State transcript) targetState,
        ¬ OutcomeSimulation.JumpAt postSource tokens loopLabel
          loopInput accept
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
      ∀ bodyTargetFuel, bodyTargetFuel < targetFuel →
        ∀ {bodySource : ObserverSemantics.State transcript},
        OutcomeSimulation.AdequateWithinFuel
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
          (OutcomeSimulation.JumpAt bodySource tokens postLabel
            { condOutput with slots := condOutput.slots.tail } accept)
          bodyLabel
          { condOutput with slots := condOutput.slots.tail }
          bodySource tokens bodyTargetFuel)
    (hPostAdequate :
      ∀ postTargetFuel, postTargetFuel < targetFuel →
        ∀ {postSource : ObserverSemantics.State transcript},
        OutcomeSimulation.AdequateWithinFuel
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
          (OutcomeSimulation.JumpAt postSource tokens loopLabel
            loopInput accept)
          postLabel
          { condOutput with slots := condOutput.slots.tail }
          postSource tokens postTargetFuel) :
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
          hOuterRegular hClose hBodyEntryNotAccepted
          hPostEntryNotAccepted hLoopEntryNotAccepted
          hRel hReach hBodyAdequate hPostAdequate
          (by
            intro smallerFuel loopSource loopTarget loopTrace
              hSmaller hLoopClose hLoopRel hLoopReach
            exact
              ih smallerFuel hSmaller
                hLoopClose hLoopRel hLoopReach
                (fun bodyTargetFuel hBodyLt =>
                  hBodyAdequate bodyTargetFuel
                    (Nat.lt_trans hBodyLt hSmaller))
                (fun postTargetFuel hPostLt =>
                  hPostAdequate postTargetFuel
                    (Nat.lt_trans hPostLt hSmaller)))

/--
Compiler-facing backward adequacy for a checked Structured `for` statement.
All generated shapes and labels are recovered from the existing compiler
result; recursive blocks cross only the shared adjacent block interface.
-/
theorem adequateWithinFuel_for_of_compileStmtFuel?
    {transcript : Trace} {compilerFuel : Nat}
    {program : Structured.Program}
    {init : Structured.Block} {cond : Structured.Code}
    {post body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word}
    {accept : TypedCfg.Outcome → Prop}
    (targetFuel : Nat)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.for_ init cond post body) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hInitEntryNotAccepted :
      ∀ {accept : TypedCfg.Outcome → Prop}
        (initSource : ObserverSemantics.State transcript)
        (loopShape : TypedCfg.Shape) targetState,
        ¬ OutcomeSimulation.JumpAt initSource tokens
          (LabelSupply.label supply 0) loopShape accept
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
        ∀ initTargetFuel, initTargetFuel ≤ targetFuel →
        ∀ {initSource : ObserverSemantics.State transcript}
          {outer : OutcomeSimulation.Continuations}
          {accept : TypedCfg.Outcome → Prop},
          OutcomeSimulation.AdequateWithinFuel
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
            (OutcomeSimulation.JumpAt initSource tokens
              (LabelSupply.label supply 0) loopInput accept)
            entry input initSource tokens initTargetFuel)
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
        ∀ bodyTargetFuel, bodyTargetFuel < targetFuel →
        ∀ {bodySource : ObserverSemantics.State transcript}
          {outer : OutcomeSimulation.Continuations}
          {accept : TypedCfg.Outcome → Prop},
          OutcomeSimulation.AdequateWithinFuel
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
            (OutcomeSimulation.JumpAt bodySource tokens
              (LabelSupply.label supply 2)
              { condOutput with slots := condOutput.slots.tail } accept)
            (LabelSupply.label supply 1)
            { condOutput with slots := condOutput.slots.tail }
            bodySource tokens bodyTargetFuel)
    (hPostAdequate :
      ∀ {bodyResult postResult : TypedCfgCompiler.Result}
        {condOutput loopInput : TypedCfg.Shape},
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
        ∀ postTargetFuel, postTargetFuel < targetFuel →
        ∀ {postSource : ObserverSemantics.State transcript}
          {outer : OutcomeSimulation.Continuations}
          {accept : TypedCfg.Outcome → Prop},
          OutcomeSimulation.AdequateWithinFuel
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
            (OutcomeSimulation.JumpAt postSource tokens
              (LabelSupply.label supply 0) loopInput accept)
            (LabelSupply.label supply 2)
            { condOutput with slots := condOutput.slots.tail }
            postSource tokens postTargetFuel) :
    OutcomeSimulation.AdequateWithinFuel
      (fun sourceFuel sourceOutcome =>
        ObserverSemantics.Stmt.Eval program sourceFuel
          (.for_ init cond post body) source sourceOutcome)
      result ctx cfg
      (TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext
        ctx regular)
      accept
      entry input source tokens targetFuel := by
  intro hAccept target trace traceFinal
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
      hReach.run (OutcomeSimulation.JumpAt.of_accept hReach.boundary)
  have hInitPositive : 0 < initPrefixFuel :=
    OutcomeSimulation.FirstReaches.fuel_pos_of_entry_not_accepted
      hInitReach (hInitEntryNotAccepted source loopInput target)
  cases initPrefixFuel with
  | zero =>
      omega
  | succ initPrefixFuel =>
      obtain
          ⟨initSourceFuel, initOutcome,
            hInitEval, hInitOutcomeRel, hInitArtifact⟩ :=
        hInitAdequate hInitCompile hInitFallthrough hInitBlocks
          initPrefixFuel (by omega)
          (fun _sourceFuel _sourceOutcome _targetOutcome _trace
              hEval hOutcomeRel hArtifact => by
            exact
              initActivationBoundary hAccept hInitFallthrough
                hEval hOutcomeRel hArtifact)
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
                  rfl
                  (fun forFuel forOutcome forTarget forTrace
                      hForEval hForRel hForJoin => by
                    let sourceFuel :=
                      Nat.max initSourceFuel forFuel
                    exact
                      hAccept (sourceFuel + 1) forOutcome
                        forTarget forTrace
                        (Structured.EffectSemantics.Stmt.Eval.for_init_regular
                          (Structured.EffectSemantics.Block.Eval.mono
                            hInitEval (by simp [sourceFuel]))
                          (Structured.EffectSemantics.For.Eval.mono
                            hForEval (by simp [sourceFuel])))
                        hForRel
                        (OutcomeSimulation.OutcomeArtifact.ofJoin
                          rfl hForJoin))
                  (by
                    intro bodySource targetState
                    simp [OutcomeSimulation.JumpAt]
                    exact
                      ⟨by simp [LabelSupply.label],
                        hGeneratedEntryNotAccepted 1 targetState⟩)
                  (by
                    intro postSource targetState
                    simp [OutcomeSimulation.JumpAt]
                    exact
                      ⟨by simp [LabelSupply.label],
                        hGeneratedEntryNotAccepted 2 targetState⟩)
                  (hGeneratedEntryNotAccepted 0)
                  hLoopAt
                  (by simpa [hResidual] using hAfterInitReach)
                  (fun bodyTargetFuel hBodyLt =>
                    hBodyAdequate hBodyCompile hBodyBlocks
                      bodyTargetFuel
                      (Nat.lt_trans hBodyLt (by omega)))
                  (fun postTargetFuel hPostLt =>
                    hPostAdequate hPostCompile hPostBlocks
                      postTargetFuel
                      (Nat.lt_trans hPostLt (by omega)))
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
              (hAccept (initSourceFuel + 1)
                (Structured.OutcomeT.leave initState)
                initTargetOutcome initTrace
                (Structured.EffectSemantics.Stmt.Eval.for_init_leave
                  hInitEval)
                hOuterRel
                (by
                  simpa [OutcomeSimulation.OutcomeArtifact,
                    OutcomeSimulation.JoinArtifact] using hInitJoin))
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
              (hAccept (initSourceFuel + 1)
                (Structured.OutcomeT.halt kind initState)
                initTargetOutcome initTrace
                (Structured.EffectSemantics.Stmt.Eval.for_init_halt
                  hInitEval)
                hOuterRel (by trivial))
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
