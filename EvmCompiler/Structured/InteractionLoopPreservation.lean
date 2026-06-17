import EvmCompiler.Structured.InteractionSwitchPreservation

namespace EvmCompiler
namespace Structured
namespace InteractionLoopPreservation

namespace Loop

def outerContext (ctx : TypedCfgCompiler.Context) :
    TypedCfgCompiler.Context :=
  { ctx with
    breakLabel? := none
    breakShape? := none
    continueLabel? := none
    continueShape? := none }

def bodyContext (ctx : TypedCfgCompiler.Context)
    (endLabel postLabel : Assembly.Label)
    (shape : TypedCfg.Shape) :
    TypedCfgCompiler.Context :=
  { ctx with
    breakLabel? := some endLabel
    breakShape? := some shape
    continueLabel? := some postLabel
    continueShape? := some shape }

def conditionBlock (loopLabel bodyLabel endLabel : Assembly.Label)
    (loopInput condOutput : TypedCfg.Shape)
    (cond : Structured.Code) : TypedCfg.Block :=
  { label := loopLabel
    input := loopInput
    body := TypedCfgCompiler.Code.toCfg cond
    output := condOutput
    term := .jumpi bodyLabel endLabel }

def postStopPolicy
    (postResult : TypedCfgCompiler.Result)
    (ctx : TypedCfgCompiler.Context)
    (loopLabel : Assembly.Label)
    (returns : List ReturnDest) (tokens : List Word)
    (policy :
      InteractionControlPreservation.OpenOutcome.StopPolicy) :
    InteractionControlPreservation.OpenOutcome.StopPolicy :=
  InteractionControlPreservation.OpenOutcome.pushStopJump
    postResult (outerContext ctx) loopLabel returns tokens policy

def initStopPolicy
    (initResult : TypedCfgCompiler.Result)
    (ctx : TypedCfgCompiler.Context)
    (loopLabel : Assembly.Label)
    (returns : List ReturnDest) (tokens : List Word)
    (policy :
      InteractionControlPreservation.OpenOutcome.StopPolicy) :
    InteractionControlPreservation.OpenOutcome.StopPolicy :=
  InteractionControlPreservation.OpenOutcome.pushStopJump
    initResult (outerContext ctx) loopLabel returns tokens policy

def bodyStopPolicy
    (bodyResult postResult : TypedCfgCompiler.Result)
    (ctx : TypedCfgCompiler.Context)
    (regular postLabel loopLabel : Assembly.Label)
    (branchInput : TypedCfg.Shape)
    (returns : List ReturnDest) (tokens : List Word)
    (policy :
      InteractionControlPreservation.OpenOutcome.StopPolicy) :
    InteractionControlPreservation.OpenOutcome.StopPolicy :=
  InteractionControlPreservation.OpenOutcome.pushStopJump
    bodyResult (bodyContext ctx regular postLabel branchInput)
    postLabel returns tokens
    (postStopPolicy postResult ctx loopLabel returns tokens policy)

/--
The compiler-generated loop condition is exactly the shared open condition
semantics followed by the TypedCfg branch selected by that condition.
-/
theorem openStep_condition
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {loopLabel bodyLabel endLabel : Assembly.Label}
    {loopInput condOutput : TypedCfg.Shape}
    {cond : Structured.Code}
    {source : RunState} {tokens : List Word} {target : EVMState}
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hMem :
      conditionBlock loopLabel bodyLabel endLabel
          loopInput condOutput cond ∈ result.blocks)
    (hType :
      TypedCfgCompiler.Code.type? cond loopInput =
        some condOutput)
    (hSource :
      TypedCfgCompiler.Shape.requireSourceWords? 1 condOutput =
        some ())
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        loopInput source.evm.stack.length)
    (hRel :
      TypedCfgPreservation.StateRel source tokens target) :
    Simulation.Interaction.Rel
      (InteractionBranchPreservation.Condition.DoneRel
        bodyLabel endLabel tokens
        { condOutput with slots := condOutput.slots.tail })
      (InteractionSemantics.Code.openRunCondition cond source)
      (TypedCfg.InteractionSemantics.Program.openStep
        cfg loopLabel target) := by
  have hFind :
      cfg.findBlock? loopLabel =
        some
          (conditionBlock loopLabel bodyLabel endLabel
            loopInput condOutput cond) :=
    hBlocks _ hMem
  simp only [
    TypedCfg.InteractionSemantics.Program.openStep,
    TypedCfg.Control.Program.step, hFind]
  simpa [conditionBlock] using
    (InteractionBranchPreservation.Condition.openRunCondition_jumpi_toCfg
      (entry := loopLabel) (trueLabel := bodyLabel)
      (falseLabel := endLabel)
      hType hSource hFits hRel)

/--
A loop-body `break` reaches the enclosing loop's regular continuation.
-/
theorem body_break_to_regular
    {bodyResult result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {regular postLabel : Assembly.Label}
    {branchInput : TypedCfg.Shape}
    {returns : List ReturnDest} {tokens : List Word}
    {source : RunState} {target : TypedCfg.Outcome}
    (hFallthrough :
      result.fallthrough? = some branchInput)
    (hRel :
      InteractionControlPreservation.OpenOutcome.Rel
        bodyResult
        (bodyContext ctx regular postLabel branchInput)
        postLabel returns tokens
        (Structured.Outcome.brk source) target) :
    InteractionControlPreservation.OpenOutcome.Rel
      result ctx regular returns tokens
      (Structured.Outcome.regular source) target := by
  rcases hRel with ⟨hOutcome, hFits, hRestored⟩
  obtain ⟨label, targetState, hLabel, rfl, hStateRel⟩ :=
    TypedCfgPreservation.OutcomeSimulation.Rel.brk_elim hOutcome
  have hLabelEq : label = regular := by
    simpa [
      bodyContext,
      TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
      using hLabel.symm
  subst label
  have hBranchFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        branchInput source.evm.stack.length := by
    simpa [
      InteractionControlPreservation.OpenOutcome.FrameFits,
      bodyContext] using hFits
  refine ⟨?_, ?_, ?_⟩
  · exact
      TypedCfgPreservation.OutcomeSimulation.Rel.regular_iff.mpr
        ⟨rfl, hStateRel⟩
  · exact ⟨branchInput, hFallthrough, hBranchFits⟩
  · simpa [
      InteractionControlPreservation.OpenOutcome.ActivationRestored]
      using hRestored

/--
A body `continue` reaches the post entry with the loop branch shape restored.
-/
theorem body_continue_to_post
    {bodyResult : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {regular postLabel : Assembly.Label}
    {branchInput : TypedCfg.Shape}
    {returns : List ReturnDest} {tokens : List Word}
    {source : RunState} {target : TypedCfg.Outcome}
    (hRel :
      InteractionControlPreservation.OpenOutcome.Rel
        bodyResult
        (bodyContext ctx regular postLabel branchInput)
        postLabel returns tokens
        (Structured.Outcome.cont source) target) :
    ∃ targetState,
      target = .jump postLabel targetState ∧
        TypedCfgPreservation.StateRel source tokens targetState ∧
          TypedCfgCompiler.Shape.SourceFrameFits
            branchInput source.evm.stack.length ∧
            source.returns = returns := by
  rcases hRel with ⟨hOutcome, hFits, hRestored⟩
  obtain ⟨label, targetState, hLabel, rfl, hStateRel⟩ :=
    TypedCfgPreservation.OutcomeSimulation.Rel.cont_elim hOutcome
  have hLabelEq : label = postLabel := by
    simpa [
      bodyContext,
      TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
      using hLabel.symm
  subst label
  have hBranchFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        branchInput source.evm.stack.length := by
    simpa [
      InteractionControlPreservation.OpenOutcome.FrameFits,
      bodyContext] using hFits
  have hReturns : source.returns = returns := by
    simpa [
      InteractionControlPreservation.OpenOutcome.ActivationRestored]
      using hRestored
  exact
    ⟨targetState, rfl, hStateRel, hBranchFits, hReturns⟩

/--
Loop-local break/continue context changes do not affect a propagated `leave`.
-/
theorem body_leave_to_outer
    {bodyResult result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {regular postLabel : Assembly.Label}
    {branchInput : TypedCfg.Shape}
    {returns : List ReturnDest} {tokens : List Word}
    {source : RunState} {target : TypedCfg.Outcome}
    (hRel :
      InteractionControlPreservation.OpenOutcome.Rel
        bodyResult
        (bodyContext ctx regular postLabel branchInput)
        postLabel returns tokens
        (Structured.Outcome.leave source) target) :
    InteractionControlPreservation.OpenOutcome.Rel
      result ctx regular returns tokens
      (Structured.Outcome.leave source) target := by
  rcases hRel with ⟨hOutcome, hFits, hRestored⟩
  obtain ⟨label, targetState, hLabel, rfl, hStateRel⟩ :=
    TypedCfgPreservation.OutcomeSimulation.Rel.leave_elim hOutcome
  refine ⟨?_, ?_, ?_⟩
  · apply
      TypedCfgPreservation.OutcomeSimulation.Rel.leave_iff.mpr
    exact
      ⟨by
        simpa [
          bodyContext,
          TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
          using hLabel,
        hStateRel⟩
  · simpa [
      InteractionControlPreservation.OpenOutcome.FrameFits,
      bodyContext] using hFits
  · simpa [
      InteractionControlPreservation.OpenOutcome.ActivationRestored]
      using hRestored

/--
Halting ignores lexical continuation contexts and compiler fallthrough data.
-/
theorem body_halt_to_outer
    {bodyResult result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {regular postLabel : Assembly.Label}
    {branchInput : TypedCfg.Shape}
    {returns : List ReturnDest} {tokens : List Word}
    {source : RunState} {kind : Assembly.HaltKind}
    {target : TypedCfg.Outcome}
    (hRel :
      InteractionControlPreservation.OpenOutcome.Rel
        bodyResult
        (bodyContext ctx regular postLabel branchInput)
        postLabel returns tokens
        (Structured.Outcome.halt kind source) target) :
    InteractionControlPreservation.OpenOutcome.Rel
      result ctx regular returns tokens
      (Structured.Outcome.halt kind source) target := by
  rcases hRel with ⟨hOutcome, _hFits, _hRestored⟩
  obtain ⟨targetState, targetFinal, rfl, hStep, hStateRel⟩ :=
    TypedCfgPreservation.OutcomeSimulation.Rel.halt_elim hOutcome
  refine ⟨?_, trivial, trivial⟩
  exact
    TypedCfgPreservation.OutcomeSimulation.Rel.halt_iff.mpr
      ⟨rfl, targetFinal, hStep, hStateRel⟩

/--
The loop initializer and post block clear only loop-local continuations, so
their `leave` result transports directly to the enclosing statement context.
-/
theorem outer_leave_to_enclosing
    {fragmentResult result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {fragmentRegular regular : Assembly.Label}
    {returns : List ReturnDest} {tokens : List Word}
    {source : RunState} {target : TypedCfg.Outcome}
    (hRel :
      InteractionControlPreservation.OpenOutcome.Rel
        fragmentResult (outerContext ctx) fragmentRegular
        returns tokens
        (Structured.Outcome.leave source) target) :
    InteractionControlPreservation.OpenOutcome.Rel
      result ctx regular returns tokens
      (Structured.Outcome.leave source) target := by
  rcases hRel with ⟨hOutcome, hFits, hRestored⟩
  obtain ⟨label, targetState, hLabel, rfl, hStateRel⟩ :=
    TypedCfgPreservation.OutcomeSimulation.Rel.leave_elim hOutcome
  refine ⟨?_, ?_, ?_⟩
  · apply
      TypedCfgPreservation.OutcomeSimulation.Rel.leave_iff.mpr
    exact
      ⟨by
        simpa [
          outerContext,
          TypedCfgPreservation.OutcomeSimulation.Continuations.ofContext]
          using hLabel,
        hStateRel⟩
  · simpa [
      InteractionControlPreservation.OpenOutcome.FrameFits,
      outerContext] using hFits
  · simpa [
      InteractionControlPreservation.OpenOutcome.ActivationRestored]
      using hRestored

theorem outer_halt_to_enclosing
    {fragmentResult result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {fragmentRegular regular : Assembly.Label}
    {returns : List ReturnDest} {tokens : List Word}
    {source : RunState} {kind : Assembly.HaltKind}
    {target : TypedCfg.Outcome}
    (hRel :
      InteractionControlPreservation.OpenOutcome.Rel
        fragmentResult (outerContext ctx) fragmentRegular
        returns tokens
        (Structured.Outcome.halt kind source) target) :
    InteractionControlPreservation.OpenOutcome.Rel
      result ctx regular returns tokens
      (Structured.Outcome.halt kind source) target := by
  rcases hRel with ⟨hOutcome, _hFits, _hRestored⟩
  obtain ⟨targetState, targetFinal, rfl, hStep, hStateRel⟩ :=
    TypedCfgPreservation.OutcomeSimulation.Rel.halt_elim hOutcome
  refine ⟨?_, trivial, trivial⟩
  exact
    TypedCfgPreservation.OutcomeSimulation.Rel.halt_iff.mpr
      ⟨rfl, targetFinal, hStep, hStateRel⟩

/--
Execution-indexed open preservation for the recursive part of a compiled
`for` loop.

The theorem is parameterized by adjacent block owners for the body and post
fragments. Recursion follows only a concrete successful source execution, so
the target budget is derived from that execution rather than from a global
uniform bound.
-/
theorem openRunForLoop_exec_under
    {sourceFuel : Nat}
    {sourceProgram : Structured.Program}
    {cond : Structured.Code} {post body : Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {loopLabel bodyLabel postLabel regular : Assembly.Label}
    {loopInput condOutput : TypedCfg.Shape}
    {result bodyResult postResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {source : RunState} {returns : List ReturnDest}
    {tokens : List Word}
    {policy :
      InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hConditionMem :
      conditionBlock loopLabel bodyLabel regular
          loopInput condOutput cond ∈ result.blocks)
    (hType :
      TypedCfgCompiler.Code.type? cond loopInput =
        some condOutput)
    (hSource :
      TypedCfgCompiler.Shape.requireSourceWords? 1 condOutput =
        some ())
    (hResultFallthrough :
      result.fallthrough? =
        some { condOutput with slots := condOutput.slots.tail })
    (hBodyRequire :
      bodyResult.requireFallthrough?
          { condOutput with slots := condOutput.slots.tail } =
        some ())
    (hPostRequire :
      postResult.requireFallthrough? loopInput = some ())
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        loopInput source.evm.stack.length)
    (hSourceReturns : source.returns = returns)
    (hStops :
      ∀ {sourceOutcome targetOutcome},
        InteractionControlPreservation.OpenOutcome.Rel
            result ctx regular returns tokens
            sourceOutcome targetOutcome →
          InteractionControlPreservation.OpenOutcome.TargetStoppedBy
            policy targetOutcome)
    (hBodyEntryNoStop :
      ∀ {bodySource : RunState} {targetState : EVMState},
        bodySource.returns = returns →
        TypedCfgPreservation.StateRel bodySource tokens targetState →
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            bodySource.evm.stack.length →
          policy bodyLabel targetState = false)
    (hPostEntryNoStop :
      ∀ {postSource : RunState} {targetState : EVMState},
        postSource.returns = returns →
        TypedCfgPreservation.StateRel postSource tokens targetState →
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            postSource.evm.stack.length →
          policy postLabel targetState = false)
    (hLoopEntryNoStop :
      ∀ {loopSource : RunState} {targetState : EVMState},
        loopSource.returns = returns →
        TypedCfgPreservation.StateRel loopSource tokens targetState →
        TypedCfgCompiler.Shape.SourceFrameFits
            loopInput loopSource.evm.stack.length →
          policy loopLabel targetState = false)
    (hBody :
      ∀ {blockFuel : Nat} {bodySource : RunState},
        blockFuel < sourceFuel →
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            bodySource.evm.stack.length →
        bodySource.returns = returns →
        InteractionControlPreservation.OpenOutcome.ExecPreservesUnder
          bodyResult cfg bodyLabel
          (bodyContext ctx regular postLabel
            { condOutput with slots := condOutput.slots.tail })
          postLabel bodySource tokens
          (InteractionSemantics.Block.openRun
            sourceProgram blockFuel body bodySource)
          (bodyStopPolicy bodyResult postResult ctx regular
            postLabel loopLabel
            { condOutput with slots := condOutput.slots.tail }
            returns tokens policy))
    (hPost :
      ∀ {blockFuel : Nat} {postSource : RunState},
        blockFuel < sourceFuel →
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            postSource.evm.stack.length →
        postSource.returns = returns →
        InteractionControlPreservation.OpenOutcome.ExecPreservesUnder
          postResult cfg postLabel (outerContext ctx)
          loopLabel postSource tokens
          (InteractionSemantics.Block.openRun
            sourceProgram blockFuel post postSource)
          (postStopPolicy postResult ctx loopLabel
            returns tokens policy)) :
    InteractionControlPreservation.OpenOutcome.ExecPreservesUnder
      result cfg loopLabel ctx regular source tokens
      (InteractionSemantics.Stmt.openRunForLoop
        sourceProgram sourceFuel cond post body source)
      policy := by
  induction sourceFuel generalizing source with
  | zero =>
      intro target hStateRel transcript sourceOutcome hSourceExec
      change
        Simulation.Interaction.Executes
          (Simulation.Interaction.error
            (Error := EVMException) .InvalidInstruction)
          transcript (.ok sourceOutcome) at hSourceExec
      cases hSourceExec
  | succ fuel ih =>
      intro target hStateRel transcript sourceOutcome hSourceExec
      have hSourceExec' :
          Simulation.Interaction.Executes
            (Simulation.Interaction.bind
              (InteractionSemantics.Code.openRunCondition cond source)
              (fun conditionResult =>
                if conditionResult.2 then
                  Simulation.Interaction.bind
                    (InteractionSemantics.Block.openRun
                      sourceProgram fuel body conditionResult.1)
                    (fun bodyOutcome =>
                      match bodyOutcome.mode with
                      | .brk =>
                          Simulation.Interaction.pure
                            (Structured.Outcome.regular
                              bodyOutcome.state)
                      | .regular | .cont =>
                          Simulation.Interaction.bind
                            (InteractionSemantics.Block.openRun
                              sourceProgram fuel post
                              bodyOutcome.state)
                            (fun postOutcome =>
                              match postOutcome.mode with
                              | .regular =>
                                  InteractionSemantics.Stmt.openRunForLoop
                                    sourceProgram fuel cond post body
                                    postOutcome.state
                              | .brk | .cont =>
                                  Simulation.Interaction.error
                                    .InvalidInstruction
                              | .leave | .halt _ =>
                                  Simulation.Interaction.pure postOutcome)
                      | .leave | .halt _ =>
                          Simulation.Interaction.pure bodyOutcome)
                else
                  Simulation.Interaction.pure
                    (Structured.Outcome.regular conditionResult.1)))
            transcript (.ok sourceOutcome) := by
        simpa [
          InteractionSemantics.Stmt.openRunForLoop,
          EffectSemantics.Control.Stmt.runForLoop] using hSourceExec
      rcases
          Simulation.Interaction.Executes.bind_cases hSourceExec' with
        hConditionError |
          ⟨conditionResult, conditionTranscript, restTranscript,
            hTranscript, hConditionExec, hRestExec⟩
      · rcases hConditionError with
          ⟨err, hOutcome, _hConditionError⟩
        cases hOutcome
      · subst transcript
        have hHeadRel :=
          openStep_condition hBlocks hConditionMem hType hSource
            hFits hStateRel
        have hHeadWithReturns :=
          Simulation.Interaction.Rel.strengthen_left hHeadRel
            (InteractionSemantics.Code.openRunCondition_returns
              cond source)
        obtain ⟨targetDone, hTargetConditionExec, hConditionDone⟩ :=
          Simulation.Interaction.Rel.executes
            hHeadWithReturns hConditionExec
        cases targetDone with
        | error targetError =>
            cases hConditionDone.1
        | ok targetOutcome =>
            rcases conditionResult with ⟨afterCond, condTrue⟩
            rcases hConditionDone with
              ⟨hConditionRel, hConditionReturns⟩
            cases hConditionRel with
            | ok hConditionRel =>
                rcases hConditionRel with
                  ⟨targetAfterCond, hTargetOutcome,
                    hAfterCondRel, hAfterCondFits⟩
                have hAfterCondReturns :
                    afterCond.returns = returns := by
                  have hEq :
                      afterCond.returns = source.returns := by
                    simpa [
                      InteractionSemantics.Code.ConditionReturnsEq]
                      using hConditionReturns
                  exact hEq.trans hSourceReturns
                cases condTrue with
                | false =>
                    simp only [if_false] at hTargetOutcome hRestExec
                    subst targetOutcome
                    cases hRestExec
                    have hWholeRel :
                        InteractionControlPreservation.OpenOutcome.Rel
                          result ctx regular returns tokens
                          (Structured.Outcome.regular afterCond)
                          (.jump regular targetAfterCond) := by
                      refine ⟨?_, ?_, ?_⟩
                      · exact
                          TypedCfgPreservation.OutcomeSimulation.Rel.regular_iff.mpr
                            ⟨rfl, hAfterCondRel⟩
                      · exact
                          ⟨{ condOutput with
                              slots := condOutput.slots.tail },
                            hResultFallthrough, hAfterCondFits⟩
                      · simpa [
                          InteractionControlPreservation.OpenOutcome.ActivationRestored]
                          using hAfterCondReturns
                    have hContinuation :=
                      InteractionControlPreservation.OpenOutcome.afterOpenStepResultWithPolicy_executes_of_targetStopped
                        (cfg := cfg) (fuel := 0)
                        (hStops hWholeRel)
                    have hCombined :=
                      Simulation.Interaction.Executes.bind_ok
                        hTargetConditionExec hContinuation
                    have hTargetExec :
                        Simulation.Interaction.Executes
                          (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                            policy cfg 1 loopLabel target)
                          (conditionTranscript ++ [])
                          (.ok
                            (.stopped 0
                              (.jump regular targetAfterCond))) := by
                      rw [show 1 = 0 + 1 by rfl,
                        TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_succ_eq_bind]
                      exact hCombined
                    exact
                      ⟨1, 0, .jump regular targetAfterCond,
                        by simpa using hTargetExec,
                        by simpa [hSourceReturns] using hWholeRel⟩
                | true =>
                    simp only [if_true] at hTargetOutcome hRestExec
                    subst targetOutcome
                    rcases
                        Simulation.Interaction.Executes.bind_cases
                          hRestExec with
                      hBodyError |
                        ⟨bodyOutcome, bodyTranscript,
                          afterBodyTranscript, hBodyTranscript,
                          hBodyExec, hAfterBodyExec⟩
                    · rcases hBodyError with
                        ⟨err, hOutcome, _hBodyError⟩
                      cases hOutcome
                    · subst restTranscript
                      have hBodyPreserves :=
                        hBody (blockFuel := fuel)
                          (Nat.lt_succ_self fuel)
                          hAfterCondFits hAfterCondReturns
                      obtain
                          ⟨bodyFuel, bodyRemaining, targetBodyOutcome,
                            hTargetBodyExec, hBodyRelRaw⟩ :=
                        hBodyPreserves targetAfterCond hAfterCondRel
                          bodyTranscript bodyOutcome hBodyExec
                      have hBodyRel :
                          InteractionControlPreservation.OpenOutcome.Rel
                            bodyResult
                            (bodyContext ctx regular postLabel
                              { condOutput with
                                slots := condOutput.slots.tail })
                            postLabel returns tokens
                            bodyOutcome targetBodyOutcome := by
                        simpa [hAfterCondReturns] using hBodyRelRaw
                      rcases bodyOutcome with
                        ⟨bodyState, bodyMode⟩
                      cases bodyMode with
                      | brk =>
                          change
                            Simulation.Interaction.Executes
                              (Simulation.Interaction.pure
                                (Structured.Outcome.regular bodyState))
                              afterBodyTranscript (.ok sourceOutcome)
                            at hAfterBodyExec
                          cases hAfterBodyExec
                          have hWholeRel :=
                            body_break_to_regular
                              hResultFallthrough hBodyRel
                          have hTargetBodyOuter :=
                            InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.close_refined
                              (outer := policy)
                              (inner :=
                                bodyStopPolicy bodyResult postResult ctx
                                  regular postLabel loopLabel
                                  { condOutput with
                                    slots := condOutput.slots.tail }
                                  returns tokens policy)
                              (hRefines := by
                                intro label state hStop
                                simp [
                                  bodyStopPolicy, postStopPolicy,
                                  InteractionControlPreservation.OpenOutcome.pushStopJump,
                                  hStop])
                              hTargetBodyExec (hStops hWholeRel)
                          have hTargetExec :=
                            InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.prepend_step_jump
                              hTargetConditionExec
                              (hBodyEntryNoStop
                                hAfterCondReturns hAfterCondRel
                                hAfterCondFits)
                              hTargetBodyOuter
                          exact
                            ⟨bodyFuel + 1, bodyRemaining,
                              targetBodyOutcome,
                              by simpa [List.append_assoc] using hTargetExec,
                              by
                                simpa [hSourceReturns] using hWholeRel⟩
                      | leave =>
                          change
                            Simulation.Interaction.Executes
                              (Simulation.Interaction.pure
                                (Structured.Outcome.leave bodyState))
                              afterBodyTranscript (.ok sourceOutcome)
                            at hAfterBodyExec
                          cases hAfterBodyExec
                          have hWholeRel :=
                            body_leave_to_outer
                              (result := result) hBodyRel
                          have hTargetBodyOuter :=
                            InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.close_refined
                              (outer := policy)
                              (inner :=
                                bodyStopPolicy bodyResult postResult ctx
                                  regular postLabel loopLabel
                                  { condOutput with
                                    slots := condOutput.slots.tail }
                                  returns tokens policy)
                              (hRefines := by
                                intro label state hStop
                                simp [
                                  bodyStopPolicy, postStopPolicy,
                                  InteractionControlPreservation.OpenOutcome.pushStopJump,
                                  hStop])
                              hTargetBodyExec (hStops hWholeRel)
                          have hTargetExec :=
                            InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.prepend_step_jump
                              hTargetConditionExec
                              (hBodyEntryNoStop
                                hAfterCondReturns hAfterCondRel
                                hAfterCondFits)
                              hTargetBodyOuter
                          exact
                            ⟨bodyFuel + 1, bodyRemaining,
                              targetBodyOutcome,
                              by simpa [List.append_assoc] using hTargetExec,
                              by
                                simpa [hSourceReturns] using hWholeRel⟩
                      | halt kind =>
                          change
                            Simulation.Interaction.Executes
                              (Simulation.Interaction.pure
                                (Structured.Outcome.halt kind bodyState))
                              afterBodyTranscript (.ok sourceOutcome)
                            at hAfterBodyExec
                          cases hAfterBodyExec
                          have hWholeRel :=
                            body_halt_to_outer
                              (result := result) hBodyRel
                          have hTargetBodyOuter :=
                            InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.close_refined
                              (outer := policy)
                              (inner :=
                                bodyStopPolicy bodyResult postResult ctx
                                  regular postLabel loopLabel
                                  { condOutput with
                                    slots := condOutput.slots.tail }
                                  returns tokens policy)
                              (hRefines := by
                                intro label state hStop
                                simp [
                                  bodyStopPolicy, postStopPolicy,
                                  InteractionControlPreservation.OpenOutcome.pushStopJump,
                                  hStop])
                              hTargetBodyExec (hStops hWholeRel)
                          have hTargetExec :=
                            InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.prepend_step_jump
                              hTargetConditionExec
                              (hBodyEntryNoStop
                                hAfterCondReturns hAfterCondRel
                                hAfterCondFits)
                              hTargetBodyOuter
                          exact
                            ⟨bodyFuel + 1, bodyRemaining,
                              targetBodyOutcome,
                              by simpa [List.append_assoc] using hTargetExec,
                              by
                                simpa [hSourceReturns] using hWholeRel⟩
                      | regular =>
                          obtain
                              ⟨targetPostEntry, rfl, hPostStateRel,
                                hPostFits, hBodyReturns⟩ :=
                            InteractionControlPreservation.OpenOutcome.Rel.regular_elim_of_required_fallthrough
                              hBodyRequire hBodyRel
                          rcases
                              Simulation.Interaction.Executes.bind_cases
                                hAfterBodyExec with
                            hPostError |
                              ⟨postOutcome, postTranscript,
                                afterPostTranscript, hPostTranscript,
                                hPostExec, hAfterPostExec⟩
                          · rcases hPostError with
                              ⟨err, hOutcome, _hPostError⟩
                            cases hOutcome
                          · subst afterBodyTranscript
                            have hPostPreserves :=
                              hPost (blockFuel := fuel)
                                (Nat.lt_succ_self fuel)
                                hPostFits hBodyReturns
                            obtain
                                ⟨postFuel, postRemaining,
                                  targetPostOutcome,
                                  hTargetPostExec, hPostRelRaw⟩ :=
                              hPostPreserves targetPostEntry
                                hPostStateRel postTranscript
                                postOutcome hPostExec
                            have hPostRel :
                                InteractionControlPreservation.OpenOutcome.Rel
                                  postResult (outerContext ctx)
                                  loopLabel returns tokens
                                  postOutcome targetPostOutcome := by
                              simpa [hBodyReturns] using hPostRelRaw
                            rcases postOutcome with
                              ⟨postState, postMode⟩
                            cases postMode with
                            | regular =>
                                obtain
                                    ⟨targetLoopEntry, rfl,
                                      hLoopStateRel, hLoopFits,
                                      hPostReturns⟩ :=
                                  InteractionControlPreservation.OpenOutcome.Rel.regular_elim_of_required_fallthrough
                                    hPostRequire hPostRel
                                have hLoopPreserves :=
                                  ih
                                    hLoopFits hPostReturns
                                    (fun {blockFuel} {bodySource} hFuel =>
                                      hBody
                                        (Nat.lt_trans hFuel
                                          (Nat.lt_succ_self fuel)))
                                    (fun {blockFuel} {postSource} hFuel =>
                                      hPost
                                        (Nat.lt_trans hFuel
                                          (Nat.lt_succ_self fuel)))
                                obtain
                                    ⟨loopFuel, loopRemaining,
                                      targetFinal, hTargetLoopExec,
                                      hLoopRel⟩ :=
                                  hLoopPreserves targetLoopEntry
                                    hLoopStateRel afterPostTranscript
                                    sourceOutcome hAfterPostExec
                                have hPostAndLoop :=
                                  InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.splice_refined_jump
                                    (outer := policy)
                                    (inner :=
                                      postStopPolicy postResult ctx
                                        loopLabel returns tokens policy)
                                    (hRefines := by
                                      intro label state hStop
                                      simp [
                                        postStopPolicy,
                                        InteractionControlPreservation.OpenOutcome.pushStopJump,
                                        hStop])
                                    hTargetPostExec
                                    (hLoopEntryNoStop
                                      hPostReturns hLoopStateRel hLoopFits)
                                    hTargetLoopExec
                                have hBodyTail :=
                                  InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.splice_refined_jump
                                    (outer := policy)
                                    (inner :=
                                      bodyStopPolicy bodyResult postResult
                                        ctx regular postLabel loopLabel
                                        { condOutput with
                                          slots := condOutput.slots.tail }
                                        returns tokens policy)
                                    (hRefines := by
                                      intro label state hStop
                                      simp [
                                        bodyStopPolicy, postStopPolicy,
                                        InteractionControlPreservation.OpenOutcome.pushStopJump,
                                        hStop])
                                    hTargetBodyExec
                                    (hPostEntryNoStop
                                      hBodyReturns hPostStateRel hPostFits)
                                    hPostAndLoop
                                have hTargetExec :=
                                  InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.prepend_step_jump
                                    hTargetConditionExec
                                    (hBodyEntryNoStop
                                      hAfterCondReturns hAfterCondRel
                                      hAfterCondFits)
                                    hBodyTail
                                exact
                                  ⟨bodyFuel + (postFuel + loopFuel) + 1,
                                    (loopRemaining + postRemaining) +
                                      bodyRemaining,
                                    targetFinal,
                                    by
                                      simpa [List.append_assoc,
                                        Nat.add_assoc] using hTargetExec,
                                    by
                                      simpa [hSourceReturns, hPostReturns]
                                        using hLoopRel⟩
                            | brk =>
                                change
                                  Simulation.Interaction.Executes
                                    (Simulation.Interaction.error
                                      (Error := EVMException)
                                      .InvalidInstruction)
                                    afterPostTranscript
                                    (.ok sourceOutcome)
                                  at hAfterPostExec
                                cases hAfterPostExec
                            | cont =>
                                change
                                  Simulation.Interaction.Executes
                                    (Simulation.Interaction.error
                                      (Error := EVMException)
                                      .InvalidInstruction)
                                    afterPostTranscript
                                    (.ok sourceOutcome)
                                  at hAfterPostExec
                                cases hAfterPostExec
                            | leave =>
                                change
                                  Simulation.Interaction.Executes
                                    (Simulation.Interaction.pure
                                      (Structured.Outcome.leave postState))
                                    afterPostTranscript
                                    (.ok sourceOutcome)
                                  at hAfterPostExec
                                cases hAfterPostExec
                                have hWholeRel :=
                                  outer_leave_to_enclosing
                                    (result := result)
                                    (regular := regular) hPostRel
                                have hTargetPostOuter :=
                                  InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.close_refined
                                    (outer := policy)
                                    (inner :=
                                      postStopPolicy postResult ctx
                                        loopLabel returns tokens policy)
                                    (hRefines := by
                                      intro label state hStop
                                      simp [
                                        postStopPolicy,
                                        InteractionControlPreservation.OpenOutcome.pushStopJump,
                                        hStop])
                                    hTargetPostExec (hStops hWholeRel)
                                have hBodyTail :=
                                  InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.splice_refined_jump
                                    (outer := policy)
                                    (inner :=
                                      bodyStopPolicy bodyResult postResult
                                        ctx regular postLabel loopLabel
                                        { condOutput with
                                          slots := condOutput.slots.tail }
                                        returns tokens policy)
                                    (hRefines := by
                                      intro label state hStop
                                      simp [
                                        bodyStopPolicy, postStopPolicy,
                                        InteractionControlPreservation.OpenOutcome.pushStopJump,
                                        hStop])
                                    hTargetBodyExec
                                    (hPostEntryNoStop
                                      hBodyReturns hPostStateRel hPostFits)
                                    hTargetPostOuter
                                have hTargetExec :=
                                  InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.prepend_step_jump
                                    hTargetConditionExec
                                    (hBodyEntryNoStop
                                      hAfterCondReturns hAfterCondRel
                                      hAfterCondFits)
                                    hBodyTail
                                exact
                                  ⟨bodyFuel + postFuel + 1,
                                    postRemaining + bodyRemaining,
                                    targetPostOutcome,
                                    by
                                      simpa [List.append_assoc,
                                        Nat.add_assoc] using hTargetExec,
                                    by
                                      simpa [hSourceReturns] using
                                        hWholeRel⟩
                            | halt kind =>
                                change
                                  Simulation.Interaction.Executes
                                    (Simulation.Interaction.pure
                                      (Structured.Outcome.halt
                                        kind postState))
                                    afterPostTranscript
                                    (.ok sourceOutcome)
                                  at hAfterPostExec
                                cases hAfterPostExec
                                have hWholeRel :=
                                  outer_halt_to_enclosing
                                    (result := result)
                                    (regular := regular) hPostRel
                                have hTargetPostOuter :=
                                  InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.close_refined
                                    (outer := policy)
                                    (inner :=
                                      postStopPolicy postResult ctx
                                        loopLabel returns tokens policy)
                                    (hRefines := by
                                      intro label state hStop
                                      simp [
                                        postStopPolicy,
                                        InteractionControlPreservation.OpenOutcome.pushStopJump,
                                        hStop])
                                    hTargetPostExec (hStops hWholeRel)
                                have hBodyTail :=
                                  InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.splice_refined_jump
                                    (outer := policy)
                                    (inner :=
                                      bodyStopPolicy bodyResult postResult
                                        ctx regular postLabel loopLabel
                                        { condOutput with
                                          slots := condOutput.slots.tail }
                                        returns tokens policy)
                                    (hRefines := by
                                      intro label state hStop
                                      simp [
                                        bodyStopPolicy, postStopPolicy,
                                        InteractionControlPreservation.OpenOutcome.pushStopJump,
                                        hStop])
                                    hTargetBodyExec
                                    (hPostEntryNoStop
                                      hBodyReturns hPostStateRel hPostFits)
                                    hTargetPostOuter
                                have hTargetExec :=
                                  InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.prepend_step_jump
                                    hTargetConditionExec
                                    (hBodyEntryNoStop
                                      hAfterCondReturns hAfterCondRel
                                      hAfterCondFits)
                                    hBodyTail
                                exact
                                  ⟨bodyFuel + postFuel + 1,
                                    postRemaining + bodyRemaining,
                                    targetPostOutcome,
                                    by
                                      simpa [List.append_assoc,
                                        Nat.add_assoc] using hTargetExec,
                                    by
                                      simpa [hSourceReturns] using
                                        hWholeRel⟩
                      | cont =>
                          obtain
                              ⟨targetPostEntry, rfl, hPostStateRel,
                                hPostFits, hBodyReturns⟩ :=
                            body_continue_to_post hBodyRel
                          rcases
                              Simulation.Interaction.Executes.bind_cases
                                hAfterBodyExec with
                            hPostError |
                              ⟨postOutcome, postTranscript,
                                afterPostTranscript, hPostTranscript,
                                hPostExec, hAfterPostExec⟩
                          · rcases hPostError with
                              ⟨err, hOutcome, _hPostError⟩
                            cases hOutcome
                          · subst afterBodyTranscript
                            have hPostPreserves :=
                              hPost (blockFuel := fuel)
                                (Nat.lt_succ_self fuel)
                                hPostFits hBodyReturns
                            obtain
                                ⟨postFuel, postRemaining,
                                  targetPostOutcome,
                                  hTargetPostExec, hPostRelRaw⟩ :=
                              hPostPreserves targetPostEntry
                                hPostStateRel postTranscript
                                postOutcome hPostExec
                            have hPostRel :
                                InteractionControlPreservation.OpenOutcome.Rel
                                  postResult (outerContext ctx)
                                  loopLabel returns tokens
                                  postOutcome targetPostOutcome := by
                              simpa [hBodyReturns] using hPostRelRaw
                            rcases postOutcome with
                              ⟨postState, postMode⟩
                            cases postMode with
                            | regular =>
                                obtain
                                    ⟨targetLoopEntry, rfl,
                                      hLoopStateRel, hLoopFits,
                                      hPostReturns⟩ :=
                                  InteractionControlPreservation.OpenOutcome.Rel.regular_elim_of_required_fallthrough
                                    hPostRequire hPostRel
                                have hLoopPreserves :=
                                  ih
                                    hLoopFits hPostReturns
                                    (fun {blockFuel} {bodySource} hFuel =>
                                      hBody
                                        (Nat.lt_trans hFuel
                                          (Nat.lt_succ_self fuel)))
                                    (fun {blockFuel} {postSource} hFuel =>
                                      hPost
                                        (Nat.lt_trans hFuel
                                          (Nat.lt_succ_self fuel)))
                                obtain
                                    ⟨loopFuel, loopRemaining,
                                      targetFinal, hTargetLoopExec,
                                      hLoopRel⟩ :=
                                  hLoopPreserves targetLoopEntry
                                    hLoopStateRel afterPostTranscript
                                    sourceOutcome hAfterPostExec
                                have hPostAndLoop :=
                                  InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.splice_refined_jump
                                    (outer := policy)
                                    (inner :=
                                      postStopPolicy postResult ctx
                                        loopLabel returns tokens policy)
                                    (hRefines := by
                                      intro label state hStop
                                      simp [
                                        postStopPolicy,
                                        InteractionControlPreservation.OpenOutcome.pushStopJump,
                                        hStop])
                                    hTargetPostExec
                                    (hLoopEntryNoStop
                                      hPostReturns hLoopStateRel hLoopFits)
                                    hTargetLoopExec
                                have hBodyTail :=
                                  InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.splice_refined_jump
                                    (outer := policy)
                                    (inner :=
                                      bodyStopPolicy bodyResult postResult
                                        ctx regular postLabel loopLabel
                                        { condOutput with
                                          slots := condOutput.slots.tail }
                                        returns tokens policy)
                                    (hRefines := by
                                      intro label state hStop
                                      simp [
                                        bodyStopPolicy, postStopPolicy,
                                        InteractionControlPreservation.OpenOutcome.pushStopJump,
                                        hStop])
                                    hTargetBodyExec
                                    (hPostEntryNoStop
                                      hBodyReturns hPostStateRel hPostFits)
                                    hPostAndLoop
                                have hTargetExec :=
                                  InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.prepend_step_jump
                                    hTargetConditionExec
                                    (hBodyEntryNoStop
                                      hAfterCondReturns hAfterCondRel
                                      hAfterCondFits)
                                    hBodyTail
                                exact
                                  ⟨bodyFuel + (postFuel + loopFuel) + 1,
                                    (loopRemaining + postRemaining) +
                                      bodyRemaining,
                                    targetFinal,
                                    by
                                      simpa [List.append_assoc,
                                        Nat.add_assoc] using hTargetExec,
                                    by
                                      simpa [hSourceReturns, hPostReturns]
                                        using hLoopRel⟩
                            | brk =>
                                change
                                  Simulation.Interaction.Executes
                                    (Simulation.Interaction.error
                                      (Error := EVMException)
                                      .InvalidInstruction)
                                    afterPostTranscript
                                    (.ok sourceOutcome)
                                  at hAfterPostExec
                                cases hAfterPostExec
                            | cont =>
                                change
                                  Simulation.Interaction.Executes
                                    (Simulation.Interaction.error
                                      (Error := EVMException)
                                      .InvalidInstruction)
                                    afterPostTranscript
                                    (.ok sourceOutcome)
                                  at hAfterPostExec
                                cases hAfterPostExec
                            | leave =>
                                change
                                  Simulation.Interaction.Executes
                                    (Simulation.Interaction.pure
                                      (Structured.Outcome.leave postState))
                                    afterPostTranscript
                                    (.ok sourceOutcome)
                                  at hAfterPostExec
                                cases hAfterPostExec
                                have hWholeRel :=
                                  outer_leave_to_enclosing
                                    (result := result)
                                    (regular := regular) hPostRel
                                have hTargetPostOuter :=
                                  InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.close_refined
                                    (outer := policy)
                                    (inner :=
                                      postStopPolicy postResult ctx
                                        loopLabel returns tokens policy)
                                    (hRefines := by
                                      intro label state hStop
                                      simp [
                                        postStopPolicy,
                                        InteractionControlPreservation.OpenOutcome.pushStopJump,
                                        hStop])
                                    hTargetPostExec (hStops hWholeRel)
                                have hBodyTail :=
                                  InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.splice_refined_jump
                                    (outer := policy)
                                    (inner :=
                                      bodyStopPolicy bodyResult postResult
                                        ctx regular postLabel loopLabel
                                        { condOutput with
                                          slots := condOutput.slots.tail }
                                        returns tokens policy)
                                    (hRefines := by
                                      intro label state hStop
                                      simp [
                                        bodyStopPolicy, postStopPolicy,
                                        InteractionControlPreservation.OpenOutcome.pushStopJump,
                                        hStop])
                                    hTargetBodyExec
                                    (hPostEntryNoStop
                                      hBodyReturns hPostStateRel hPostFits)
                                    hTargetPostOuter
                                have hTargetExec :=
                                  InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.prepend_step_jump
                                    hTargetConditionExec
                                    (hBodyEntryNoStop
                                      hAfterCondReturns hAfterCondRel
                                      hAfterCondFits)
                                    hBodyTail
                                exact
                                  ⟨bodyFuel + postFuel + 1,
                                    postRemaining + bodyRemaining,
                                    targetPostOutcome,
                                    by
                                      simpa [List.append_assoc,
                                        Nat.add_assoc] using hTargetExec,
                                    by
                                      simpa [hSourceReturns] using
                                        hWholeRel⟩
                            | halt kind =>
                                change
                                  Simulation.Interaction.Executes
                                    (Simulation.Interaction.pure
                                      (Structured.Outcome.halt
                                        kind postState))
                                    afterPostTranscript
                                    (.ok sourceOutcome)
                                  at hAfterPostExec
                                cases hAfterPostExec
                                have hWholeRel :=
                                  outer_halt_to_enclosing
                                    (result := result)
                                    (regular := regular) hPostRel
                                have hTargetPostOuter :=
                                  InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.close_refined
                                    (outer := policy)
                                    (inner :=
                                      postStopPolicy postResult ctx
                                        loopLabel returns tokens policy)
                                    (hRefines := by
                                      intro label state hStop
                                      simp [
                                        postStopPolicy,
                                        InteractionControlPreservation.OpenOutcome.pushStopJump,
                                        hStop])
                                    hTargetPostExec (hStops hWholeRel)
                                have hBodyTail :=
                                  InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.splice_refined_jump
                                    (outer := policy)
                                    (inner :=
                                      bodyStopPolicy bodyResult postResult
                                        ctx regular postLabel loopLabel
                                        { condOutput with
                                          slots := condOutput.slots.tail }
                                        returns tokens policy)
                                    (hRefines := by
                                      intro label state hStop
                                      simp [
                                        bodyStopPolicy, postStopPolicy,
                                        InteractionControlPreservation.OpenOutcome.pushStopJump,
                                        hStop])
                                    hTargetBodyExec
                                    (hPostEntryNoStop
                                      hBodyReturns hPostStateRel hPostFits)
                                    hTargetPostOuter
                                have hTargetExec :=
                                  InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.prepend_step_jump
                                    hTargetConditionExec
                                    (hBodyEntryNoStop
                                      hAfterCondReturns hAfterCondRel
                                      hAfterCondFits)
                                    hBodyTail
                                exact
                                  ⟨bodyFuel + postFuel + 1,
                                    postRemaining + bodyRemaining,
                                    targetPostOutcome,
                                    by
                                      simpa [List.append_assoc,
                                        Nat.add_assoc] using hTargetExec,
                                    by
                                      simpa [hSourceReturns] using
                                        hWholeRel⟩

namespace Stmt

/--
Compiler-owned facts shared by the recursive body and post owners of one
compiled loop.
-/
structure OwnerFacts
    (cfg : TypedCfg.Program)
    (generatedCalls : List TypedCfgCompiler.DispatchSite)
    (tokens : List Word)
    (supply : LabelSupply)
    (result initResult bodyResult postResult :
      TypedCfgCompiler.Result)
    (loopInput condOutput : TypedCfg.Shape) : Prop where
  bodyCalls :
    TypedCfgPreservation.CallsInProgram bodyResult generatedCalls
  postCalls :
    TypedCfgPreservation.CallsInProgram postResult generatedCalls
  loopShape :
    TypedCfgPreservation.LabelShape cfg
      (LabelSupply.label supply 0) loopInput
  bodyShape :
    TypedCfgPreservation.LabelShape cfg
      (LabelSupply.label supply 1)
      { condOutput with slots := condOutput.slots.tail }
  postShape :
    TypedCfgPreservation.LabelShape cfg
      (LabelSupply.label supply 2)
      { condOutput with slots := condOutput.slots.tail }
  bodyActivation :
    TypedCfgPreservation.ActivationInput tokens
      { condOutput with slots := condOutput.slots.tail }
  initSupply : supply + 1 ≤ initResult.next
  bodySupply : supply + 1 ≤ bodyResult.next
  bodyRequire :
    bodyResult.requireFallthrough?
        { condOutput with slots := condOutput.slots.tail } =
      some ()
  postRequire :
    postResult.requireFallthrough? loopInput = some ()
  enclosingFallthrough :
    result.fallthrough? =
      some { condOutput with slots := condOutput.slots.tail }

/--
Compiler-facing successful-execution preservation for `for`.

The theorem decomposes the compiler artifact once, delegates only the three
adjacent block fragments to recursive owners, and composes the initializer
with the execution-indexed loop theorem above.
-/
theorem openRun_for_exec_under_of_compileStmtFuel?
    {compilerFuel sourceFuel : Nat}
    {sourceProgram : Structured.Program}
    {init post body : Structured.Block} {cond : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word}
    {generatedCalls : List TypedCfgCompiler.DispatchSite}
    {policy :
      InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.for_ init cond post body) ctx supply entry input regular =
        some result)
    (hBlocks :
      TypedCfgPreservation.BlocksInProgram result cfg)
    (hResultCalls :
      TypedCfgPreservation.CallsInProgram result generatedCalls)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        input source.evm.stack.length)
    (hRegular :
      TypedCfgCompilerFacts.RegularAtSupply regular supply)
    (hActivation :
      TypedCfgPreservation.ActivationInput tokens input)
    (hBoundary :
      InteractionBoundaryPreservation.OpenOutcome.StopPolicy.RecursiveBoundary
        cfg source.returns tokens policy supply regular)
    (hStops :
      ∀ {sourceOutcome targetOutcome},
        InteractionControlPreservation.OpenOutcome.Rel
            result ctx regular source.returns tokens
            sourceOutcome targetOutcome →
          InteractionControlPreservation.OpenOutcome.TargetStoppedBy
            policy targetOutcome)
    (hInit :
      ∀ {initResult : TypedCfgCompiler.Result}
        {loopInput : TypedCfg.Shape},
        TypedCfgCompiler.compileBlockFuel? compilerFuel init
            (outerContext ctx) (supply + 1) entry input
            (LabelSupply.label supply 0) =
          some initResult →
        TypedCfgPreservation.BlocksInProgram initResult cfg →
        TypedCfgPreservation.CallsInProgram initResult generatedCalls →
        TypedCfgPreservation.LabelShape cfg
          (LabelSupply.label supply 0) loopInput →
        initResult.fallthrough? = some loopInput →
        InteractionControlPreservation.OpenOutcome.ExecPreservesUnder
          initResult cfg entry (outerContext ctx)
          (LabelSupply.label supply 0) source tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel init source)
          (initStopPolicy initResult ctx
            (LabelSupply.label supply 0)
            source.returns tokens policy))
    (hBody :
      ∀ {initResult bodyResult postResult :
            TypedCfgCompiler.Result}
        {loopInput condOutput : TypedCfg.Shape}
        {blockFuel : Nat} {bodySource : RunState},
        blockFuel < sourceFuel →
        TypedCfgCompiler.compileBlockFuel? compilerFuel body
            (bodyContext ctx regular (LabelSupply.label supply 2)
              { condOutput with slots := condOutput.slots.tail })
            initResult.next
            (LabelSupply.label supply 1)
            { condOutput with slots := condOutput.slots.tail }
            (LabelSupply.label supply 2) =
          some bodyResult →
        TypedCfgCompiler.compileBlockFuel? compilerFuel post
            (outerContext ctx) bodyResult.next
            (LabelSupply.label supply 2)
            { condOutput with slots := condOutput.slots.tail }
            (LabelSupply.label supply 0) =
          some postResult →
        TypedCfgPreservation.BlocksInProgram bodyResult cfg →
        OwnerFacts cfg generatedCalls tokens supply result
          initResult bodyResult postResult loopInput condOutput →
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            bodySource.evm.stack.length →
        bodySource.returns = source.returns →
        InteractionControlPreservation.OpenOutcome.ExecPreservesUnder
          bodyResult cfg (LabelSupply.label supply 1)
          (bodyContext ctx regular (LabelSupply.label supply 2)
            { condOutput with slots := condOutput.slots.tail })
          (LabelSupply.label supply 2) bodySource tokens
          (InteractionSemantics.Block.openRun
            sourceProgram blockFuel body bodySource)
          (bodyStopPolicy bodyResult postResult ctx regular
            (LabelSupply.label supply 2)
            (LabelSupply.label supply 0)
            { condOutput with slots := condOutput.slots.tail }
            source.returns tokens policy))
    (hPost :
      ∀ {initResult bodyResult postResult : TypedCfgCompiler.Result}
        {loopInput condOutput : TypedCfg.Shape}
        {blockFuel : Nat} {postSource : RunState},
        blockFuel < sourceFuel →
        TypedCfgCompiler.compileBlockFuel? compilerFuel post
            (outerContext ctx) bodyResult.next
            (LabelSupply.label supply 2)
            { condOutput with slots := condOutput.slots.tail }
            (LabelSupply.label supply 0) =
          some postResult →
        TypedCfgPreservation.BlocksInProgram postResult cfg →
        OwnerFacts cfg generatedCalls tokens supply result
          initResult bodyResult postResult loopInput condOutput →
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            postSource.evm.stack.length →
        postSource.returns = source.returns →
        InteractionControlPreservation.OpenOutcome.ExecPreservesUnder
          postResult cfg (LabelSupply.label supply 2)
          (outerContext ctx) (LabelSupply.label supply 0)
          postSource tokens
          (InteractionSemantics.Block.openRun
            sourceProgram blockFuel post postSource)
          (postStopPolicy postResult ctx
            (LabelSupply.label supply 0)
            source.returns tokens policy)) :
    InteractionControlPreservation.OpenOutcome.ExecPreservesUnder
      result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram (sourceFuel + 1)
        (.for_ init cond post body) source)
      policy := by
  rcases
      TypedCfgCompilerFacts.Loop.components_of_compileStmtFuel?_for
        hCompile with
    ⟨initResult, loopInput, condOutput, _condition,
      bodyResult, postResult, hInitCompileRaw, hInitFallthrough,
      hType, hSource, _hHead, hBodyCompileRaw, hBodyRequire,
      hPostCompileRaw, hPostRequire, hResult⟩
  have hInitCompile :
      TypedCfgCompiler.compileBlockFuel? compilerFuel init
          (outerContext ctx) (supply + 1) entry input
          (LabelSupply.label supply 0) =
        some initResult := by
    simpa [outerContext] using hInitCompileRaw
  have hBodyCompile :
      TypedCfgCompiler.compileBlockFuel? compilerFuel body
          (bodyContext ctx regular (LabelSupply.label supply 2)
            { condOutput with slots := condOutput.slots.tail })
          initResult.next (LabelSupply.label supply 1)
          { condOutput with slots := condOutput.slots.tail }
          (LabelSupply.label supply 2) =
        some bodyResult := by
    simpa [bodyContext] using hBodyCompileRaw
  have hPostCompile :
      TypedCfgCompiler.compileBlockFuel? compilerFuel post
          (outerContext ctx) bodyResult.next
          (LabelSupply.label supply 2)
          { condOutput with slots := condOutput.slots.tail }
          (LabelSupply.label supply 0) =
        some postResult := by
    simpa [outerContext] using hPostCompileRaw
  subst result
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
  have hInitCalls :
      TypedCfgPreservation.CallsInProgram
        initResult generatedCalls := by
    intro site hMem
    apply hResultCalls site
    simp [hMem]
  have hBodyCalls :
      TypedCfgPreservation.CallsInProgram
        bodyResult generatedCalls := by
    intro site hMem
    apply hResultCalls site
    simp [hMem]
  have hPostCalls :
      TypedCfgPreservation.CallsInProgram
        postResult generatedCalls := by
    intro site hMem
    apply hResultCalls site
    simp [hMem]
  have hConditionMem :
      conditionBlock
          (LabelSupply.label supply 0)
          (LabelSupply.label supply 1)
          regular loopInput condOutput cond ∈
        ({ blocks :=
            initResult.blocks ++
              [{ label := LabelSupply.label supply 0
                 input := loopInput
                 body := TypedCfgCompiler.Code.toCfg cond
                 output := condOutput
                 term :=
                   .jumpi (LabelSupply.label supply 1) regular }] ++
              bodyResult.blocks ++ postResult.blocks
           next := postResult.next
           calls :=
             initResult.calls ++ bodyResult.calls ++ postResult.calls
           fallthrough? :=
             some { condOutput with
               slots := condOutput.slots.tail } } :
          TypedCfgCompiler.Result).blocks := by
    simp [conditionBlock]
  have hLoopShape :
      TypedCfgPreservation.LabelShape cfg
        (LabelSupply.label supply 0) loopInput := by
    refine
      ⟨conditionBlock
          (LabelSupply.label supply 0)
          (LabelSupply.label supply 1)
          regular loopInput condOutput cond,
        hBlocks _ hConditionMem, rfl⟩
  have hBodyShape :
      TypedCfgPreservation.LabelShape cfg
        (LabelSupply.label supply 1)
        { condOutput with slots := condOutput.slots.tail } :=
    TypedCfgPreservation.LabelShape.of_compileBlockFuel?
      hBodyCompile hBodyBlocks
  have hPostShape :
      TypedCfgPreservation.LabelShape cfg
        (LabelSupply.label supply 2)
        { condOutput with slots := condOutput.slots.tail } :=
    TypedCfgPreservation.LabelShape.of_compileBlockFuel?
      hPostCompile hPostBlocks
  have hLoopActivation :
      TypedCfgPreservation.ActivationInput tokens loopInput :=
    hActivation.blockFallthrough
      hInitCompile hInitFallthrough
  have hBodyActivation :
      TypedCfgPreservation.ActivationInput tokens
        { condOutput with slots := condOutput.slots.tail } :=
    (hLoopActivation.code hType).tail
      (TypedCfgCompilerFacts.Shape.requireSourceWords?_eq_some_iff.mp
        hSource)
  have hInitSupply : supply + 1 ≤ initResult.next :=
    TypedCfgCompilerFacts.Supply.block_next_ge hInitCompile
  have hBodySupply : supply + 1 ≤ bodyResult.next :=
    Nat.le_trans hInitSupply
      (TypedCfgCompilerFacts.Supply.block_next_ge hBodyCompile)
  have hOwnerFacts :
      OwnerFacts cfg generatedCalls tokens supply
        { blocks :=
            initResult.blocks ++
              [{ label := LabelSupply.label supply 0
                 input := loopInput
                 body := TypedCfgCompiler.Code.toCfg cond
                 output := condOutput
                 term :=
                   .jumpi (LabelSupply.label supply 1) regular }] ++
              bodyResult.blocks ++ postResult.blocks
          next := postResult.next
          calls :=
            initResult.calls ++ bodyResult.calls ++ postResult.calls
          fallthrough? :=
            some { condOutput with slots := condOutput.slots.tail } }
        initResult bodyResult postResult loopInput condOutput :=
    { bodyCalls := hBodyCalls
      postCalls := hPostCalls
      loopShape := hLoopShape
      bodyShape := hBodyShape
      postShape := hPostShape
      bodyActivation := hBodyActivation
      initSupply := hInitSupply
      bodySupply := hBodySupply
      bodyRequire := hBodyRequire
      postRequire := hPostRequire
      enclosingFallthrough := rfl }
  have hLoopEntryNoStop :
      ∀ {loopSource : RunState} {targetState : EVMState},
        loopSource.returns = source.returns →
        TypedCfgPreservation.StateRel loopSource tokens targetState →
        TypedCfgCompiler.Shape.SourceFrameFits
            loopInput loopSource.evm.stack.length →
          policy (LabelSupply.label supply 0) targetState = false := by
    intro loopSource targetState hReturns hRel hLoopFits
    simpa [LabelSupply.label] using
      (hBoundary.congr_returns hReturns.symm).eq_false_of_stateRel
        (scope := supply) (tag := 0)
        (Nat.le_refl supply)
        (hRegular.current_generated_ne (by omega))
        hLoopShape hLoopActivation hRel hLoopFits
  have hBodyEntryNoStop :
      ∀ {bodySource : RunState} {targetState : EVMState},
        bodySource.returns = source.returns →
        TypedCfgPreservation.StateRel bodySource tokens targetState →
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            bodySource.evm.stack.length →
          policy (LabelSupply.label supply 1) targetState = false := by
    intro bodySource targetState hReturns hRel hBodyFits
    simpa [LabelSupply.label] using
      (hBoundary.congr_returns hReturns.symm).eq_false_of_stateRel
        (scope := supply) (tag := 1)
        (Nat.le_refl supply)
        (hRegular.current_generated_ne (by omega))
        hBodyShape hBodyActivation hRel hBodyFits
  have hPostEntryNoStop :
      ∀ {postSource : RunState} {targetState : EVMState},
        postSource.returns = source.returns →
        TypedCfgPreservation.StateRel postSource tokens targetState →
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            postSource.evm.stack.length →
          policy (LabelSupply.label supply 2) targetState = false := by
    intro postSource targetState hReturns hRel hPostFits
    simpa [LabelSupply.label] using
      (hBoundary.congr_returns hReturns.symm).eq_false_of_stateRel
        (scope := supply) (tag := 2)
        (Nat.le_refl supply)
        (hRegular.current_generated_ne (by omega))
        hPostShape hBodyActivation hRel hPostFits
  have hInitPreserves :=
    hInit hInitCompile hInitBlocks hInitCalls
      hLoopShape hInitFallthrough
  intro target hStateRel transcript sourceOutcome hSourceExec
  have hSourceExec' :
      Simulation.Interaction.Executes
        (Simulation.Interaction.bind
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel init source)
          (fun initOutcome =>
            match initOutcome.mode with
            | .regular =>
                InteractionSemantics.Stmt.openRunForLoop
                  sourceProgram sourceFuel cond post body
                  initOutcome.state
            | .brk | .cont =>
                Simulation.Interaction.error .InvalidInstruction
            | .leave | .halt _ =>
                Simulation.Interaction.pure initOutcome))
        transcript (.ok sourceOutcome) := by
    simpa [
      InteractionSemantics.Stmt.openRun,
      EffectSemantics.Control.Stmt.run] using hSourceExec
  rcases
      Simulation.Interaction.Executes.bind_cases hSourceExec' with
    hInitError |
      ⟨initOutcome, initTranscript, restTranscript,
        hTranscript, hInitExec, hAfterInitExec⟩
  · rcases hInitError with ⟨err, hOutcome, _hInitError⟩
    cases hOutcome
  · subst transcript
    obtain
        ⟨initFuel, initRemaining, targetInitOutcome,
          hTargetInitExec, hInitRel⟩ :=
      hInitPreserves target hStateRel initTranscript
        initOutcome hInitExec
    rcases initOutcome with ⟨initState, initMode⟩
    cases initMode with
    | regular =>
        have hInitRequire :
            initResult.requireFallthrough? loopInput = some () :=
          TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mpr
            (Or.inr hInitFallthrough)
        obtain
            ⟨targetLoopEntry, rfl, hLoopStateRel,
              hLoopFits, hInitReturns⟩ :=
          InteractionControlPreservation.OpenOutcome.Rel.regular_elim_of_required_fallthrough
            hInitRequire hInitRel
        have hLoopPreserves :=
          openRunForLoop_exec_under
            (sourceFuel := sourceFuel)
            (sourceProgram := sourceProgram)
            (cond := cond) (post := post) (body := body)
            (ctx := ctx)
            (loopLabel := LabelSupply.label supply 0)
            (bodyLabel := LabelSupply.label supply 1)
            (postLabel := LabelSupply.label supply 2)
            (regular := regular)
            (loopInput := loopInput) (condOutput := condOutput)
            (result :=
              { blocks :=
                  initResult.blocks ++
                    [{ label := LabelSupply.label supply 0
                       input := loopInput
                       body := TypedCfgCompiler.Code.toCfg cond
                       output := condOutput
                       term :=
                         .jumpi (LabelSupply.label supply 1) regular }] ++
                    bodyResult.blocks ++ postResult.blocks
                next := postResult.next
                calls :=
                  initResult.calls ++ bodyResult.calls ++ postResult.calls
                fallthrough? :=
                  some { condOutput with
                    slots := condOutput.slots.tail } })
            (bodyResult := bodyResult) (postResult := postResult)
            (cfg := cfg) (source := initState)
            (returns := source.returns) (tokens := tokens)
            (policy := policy)
            hBlocks hConditionMem hType hSource rfl
            hBodyRequire hPostRequire hLoopFits hInitReturns
            hStops hBodyEntryNoStop hPostEntryNoStop
            hLoopEntryNoStop
            (fun {blockFuel} {bodySource} hFuel hBodyFits hBodyReturns =>
              hBody hFuel hBodyCompile hPostCompile hBodyBlocks
                hOwnerFacts hBodyFits hBodyReturns)
            (fun {blockFuel} {postSource} hFuel hPostFits hPostReturns =>
              hPost hFuel hPostCompile hPostBlocks
                hOwnerFacts hPostFits hPostReturns)
        obtain
            ⟨loopFuel, loopRemaining, targetFinal,
              hTargetLoopExec, hLoopRel⟩ :=
          hLoopPreserves targetLoopEntry hLoopStateRel
            restTranscript sourceOutcome hAfterInitExec
        have hTargetExec :=
          InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.splice_refined_jump
            (outer := policy)
            (inner :=
              initStopPolicy initResult ctx
                (LabelSupply.label supply 0)
                source.returns tokens policy)
            (hRefines := by
              intro label state hStop
              simp [
                initStopPolicy,
                InteractionControlPreservation.OpenOutcome.pushStopJump,
                hStop])
            hTargetInitExec
            (hLoopEntryNoStop
              hInitReturns hLoopStateRel hLoopFits)
            hTargetLoopExec
        exact
          ⟨initFuel + loopFuel,
            loopRemaining + initRemaining, targetFinal,
            by simpa using hTargetExec,
            by simpa [hInitReturns] using hLoopRel⟩
    | brk =>
        change
          Simulation.Interaction.Executes
            (Simulation.Interaction.error
              (Error := EVMException) .InvalidInstruction)
            restTranscript (.ok sourceOutcome) at hAfterInitExec
        cases hAfterInitExec
    | cont =>
        change
          Simulation.Interaction.Executes
            (Simulation.Interaction.error
              (Error := EVMException) .InvalidInstruction)
            restTranscript (.ok sourceOutcome) at hAfterInitExec
        cases hAfterInitExec
    | leave =>
        change
          Simulation.Interaction.Executes
            (Simulation.Interaction.pure
              (Structured.Outcome.leave initState))
            restTranscript (.ok sourceOutcome) at hAfterInitExec
        cases hAfterInitExec
        have hWholeRel :=
          outer_leave_to_enclosing
            (result :=
              { blocks :=
                  initResult.blocks ++
                    [{ label := LabelSupply.label supply 0
                       input := loopInput
                       body := TypedCfgCompiler.Code.toCfg cond
                       output := condOutput
                       term :=
                         .jumpi (LabelSupply.label supply 1) regular }] ++
                    bodyResult.blocks ++ postResult.blocks
                next := postResult.next
                calls :=
                  initResult.calls ++ bodyResult.calls ++ postResult.calls
                fallthrough? :=
                  some { condOutput with
                    slots := condOutput.slots.tail } })
            (regular := regular) hInitRel
        have hTargetOuter :=
          InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.close_refined
            (outer := policy)
            (inner :=
              initStopPolicy initResult ctx
                (LabelSupply.label supply 0)
                source.returns tokens policy)
            (hRefines := by
              intro label state hStop
              simp [
                initStopPolicy,
                InteractionControlPreservation.OpenOutcome.pushStopJump,
                hStop])
            hTargetInitExec (hStops hWholeRel)
        exact
          ⟨initFuel, initRemaining, targetInitOutcome,
            by simpa using hTargetOuter, hWholeRel⟩
    | halt kind =>
        change
          Simulation.Interaction.Executes
            (Simulation.Interaction.pure
              (Structured.Outcome.halt kind initState))
            restTranscript (.ok sourceOutcome) at hAfterInitExec
        cases hAfterInitExec
        have hWholeRel :=
          outer_halt_to_enclosing
            (result :=
              { blocks :=
                  initResult.blocks ++
                    [{ label := LabelSupply.label supply 0
                       input := loopInput
                       body := TypedCfgCompiler.Code.toCfg cond
                       output := condOutput
                       term :=
                         .jumpi (LabelSupply.label supply 1) regular }] ++
                    bodyResult.blocks ++ postResult.blocks
                next := postResult.next
                calls :=
                  initResult.calls ++ bodyResult.calls ++ postResult.calls
                fallthrough? :=
                  some { condOutput with
                    slots := condOutput.slots.tail } })
            (regular := regular) hInitRel
        have hTargetOuter :=
          InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.close_refined
            (outer := policy)
            (inner :=
              initStopPolicy initResult ctx
                (LabelSupply.label supply 0)
                source.returns tokens policy)
            (hRefines := by
              intro label state hStop
              simp [
                initStopPolicy,
                InteractionControlPreservation.OpenOutcome.pushStopJump,
                hStop])
            hTargetInitExec (hStops hWholeRel)
        exact
          ⟨initFuel, initRemaining, targetInitOutcome,
            by simpa using hTargetOuter, hWholeRel⟩

end Stmt

end Loop

end InteractionLoopPreservation
end Structured
end EvmCompiler
