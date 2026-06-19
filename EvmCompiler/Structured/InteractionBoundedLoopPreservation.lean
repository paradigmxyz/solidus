import EvmCompiler.Structured.InteractionLoopPreservation
import EvmCompiler.Structured.InteractionStaticCost

namespace EvmCompiler
namespace Structured
namespace InteractionLoopPreservation
namespace Loop

/-- Source-budgeted preservation for the recursive part of a compiled loop. -/
theorem openRunForLoop_bounded_under
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
    {policy : InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hConditionMem :
      conditionBlock loopLabel bodyLabel regular
          loopInput condOutput cond ∈ result.blocks)
    (hType :
      TypedCfgCompiler.Code.type? cond loopInput = some condOutput)
    (hSource :
      TypedCfgCompiler.Shape.requireSourceWords? 1 condOutput = some ())
    (hResultFallthrough :
      result.fallthrough? =
        some { condOutput with slots := condOutput.slots.tail })
    (hBodyRequire :
      bodyResult.requireFallthrough?
          { condOutput with slots := condOutput.slots.tail } = some ())
    (hPostRequire : postResult.requireFallthrough? loopInput = some ())
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        loopInput source.evm.stack.length)
    (hSourceReturns : source.returns = returns)
    (hStops :
      forall {sourceOutcome targetOutcome},
        InteractionControlPreservation.OpenOutcome.Rel
            result ctx regular returns tokens
            sourceOutcome targetOutcome ->
          InteractionControlPreservation.OpenOutcome.TargetStoppedBy
            policy targetOutcome)
    (hBodyEntryNoStop :
      forall {bodySource : RunState} {targetState : EVMState},
        bodySource.returns = returns ->
        TypedCfgPreservation.StateRel bodySource tokens targetState ->
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            bodySource.evm.stack.length ->
          policy bodyLabel targetState = false)
    (hPostEntryNoStop :
      forall {postSource : RunState} {targetState : EVMState},
        postSource.returns = returns ->
        TypedCfgPreservation.StateRel postSource tokens targetState ->
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            postSource.evm.stack.length ->
          policy postLabel targetState = false)
    (hLoopEntryNoStop :
      forall {loopSource : RunState} {targetState : EVMState},
        loopSource.returns = returns ->
        TypedCfgPreservation.StateRel loopSource tokens targetState ->
        TypedCfgCompiler.Shape.SourceFrameFits
            loopInput loopSource.evm.stack.length ->
          policy loopLabel targetState = false)
    (hBody :
      forall {blockFuel : Nat} {bodySource : RunState},
        blockFuel < sourceFuel ->
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            bodySource.evm.stack.length ->
        bodySource.returns = returns ->
        InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
          bodyResult cfg bodyLabel
          (bodyContext ctx regular postLabel
            { condOutput with slots := condOutput.slots.tail })
          postLabel bodySource tokens
          (InteractionSemantics.Block.openRun
            sourceProgram blockFuel body bodySource)
          (InteractionStaticCost.blockBudget sourceProgram blockFuel body)
          (bodyStopPolicy bodyResult postResult ctx regular
            postLabel loopLabel
            { condOutput with slots := condOutput.slots.tail }
            returns tokens policy))
    (hPost :
      forall {blockFuel : Nat} {postSource : RunState},
        blockFuel < sourceFuel ->
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            postSource.evm.stack.length ->
        postSource.returns = returns ->
        InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
          postResult cfg postLabel (outerContext ctx)
          loopLabel postSource tokens
          (InteractionSemantics.Block.openRun
            sourceProgram blockFuel post postSource)
          (InteractionStaticCost.blockBudget sourceProgram blockFuel post)
          (postStopPolicy postResult ctx loopLabel returns tokens policy)) :
    InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
      result cfg loopLabel ctx regular source tokens
      (InteractionSemantics.Stmt.openRunForLoop
        sourceProgram sourceFuel cond post body source)
      (InteractionStaticCost.loopBudget
        sourceProgram sourceFuel cond post body)
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
                            (Structured.Outcome.regular bodyOutcome.state)
                      | .regular | .cont =>
                          Simulation.Interaction.bind
                            (InteractionSemantics.Block.openRun
                              sourceProgram fuel post bodyOutcome.state)
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
      rcases Simulation.Interaction.Executes.bind_cases hSourceExec' with
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
            (InteractionSemantics.Code.openRunCondition_returns cond source)
        obtain ⟨targetDone, hTargetConditionExec, hConditionDone⟩ :=
          Simulation.Interaction.Rel.executes hHeadWithReturns hConditionExec
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
                have hAfterCondReturns : afterCond.returns = returns := by
                  have hEq : afterCond.returns = source.returns := by
                    simpa [InteractionSemantics.Code.ConditionReturnsEq]
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
                        (cfg := cfg) (fuel := 0) (hStops hWholeRel)
                    have hCombined :=
                      Simulation.Interaction.Executes.bind_ok
                        hTargetConditionExec hContinuation
                    have hTargetExec :
                        Simulation.Interaction.Executes
                          (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                            policy cfg 1 loopLabel target)
                          (conditionTranscript ++ [])
                          (.ok (.stopped 0
                            (.jump regular targetAfterCond))) := by
                      rw [show 1 = 0 + 1 by rfl,
                        TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_succ_eq_bind]
                      exact hCombined
                    exact
                      ⟨1, 0, .jump regular targetAfterCond,
                        by
                          rw [InteractionStaticCost.loopBudget_succ]
                          omega,
                        by simpa using hTargetExec,
                        by simpa [hSourceReturns] using hWholeRel⟩
                | true =>
                    simp only [if_true] at hTargetOutcome hRestExec
                    subst targetOutcome
                    rcases
                        Simulation.Interaction.Executes.bind_cases hRestExec with
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
                            hBodyFuel, hTargetBodyExec, hBodyRelRaw⟩ :=
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
                      rcases bodyOutcome with ⟨bodyState, bodyMode⟩
                      have finishBodyAbrupt
                          {finalSource : Structured.Outcome}
                          (hAfter :
                            Simulation.Interaction.Executes
                              (Simulation.Interaction.pure
                                (Error := EVMException) finalSource)
                              afterBodyTranscript (.ok sourceOutcome))
                          (hWholeRel :
                            InteractionControlPreservation.OpenOutcome.Rel
                              result ctx regular returns tokens
                              finalSource targetBodyOutcome) :
                          exists used remaining targetFinal,
                            used <=
                              InteractionStaticCost.loopBudget sourceProgram
                                (Nat.succ fuel) cond post body /\
                            Simulation.Interaction.Executes
                              (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                                policy cfg used loopLabel target)
                              (conditionTranscript ++
                                (bodyTranscript ++ afterBodyTranscript))
                              (.ok (.stopped remaining targetFinal)) /\
                            InteractionControlPreservation.OpenOutcome.Rel
                              result ctx regular returns tokens
                              sourceOutcome targetFinal := by
                        cases hAfter
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
                            (hBodyEntryNoStop hAfterCondReturns hAfterCondRel
                              hAfterCondFits)
                            hTargetBodyOuter
                        exact
                          ⟨bodyFuel + 1, bodyRemaining, targetBodyOutcome,
                            by
                              rw [InteractionStaticCost.loopBudget_succ]
                              omega,
                            by
                              simpa [List.append_assoc] using hTargetExec,
                            hWholeRel⟩
                      have continueWithPost
                          (hExit :
                            exists targetPostEntry,
                              targetBodyOutcome =
                                  .jump postLabel targetPostEntry /\
                              TypedCfgPreservation.StateRel bodyState tokens
                                targetPostEntry /\
                              TypedCfgCompiler.Shape.SourceFrameFits
                                { condOutput with
                                  slots := condOutput.slots.tail }
                              bodyState.evm.stack.length /\
                              bodyState.returns = returns) :
                          Simulation.Interaction.Executes
                              (Simulation.Interaction.bind
                                (InteractionSemantics.Block.openRun
                                  sourceProgram fuel post bodyState)
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
                                      Simulation.Interaction.pure postOutcome))
                              afterBodyTranscript (.ok sourceOutcome) ->
                          exists used remaining targetFinal,
                            used <=
                              InteractionStaticCost.loopBudget sourceProgram
                                (Nat.succ fuel) cond post body /\
                            Simulation.Interaction.Executes
                              (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                                policy cfg used loopLabel target)
                              (conditionTranscript ++
                                (bodyTranscript ++ afterBodyTranscript))
                              (.ok (.stopped remaining targetFinal)) /\
                            InteractionControlPreservation.OpenOutcome.Rel
                              result ctx regular returns tokens
                              sourceOutcome targetFinal := by
                        intro hAfterBodyPostExec
                        obtain
                            ⟨targetPostEntry, rfl, hPostStateRel,
                              hPostFits, hBodyReturns⟩ := hExit
                        rcases
                            Simulation.Interaction.Executes.bind_cases
                              hAfterBodyPostExec with
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
                              (Nat.lt_succ_self fuel) hPostFits hBodyReturns
                          obtain
                              ⟨postFuel, postRemaining, targetPostOutcome,
                                hPostFuel, hTargetPostExec, hPostRelRaw⟩ :=
                            hPostPreserves targetPostEntry hPostStateRel
                              postTranscript postOutcome hPostExec
                          have hPostRel :
                              InteractionControlPreservation.OpenOutcome.Rel
                                postResult (outerContext ctx) loopLabel
                                returns tokens postOutcome targetPostOutcome := by
                            simpa [hBodyReturns] using hPostRelRaw
                          rcases postOutcome with ⟨postState, postMode⟩
                          have finishPostAbrupt
                              {finalSource : Structured.Outcome}
                              (hAfter :
                                Simulation.Interaction.Executes
                                  (Simulation.Interaction.pure
                                    (Error := EVMException) finalSource)
                                  afterPostTranscript (.ok sourceOutcome))
                              (hWholeRel :
                                InteractionControlPreservation.OpenOutcome.Rel
                                  result ctx regular returns tokens
                                  finalSource targetPostOutcome) :
                              exists used remaining targetFinal,
                                used <=
                                  InteractionStaticCost.loopBudget sourceProgram
                                    (Nat.succ fuel) cond post body /\
                                Simulation.Interaction.Executes
                                  (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                                    policy cfg used loopLabel target)
                                  (conditionTranscript ++
                                    (bodyTranscript ++
                                      (postTranscript ++ afterPostTranscript)))
                                  (.ok (.stopped remaining targetFinal)) /\
                                InteractionControlPreservation.OpenOutcome.Rel
                                  result ctx regular returns tokens
                                  sourceOutcome targetFinal := by
                            cases hAfter
                            have hTargetPostOuter :=
                              InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.close_refined
                                (outer := policy)
                                (inner :=
                                  postStopPolicy postResult ctx loopLabel
                                    returns tokens policy)
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
                                hTargetBodyExec
                                (hPostEntryNoStop hBodyReturns hPostStateRel
                                  hPostFits)
                                hTargetPostOuter
                            have hTargetExec :=
                              InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.prepend_step_jump
                                hTargetConditionExec
                                (hBodyEntryNoStop hAfterCondReturns
                                  hAfterCondRel hAfterCondFits)
                                hBodyTail
                            exact
                              ⟨bodyFuel + postFuel + 1,
                                postRemaining + bodyRemaining,
                                targetPostOutcome,
                                by
                                  rw [InteractionStaticCost.loopBudget_succ]
                                  omega,
                                by
                                  simpa [List.append_assoc, Nat.add_assoc]
                                    using hTargetExec,
                                hWholeRel⟩
                          cases postMode with
                          | regular =>
                              obtain
                                  ⟨targetLoopEntry, rfl, hLoopStateRel,
                                    hLoopFits, hPostReturns⟩ :=
                                InteractionControlPreservation.OpenOutcome.Rel.regular_elim_of_required_fallthrough
                                  hPostRequire hPostRel
                              have hLoopPreserves :=
                                ih hLoopFits hPostReturns
                                  (fun {blockFuel} {bodySource} hFuel =>
                                    hBody (Nat.lt_trans hFuel
                                      (Nat.lt_succ_self fuel)))
                                  (fun {blockFuel} {postSource} hFuel =>
                                    hPost (Nat.lt_trans hFuel
                                      (Nat.lt_succ_self fuel)))
                              obtain
                                  ⟨loopFuel, loopRemaining, targetFinal,
                                    hLoopFuel, hTargetLoopExec, hLoopRel⟩ :=
                                hLoopPreserves targetLoopEntry hLoopStateRel
                                  afterPostTranscript sourceOutcome
                                  hAfterPostExec
                              have hPostAndLoop :=
                                InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.splice_refined_jump
                                  (outer := policy)
                                  (inner :=
                                    postStopPolicy postResult ctx loopLabel
                                      returns tokens policy)
                                  (hRefines := by
                                    intro label state hStop
                                    simp [
                                      postStopPolicy,
                                      InteractionControlPreservation.OpenOutcome.pushStopJump,
                                      hStop])
                                  hTargetPostExec
                                  (hLoopEntryNoStop hPostReturns hLoopStateRel
                                    hLoopFits)
                                  hTargetLoopExec
                              have hBodyTail :=
                                InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.splice_refined_jump
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
                                  hTargetBodyExec
                                  (hPostEntryNoStop hBodyReturns hPostStateRel
                                    hPostFits)
                                  hPostAndLoop
                              have hTargetExec :=
                                InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.prepend_step_jump
                                  hTargetConditionExec
                                  (hBodyEntryNoStop hAfterCondReturns
                                    hAfterCondRel hAfterCondFits)
                                  hBodyTail
                              exact
                                ⟨bodyFuel + (postFuel + loopFuel) + 1,
                                  (loopRemaining + postRemaining) +
                                    bodyRemaining,
                                  targetFinal,
                                  by
                                    rw [InteractionStaticCost.loopBudget_succ]
                                    omega,
                                  by
                                    simpa [List.append_assoc, Nat.add_assoc]
                                      using hTargetExec,
                                  by
                                    simpa [hSourceReturns, hPostReturns]
                                      using hLoopRel⟩
                          | brk =>
                              change
                                Simulation.Interaction.Executes
                                  (Simulation.Interaction.error
                                    (Error := EVMException)
                                    .InvalidInstruction)
                                  afterPostTranscript (.ok sourceOutcome)
                                at hAfterPostExec
                              cases hAfterPostExec
                          | cont =>
                              change
                                Simulation.Interaction.Executes
                                  (Simulation.Interaction.error
                                    (Error := EVMException)
                                    .InvalidInstruction)
                                  afterPostTranscript (.ok sourceOutcome)
                                at hAfterPostExec
                              cases hAfterPostExec
                          | leave =>
                              exact finishPostAbrupt hAfterPostExec
                                (outer_leave_to_enclosing
                                  (result := result) (regular := regular)
                                  hPostRel)
                          | halt kind =>
                              exact finishPostAbrupt hAfterPostExec
                                (outer_halt_to_enclosing
                                  (result := result) (regular := regular)
                                  hPostRel)
                      cases bodyMode with
                      | brk =>
                          simpa [hSourceReturns] using
                            finishBodyAbrupt hAfterBodyExec
                              (body_break_to_regular
                                hResultFallthrough hBodyRel)
                      | regular =>
                          simpa [hSourceReturns] using
                            continueWithPost
                              (InteractionControlPreservation.OpenOutcome.Rel.regular_elim_of_required_fallthrough
                                hBodyRequire hBodyRel)
                              hAfterBodyExec
                      | cont =>
                          simpa [hSourceReturns] using
                            continueWithPost
                              (body_continue_to_post hBodyRel)
                              hAfterBodyExec
                      | leave =>
                          simpa [hSourceReturns] using
                            finishBodyAbrupt hAfterBodyExec
                              (body_leave_to_outer (result := result) hBodyRel)
                      | halt kind =>
                          simpa [hSourceReturns] using
                            finishBodyAbrupt hAfterBodyExec
                              (body_halt_to_outer (result := result) hBodyRel)

/--
Compose a bounded loop initializer with the bounded recursive loop owner.

Unlike ordinary statement-list sequencing, `break` and `continue` are invalid
initializer outcomes. `leave` and `halt` bypass the loop and are transported
from the loop-cleared context back to the enclosing statement context.
-/
theorem composeInitializer_bounded_under
    {initResult result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    {entry loopLabel regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context} {loopInput : TypedCfg.Shape}
    {source : RunState} {tokens : List Word}
    {initRun : Simulation.Interaction EVMException Structured.Outcome}
    {loopRun : RunState ->
      Simulation.Interaction EVMException Structured.Outcome}
    {initBudget loopBudget : Nat}
    {policy : InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hInitRequire :
      initResult.requireFallthrough? loopInput = some ())
    (hInit :
      InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
        initResult cfg entry (outerContext ctx) loopLabel source tokens
        initRun initBudget
        (initStopPolicy initResult ctx loopLabel
          source.returns tokens policy))
    (hLoopEntryNoStop :
      forall {loopSource : RunState} {targetState : EVMState},
        loopSource.returns = source.returns ->
        TypedCfgPreservation.StateRel loopSource tokens targetState ->
        TypedCfgCompiler.Shape.SourceFrameFits
            loopInput loopSource.evm.stack.length ->
          policy loopLabel targetState = false)
    (hStops :
      forall {sourceOutcome targetOutcome},
        InteractionControlPreservation.OpenOutcome.Rel
            result ctx regular source.returns tokens
            sourceOutcome targetOutcome ->
          InteractionControlPreservation.OpenOutcome.TargetStoppedBy
            policy targetOutcome)
    (hLoop :
      forall loopSource,
        loopSource.returns = source.returns ->
        InteractionControlPreservation.OpenOutcome.FrameFits
            initResult (outerContext ctx)
            (Structured.Outcome.regular loopSource) ->
          InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
            result cfg loopLabel ctx regular loopSource tokens
            (loopRun loopSource) loopBudget policy) :
    InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
      result cfg entry ctx regular source tokens
      (Simulation.Interaction.bind initRun
        (fun initOutcome =>
          match initOutcome.mode with
          | .regular => loopRun initOutcome.state
          | .brk | .cont =>
              Simulation.Interaction.error .InvalidInstruction
          | .leave | .halt _ =>
              Simulation.Interaction.pure initOutcome))
      (initBudget + loopBudget) policy := by
  intro target hStateRel transcript sourceOutcome hSourceExec
  rcases Simulation.Interaction.Executes.bind_cases hSourceExec with
    hInitError |
      ⟨initOutcome, initTranscript, restTranscript,
        hTranscript, hInitExec, hAfterInitExec⟩
  · rcases hInitError with ⟨err, hOutcome, _hInitError⟩
    cases hOutcome
  · subst transcript
    obtain
        ⟨initFuel, initRemaining, targetInitOutcome, hInitFuel,
          hTargetInitExec, hInitRel⟩ :=
      hInit target hStateRel initTranscript initOutcome hInitExec
    rcases initOutcome with ⟨initState, initMode⟩
    cases initMode with
    | regular =>
        obtain
            ⟨targetLoopEntry, rfl, hLoopStateRel,
              hLoopFits, hInitReturns⟩ :=
          InteractionControlPreservation.OpenOutcome.Rel.regular_elim_of_required_fallthrough
            hInitRequire hInitRel
        obtain
            ⟨tailFuel, tailRemaining, targetFinal, hTailFuel,
              hTargetLoopExec, hLoopRel⟩ :=
          hLoop initState hInitReturns hInitRel.2.1
            targetLoopEntry hLoopStateRel restTranscript
            sourceOutcome hAfterInitExec
        have hTargetExec :=
          InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.splice_refined_jump
            (outer := policy)
            (inner :=
              initStopPolicy initResult ctx loopLabel
                source.returns tokens policy)
            (hRefines := by
              intro label state hStop
              simp [
                initStopPolicy,
                InteractionControlPreservation.OpenOutcome.pushStopJump,
                hStop])
            hTargetInitExec
            (hLoopEntryNoStop hInitReturns hLoopStateRel hLoopFits)
            hTargetLoopExec
        exact
          ⟨initFuel + tailFuel,
            tailRemaining + initRemaining, targetFinal,
            by omega,
            by simpa [List.append_assoc] using hTargetExec,
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
            (result := result) (regular := regular) hInitRel
        have hTargetOuter :=
          InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.close_refined
            (outer := policy)
            (inner :=
              initStopPolicy initResult ctx loopLabel
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
            by omega, by simpa using hTargetOuter, hWholeRel⟩
    | halt kind =>
        change
          Simulation.Interaction.Executes
            (Simulation.Interaction.pure
              (Structured.Outcome.halt kind initState))
            restTranscript (.ok sourceOutcome) at hAfterInitExec
        cases hAfterInitExec
        have hWholeRel :=
          outer_halt_to_enclosing
            (result := result) (regular := regular) hInitRel
        have hTargetOuter :=
          InteractionControlPreservation.OpenOutcome.ExecPreservesUnder.close_refined
            (outer := policy)
            (inner :=
              initStopPolicy initResult ctx loopLabel
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
            by omega, by simpa using hTargetOuter, hWholeRel⟩

namespace Stmt

/-- Compiler-facing source-budgeted preservation for a compiled `for`. -/
theorem openRun_for_bounded_under_of_compileStmtFuel?
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
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
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
      forall {sourceOutcome targetOutcome},
        InteractionControlPreservation.OpenOutcome.Rel
            result ctx regular source.returns tokens
            sourceOutcome targetOutcome ->
          InteractionControlPreservation.OpenOutcome.TargetStoppedBy
            policy targetOutcome)
    (hInit :
      forall {initResult : TypedCfgCompiler.Result}
        {loopInput : TypedCfg.Shape},
        TypedCfgCompiler.compileBlockFuel? compilerFuel init
            (outerContext ctx) (supply + 1) entry input
            (LabelSupply.label supply 0) =
          some initResult ->
        TypedCfgPreservation.BlocksInProgram initResult cfg ->
        TypedCfgPreservation.CallsInProgram initResult generatedCalls ->
        TypedCfgPreservation.LabelShape cfg
          (LabelSupply.label supply 0) loopInput ->
        initResult.fallthrough? = some loopInput ->
        InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
          initResult cfg entry (outerContext ctx)
          (LabelSupply.label supply 0) source tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel init source)
          (InteractionStaticCost.blockBudget
            sourceProgram sourceFuel init)
          (initStopPolicy initResult ctx
            (LabelSupply.label supply 0)
            source.returns tokens policy))
    (hBody :
      forall {initResult bodyResult postResult :
            TypedCfgCompiler.Result}
        {loopInput condOutput : TypedCfg.Shape}
        {blockFuel : Nat} {bodySource : RunState},
        blockFuel < sourceFuel ->
        TypedCfgCompiler.compileBlockFuel? compilerFuel body
            (bodyContext ctx regular (LabelSupply.label supply 2)
              { condOutput with slots := condOutput.slots.tail })
            initResult.next (LabelSupply.label supply 1)
            { condOutput with slots := condOutput.slots.tail }
            (LabelSupply.label supply 2) =
          some bodyResult ->
        TypedCfgCompiler.compileBlockFuel? compilerFuel post
            (outerContext ctx) bodyResult.next
            (LabelSupply.label supply 2)
            { condOutput with slots := condOutput.slots.tail }
            (LabelSupply.label supply 0) =
          some postResult ->
        TypedCfgPreservation.BlocksInProgram bodyResult cfg ->
        OwnerFacts cfg generatedCalls tokens supply result
          initResult bodyResult postResult loopInput condOutput ->
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            bodySource.evm.stack.length ->
        bodySource.returns = source.returns ->
        InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
          bodyResult cfg (LabelSupply.label supply 1)
          (bodyContext ctx regular (LabelSupply.label supply 2)
            { condOutput with slots := condOutput.slots.tail })
          (LabelSupply.label supply 2) bodySource tokens
          (InteractionSemantics.Block.openRun
            sourceProgram blockFuel body bodySource)
          (InteractionStaticCost.blockBudget
            sourceProgram blockFuel body)
          (bodyStopPolicy bodyResult postResult ctx regular
            (LabelSupply.label supply 2)
            (LabelSupply.label supply 0)
            { condOutput with slots := condOutput.slots.tail }
            source.returns tokens policy))
    (hPost :
      forall {initResult bodyResult postResult :
            TypedCfgCompiler.Result}
        {loopInput condOutput : TypedCfg.Shape}
        {blockFuel : Nat} {postSource : RunState},
        blockFuel < sourceFuel ->
        TypedCfgCompiler.compileBlockFuel? compilerFuel post
            (outerContext ctx) bodyResult.next
            (LabelSupply.label supply 2)
            { condOutput with slots := condOutput.slots.tail }
            (LabelSupply.label supply 0) =
          some postResult ->
        TypedCfgPreservation.BlocksInProgram postResult cfg ->
        OwnerFacts cfg generatedCalls tokens supply result
          initResult bodyResult postResult loopInput condOutput ->
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            postSource.evm.stack.length ->
        postSource.returns = source.returns ->
        InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
          postResult cfg (LabelSupply.label supply 2)
          (outerContext ctx) (LabelSupply.label supply 0)
          postSource tokens
          (InteractionSemantics.Block.openRun
            sourceProgram blockFuel post postSource)
          (InteractionStaticCost.blockBudget
            sourceProgram blockFuel post)
          (postStopPolicy postResult ctx
            (LabelSupply.label supply 0)
            source.returns tokens policy)) :
    InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
      result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram (sourceFuel + 1)
        (.for_ init cond post body) source)
      (InteractionStaticCost.stmtBudget sourceProgram (sourceFuel + 1)
        (.for_ init cond post body))
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
      TypedCfgPreservation.CallsInProgram initResult generatedCalls := by
    intro site hMem
    apply hResultCalls site
    simp [hMem]
  have hBodyCalls :
      TypedCfgPreservation.CallsInProgram bodyResult generatedCalls := by
    intro site hMem
    apply hResultCalls site
    simp [hMem]
  have hPostCalls :
      TypedCfgPreservation.CallsInProgram postResult generatedCalls := by
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
    hActivation.blockFallthrough hInitCompile hInitFallthrough
  have hBodyActivation :
      TypedCfgPreservation.ActivationInput tokens
        { condOutput with slots := condOutput.slots.tail } :=
    (hLoopActivation.code hType).tail
      (TypedCfgCompilerFacts.Shape.requireSourceWords?_eq_some_iff.mp
        hSource)
  have hInitSupply : supply + 1 <= initResult.next :=
    TypedCfgCompilerFacts.Supply.block_next_ge hInitCompile
  have hBodySupply : supply + 1 <= bodyResult.next :=
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
      forall {loopSource : RunState} {targetState : EVMState},
        loopSource.returns = source.returns ->
        TypedCfgPreservation.StateRel loopSource tokens targetState ->
        TypedCfgCompiler.Shape.SourceFrameFits
            loopInput loopSource.evm.stack.length ->
          policy (LabelSupply.label supply 0) targetState = false := by
    intro loopSource targetState hReturns hRel hLoopFits
    simpa [LabelSupply.label] using
      (hBoundary.congr_returns hReturns.symm).eq_false_of_stateRel
        (scope := supply) (tag := 0)
        (Nat.le_refl supply)
        (hRegular.current_generated_ne (by omega))
        hLoopShape hLoopActivation hRel hLoopFits
  have hBodyEntryNoStop :
      forall {bodySource : RunState} {targetState : EVMState},
        bodySource.returns = source.returns ->
        TypedCfgPreservation.StateRel bodySource tokens targetState ->
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            bodySource.evm.stack.length ->
          policy (LabelSupply.label supply 1) targetState = false := by
    intro bodySource targetState hReturns hRel hBodyFits
    simpa [LabelSupply.label] using
      (hBoundary.congr_returns hReturns.symm).eq_false_of_stateRel
        (scope := supply) (tag := 1)
        (Nat.le_refl supply)
        (hRegular.current_generated_ne (by omega))
        hBodyShape hBodyActivation hRel hBodyFits
  have hPostEntryNoStop :
      forall {postSource : RunState} {targetState : EVMState},
        postSource.returns = source.returns ->
        TypedCfgPreservation.StateRel postSource tokens targetState ->
        TypedCfgCompiler.Shape.SourceFrameFits
            { condOutput with slots := condOutput.slots.tail }
            postSource.evm.stack.length ->
          policy (LabelSupply.label supply 2) targetState = false := by
    intro postSource targetState hReturns hRel hPostFits
    simpa [LabelSupply.label] using
      (hBoundary.congr_returns hReturns.symm).eq_false_of_stateRel
        (scope := supply) (tag := 2)
        (Nat.le_refl supply)
        (hRegular.current_generated_ne (by omega))
        hPostShape hBodyActivation hRel hPostFits
  have hInitRequire :
      initResult.requireFallthrough? loopInput = some () :=
    TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mpr
      (Or.inr hInitFallthrough)
  have hInitPreserves :=
    hInit hInitCompile hInitBlocks hInitCalls
      hLoopShape hInitFallthrough
  have hComposed :=
    composeInitializer_bounded_under
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
            some { condOutput with slots := condOutput.slots.tail } })
      (loopInput := loopInput)
      (loopRun := fun loopSource =>
        InteractionSemantics.Stmt.openRunForLoop
          sourceProgram sourceFuel cond post body loopSource)
      hInitRequire hInitPreserves hLoopEntryNoStop hStops
      (fun loopSource hReturns hFrame => by
        rcases hFrame with ⟨shape, hShape, hLoopFits⟩
        rw [hInitFallthrough] at hShape
        cases hShape
        exact
          openRunForLoop_bounded_under
            hBlocks hConditionMem hType hSource rfl
            hBodyRequire hPostRequire hLoopFits hReturns hStops
            hBodyEntryNoStop hPostEntryNoStop hLoopEntryNoStop
            (fun {blockFuel} {bodySource} hFuel hBodyFits hBodyReturns =>
              hBody hFuel hBodyCompile hPostCompile hBodyBlocks
                hOwnerFacts hBodyFits hBodyReturns)
            (fun {blockFuel} {postSource} hFuel hPostFits hPostReturns =>
              hPost hFuel hPostCompile hPostBlocks
                hOwnerFacts hPostFits hPostReturns))
  simpa [
      InteractionSemantics.Stmt.openRun,
      EffectSemantics.Control.Stmt.run,
      InteractionStaticCost.stmtBudget_for_succ] using hComposed

end Stmt

end Loop
end InteractionLoopPreservation
end Structured
end EvmCompiler
