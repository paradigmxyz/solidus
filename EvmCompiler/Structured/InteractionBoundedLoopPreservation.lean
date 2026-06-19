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

end Loop
end InteractionLoopPreservation
end Structured
end EvmCompiler
