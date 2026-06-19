import EvmCompiler.Structured.InteractionBranchPreservation
import EvmCompiler.Structured.InteractionStaticCost

namespace EvmCompiler
namespace Structured
namespace InteractionBranchPreservation
namespace Stmt

/-- Source-budgeted successful-execution preservation for a compiled `if`. -/
theorem openRun_if_bounded_under_of_compileStmtFuel?
    {compilerFuel sourceFuel : Nat}
    {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {source : RunState} {tokens : List Word}
    {generatedCalls : List TypedCfgCompiler.DispatchSite}
    {policy :
      InteractionControlPreservation.OpenOutcome.StopPolicy}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
          (.if_ cond body) ctx supply entry input regular =
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
    (hBody :
      forall {output : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result}
        {afterCond : RunState},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            (supply + 1) (LabelSupply.label supply 0)
            { output with slots := output.slots.tail } regular =
          some bodyResult ->
        TypedCfgPreservation.BlocksInProgram bodyResult cfg ->
        TypedCfgPreservation.CallsInProgram bodyResult generatedCalls ->
        afterCond.returns = source.returns ->
        TypedCfgCompiler.Shape.SourceFrameFits
            { output with slots := output.slots.tail }
            afterCond.evm.stack.length ->
        bodyResult.requireFallthrough?
            { output with slots := output.slots.tail } =
          some () ->
        result.fallthrough? =
          some { output with slots := output.slots.tail } ->
        InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
          bodyResult cfg (LabelSupply.label supply 0) ctx
          regular afterCond tokens
          (InteractionSemantics.Block.openRun
            sourceProgram sourceFuel body afterCond)
          (InteractionStaticCost.blockBudget
            sourceProgram sourceFuel body)
          policy) :
    InteractionControlPreservation.OpenOutcome.BoundedExecPreservesUnder
      result cfg entry ctx regular source tokens
      (InteractionSemantics.Stmt.openRun
        sourceProgram (sourceFuel + 1) (.if_ cond body) source)
      (InteractionStaticCost.stmtBudget
        sourceProgram (sourceFuel + 1) (.if_ cond body))
      policy := by
  intro target hStateRel transcript sourceOutcome hSourceExec
  obtain
      ⟨output, _condition, bodyResult,
        hType, hSource, _hHead, hBodyCompile,
        hBodyRequire, hResult⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_if hCompile
  let bodyInput : TypedCfg.Shape :=
    { output with slots := output.slots.tail }
  have hFallthrough : result.fallthrough? = some bodyInput := by
    simp [bodyInput, hResult]
  have hBodyBlocks :
      TypedCfgPreservation.BlocksInProgram bodyResult cfg := by
    intro block hMem
    apply hBlocks block
    simp [hResult, hMem]
  have hBodyCalls :
      TypedCfgPreservation.CallsInProgram bodyResult generatedCalls := by
    intro site hMem
    apply hResultCalls site
    simp [hResult, hMem]
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := TypedCfgCompiler.Code.toCfg cond
      output := output
      term := .jumpi (LabelSupply.label supply 0) regular }
  have hFind : cfg.findBlock? entry = some generated := by
    exact hBlocks generated (by simp [generated, hResult])
  have hHeadRel :
      Simulation.Interaction.Rel
        (Condition.DoneRel
          (LabelSupply.label supply 0) regular tokens bodyInput)
        (InteractionSemantics.Code.openRunCondition cond source)
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target) := by
    simp only [
      TypedCfg.InteractionSemantics.Program.openStep,
      TypedCfg.Control.Program.step, hFind]
    simpa [generated, bodyInput] using
      (Condition.openRunCondition_jumpi_toCfg
        (entry := entry)
        (trueLabel := LabelSupply.label supply 0)
        (falseLabel := regular)
        hType hSource hFits hStateRel)
  have hHeadWithReturns :=
    Simulation.Interaction.Rel.strengthen_left hHeadRel
      (InteractionSemantics.Code.openRunCondition_returns cond source)
  have hSourceExec' :
      Simulation.Interaction.Executes
        (Simulation.Interaction.bind
          (InteractionSemantics.Code.openRunCondition cond source)
          (fun result =>
            if result.2 then
              InteractionSemantics.Block.openRun
                sourceProgram sourceFuel body result.1
            else
              Simulation.Interaction.pure
                (Structured.Outcome.regular result.1)))
        transcript (.ok sourceOutcome) := by
    simpa [
      InteractionSemantics.Stmt.openRun,
      EffectSemantics.Control.Stmt.run] using hSourceExec
  rcases Simulation.Interaction.Executes.bind_cases hSourceExec' with
    hSourceError |
      ⟨conditionResult, headTranscript, restTranscript,
        hTranscript, hConditionExec, hRestExec⟩
  · rcases hSourceError with ⟨err, hOutcome, _hConditionError⟩
    cases hOutcome
  · subst transcript
    obtain ⟨targetDone, hTargetHeadExec, hDone⟩ :=
      Simulation.Interaction.Rel.executes hHeadWithReturns hConditionExec
    cases targetDone with
    | error targetError =>
        cases hDone.1
    | ok targetOutcome =>
        rcases conditionResult with ⟨afterCond, condTrue⟩
        rcases hDone with ⟨hCondition, hReturns⟩
        cases hCondition with
        | ok hCondition =>
            rcases hCondition with
              ⟨targetAfterCond, hTargetOutcome,
                hAfterCondRel, hAfterCondFits⟩
            have hReturnsEq : afterCond.returns = source.returns := by
              simpa [InteractionSemantics.Code.ConditionReturnsEq] using hReturns
            cases condTrue with
            | false =>
                simp only [if_false] at hTargetOutcome hRestExec
                subst targetOutcome
                cases hRestExec
                have hWholeRel :
                    InteractionControlPreservation.OpenOutcome.Rel
                      result ctx regular source.returns tokens
                      (Structured.Outcome.regular afterCond)
                      (.jump regular targetAfterCond) := by
                  refine ⟨?_, ?_, ?_⟩
                  · exact
                      TypedCfgPreservation.OutcomeSimulation.Rel.regular_iff.mpr
                        ⟨rfl, hAfterCondRel⟩
                  · exact ⟨bodyInput, hFallthrough, hAfterCondFits⟩
                  · simpa [
                      InteractionControlPreservation.OpenOutcome.ActivationRestored]
                      using hReturnsEq
                have hContinuationExec :=
                  InteractionControlPreservation.OpenOutcome.afterOpenStepResultWithPolicy_executes_of_targetStopped
                    (cfg := cfg) (fuel := 0) (hStops hWholeRel)
                have hCombined :=
                  Simulation.Interaction.Executes.bind_ok
                    hTargetHeadExec hContinuationExec
                have hTargetExec :
                    Simulation.Interaction.Executes
                      (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                        policy cfg 1 entry target)
                      (headTranscript ++ [])
                      (.ok (.stopped 0 (.jump regular targetAfterCond))) := by
                  rw [show 1 = 0 + 1 by rfl,
                    TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_succ_eq_bind]
                  exact hCombined
                exact
                  ⟨1, 0, .jump regular targetAfterCond,
                    by
                      rw [InteractionStaticCost.stmtBudget_if_succ]
                      omega,
                    by simpa using hTargetExec, hWholeRel⟩
            | true =>
                simp only [if_true] at hTargetOutcome hRestExec
                subst targetOutcome
                obtain
                    ⟨bodyFuel, bodyRemaining, targetFinal, hBodyFuel,
                      hTargetBodyExec, hBodyRel⟩ :=
                  hBody hBodyCompile hBodyBlocks hBodyCalls hReturnsEq
                    hAfterCondFits hBodyRequire hFallthrough
                    targetAfterCond hAfterCondRel restTranscript
                    sourceOutcome hRestExec
                have hBodyShape :
                    TypedCfgPreservation.LabelShape
                      cfg (LabelSupply.label supply 0) bodyInput :=
                  TypedCfgPreservation.LabelShape.of_compileBlockFuel?
                    hBodyCompile hBodyBlocks
                have hBodyActivation :
                    TypedCfgPreservation.ActivationInput tokens bodyInput :=
                  (hActivation.code hType).tail
                    (TypedCfgCompilerFacts.Shape.requireSourceWords?_eq_some_iff.mp
                      hSource)
                have hNoStop :
                    policy (LabelSupply.label supply 0) targetAfterCond = false :=
                  (hBoundary.congr_returns hReturnsEq.symm).eq_false_of_stateRel
                    (scope := supply) (tag := 0)
                    (Nat.le_refl supply)
                    (hRegular.current_generated_ne (by omega))
                    hBodyShape hBodyActivation hAfterCondRel hAfterCondFits
                have hContinuationExec :
                    Simulation.Interaction.Executes
                      (TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop
                        policy cfg bodyFuel
                        (.jump (LabelSupply.label supply 0) targetAfterCond))
                      restTranscript
                      (.ok (.stopped bodyRemaining targetFinal)) := by
                  simpa [
                    TypedCfg.InteractionSemantics.Program.afterOpenStepResultWithStop,
                    hNoStop] using hTargetBodyExec
                have hCombined :=
                  Simulation.Interaction.Executes.bind_ok
                    hTargetHeadExec hContinuationExec
                have hTargetExec :
                    Simulation.Interaction.Executes
                      (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
                        policy cfg (bodyFuel + 1) entry target)
                      (headTranscript ++ restTranscript)
                      (.ok (.stopped bodyRemaining targetFinal)) := by
                  rw [
                    TypedCfg.InteractionSemantics.Program.openRunNResultWithStop_succ_eq_bind]
                  exact hCombined
                exact
                  ⟨bodyFuel + 1, bodyRemaining, targetFinal,
                    by
                      rw [InteractionStaticCost.stmtBudget_if_succ]
                      omega,
                    hTargetExec,
                    by
                      simpa [hReturnsEq] using
                        (InteractionControlPreservation.OpenOutcome.Rel.change_result_of_required_fallthrough
                          hBodyRequire hFallthrough hBodyRel)⟩

end Stmt
end InteractionBranchPreservation
end Structured
end EvmCompiler
