import EvmCompiler.Functions.AllocationInteractionControl
import EvmCompiler.Functions.AllocationInteractionCleanupResource
import EvmCompiler.Functions.AllocationInteractionExpressionResource
import EvmCompiler.Functions.AllocationInteractionLoop
import EvmCompiler.Functions.AllocationInteractionResourceComposition

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionControlResource

open AllocationInteractionRelation
open AllocationInteractionComposition
open AllocationInteractionFrame
open AllocationInteractionResource
open AllocationInteractionResourceComposition

/--
Lexical cleanup composes with the body effect only on regular completion;
abrupt outcomes retain the body's exact effect and skip cleanup.
-/
theorem block_of_components
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {contract : MemoryContract.Contract}
    {config : Config} {allocatorDepth : Nat}
    {lowerCtx : AllocationLowering.Ctx}
    {bodyState : AllocationLowering.State}
    {bodyLocals outerLocals : Locals.Ctx}
    {bodyPlan : Plan}
    {returns live bodyLive : List Functions.Name}
    {frameBase sourceFuel targetFuel : Nat}
    {entryMode : ActivationMode}
    {sourceCtx bodyCtx : Functions.Source.Ctx}
    {body : Functions.Block}
    {bodyCode : List Expressions.Stmt}
    {targetBlock : Expressions.Block}
    {source : SourceState} {target : TargetState}
    (hSourceScope : sourceCtx.scope = live)
    (hFinish :
      Locals.finishScoped outerLocals bodyLocals bodyCode = some targetBlock)
    (hCleanupFuel : 2 ≤ targetFuel - bodyCode.length)
    (hBody :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract lowerCtx bodyState bodyLocals bodyPlan
          returns bodyLive frameBase entryMode sourceCtx bodyCtx config
          allocatorDepth target)
        (Functions.InteractionSemantics.Block.openRun
          program sourceCtx sourceFuel body source)
        (Expressions.InteractionSemantics.Block.openRun
          expressions targetFuel { stmts := bodyCode } target)) :
    Simulation.Interaction.Rel
      (OpenResultRel config allocatorDepth entryMode target)
      (Functions.InteractionSemantics.Stmt.openRun
        program sourceCtx sourceFuel (.block body) source)
      (Expressions.InteractionSemantics.Block.openRun
        expressions targetFuel targetBlock target) := by
  obtain ⟨cleanup, hCleanup, hTargetShape⟩ :=
    AllocationInteractionCleanup.Plain.finishScoped_shape hFinish
  have hTargetBlock :
      targetBlock =
        { stmts := bodyCode ++ [Expressions.Stmt.code cleanup] } := by
    cases targetBlock
    cases hTargetShape
    rfl
  rw [Functions.InteractionSemantics.Stmt.openRun_block]
  rw [hTargetBlock,
    Expressions.InteractionSemantics.Block.openRun_append]
  apply Simulation.Interaction.Rel.bind_custom hBody
  intro sourceDone targetDone hDone
  rcases hDone with ⟨hSemantic, hEffect⟩
  cases hSemantic with
  | error hError =>
      cases hEffect with
      | error _hResourceError => exact .done (.error hError)
  | ok hResult =>
      cases hEffect with
      | ok hActivation =>
        cases hResult with
        | @regular sourceFinal targetMid bodyMode
            bodyInvariant sameFrame control =>
          have hActivation' :=
            hActivation.activation_of_not_halt (by
              intro kind hEq
              cases hEq)
          obtain ⟨targetFinal, hCleanupRun, hCleanupEffect⟩ :=
            AllocationInteractionCleanupResource.Plain.forward_allocator
              bodyInvariant hCleanup hActivation'.ready
          have hTargetCleanup :=
            Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code_done
              expressions (targetFuel - bodyCode.length) cleanup
              targetMid targetFinal hCleanupFuel hCleanupRun
          change
            Simulation.Interaction.Rel _
              (Simulation.Interaction.pure
                (Functions.Source.Effectful.Outcome.regular
                  (Functions.InteractionSemantics.stateModel.restrictTo
                    sourceCtx.scope sourceFinal), sourceCtx))
              (Expressions.InteractionSemantics.Block.openRun expressions
                (targetFuel - bodyCode.length)
                { stmts := [Expressions.Stmt.code cleanup] } targetMid)
          rw [hTargetCleanup]
          apply Simulation.Interaction.Rel.done
          apply Simulation.Interaction.ExceptRel.ok
          simpa [hSourceScope,
            Functions.InteractionSemantics.stateModel,
            Locals.InteractionSemantics.stateModel,
            Locals.Source.Effectful.Ordinary.stateModel,
            Locals.Source.Effectful.StateModel.restrictTo] using
            (OutcomeEffect.of_activation
              (ActivationEffect.trans hActivation'
                (ActivationEffect.of_allocatorEffect hCleanupEffect)))
        | @nonregular sourceOutcome targetOutcome finalCtx mode
            hNonregular sameFrame control state =>
          cases state with
          | regular state => exact False.elim (hNonregular rfl)
          | brk defined stackLength modeMatches stateRel =>
              change
                Simulation.Interaction.Rel _
                  (Simulation.Interaction.pure (_, sourceCtx))
                  (Simulation.Interaction.pure _)
              exact .done (.ok hActivation)
          | cont defined stackLength modeMatches stateRel =>
              change
                Simulation.Interaction.Rel _
                  (Simulation.Interaction.pure (_, sourceCtx))
                  (Simulation.Interaction.pure _)
              exact .done (.ok hActivation)
          | leave stateRel =>
              change
                Simulation.Interaction.Rel _
                  (Simulation.Interaction.pure (_, sourceCtx))
                  (Simulation.Interaction.pure _)
              exact .done (.ok hActivation)
          | halt kind stateRel =>
              change
                Simulation.Interaction.Rel _
                  (Simulation.Interaction.pure (_, sourceCtx))
                  (Simulation.Interaction.pure _)
              exact .done (.ok hActivation)

/-- The scoped-block interface combines the same semantic and resource run. -/
theorem blockScoped_of_components
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {contract : MemoryContract.Contract}
    {config : Config} {allocatorDepth : Nat}
    {lowerCtx : AllocationLowering.Ctx}
    {bodyState outerState : AllocationLowering.State}
    {bodyLocals outerLocals : Locals.Ctx}
    {bodyPlan outerPlan : Plan}
    {returns live bodyLive : List Functions.Name}
    {frameBase sourceFuel targetFuel : Nat}
    {entryMode : ActivationMode}
    {sourceCtx bodyCtx : Functions.Source.Ctx}
    {body : Functions.Block}
    {bodyCode : List Expressions.Stmt}
    {targetBlock : Expressions.Block}
    {source : SourceState} {target : TargetState}
    (hSourceScope : sourceCtx.scope = live)
    (hBodyCtx : bodyCtx = { sourceCtx with scope := bodyLive })
    (hBodyLive : bodyLive = Functions.Scope.Block.outEnv live body)
    (hControl :
      AllocationInteractionStatement.ControlScopesWithin
        returns live sourceCtx)
    (hOuter :
      AllocationContext.ActivationInvariant contract lowerCtx outerState
        outerLocals outerPlan live frameBase entryMode source target)
    (hExtends :
      AllocationLowering.StateExtends live outerState bodyState)
    (hPlanAgree : PlanAgreesOn bodyPlan outerPlan live)
    (hFinish :
      Locals.finishScoped outerLocals bodyLocals bodyCode = some targetBlock)
    (hCleanupFuel : 2 ≤ targetFuel - bodyCode.length)
    (hBody :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract lowerCtx bodyState bodyLocals bodyPlan
          returns bodyLive frameBase entryMode sourceCtx bodyCtx config
          allocatorDepth target)
        (Functions.InteractionSemantics.Block.openRun
          program sourceCtx sourceFuel body source)
        (Expressions.InteractionSemantics.Block.openRun
          expressions targetFuel { stmts := bodyCode } target)) :
    Simulation.Interaction.Rel
      (AllocationInteractionLoop.OpenScopedEffectResultRel
        (OutcomeEffect config allocatorDepth) contract lowerCtx outerState
        outerLocals outerPlan returns live frameBase entryMode sourceCtx target)
      (Functions.InteractionSemantics.Block.openRunScoped
        program sourceCtx body sourceFuel source)
      (Expressions.InteractionSemantics.Block.openRun
        expressions targetFuel targetBlock target) := by
  have hSemantic :=
    AllocationInteractionControl.blockScoped_of_components
      hSourceScope hBodyCtx hBodyLive hControl hOuter hExtends hPlanAgree
      hFinish hCleanupFuel
      (Simulation.Interaction.Rel.mono hBody (fun _ _ hDone => hDone.1))
  have hResourceOpen :=
    block_of_components hSourceScope hFinish hCleanupFuel hBody
  have hResourceOpen' :
      Simulation.Interaction.Rel
        (OpenResultRel config allocatorDepth entryMode target)
        (Simulation.Interaction.bind
          (Functions.InteractionSemantics.Block.openRunScoped
            program sourceCtx body sourceFuel source)
          (fun outcome => Simulation.Interaction.pure (outcome, sourceCtx)))
        (Expressions.InteractionSemantics.Block.openRun
          expressions targetFuel targetBlock target) := by
    simpa [Functions.InteractionSemantics.Stmt.openRun,
      Functions.Source.Canonical.Stmt.run,
      Functions.Source.Effectful.Control.Stmt.run] using hResourceOpen
  have hResourceErased :=
    Simulation.Interaction.Rel.bind_pure_left_inv hResourceOpen'
  have hResource :
      Simulation.Interaction.Rel
        (Simulation.Interaction.ExceptRel
          (fun left right : EVMException => left = right)
          (fun sourceFinal targetFinal =>
            OutcomeEffect config allocatorDepth entryMode target
              targetFinal.state sourceFinal.mode))
        (Functions.InteractionSemantics.Block.openRunScoped
          program sourceCtx body sourceFuel source)
        (Expressions.InteractionSemantics.Block.openRun
          expressions targetFuel targetBlock target) := by
    apply Simulation.Interaction.Rel.mono hResourceErased
    intro sourceDone targetDone hDone
    cases sourceDone with
    | error err =>
        cases hDone with
        | error hError => exact .error hError
    | ok outcome =>
        cases hDone with
        | ok hEffect => exact .ok hEffect
  exact Simulation.Interaction.Rel.inter hSemantic hResource

/-- Preserve condition resources and compose the selected true branch. -/
theorem if_of_components
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {contract : MemoryContract.Contract}
    {config : Config} {allocatorDepth : Nat}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Plan}
    {returns live : List Functions.Name}
    {frameBase sourceBodyFuel targetBodyFuel : Nat}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {cond : Functions.Expr 1} {body : Functions.Block}
    {targetCond : Expressions.Expr 1}
    {targetBody : Expressions.Block}
    {source : SourceState} {target : TargetState}
    (hInitial :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan live frameBase mode source target)
    (hCond :
      Simulation.Interaction.Rel
        (AllocationInteractionExpressionResource.ConditionOutcomeRel contract
          config allocatorDepth plan live frameBase mode target)
        (Functions.InteractionSemantics.Expr.openEvalCondition cond source)
        (Expressions.InteractionSemantics.Expr.openRunCondition
          targetCond target))
    (hVars :
      Simulation.Interaction.AllDone
        (Locals.InteractionStatePreservation.ResultVars
          (α := Bool) source)
        (Functions.InteractionSemantics.Expr.openEvalCondition cond source))
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          (sourceBodyFuel + 1) (.if_ cond body) source))
    (hTrue :
      ∀ {sourceAfter targetAfter},
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode sourceAfter targetAfter →
          AllocatorReady config allocatorDepth targetAfter →
          targetAfter.returns = target.returns →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
              sourceBodyFuel (.block body) sourceAfter) →
          Simulation.Interaction.Rel
            (RuntimeResultRel contract lowerCtx lowerState localsCtx plan
              returns live frameBase mode sourceCtx sourceCtx config
              allocatorDepth targetAfter)
            (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
              sourceBodyFuel (.block body) sourceAfter)
            (Expressions.InteractionSemantics.Block.openRun expressions
              targetBodyFuel targetBody targetAfter)) :
    Simulation.Interaction.Rel
      (RuntimeResultRel contract lowerCtx lowerState localsCtx plan returns live
        frameBase mode sourceCtx sourceCtx config allocatorDepth target)
      (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
        (sourceBodyFuel + 1) (.if_ cond body) source)
      (Expressions.InteractionSemantics.Block.openRun expressions
        (targetBodyFuel + 2)
        { stmts := [.if_ targetCond targetBody] } target) := by
  rw [Functions.InteractionSemantics.Stmt.openRun_if,
    Expressions.InteractionSemantics.Block.openRun_single_if]
  rw [Functions.InteractionSemantics.Stmt.openRun_if] at hSuccess
  have hCondSuccess := Simulation.Interaction.Successful.bind_inv hSuccess
  have hCondStrong :=
    Simulation.Interaction.Rel.strengthen_right
      (Simulation.Interaction.Rel.strengthen_left
        (Simulation.Interaction.Rel.strengthen_left hCond hVars) hCondSuccess)
      (Expressions.InteractionReturns.Expr.openRunCondition_returns
        targetCond target)
  apply Simulation.Interaction.Rel.bind_custom hCondStrong
  intro sourceDone targetDone hDone
  rcases hDone with
    ⟨⟨⟨hRelated, hVarsDone⟩, hContinuationSuccess⟩, hTargetReturns⟩
  cases hRelated with
  | error hError => exact .done ⟨.error hError, .error hError⟩
  | @ok sourceResult targetResult hResult =>
      rcases sourceResult with ⟨sourceAfter, sourceCondition⟩
      rcases targetResult with ⟨targetAfter, targetCondition⟩
      cases hResult.1.condition
      have hDefined : LiveDefined live sourceAfter :=
        hInitial.defined.congr_vars hVarsDone
      have hAfter :
          AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode sourceAfter targetAfter :=
        { compiler := hInitial.compiler
          planWF := hInitial.planWF
          defined := hDefined
          state := hResult.1.state
          stackLength :=
            (congrArg List.length hResult.1.stack).trans
              hInitial.stackLength }
      cases sourceCondition with
      | false =>
          apply Simulation.Interaction.Rel.done
          refine ⟨Simulation.Interaction.ExceptRel.ok ?_,
            Simulation.Interaction.ExceptRel.ok ?_⟩
          · exact ControlResultRel.regular hAfter (SameFrame.refl mode)
              (Functions.Source.Ctx.SameControl.refl sourceCtx)
          · exact OutcomeEffect.of_activation
              (ActivationEffect.of_allocatorEffect hResult.2)
      | true =>
          apply Simulation.Interaction.Rel.mono
            (hTrue hAfter hResult.2.ready
              (by
                simpa [Structured.InteractionSemantics.Code.ConditionReturnsEq]
                  using hTargetReturns)
              hContinuationSuccess)
          intro sourceFinal targetFinal hFinal
          rcases hFinal with ⟨hSemantic, hBodyEffect⟩
          cases hBodyEffect with
          | error hError => exact ⟨hSemantic, .error hError⟩
          | ok hEffect =>
              exact ⟨hSemantic, .ok
                (OutcomeEffect.prepend_activation
                  (ActivationEffect.of_allocatorEffect hResult.2)
                  (SameFrame.refl mode) hEffect)⟩

/-- Preserve one-value resources and compose the compiler-selected branch. -/
theorem switch_of_components
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {contract : MemoryContract.Contract}
    {config : Config} {allocatorDepth : Nat}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Plan}
    {returns live : List Functions.Name}
    {frameBase sourceBodyFuel targetBodyFuel : Nat}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {scrutinee : Functions.Expr 1}
    {sourceCases : List (Word × Functions.Block)}
    {sourceDefault : Option Functions.Block}
    {targetScrutinee : Expressions.Expr 1}
    {targetCases : List (Word × Expressions.Block)}
    {targetDefault : Option Expressions.Block}
    {source : SourceState} {target : TargetState}
    (hInitial :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan live frameBase mode source target)
    (hScrutinee :
      Simulation.Interaction.Rel
        (AllocationInteractionExpressionResource.ValueOutcomeRel contract
          config allocatorDepth plan live frameBase mode target)
        (Functions.InteractionSemantics.Expr.openEvalOne scrutinee source)
        (Expressions.InteractionSemantics.Expr.openRunOne
          targetScrutinee target))
    (hVars :
      Simulation.Interaction.AllDone
        (Locals.InteractionStatePreservation.ResultVars
          (α := Word) source)
        (Functions.InteractionSemantics.Expr.openEvalOne scrutinee source))
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          (sourceBodyFuel + 1)
          (.switch scrutinee sourceCases sourceDefault) source))
    (hSelection :
      ∀ value,
        AllocationInteractionControl.SwitchSelection sourceCases sourceDefault
          targetCases targetDefault value)
    (hSelected :
      ∀ {value sourceBody targetBody sourceAfter targetAfter},
        Functions.Source.Switch.select value sourceCases sourceDefault =
            some sourceBody →
        Expressions.EffectSemantics.Switch.select value targetCases
            targetDefault = some targetBody →
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode sourceAfter targetAfter →
        AllocatorReady config allocatorDepth targetAfter →
        targetAfter.returns = target.returns →
        Simulation.Interaction.Successful
          (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
            sourceBodyFuel (.block sourceBody) sourceAfter) →
          Simulation.Interaction.Rel
            (RuntimeResultRel contract lowerCtx lowerState localsCtx plan
              returns live frameBase mode sourceCtx sourceCtx config
              allocatorDepth targetAfter)
            (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
              sourceBodyFuel (.block sourceBody) sourceAfter)
            (Expressions.InteractionSemantics.Block.openRun expressions
              targetBodyFuel targetBody targetAfter)) :
    Simulation.Interaction.Rel
      (RuntimeResultRel contract lowerCtx lowerState localsCtx plan returns live
        frameBase mode sourceCtx sourceCtx config allocatorDepth target)
      (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
        (sourceBodyFuel + 1)
        (.switch scrutinee sourceCases sourceDefault) source)
      (Expressions.InteractionSemantics.Block.openRun expressions
        (targetBodyFuel + 2)
        { stmts := [.switch targetScrutinee targetCases targetDefault] }
        target) := by
  rw [Functions.InteractionSemantics.Stmt.openRun_switch,
    Expressions.InteractionSemantics.Block.openRun_single_switch]
  rw [Functions.InteractionSemantics.Stmt.openRun_switch] at hSuccess
  have hScrutineeSuccess :=
    Simulation.Interaction.Successful.bind_inv hSuccess
  have hScrutineeStrong :=
    Simulation.Interaction.Rel.strengthen_right
      (Simulation.Interaction.Rel.strengthen_left
        (Simulation.Interaction.Rel.strengthen_left hScrutinee hVars)
        hScrutineeSuccess)
      (Expressions.InteractionReturns.Expr.openRunOne_returns
        targetScrutinee target)
  apply Simulation.Interaction.Rel.bind_custom hScrutineeStrong
  intro sourceDone targetDone hDone
  rcases hDone with
    ⟨⟨⟨hRelated, hVarsDone⟩, hContinuationSuccess⟩, hTargetReturns⟩
  cases hRelated with
  | error hError => exact .done ⟨.error hError, .error hError⟩
  | @ok sourceResult targetResult hResult =>
      rcases sourceResult with ⟨sourceAfter, sourceValue⟩
      rcases targetResult with ⟨targetAfter, targetValue⟩
      cases hResult.1.value
      have hDefined : LiveDefined live sourceAfter :=
        hInitial.defined.congr_vars hVarsDone
      have hAfter :
          AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode sourceAfter targetAfter :=
        { compiler := hInitial.compiler
          planWF := hInitial.planWF
          defined := hDefined
          state := hResult.1.state
          stackLength :=
            (congrArg List.length hResult.1.stack).trans
              hInitial.stackLength }
      cases hSelection sourceValue with
      | none hSource hTarget =>
          simp only
          rw [hSource, hTarget]
          apply Simulation.Interaction.Rel.done
          refine ⟨Simulation.Interaction.ExceptRel.ok ?_,
            Simulation.Interaction.ExceptRel.ok ?_⟩
          · exact ControlResultRel.regular hAfter (SameFrame.refl mode)
              (Functions.Source.Ctx.SameControl.refl sourceCtx)
          · exact OutcomeEffect.of_activation
              (ActivationEffect.of_allocatorEffect hResult.2)
      | some sourceBody targetBody hSource hTarget =>
          simp only
          rw [hSource, hTarget]
          have hSelectedSuccess :
              Simulation.Interaction.Successful
                (Functions.InteractionSemantics.Stmt.openRun program
                  sourceCtx sourceBodyFuel (.block sourceBody)
                  sourceAfter) := by
            simpa [hSource] using hContinuationSuccess
          apply Simulation.Interaction.Rel.mono
            (hSelected hSource hTarget hAfter hResult.2.ready hTargetReturns
              hSelectedSuccess)
          intro sourceFinal targetFinal hFinal
          rcases hFinal with ⟨hSemantic, hBodyEffect⟩
          cases hBodyEffect with
          | error hError => exact ⟨hSemantic, .error hError⟩
          | ok hEffect =>
              exact ⟨hSemantic, .ok
                (OutcomeEffect.prepend_activation
                  (ActivationEffect.of_allocatorEffect hResult.2)
                  (SameFrame.refl mode) hEffect)⟩

end AllocationInteractionControlResource
end Functions
end EvmCompiler
