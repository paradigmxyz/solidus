import EvmCompiler.Functions.AllocationInteractionCallResult
import EvmCompiler.Functions.AllocationInteractionCallTargets
import EvmCompiler.Functions.AllocationInteractionPreparedCall

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionCallStatement

open AllocationInteractionCall
open AllocationInteractionComposition
open AllocationInteractionRelation

/-- Return assignment changes only caller values; compiler context and stack
shape are inherited from the all-stack call boundary. -/
theorem callerInvariant_after_writeback
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Plan} {live : List Locals.Name}
    {frameBase : Nat}
    {sourceInitial sourceAfterArgs sourceReturned : SourceState}
    {targetInitial targetFinal : TargetState}
    {targets : List Locals.Name} {returnValues : List Word}
    {returnStore : Locals.Source.Store}
    (hInitial :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan live frameBase .stack sourceInitial targetInitial)
    (hArgsVars : sourceAfterArgs.vars = sourceInitial.vars)
    (hAssign :
      Functions.Source.Store.assignMany targets returnValues
          sourceAfterArgs.vars =
        some returnStore)
    (hFinalRel :
      ActivationStateRel contract plan live 0 frameBase .stack
        { shared := sourceReturned.shared, vars := returnStore } targetFinal)
    (hFinalStack : targetFinal.evm.stack.length = localsCtx.layout.length) :
    AllocationContext.ActivationInvariant contract lowerCtx lowerState
      localsCtx plan live frameBase .stack
      { shared := sourceReturned.shared, vars := returnStore } targetFinal := by
  refine
    { compiler := hInitial.compiler
      planWF := hInitial.planWF
      defined := ?_
      state := hFinalRel
      stackLength := hFinalStack }
  have hAfterArgsDefined : LiveDefined live sourceAfterArgs :=
    hInitial.defined.congr_vars hArgsVars
  have hAssigned := hAfterArgsDefined.assignMany_preserves hAssign
  simpa [Locals.Source.State.withVars] using hAssigned

/-- Restore an all-stack caller and execute the exact returned-value stores. -/
theorem returned_writeback
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {frameBase : Nat}
    {sourceAfterArgs sourceReturned : SourceState}
    {targetCaller callerBase callFinal : TargetState}
    {callerStack returnValues : List Word}
    {targets : List Locals.Name} {returnStore : Locals.Source.Store}
    {stores : Structured.Code}
    (hCallerRel :
      ActivationStateRel contract plan live 0 frameBase .stack
        sourceAfterArgs callerBase)
    (hCallerStack : callerBase.evm.stack = callerStack)
    (hCall :
      AllocationInteractionCallResult.CallResultRel contract targetCaller
        callerStack (.returned sourceReturned returnValues)
        (Structured.EffectSemantics.Outcome.regular callFinal))
    (hCallerContext :
      AllocationContext.ActivationExprContext lowerCtx lowerState localsCtx
        plan live .stack)
    (hCallerWF : plan.WellFormed)
    (hTargetsLive : forall target, target ∈ targets -> target ∈ live)
    (hTargetsNodup : targets.Nodup)
    (hAssign :
      Functions.Source.Store.assignMany targets returnValues
          sourceAfterArgs.vars =
        some returnStore)
    (hStores :
      AllocationLowering.lowerCallTargetsCode?
          lowerCtx lowerState targets.reverse targets.length =
        some stores) :
    ∃ targetFinal,
      Structured.InteractionSemantics.Code.openRun stores callFinal =
          .done (.ok targetFinal) ∧
        ActivationStateRel contract plan live 0 frameBase .stack
          { shared := sourceReturned.shared, vars := returnStore }
          targetFinal ∧
        targetFinal.evm.stack.length = callerBase.evm.stack.length := by
  cases hCall with
  | returned hShared hStack _hReturns hActiveNoWrap =>
      let callerReturned : SourceState :=
        { shared := sourceReturned.shared, vars := sourceAfterArgs.vars }
      have hResumed :
          ActivationStateRel contract plan live returnValues.reverse.length
            frameBase .stack callerReturned callFinal := by
        apply PreparedArguments.resume_after_stack_call hCallerRel
        · rfl
        · exact hShared
        · rw [hCallerStack]
          exact hStack
        · exact hActiveNoWrap
      have hAssignReverse :
          Functions.Source.Store.assignMany targets.reverse
              returnValues.reverse callerReturned.vars =
            some returnStore := by
        change
          Functions.Source.Store.assignMany targets.reverse
              returnValues.reverse sourceAfterArgs.vars =
            some returnStore
        exact Functions.Source.Store.assignMany_reverse_of_run
          hAssign hTargetsNodup
      have hStores' :
          AllocationLowering.lowerCallTargetsCode?
              lowerCtx lowerState targets.reverse
                returnValues.reverse.length =
            some stores := by
        simpa [Functions.Source.Store.assignMany_length hAssign] using hStores
      obtain ⟨targetFinal, hStoresRun, hFinalRel, hFinalStack⟩ :=
        CallTargets.forward hCallerContext hCallerWF
          (fun target hTarget => hTargetsLive target (by simpa using hTarget))
          hAssignReverse hStores' hResumed hStack
      refine ⟨targetFinal, hStoresRun, ?_, ?_⟩
      simpa [callerReturned, Locals.Source.State.withVars] using hFinalRel
      exact hFinalStack.trans (congrArg List.length hCallerStack).symm

/-- Bind an all-stack selected call to the canonical source continuation and
the exact compiler-emitted return stores. -/
theorem finish
    {contract : MemoryContract.Contract}
    {expressions : Expressions.Program}
    {storesFuel : Nat}
    {callerLowerCtx : AllocationLowering.Ctx}
    {callerLowerState : AllocationLowering.State}
    {callerLocalsCtx : Locals.Ctx}
    {callerPlan : Plan} {returns callerLive : List Locals.Name}
    {callerFrameBase : Nat}
    {controlCtx : Functions.Source.Ctx}
    {sourceInitial sourceAfterArgs : SourceState}
    {targetInitial targetCaller callerBase : TargetState}
    {callerStack : List Word}
    {targets : List Locals.Name} {stores : Structured.Code}
    {sourceCall : Simulation.Interaction EVMException
      Functions.InteractionSemantics.CallResult}
    {targetCall : Simulation.Interaction EVMException
      Expressions.InteractionSemantics.Outcome}
    (hInitial :
      AllocationContext.ActivationInvariant contract callerLowerCtx
        callerLowerState callerLocalsCtx callerPlan callerLive callerFrameBase
        .stack sourceInitial targetInitial)
    (hArgsVars : sourceAfterArgs.vars = sourceInitial.vars)
    (hCallerRel :
      ActivationStateRel contract callerPlan callerLive 0 callerFrameBase
        .stack sourceAfterArgs callerBase)
    (hInitialStack : targetInitial.evm.stack = callerStack)
    (hCallerStack : callerBase.evm.stack = callerStack)
    (hCall :
      Simulation.Interaction.Rel
        (AllocationInteractionCallResult.OpenCallResultRel
          contract targetCaller callerStack)
        sourceCall targetCall)
    (hFinish :
      Simulation.Interaction.AllDone
        (fun callDone =>
          match callDone with
          | .error _ => False
          | .ok callResult =>
              Simulation.Interaction.Successful
                (Functions.InteractionSemantics.Stmt.finishCall targets
                  controlCtx sourceAfterArgs callResult))
        sourceCall)
    (hTargetsLive : forall target, target ∈ targets -> target ∈ callerLive)
    (hTargetsNodup : targets.Nodup)
    (hStores :
      AllocationLowering.lowerCallTargetsCode?
          callerLowerCtx callerLowerState targets.reverse targets.length =
        some stores)
    (hStoresFuel : 2 <= storesFuel) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract callerLowerCtx callerLowerState
        callerLocalsCtx callerPlan returns callerLive callerFrameBase .stack
        controlCtx controlCtx)
      (Simulation.Interaction.bind sourceCall
        (Functions.InteractionSemantics.Stmt.finishCall targets controlCtx
          sourceAfterArgs))
      (Simulation.Interaction.bind targetCall
        (fun outcome =>
          match outcome.mode with
          | .regular =>
              Expressions.InteractionSemantics.Block.openRun expressions
                storesFuel { stmts := Locals.codeStmt stores } outcome.state
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure outcome)) := by
  have hStrong := Simulation.Interaction.Rel.strengthen_left hCall hFinish
  apply Simulation.Interaction.Rel.bind_custom hStrong
  intro sourceDone targetDone hDone
  rcases hDone with ⟨hRelated, hSuccessful⟩
  cases hRelated with
  | error _ => exact False.elim hSuccessful
  | ok hCallResult =>
      cases hCallResult with
      | @returned sourceReturned returnValues callFinal hShared hStack
          hReturns hActiveNoWrap =>
          obtain ⟨returnStore, hAssign⟩ :=
            Functions.InteractionSemantics.Stmt.successful_finishCall_returned
              targets controlCtx sourceAfterArgs _ _ hSuccessful
          have hAssign' :
              Functions.Source.Store.assignMany targets returnValues
                  sourceAfterArgs.vars =
                some returnStore := by
            simpa [Functions.InteractionSemantics.stateModel,
              Locals.InteractionSemantics.stateModel,
              Locals.Source.Effectful.Ordinary.stateModel,
              Locals.Source.Effectful.StateModel.vars,
              Locals.Source.Effectful.StateModel.source, id_eq] using hAssign
          have hCallResult :
              AllocationInteractionCallResult.CallResultRel
                contract targetCaller callerStack
                (.returned _ _) (.regular _) :=
            .returned hShared hStack hReturns hActiveNoWrap
          obtain ⟨targetFinal, hStoresRun, hFinalRel, hFinalStack⟩ :=
            returned_writeback hCallerRel hCallerStack hCallResult
              hInitial.compiler
              hInitial.planWF hTargetsLive hTargetsNodup hAssign' hStores
          have hInvariant :=
            callerInvariant_after_writeback hInitial hArgsVars hAssign'
              hFinalRel (hFinalStack.trans (by
                rw [hCallerStack, ← hInitialStack]
                exact hInitial.stackLength))
          have hTargetRun :=
            Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code_done
              expressions storesFuel stores _ targetFinal hStoresFuel
              hStoresRun
          simp only [Simulation.Interaction.bind_done_ok,
            Structured.Outcome.mode, Structured.Outcome.state,
            Locals.codeStmt]
          change Simulation.Interaction.Rel
            (OpenControlResultRel contract callerLowerCtx callerLowerState
              callerLocalsCtx callerPlan returns callerLive callerFrameBase
              .stack controlCtx controlCtx)
            (Functions.InteractionSemantics.Stmt.finishCall targets controlCtx
              sourceAfterArgs (.returned sourceReturned returnValues))
            (Expressions.InteractionSemantics.Block.openRun expressions
              storesFuel { stmts := [.code stores] } callFinal)
          rw [hTargetRun]
          simpa [Functions.InteractionSemantics.Stmt.finishCall, hAssign',
            Functions.InteractionSemantics.stateModel,
            Locals.InteractionSemantics.stateModel,
            Locals.Source.Effectful.Ordinary.stateModel,
            Locals.Source.Effectful.StateModel.source,
            Locals.Source.Effectful.StateModel.vars,
            Locals.Source.Effectful.StateModel.withSource, id_eq] using
            (Simulation.Interaction.Rel.done
              (Simulation.Interaction.ExceptRel.ok
                (ControlResultRel.regular hInvariant
                  (SameFrame.refl .stack)
                  (Functions.Source.Ctx.SameControl.refl controlCtx))))
      | @halted kind haltedState targetFinal hShared =>
          have hResult :
              OpenControlResultRel contract callerLowerCtx callerLowerState
                callerLocalsCtx callerPlan returns callerLive callerFrameBase
                .stack controlCtx controlCtx
                (.ok
                  (Functions.Source.Effectful.Outcome.halt kind haltedState,
                    controlCtx))
                (.ok (Structured.EffectSemantics.Outcome.halt kind
                  targetFinal)) :=
            Simulation.Interaction.ExceptRel.ok
              (ControlResultRel.nonregular (mode := .stack)
                (by simp) (SameFrame.refl .stack)
                (Functions.Source.Ctx.SameControl.refl controlCtx)
                (ActivationOutcomeRel.halt kind { shared := hShared }))
          simpa [Functions.InteractionSemantics.Stmt.finishCall,
            Simulation.Interaction.pure] using
            (Simulation.Interaction.Rel.done hResult)

end AllocationInteractionCallStatement
end Functions
end EvmCompiler
