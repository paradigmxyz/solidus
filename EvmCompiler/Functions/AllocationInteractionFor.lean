import EvmCompiler.Functions.AllocationInteractionLoop
import EvmCompiler.Expressions.InteractionReturns

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionFor

open AllocationInteractionRelation
open AllocationInteractionComposition
open AllocationInteractionLoop

/-- A control result paired with one abstract target effect. -/
abbrev OpenControlEffectResultRel
    (Effect :
      ActivationMode → TargetState → TargetState → Locals.Source.Mode → Prop)
    (contract : MemoryContract.Contract)
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx) (plan : Plan)
    (returns regularLive : List Functions.Name) (frameBase : Nat)
    (entryMode : ActivationMode)
    (controlCtx regularCtx : Functions.Source.Ctx)
    (targetInitial : TargetState) :=
  fun sourceDone targetDone =>
    OpenControlResultRel contract lowerCtx lowerState localsCtx plan returns
        regularLive frameBase entryMode controlCtx regularCtx sourceDone
        targetDone ∧
      Simulation.Interaction.ExceptRel
        (fun left right : EVMException => left = right)
        (fun source target =>
          Effect entryMode targetInitial target.state source.1.mode)
        sourceDone targetDone

/--
Compose an already-related initializer and recursive loop with the exact outer
cleanup emitted for a Functions `for`. Compiler cursor decomposition remains
outside this theorem; this owner only sequences adjacent semantic components.
-/
theorem forward_effect_with
    {Effect :
      ActivationMode → TargetState → TargetState → Locals.Source.Mode → Prop}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {outerState loopState : AllocationLowering.State}
    {outerLocals initLocals : Locals.Ctx}
    {outerPlan loopPlan : Plan}
    {returns live loopLive : List Functions.Name}
    {frameBase sourceFuel slack : Nat}
    {entryMode : ActivationMode}
    {sourceCtx initCtx loopCtx postCtx bodyCtx : Functions.Source.Ctx}
    {init : Functions.Block} {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {targetInit targetPost targetBody : Expressions.Block}
    {targetCond : Expressions.Expr 1}
    {cleanup : Structured.Code}
    {source : SourceState} {target : TargetState}
    (sourceModel : AllocationInteractionLoop.SourceSemantics)
    (effectAlgebra : EffectAlgebra Effect)
    (hSourceScope : sourceCtx.scope = live)
    (hLoopLive : loopLive = Functions.Scope.Block.outEnv live init)
    (hInitCtx : initCtx = sourceCtx.withoutLoopControl)
    (hLoopCtx : loopCtx = { initCtx with scope := loopLive })
    (hPostCtx : postCtx = loopCtx.withoutLoopControl)
    (hBodyCtx : bodyCtx = loopCtx.withLoopControl loopLive loopLive)
    (hOuter :
      AllocationContext.ActivationInvariant contract lowerCtx outerState
        outerLocals outerPlan live frameBase entryMode source target)
    (hContext : effectAlgebra.Context entryMode)
    (hExtends :
      AllocationLowering.StateExtends live outerState loopState)
    (hPlanAgree : PlanAgreesOn loopPlan outerPlan live)
    (hCleanup :
      initLocals.cleanupTo? outerLocals.layout.length = some cleanup)
    (hTargetFuel : 1 ≤ sourceFuel + slack)
    (hInit :
      Simulation.Interaction.Rel
        (OpenControlEffectResultRel Effect contract lowerCtx loopState
          initLocals loopPlan returns loopLive frameBase entryMode initCtx
          loopCtx target)
        (sourceModel.openRunBlock
          program initCtx sourceFuel init source)
        (Expressions.InteractionSemantics.Block.openRun
          expressions (sourceFuel + slack) targetInit target))
    (hInitReturns :
      Simulation.Interaction.AllDone
        (Structured.InteractionReturns.OutcomeReturnsEq target.returns)
        (Expressions.InteractionSemantics.Block.openRun
          expressions (sourceFuel + slack) targetInit target))
    (hLoop :
      ∀ {mode sourceAfter targetAfter},
        effectAlgebra.Context mode →
        SameFrame entryMode mode →
        Effect entryMode target targetAfter .regular →
        targetAfter.returns = target.returns →
        AllocationContext.ActivationInvariant contract lowerCtx loopState
            initLocals loopPlan loopLive frameBase mode sourceAfter
              targetAfter →
          Simulation.Interaction.Successful
            (sourceModel.openRunForLoop program
              loopCtx cond postCtx post bodyCtx body sourceFuel sourceAfter) →
            Simulation.Interaction.Rel
              (OpenLoopEffectResultRel Effect contract lowerCtx loopState
                initLocals loopPlan returns loopLive frameBase mode loopCtx
                targetAfter)
              (sourceModel.openRunForLoop program
                loopCtx cond postCtx post bodyCtx body sourceFuel sourceAfter)
              (Expressions.InteractionSemantics.Stmt.openRunForLoop
                expressions (sourceFuel + slack) targetCond targetPost
                  targetBody targetAfter))
    (hCleanupEffect :
      ∀ {mode sourceMid targetMid targetFinal},
        AllocationContext.ActivationInvariant contract lowerCtx loopState
            initLocals loopPlan loopLive frameBase mode sourceMid targetMid →
          Effect entryMode target targetMid .regular →
          Structured.InteractionSemantics.Code.openRun cleanup targetMid =
            .done (.ok targetFinal) →
          Effect mode targetMid targetFinal .regular)
    (hSuccess :
      Simulation.Interaction.Successful
        (sourceModel.openRunStmt program sourceCtx
          (sourceFuel + 1) (.for_ init cond post body) source)) :
    Simulation.Interaction.Rel
      (OpenControlEffectResultRel Effect contract lowerCtx outerState
        outerLocals outerPlan returns live frameBase entryMode sourceCtx
        sourceCtx target)
      (sourceModel.openRunStmt program sourceCtx
        (sourceFuel + 1) (.for_ init cond post body) source)
      (Expressions.InteractionSemantics.Block.openRun expressions
        (sourceFuel + slack + 2)
        { stmts :=
            [.for_ targetInit targetCond targetPost targetBody,
              .code cleanup] }
        target) := by
  subst initCtx
  subst loopCtx
  subst postCtx
  subst bodyCtx
  let sourceNext :=
    fun result : Functions.InteractionSemantics.Outcome × Functions.Source.Ctx =>
      match result.1.mode with
      | .regular =>
          Simulation.Interaction.bind
            (sourceModel.openRunForLoop program
              result.2 cond result.2.withoutLoopControl post
              (result.2.withLoopControl result.2.scope result.2.scope)
              body sourceFuel result.1.state)
            (fun loopOutcome =>
              match loopOutcome.mode with
              | .regular =>
                  Simulation.Interaction.pure
                    (Functions.Source.Effectful.Outcome.regular
                      (loopOutcome.state.restrictTo sourceCtx.scope),
                      sourceCtx)
              | .brk | .cont =>
                  Simulation.Interaction.error
                    (.InvalidInstruction : EVMException)
              | .leave | .halt _ =>
                  Simulation.Interaction.pure (loopOutcome, sourceCtx))
      | .brk | .cont =>
          Simulation.Interaction.error (.InvalidInstruction : EVMException)
      | .leave | .halt _ =>
          Simulation.Interaction.pure (result.1, sourceCtx)
  let targetNext :=
    fun initOutcome : Expressions.InteractionSemantics.Outcome =>
      match initOutcome.mode with
      | .regular =>
          Simulation.Interaction.bind
            (Expressions.InteractionSemantics.Stmt.openRunForLoop
              expressions (sourceFuel + slack) targetCond targetPost
                targetBody initOutcome.state)
            (fun loopOutcome =>
              match loopOutcome.mode with
              | .regular =>
                  Expressions.InteractionSemantics.Block.openRun expressions
                    (sourceFuel + slack + 1)
                    { stmts := [.code cleanup] } loopOutcome.state
              | .brk | .cont | .leave | .halt _ =>
                  Simulation.Interaction.pure loopOutcome)
      | .brk | .cont =>
          Simulation.Interaction.error (.InvalidInstruction : EVMException)
      | .leave | .halt _ => Simulation.Interaction.pure initOutcome
  have hSourceShape :
      sourceModel.openRunStmt program sourceCtx
          (sourceFuel + 1) (.for_ init cond post body) source =
        Simulation.Interaction.bind
          (sourceModel.openRunBlock program
            sourceCtx.withoutLoopControl sourceFuel init source)
          sourceNext := by
    unfold AllocationInteractionLoop.SourceSemantics.openRunStmt
      Functions.Source.Canonical.Stmt.run
    simp only [Functions.Source.Effectful.Control.Stmt.run]
    rfl
  have hTargetShape :
      Expressions.InteractionSemantics.Block.openRun expressions
          (sourceFuel + slack + 2)
          { stmts :=
              [.for_ targetInit targetCond targetPost targetBody,
                .code cleanup] }
          target =
        Simulation.Interaction.bind
          (Expressions.InteractionSemantics.Block.openRun expressions
            (sourceFuel + slack) targetInit target)
          targetNext := by
    unfold Expressions.InteractionSemantics.Block.openRun
    simp only [Expressions.EffectSemantics.Control.Block.run,
      Expressions.EffectSemantics.Control.Stmt.run]
    change Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Expressions.InteractionSemantics.Block.openRun expressions
            (sourceFuel + slack) targetInit target) _)
        _ =
      Simulation.Interaction.bind
        (Expressions.InteractionSemantics.Block.openRun expressions
          (sourceFuel + slack) targetInit target)
        targetNext
    rw [Simulation.Interaction.bind_assoc]
    apply Simulation.Interaction.AllDone.bind_congr
      (Simulation.Interaction.AllDone.trivial
        (Expressions.InteractionSemantics.Block.openRun expressions
          (sourceFuel + slack) targetInit target))
    intro initOutcome _
    rcases initOutcome with ⟨initState, initMode⟩
    cases initMode with
    | regular =>
        simp only [targetNext]
        apply Simulation.Interaction.AllDone.bind_congr
          (Simulation.Interaction.AllDone.trivial
            (Expressions.InteractionSemantics.Stmt.openRunForLoop
              expressions (sourceFuel + slack) targetCond targetPost
                targetBody initState))
        intro loopOutcome _
        rcases loopOutcome with ⟨loopState, loopMode⟩
        cases loopMode with
        | regular =>
            unfold Expressions.InteractionSemantics.Block.openRun
            simp only [Expressions.EffectSemantics.Control.Block.run,
              Expressions.EffectSemantics.Control.Stmt.run]
        | brk => rfl
        | cont => rfl
        | leave => rfl
        | halt kind => rfl
    | brk => rfl
    | cont => rfl
    | leave => rfl
    | halt kind => rfl
  rw [hSourceShape] at hSuccess ⊢
  rw [hTargetShape]
  have hInitSuccess :=
    Simulation.Interaction.Successful.bind_inv hSuccess
  have hInitStrong :=
    Simulation.Interaction.Rel.strengthen_right
      (Simulation.Interaction.Rel.strengthen_left hInit hInitSuccess)
      hInitReturns
  apply Simulation.Interaction.Rel.bind_custom hInitStrong
  intro sourceDone targetDone hDone
  rcases hDone with
    ⟨⟨⟨hInitResult, hInitEffectRel⟩, hAfterInitSuccess⟩,
      hInitReturnsDone⟩
  cases hInitResult with
  | error hError => exact False.elim hAfterInitSuccess
  | @ok sourceResult targetOutcome hResult =>
      have hInitEffect :
          Effect entryMode target targetOutcome.state sourceResult.1.mode := by
        cases hInitEffectRel with
        | ok hEffect => exact hEffect
      cases hResult with
      | @regular initSource initTarget initMode hInitInvariant initFrame
          initControl =>
          let canonicalLoopCtx : Functions.Source.Ctx :=
            { sourceCtx.withoutLoopControl with scope := loopLive }
          have hLoopSuccess :=
            Simulation.Interaction.Successful.bind_inv hAfterInitSuccess
          have hLoopRunSuccess :
              Simulation.Interaction.Successful
                (sourceModel.openRunForLoop program
                  canonicalLoopCtx cond canonicalLoopCtx.withoutLoopControl
                  post (canonicalLoopCtx.withLoopControl loopLive loopLive)
                  body sourceFuel initSource) := by
            apply Simulation.Interaction.AllDone.mono hLoopSuccess
            intro outcome hOutcome
            cases outcome with
            | error err => exact hOutcome
            | ok value => trivial
          have hLoopRel :=
            hLoop (effectAlgebra.contextSame hContext initFrame) initFrame
              hInitEffect
              (by
                simpa [Structured.InteractionReturns.OutcomeReturnsEq] using
                  hInitReturnsDone)
              hInitInvariant (by
                simpa [canonicalLoopCtx] using hLoopRunSuccess)
          have hLoopStrong :=
            Simulation.Interaction.Rel.strengthen_left hLoopRel hLoopSuccess
          apply Simulation.Interaction.Rel.bind_custom hLoopStrong
          intro loopSourceDone loopTargetDone hLoopDone
          rcases hLoopDone with
            ⟨⟨hLoopResult, hLoopEffectRel⟩, hAfterLoopSuccess⟩
          cases hLoopResult with
          | error hError => exact False.elim hAfterLoopSuccess
          | @ok sourceLoopOutcome targetLoopOutcome hLoopRelated =>
              have hLoopEffect :
                  Effect initMode initTarget targetLoopOutcome.state
                    sourceLoopOutcome.mode := by
                cases hLoopEffectRel with
                | ok hEffect => exact hEffect
              have hThroughLoop :
                  Effect entryMode target targetLoopOutcome.state
                    sourceLoopOutcome.mode :=
                effectAlgebra.transSame hInitEffect initFrame hLoopEffect
              cases hLoopRelated with
              | @regular sourceFinal targetMid loopMode hLoopInvariant
                  loopFrame loopControl =>
                  have hSubset : ∀ name, name ∈ live → name ∈ loopLive := by
                    rw [hLoopLive]
                    intro name hName
                    exact Functions.Scope.Block.mem_outEnv hName
                  obtain ⟨transition, _hLayout⟩ :=
                    AllocationInteractionCleanup.Plain.transition_of_stateExtends
                      hLoopInvariant.compiler hOuter.compiler hSubset
                      (initFrame.trans loopFrame).symm rfl hExtends
                  obtain ⟨targetFinal, hCleanupRun, hFinalState,
                      hFinalLength⟩ :=
                    AllocationInteractionCleanup.Plain.forward_exact
                      hLoopInvariant transition hCleanup
                  have hCleanupBlock :=
                    Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code_done
                      expressions (sourceFuel + slack + 1) cleanup
                        targetMid targetFinal
                        (by omega) hCleanupRun
                  change Simulation.Interaction.Rel _
                    (Simulation.Interaction.pure
                      (Functions.Source.Effectful.Outcome.regular
                        (sourceFinal.restrictTo sourceCtx.scope), sourceCtx))
                    (Expressions.InteractionSemantics.Block.openRun
                      expressions (sourceFuel + slack + 1)
                        { stmts := [.code cleanup] } targetMid)
                  rw [hCleanupBlock]
                  apply Simulation.Interaction.Rel.done
                  constructor
                  · apply Simulation.Interaction.ExceptRel.ok
                    have hDefined :
                        LiveDefined live
                          (sourceFinal.restrictTo live) :=
                      hLoopInvariant.defined.restrictTo hSubset
                    have hFinalInvariant :
                        AllocationContext.ActivationInvariant contract lowerCtx
                          outerState outerLocals outerPlan live frameBase
                            entryMode
                          (sourceFinal.restrictTo live) targetFinal :=
                      { compiler := hOuter.compiler
                        planWF := hOuter.planWF
                        defined := hDefined
                        state := hFinalState.transport_plan hPlanAgree
                        stackLength := by simpa using hFinalLength }
                    simpa [hSourceScope,
                      Functions.InteractionSemantics.stateModel,
                      Locals.InteractionSemantics.stateModel,
                      Locals.Source.Effectful.Ordinary.stateModel,
                      Locals.Source.Effectful.StateModel.restrictTo] using
                      (ControlResultRel.regular hFinalInvariant
                        (SameFrame.refl entryMode)
                        (Functions.Source.Ctx.SameControl.refl sourceCtx))
                  · apply Simulation.Interaction.ExceptRel.ok
                    exact effectAlgebra.transSame hThroughLoop
                      (initFrame.trans loopFrame)
                      (hCleanupEffect hLoopInvariant hThroughLoop hCleanupRun)
              | @nonregular sourceOutcome targetOutcome finalCtx loopMode
                  hNonregular loopFrame loopControl loopStateRel =>
                  cases loopStateRel with
                  | regular state => exact False.elim (hNonregular rfl)
                  | brk defined stackLength modeMatches state =>
                      exact False.elim
                        (Simulation.Interaction.Successful.error_false
                          (.InvalidInstruction : EVMException)
                          hAfterLoopSuccess)
                  | cont defined stackLength modeMatches state =>
                      exact False.elim
                        (Simulation.Interaction.Successful.error_false
                          (.InvalidInstruction : EVMException)
                          hAfterLoopSuccess)
                  | leave state =>
                      apply Simulation.Interaction.Rel.done
                      constructor
                      · apply Simulation.Interaction.ExceptRel.ok
                        exact ControlResultRel.nonregular
                          (mode := loopMode) hNonregular
                          (initFrame.trans loopFrame)
                          (Functions.Source.Ctx.SameControl.refl sourceCtx)
                          (.leave state)
                      · exact Simulation.Interaction.ExceptRel.ok hThroughLoop
                  | halt kind state =>
                      apply Simulation.Interaction.Rel.done
                      constructor
                      · apply Simulation.Interaction.ExceptRel.ok
                        exact ControlResultRel.nonregular
                          (mode := loopMode) hNonregular
                          (initFrame.trans loopFrame)
                          (Functions.Source.Ctx.SameControl.refl sourceCtx)
                          (.halt kind { shared := state.shared })
                      · exact Simulation.Interaction.ExceptRel.ok hThroughLoop
      | @nonregular sourceOutcome targetOutcome finalCtx initMode
          hNonregular initFrame initControl initStateRel =>
          cases initStateRel with
          | regular state => exact False.elim (hNonregular rfl)
          | brk defined stackLength modeMatches state =>
              exact False.elim
                (Simulation.Interaction.Successful.error_false
                  (.InvalidInstruction : EVMException) hAfterInitSuccess)
          | cont defined stackLength modeMatches state =>
              exact False.elim
                (Simulation.Interaction.Successful.error_false
                  (.InvalidInstruction : EVMException) hAfterInitSuccess)
          | leave state =>
              apply Simulation.Interaction.Rel.done
              constructor
              · apply Simulation.Interaction.ExceptRel.ok
                exact ControlResultRel.nonregular
                  (mode := initMode) hNonregular initFrame
                  (Functions.Source.Ctx.SameControl.refl sourceCtx)
                  (.leave state)
              · exact Simulation.Interaction.ExceptRel.ok hInitEffect
          | halt kind state =>
              apply Simulation.Interaction.Rel.done
              constructor
              · apply Simulation.Interaction.ExceptRel.ok
                exact ControlResultRel.nonregular
                  (mode := initMode) hNonregular initFrame
                  (Functions.Source.Ctx.SameControl.refl sourceCtx)
                  (.halt kind { shared := state.shared })
              · exact Simulation.Interaction.ExceptRel.ok hInitEffect

/-- The semantic-only `for` theorem is the trivial-effect specialization. -/
theorem forward
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {outerState loopState : AllocationLowering.State}
    {outerLocals initLocals : Locals.Ctx}
    {outerPlan loopPlan : Plan}
    {returns live loopLive : List Functions.Name}
    {frameBase sourceFuel slack : Nat}
    {entryMode : ActivationMode}
    {sourceCtx initCtx loopCtx postCtx bodyCtx : Functions.Source.Ctx}
    {init : Functions.Block} {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {targetInit targetPost targetBody : Expressions.Block}
    {targetCond : Expressions.Expr 1}
    {cleanup : Structured.Code}
    {source : SourceState} {target : TargetState}
    (hSourceScope : sourceCtx.scope = live)
    (hLoopLive : loopLive = Functions.Scope.Block.outEnv live init)
    (hInitCtx : initCtx = sourceCtx.withoutLoopControl)
    (hLoopCtx : loopCtx = { initCtx with scope := loopLive })
    (hPostCtx : postCtx = loopCtx.withoutLoopControl)
    (hBodyCtx : bodyCtx = loopCtx.withLoopControl loopLive loopLive)
    (hOuter :
      AllocationContext.ActivationInvariant contract lowerCtx outerState
        outerLocals outerPlan live frameBase entryMode source target)
    (hExtends :
      AllocationLowering.StateExtends live outerState loopState)
    (hPlanAgree : PlanAgreesOn loopPlan outerPlan live)
    (hCleanup :
      initLocals.cleanupTo? outerLocals.layout.length = some cleanup)
    (hTargetFuel : 1 ≤ sourceFuel + slack)
    (hInit :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract lowerCtx loopState initLocals loopPlan
          returns loopLive frameBase entryMode initCtx loopCtx)
        (Functions.InteractionSemantics.Block.openRun
          program initCtx sourceFuel init source)
        (Expressions.InteractionSemantics.Block.openRun
          expressions (sourceFuel + slack) targetInit target))
    (hLoop :
      ∀ {mode sourceAfter targetAfter},
        AllocationContext.ActivationInvariant contract lowerCtx loopState
            initLocals loopPlan loopLive frameBase mode sourceAfter
              targetAfter →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Stmt.openRunForLoop program
              loopCtx cond postCtx post bodyCtx body sourceFuel sourceAfter) →
            Simulation.Interaction.Rel
              (OpenLoopResultRel contract lowerCtx loopState initLocals
                loopPlan returns loopLive frameBase mode loopCtx)
              (Functions.InteractionSemantics.Stmt.openRunForLoop program
                loopCtx cond postCtx post bodyCtx body sourceFuel sourceAfter)
              (Expressions.InteractionSemantics.Stmt.openRunForLoop
                expressions (sourceFuel + slack) targetCond targetPost
                  targetBody targetAfter))
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          (sourceFuel + 1) (.for_ init cond post body) source)) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract lowerCtx outerState outerLocals outerPlan
        returns live frameBase entryMode sourceCtx sourceCtx)
      (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
        (sourceFuel + 1) (.for_ init cond post body) source)
      (Expressions.InteractionSemantics.Block.openRun expressions
        (sourceFuel + slack + 2)
        { stmts :=
            [.for_ targetInit targetCond targetPost targetBody,
              .code cleanup] }
        target) := by
  have hInitEffect :
      Simulation.Interaction.Rel
        (OpenControlEffectResultRel (fun _ _ _ _ => True) contract lowerCtx
          loopState initLocals loopPlan returns loopLive frameBase entryMode
          initCtx loopCtx target)
        (Functions.InteractionSemantics.Block.openRun
          program initCtx sourceFuel init source)
        (Expressions.InteractionSemantics.Block.openRun
          expressions (sourceFuel + slack) targetInit target) := by
    apply Simulation.Interaction.Rel.mono hInit
    intro sourceDone targetDone hDone
    constructor
    · exact hDone
    · cases hDone with
      | error hError => exact .error hError
      | ok _ => exact .ok trivial
  have hLoopEffect :
      ∀ {mode sourceAfter targetAfter},
        True →
        SameFrame entryMode mode →
        True →
        targetAfter.returns = target.returns →
        AllocationContext.ActivationInvariant contract lowerCtx loopState
            initLocals loopPlan loopLive frameBase mode sourceAfter
              targetAfter →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Stmt.openRunForLoop program
              loopCtx cond postCtx post bodyCtx body sourceFuel sourceAfter) →
            Simulation.Interaction.Rel
              (OpenLoopEffectResultRel (fun _ _ _ _ => True) contract lowerCtx
                loopState initLocals loopPlan returns loopLive frameBase mode
                loopCtx targetAfter)
              (Functions.InteractionSemantics.Stmt.openRunForLoop program
                loopCtx cond postCtx post bodyCtx body sourceFuel sourceAfter)
              (Expressions.InteractionSemantics.Stmt.openRunForLoop
                expressions (sourceFuel + slack) targetCond targetPost
                  targetBody targetAfter) := by
    intro mode sourceAfter targetAfter _hContext _hSame _hPrefix _hReturns
      hInvariant hRunSuccess
    apply Simulation.Interaction.Rel.mono (hLoop hInvariant hRunSuccess)
    intro sourceDone targetDone hDone
    constructor
    · exact hDone
    · cases hDone with
      | error hError => exact .error hError
      | ok _ => exact .ok trivial
  apply Simulation.Interaction.Rel.mono
    (forward_effect_with (Effect := fun _ _ _ _ => True)
      AllocationInteractionLoop.SourceSemantics.ordinary
      EffectAlgebra.trivial
      hSourceScope hLoopLive hInitCtx hLoopCtx hPostCtx hBodyCtx hOuter
      (by simp [EffectAlgebra.trivial]) hExtends hPlanAgree hCleanup hTargetFuel
      hInitEffect
      (Expressions.InteractionReturns.Block.openRun_returns expressions
        (sourceFuel + slack) targetInit target)
      hLoopEffect
      (by intros; trivial) hSuccess)
  intro sourceDone targetDone hDone
  exact hDone.1

end AllocationInteractionFor
end Functions
end EvmCompiler
