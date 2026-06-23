import EvmCompiler.Functions.AllocationInteractionCleanup
import EvmCompiler.Functions.AllocationInteractionComposition
import EvmCompiler.Functions.AllocationInteractionSafeSemantics
import EvmCompiler.Locals.InteractionPreservation

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionControl

open AllocationInteractionRelation
open AllocationInteractionComposition
open AllocationInteractionStatement

/--
Close one lexical block around an already-related nested body. Regular
execution runs the exact compiler-emitted cleanup; abrupt execution skips it
and retains only the source control destination.
-/
theorem block_of_components
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {contract : MemoryContract.Contract}
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
    (hControl : ControlScopesWithin returns live sourceCtx)
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
        (OpenControlResultRel contract lowerCtx bodyState bodyLocals bodyPlan
          returns bodyLive frameBase entryMode sourceCtx bodyCtx)
        (Functions.InteractionSemantics.Block.openRun
          program sourceCtx sourceFuel body source)
        (Expressions.InteractionSemantics.Block.openRun
          expressions targetFuel { stmts := bodyCode } target)) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract lowerCtx outerState outerLocals outerPlan
        returns live frameBase entryMode sourceCtx sourceCtx)
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
  cases hDone with
  | error hError => exact .done (.error hError)
  | ok hResult =>
      cases hResult with
      | @regular sourceFinal targetMid bodyMode
          bodyInvariant sameFrame control =>
          have hSubset : ∀ name, name ∈ live → name ∈ bodyLive := by
            rw [hBodyLive]
            intro name hName
            exact Functions.Scope.Block.mem_outEnv hName
          obtain ⟨transition, _hLayout⟩ :=
            AllocationInteractionCleanup.Plain.transition_of_stateExtends
              bodyInvariant.compiler hOuter.compiler hSubset
              sameFrame.symm rfl hExtends
          obtain ⟨targetFinal, hCleanupRun, hFinalState, hFinalLength⟩ :=
            AllocationInteractionCleanup.Plain.forward_exact
              bodyInvariant transition hCleanup
          have hTargetCleanup :=
            Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code_done
              expressions (targetFuel - bodyCode.length) cleanup
              targetMid targetFinal hCleanupFuel hCleanupRun
          have hDefined :
              LiveDefined live (sourceFinal.restrictTo live) :=
            bodyInvariant.defined.restrictTo hSubset
          have hState :
              ActivationStateRel contract outerPlan live 0 frameBase
                entryMode (sourceFinal.restrictTo live) targetFinal :=
            hFinalState.transport_plan hPlanAgree
          have hFinalInvariant :
              AllocationContext.ActivationInvariant contract lowerCtx
                outerState outerLocals outerPlan live frameBase entryMode
                (sourceFinal.restrictTo live) targetFinal :=
            { compiler := hOuter.compiler
              planWF := hOuter.planWF
              defined := hDefined
              state := hState
              stackLength := by
                simpa using hFinalLength }
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
            (ControlResultRel.regular hFinalInvariant
              (SameFrame.refl entryMode)
              (Functions.Source.Ctx.SameControl.refl sourceCtx))
      | @nonregular sourceOutcome targetOutcome finalCtx mode
          hNonregular sameFrame control state =>
          have hReindexed :=
            ControlResultRel.reindex_nonregular_live
              (afterLive := live) state hNonregular
          have hAgree :=
            hPlanAgree.mono
              (hControl.outcomeLive_subset sourceOutcome.mode)
          have hOuterState := hReindexed.transport_plan hAgree
          cases hOuterState with
          | regular state => exact False.elim (hNonregular rfl)
          | brk defined stackLength modeMatches stateRel =>
              change
                Simulation.Interaction.Rel _
                  (Simulation.Interaction.pure (_, sourceCtx))
                  (Simulation.Interaction.pure _)
              apply Simulation.Interaction.Rel.done
              apply Simulation.Interaction.ExceptRel.ok
              exact ControlResultRel.nonregular (mode := mode) hNonregular
                sameFrame
                (Functions.Source.Ctx.SameControl.refl sourceCtx)
                (.brk defined stackLength modeMatches stateRel)
          | cont defined stackLength modeMatches stateRel =>
              change
                Simulation.Interaction.Rel _
                  (Simulation.Interaction.pure (_, sourceCtx))
                  (Simulation.Interaction.pure _)
              apply Simulation.Interaction.Rel.done
              apply Simulation.Interaction.ExceptRel.ok
              exact ControlResultRel.nonregular (mode := mode) hNonregular
                sameFrame
                (Functions.Source.Ctx.SameControl.refl sourceCtx)
                (.cont defined stackLength modeMatches stateRel)
          | leave stateRel =>
              change
                Simulation.Interaction.Rel _
                  (Simulation.Interaction.pure (_, sourceCtx))
                  (Simulation.Interaction.pure _)
              apply Simulation.Interaction.Rel.done
              apply Simulation.Interaction.ExceptRel.ok
              exact ControlResultRel.nonregular (mode := mode) hNonregular
                sameFrame
                (Functions.Source.Ctx.SameControl.refl sourceCtx)
                (.leave stateRel)
          | halt kind stateRel =>
              change
                Simulation.Interaction.Rel _
                  (Simulation.Interaction.pure (_, sourceCtx))
                  (Simulation.Interaction.pure _)
              apply Simulation.Interaction.Rel.done
              apply Simulation.Interaction.ExceptRel.ok
              exact ControlResultRel.nonregular (mode := mode) hNonregular
                sameFrame
                (Functions.Source.Ctx.SameControl.refl sourceCtx)
                (.halt kind stateRel)

/--
Close a lexical block compiled with the abrupt-aware Locals closure.  The
ordinary branch reuses `block_of_components`; the fallback branch derives the
source direct-exit fact from the checked lowering and therefore cannot expose
a regular source result that would require cleanup.
-/
theorem block_of_components_or_abrupt
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerStart bodyState outerState : AllocationLowering.State}
    {bodyLocals outerLocals : Locals.Ctx}
    {bodyPlan outerPlan : Plan}
    {returns live bodyLive : List Functions.Name}
    {frameBase sourceFuel targetFuel : Nat}
    {entryMode : ActivationMode}
    {sourceCtx bodyCtx : Functions.Source.Ctx}
    {body : Functions.Block}
    {loweredBody : Locals.Block}
    {bodyCode : List Expressions.Stmt}
    {targetBlock : Expressions.Block}
    {source : SourceState} {target : TargetState}
    (hSourceScope : sourceCtx.scope = live)
    (hBodyCtx : bodyCtx = { sourceCtx with scope := bodyLive })
    (hBodyLive : bodyLive = Functions.Scope.Block.outEnv live body)
    (hControl : ControlScopesWithin returns live sourceCtx)
    (hOuter :
      AllocationContext.ActivationInvariant contract lowerCtx outerState
        outerLocals outerPlan live frameBase entryMode source target)
    (hLower :
      AllocationLowering.lowerBlockOpen lowerCtx returns lowerStart body =
        some (loweredBody, bodyState))
    (hExtends :
      AllocationLowering.StateExtends live outerState bodyState)
    (hPlanAgree : PlanAgreesOn bodyPlan outerPlan live)
    (hFinish :
      Locals.finishScopedOrAbrupt outerLocals bodyLocals loweredBody bodyCode =
        some targetBlock)
    (hCleanupFuel : 2 ≤ targetFuel - bodyCode.length)
    (hBody :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract lowerCtx bodyState bodyLocals bodyPlan
          returns bodyLive frameBase entryMode sourceCtx bodyCtx)
        (Functions.InteractionSemantics.Block.openRun
          program sourceCtx sourceFuel body source)
        (Expressions.InteractionSemantics.Block.openRun
          expressions targetFuel { stmts := bodyCode } target)) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract lowerCtx outerState outerLocals outerPlan
        returns live frameBase entryMode sourceCtx sourceCtx)
      (Functions.InteractionSemantics.Stmt.openRun
        program sourceCtx sourceFuel (.block body) source)
      (Expressions.InteractionSemantics.Block.openRun
        expressions targetFuel targetBlock target) := by
  rcases Locals.finishScopedOrAbrupt_components hFinish with
    hRegular | ⟨_hNoCleanup, hLoweredExit, hTargetShape⟩
  · exact
      block_of_components hSourceScope hBodyCtx hBodyLive hControl hOuter
        hExtends hPlanAgree hRegular hCleanupFuel hBody
  · have hSourceExit :
        Functions.StmtList.hasDirectExit body.stmts = true := by
      calc
        Functions.StmtList.hasDirectExit body.stmts =
            Locals.StmtList.hasDirectExit loweredBody.stmts :=
          (AllocationLowering.lowerBlockOpen_hasDirectExit_eq hLower).symm
        _ = true := hLoweredExit
    have hNonregular :=
      Functions.InteractionSemantics.Abrupt.block_allDone_of_hasDirectExit
        program sourceCtx sourceFuel body source hSourceExit
    have hStrong :=
      Simulation.Interaction.Rel.strengthen_left hBody hNonregular
    have hStrong' :
        Simulation.Interaction.Rel
          (Simulation.Interaction.ExceptRel
            (fun left right : EVMException => left = right)
            (fun sourceResult targetResult =>
              ControlResultRel contract lowerCtx bodyState bodyLocals bodyPlan
                  returns bodyLive frameBase entryMode sourceCtx bodyCtx
                  sourceResult targetResult ∧
                sourceResult.1.mode ≠ .regular))
          (Functions.InteractionSemantics.Block.openRun
            program sourceCtx sourceFuel body source)
          (Expressions.InteractionSemantics.Block.openRun
            expressions targetFuel { stmts := bodyCode } target) := by
      apply Simulation.Interaction.Rel.mono hStrong
      intro sourceDone targetDone hDone
      rcases hDone with ⟨hRelated, hMode⟩
      cases hRelated with
      | error hError => exact .error hError
      | ok hResult => exact .ok ⟨hResult, hMode⟩
    rw [Functions.InteractionSemantics.Stmt.openRun_block]
    subst targetBlock
    conv_rhs =>
      rw [← Simulation.Interaction.bind_pure
        (Expressions.InteractionSemantics.Block.openRun expressions
          targetFuel { stmts := bodyCode } target)]
    apply Simulation.Interaction.Rel.bind hStrong'
    intro sourceResult targetResult hResult
    rcases hResult with ⟨hRelated, hMode⟩
    cases hRelated with
    | regular _hInvariant _hSameFrame _hControl =>
        exact False.elim (hMode rfl)
    | @nonregular sourceOutcome targetOutcome finalCtx mode
        hNonregular sameFrame _control state =>
        have hReindexed :=
          ControlResultRel.reindex_nonregular_live
            (afterLive := live) state hNonregular
        have hAgree :=
          hPlanAgree.mono
            (hControl.outcomeLive_subset sourceOutcome.mode)
        have hOuterState := hReindexed.transport_plan hAgree
        cases hOuterState with
        | regular state => exact False.elim (hNonregular rfl)
        | brk defined stackLength modeMatches stateRel =>
            exact Simulation.Interaction.Rel.done
              (.ok (ControlResultRel.nonregular (mode := mode) hNonregular
                sameFrame
                (Functions.Source.Ctx.SameControl.refl sourceCtx)
                (.brk defined stackLength modeMatches stateRel)))
        | cont defined stackLength modeMatches stateRel =>
            exact Simulation.Interaction.Rel.done
              (.ok (ControlResultRel.nonregular (mode := mode) hNonregular
                sameFrame
                (Functions.Source.Ctx.SameControl.refl sourceCtx)
                (.cont defined stackLength modeMatches stateRel)))
        | leave stateRel =>
            exact Simulation.Interaction.Rel.done
              (.ok (ControlResultRel.nonregular (mode := mode) hNonregular
                sameFrame
                (Functions.Source.Ctx.SameControl.refl sourceCtx)
                (.leave stateRel)))
        | halt kind stateRel =>
            exact Simulation.Interaction.Rel.done
              (.ok (ControlResultRel.nonregular (mode := mode) hNonregular
                sameFrame
                (Functions.Source.Ctx.SameControl.refl sourceCtx)
                (.halt kind stateRel)))

/-- The same lexical-block theorem with its constant source context erased. -/
theorem blockScoped_of_components
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {contract : MemoryContract.Contract}
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
    (hControl : ControlScopesWithin returns live sourceCtx)
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
        (OpenControlResultRel contract lowerCtx bodyState bodyLocals bodyPlan
          returns bodyLive frameBase entryMode sourceCtx bodyCtx)
        (Functions.InteractionSemantics.Block.openRun
          program sourceCtx sourceFuel body source)
        (Expressions.InteractionSemantics.Block.openRun
          expressions targetFuel { stmts := bodyCode } target)) :
    Simulation.Interaction.Rel
      (Simulation.Interaction.ExceptRel
        (fun left right : EVMException => left = right)
        (fun sourceOutcome targetOutcome =>
          ControlResultRel contract lowerCtx outerState outerLocals outerPlan
            returns live frameBase entryMode sourceCtx sourceCtx
            (sourceOutcome, sourceCtx) targetOutcome))
      (Functions.InteractionSemantics.Block.openRunScoped
        program sourceCtx body sourceFuel source)
      (Expressions.InteractionSemantics.Block.openRun
        expressions targetFuel targetBlock target) := by
  have hOpen :=
    block_of_components hSourceScope hBodyCtx hBodyLive hControl hOuter
      hExtends hPlanAgree hFinish hCleanupFuel hBody
  have hOpen' :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract lowerCtx outerState outerLocals
          outerPlan returns live frameBase entryMode sourceCtx sourceCtx)
        (Simulation.Interaction.bind
          (Functions.InteractionSemantics.Block.openRunScoped
            program sourceCtx body sourceFuel source)
          (fun outcome =>
            Simulation.Interaction.pure (outcome, sourceCtx)))
        (Expressions.InteractionSemantics.Block.openRun
          expressions targetFuel targetBlock target) := by
    simpa [Functions.InteractionSemantics.Stmt.openRun,
      Functions.Source.Canonical.Stmt.run,
      Functions.Source.Effectful.Control.Stmt.run,
      Functions.InteractionSemantics.Block.openRunScoped,
      Functions.Source.Canonical.Block.runScoped] using hOpen
  have hErased :=
    Simulation.Interaction.Rel.bind_pure_left_inv hOpen'
  apply Simulation.Interaction.Rel.mono hErased
  intro leftDone rightDone hDone
  cases leftDone with
  | error err =>
      cases hDone with
      | error hError => exact .error hError
  | ok outcome =>
      cases hDone with
      | ok hResult => exact .ok hResult

/-- Preserve a conditional from condition truth and the selected body theorem. -/
theorem if_of_components
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {contract : MemoryContract.Contract}
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
        (Simulation.Interaction.ExceptRel
          (fun left right : EVMException => left = right)
          (ActivationConditionResultRel contract plan live frameBase mode
            target))
        (Functions.InteractionSemantics.Expr.openEvalCondition cond source)
        (Expressions.InteractionSemantics.Expr.openRunCondition
          targetCond target))
    (hVars :
      Simulation.Interaction.AllDone
        (Locals.InteractionStatePreservation.ResultVars
          (α := Bool) source)
        (Functions.InteractionSemantics.Expr.openEvalCondition cond source))
    (hTrue :
      ∀ {sourceAfter targetAfter},
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode sourceAfter targetAfter →
          Simulation.Interaction.Rel
            (OpenControlResultRel contract lowerCtx lowerState localsCtx plan
              returns live frameBase mode sourceCtx sourceCtx)
            (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
              sourceBodyFuel (.block body) sourceAfter)
            (Expressions.InteractionSemantics.Block.openRun expressions
              targetBodyFuel targetBody targetAfter)) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract lowerCtx lowerState localsCtx plan
        returns live frameBase mode sourceCtx sourceCtx)
      (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
        (sourceBodyFuel + 1) (.if_ cond body) source)
      (Expressions.InteractionSemantics.Block.openRun expressions
        (targetBodyFuel + 2)
        { stmts := [.if_ targetCond targetBody] } target) := by
  rw [Functions.InteractionSemantics.Stmt.openRun_if,
    Expressions.InteractionSemantics.Block.openRun_single_if]
  have hCondStrong :=
    Simulation.Interaction.Rel.strengthen_left hCond hVars
  apply Simulation.Interaction.Rel.bind_custom hCondStrong
  intro sourceDone targetDone hDone
  rcases hDone with ⟨hRelated, hVarsDone⟩
  cases hRelated with
  | error hError => exact .done (.error hError)
  | @ok sourceResult targetResult hResult =>
      rcases sourceResult with ⟨sourceAfter, sourceCondition⟩
      rcases targetResult with ⟨targetAfter, targetCondition⟩
      cases hResult.condition
      have hDefined : LiveDefined live sourceAfter :=
        hInitial.defined.congr_vars hVarsDone
      have hAfter :
          AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode sourceAfter targetAfter :=
        { compiler := hInitial.compiler
          planWF := hInitial.planWF
          defined := hDefined
          state := hResult.state
          stackLength :=
            (congrArg List.length hResult.stack).trans
              hInitial.stackLength }
      cases sourceCondition with
      | false =>
          apply Simulation.Interaction.Rel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact ControlResultRel.regular hAfter (SameFrame.refl mode)
            (Functions.Source.Ctx.SameControl.refl sourceCtx)
      | true => exact hTrue hAfter

/-- Preserve a successful conditional while exposing source success only for
the dynamically selected true branch. -/
theorem if_of_components_successful
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {contract : MemoryContract.Contract}
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
        (Simulation.Interaction.ExceptRel
          (fun left right : EVMException => left = right)
          (ActivationConditionResultRel contract plan live frameBase mode
            target))
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
          targetAfter.returns = target.returns →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
              sourceBodyFuel (.block body) sourceAfter) →
          Simulation.Interaction.Rel
            (OpenControlResultRel contract lowerCtx lowerState localsCtx plan
              returns live frameBase mode sourceCtx sourceCtx)
            (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
              sourceBodyFuel (.block body) sourceAfter)
            (Expressions.InteractionSemantics.Block.openRun expressions
              targetBodyFuel targetBody targetAfter)) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract lowerCtx lowerState localsCtx plan
        returns live frameBase mode sourceCtx sourceCtx)
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
  | error hError => exact .done (.error hError)
  | @ok sourceResult targetResult hResult =>
      rcases sourceResult with ⟨sourceAfter, sourceCondition⟩
      rcases targetResult with ⟨targetAfter, targetCondition⟩
      cases hResult.condition
      have hDefined : LiveDefined live sourceAfter :=
        hInitial.defined.congr_vars hVarsDone
      have hAfter :
          AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode sourceAfter targetAfter :=
        { compiler := hInitial.compiler
          planWF := hInitial.planWF
          defined := hDefined
          state := hResult.state
          stackLength :=
            (congrArg List.length hResult.stack).trans
              hInitial.stackLength }
      cases sourceCondition with
      | false =>
          apply Simulation.Interaction.Rel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact ControlResultRel.regular hAfter (SameFrame.refl mode)
            (Functions.Source.Ctx.SameControl.refl sourceCtx)
      | true =>
          exact hTrue hAfter
            (by
              simpa [Structured.InteractionSemantics.Code.ConditionReturnsEq]
                using hTargetReturns)
            hContinuationSuccess

/-- Preserve a conditional while carrying ordinary and guarded success into
the exact dynamically selected true branch. -/
theorem if_of_components_executionSafe
    {program : Functions.Program} {expressions : Expressions.Program}
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State} {localsCtx : Locals.Ctx}
    {plan : Plan} {returns live : List Functions.Name}
    {frameBase sourceBodyFuel targetBodyFuel : Nat}
    {mode : ActivationMode} {sourceCtx : Functions.Source.Ctx}
    {cond : Functions.Expr 1} {body : Functions.Block}
    {targetCond : Expressions.Expr 1} {targetBody : Expressions.Block}
    {source : SourceState} {target : TargetState}
    (hInitial : AllocationContext.ActivationInvariant contract lowerCtx
      lowerState localsCtx plan live frameBase mode source target)
    (hCond :
      Simulation.Interaction.Rel
        (Simulation.Interaction.ExceptRel
          (fun left right : EVMException => left = right)
          (ActivationConditionResultRel contract plan live frameBase mode
            target))
        (Functions.InteractionSemantics.Expr.openEvalCondition cond source)
        (Expressions.InteractionSemantics.Expr.openRunCondition
          targetCond target))
    (hVars : Simulation.Interaction.AllDone
      (Locals.InteractionStatePreservation.ResultVars (α := Bool) source)
      (Functions.InteractionSemantics.Expr.openEvalCondition cond source))
    (hSuccess : Simulation.Interaction.Successful
      (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
        (sourceBodyFuel + 1) (.if_ cond body) source))
    (hSafeSuccess : Simulation.Interaction.Successful
      (AllocationInteractionSafeSemantics.Stmt.openRun contract program
        sourceCtx (sourceBodyFuel + 1) (.if_ cond body) source))
    (hSafeConditionOrdinary :
      AllocationInteractionSafeSemantics.Expr.openEvalCondition
          contract cond source =
        Functions.InteractionSemantics.Expr.openEvalCondition cond source)
    (hTrue :
      ∀ {sourceAfter targetAfter},
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode sourceAfter targetAfter →
          targetAfter.returns = target.returns →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
              sourceBodyFuel (.block body) sourceAfter) →
          Simulation.Interaction.Successful
            (AllocationInteractionSafeSemantics.Stmt.openRun contract program
              sourceCtx sourceBodyFuel (.block body) sourceAfter) →
          Simulation.Interaction.Rel
            (OpenControlResultRel contract lowerCtx lowerState localsCtx plan
              returns live frameBase mode sourceCtx sourceCtx)
            (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
              sourceBodyFuel (.block body) sourceAfter)
            (Expressions.InteractionSemantics.Block.openRun expressions
              targetBodyFuel targetBody targetAfter)) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract lowerCtx lowerState localsCtx plan
        returns live frameBase mode sourceCtx sourceCtx)
      (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
        (sourceBodyFuel + 1) (.if_ cond body) source)
      (Expressions.InteractionSemantics.Block.openRun expressions
        (targetBodyFuel + 2) { stmts := [.if_ targetCond targetBody] }
        target) := by
  rw [Functions.InteractionSemantics.Stmt.openRun_if,
    Expressions.InteractionSemantics.Block.openRun_single_if]
  rw [Functions.InteractionSemantics.Stmt.openRun_if] at hSuccess
  rw [AllocationInteractionSafeSemantics.Stmt.openRun_if] at hSafeSuccess
  have hCondSuccess := Simulation.Interaction.Successful.bind_inv hSuccess
  have hSafeCondSuccess :=
    Simulation.Interaction.Successful.bind_inv hSafeSuccess
  rw [hSafeConditionOrdinary] at hSafeCondSuccess
  have hCondStrong :=
    Simulation.Interaction.Rel.strengthen_right
      (Simulation.Interaction.Rel.strengthen_left
        (Simulation.Interaction.Rel.strengthen_left
          (Simulation.Interaction.Rel.strengthen_left hCond hVars)
          hCondSuccess)
        hSafeCondSuccess)
      (Expressions.InteractionReturns.Expr.openRunCondition_returns
        targetCond target)
  apply Simulation.Interaction.Rel.bind_custom hCondStrong
  intro sourceDone targetDone hDone
  rcases hDone with
    ⟨⟨⟨⟨hRelated, hVarsDone⟩, hContinuationSuccess⟩,
      hContinuationSafe⟩, hTargetReturns⟩
  cases hRelated with
  | error hError => exact .done (.error hError)
  | @ok sourceResult targetResult hResult =>
      rcases sourceResult with ⟨sourceAfter, sourceCondition⟩
      rcases targetResult with ⟨targetAfter, targetCondition⟩
      cases hResult.condition
      have hDefined : LiveDefined live sourceAfter :=
        hInitial.defined.congr_vars hVarsDone
      have hAfter : AllocationContext.ActivationInvariant contract lowerCtx
          lowerState localsCtx plan live frameBase mode sourceAfter
            targetAfter :=
        { compiler := hInitial.compiler
          planWF := hInitial.planWF
          defined := hDefined
          state := hResult.state
          stackLength :=
            (congrArg List.length hResult.stack).trans hInitial.stackLength }
      cases sourceCondition with
      | false =>
          apply Simulation.Interaction.Rel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact ControlResultRel.regular hAfter (SameFrame.refl mode)
            (Functions.Source.Ctx.SameControl.refl sourceCtx)
      | true =>
          exact hTrue hAfter
            (by
              simpa [Structured.InteractionSemantics.Code.ConditionReturnsEq]
                using hTargetReturns)
            hContinuationSuccess hContinuationSafe

/-- Exact source/target branch selected by one compiled switch. -/
inductive SwitchSelection
    (sourceCases : List (Word × Functions.Block))
    (sourceDefault : Option Functions.Block)
    (targetCases : List (Word × Expressions.Block))
    (targetDefault : Option Expressions.Block)
    (value : Word) : Prop where
  | none
      (source :
        Functions.Source.Switch.select value sourceCases sourceDefault = none)
      (target :
        Expressions.EffectSemantics.Switch.select value targetCases
          targetDefault = none) :
      SwitchSelection sourceCases sourceDefault targetCases targetDefault value
  | some
      (sourceBody : Functions.Block) (targetBody : Expressions.Block)
      (source :
        Functions.Source.Switch.select value sourceCases sourceDefault =
          some sourceBody)
      (target :
        Expressions.EffectSemantics.Switch.select value targetCases
          targetDefault = some targetBody) :
      SwitchSelection sourceCases sourceDefault targetCases targetDefault value

/-- Preserve a switch from one-value evaluation and exact branch selection. -/
theorem switch_of_components
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {contract : MemoryContract.Contract}
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
        (Simulation.Interaction.ExceptRel
          (fun left right : EVMException => left = right)
          (ActivationValueResultRel contract plan live frameBase mode target))
        (Functions.InteractionSemantics.Expr.openEvalOne scrutinee source)
        (Expressions.InteractionSemantics.Expr.openRunOne
          targetScrutinee target))
    (hVars :
      Simulation.Interaction.AllDone
        (Locals.InteractionStatePreservation.ResultVars
          (α := Word) source)
        (Functions.InteractionSemantics.Expr.openEvalOne scrutinee source))
    (hSelection :
      ∀ value,
        SwitchSelection sourceCases sourceDefault targetCases targetDefault
          value)
    (hSelected :
      ∀ {value sourceBody targetBody sourceAfter targetAfter},
        Functions.Source.Switch.select value sourceCases sourceDefault =
            some sourceBody →
        Expressions.EffectSemantics.Switch.select value targetCases
            targetDefault =
          some targetBody →
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode sourceAfter targetAfter →
          Simulation.Interaction.Rel
            (OpenControlResultRel contract lowerCtx lowerState localsCtx plan
              returns live frameBase mode sourceCtx sourceCtx)
            (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
              sourceBodyFuel (.block sourceBody) sourceAfter)
            (Expressions.InteractionSemantics.Block.openRun expressions
              targetBodyFuel targetBody targetAfter)) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract lowerCtx lowerState localsCtx plan
        returns live frameBase mode sourceCtx sourceCtx)
      (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
        (sourceBodyFuel + 1)
        (.switch scrutinee sourceCases sourceDefault) source)
      (Expressions.InteractionSemantics.Block.openRun expressions
        (targetBodyFuel + 2)
        { stmts :=
            [.switch targetScrutinee targetCases targetDefault] }
        target) := by
  rw [Functions.InteractionSemantics.Stmt.openRun_switch,
    Expressions.InteractionSemantics.Block.openRun_single_switch]
  have hScrutineeStrong :=
    Simulation.Interaction.Rel.strengthen_left hScrutinee hVars
  apply Simulation.Interaction.Rel.bind_custom hScrutineeStrong
  intro sourceDone targetDone hDone
  rcases hDone with ⟨hRelated, hVarsDone⟩
  cases hRelated with
  | error hError => exact .done (.error hError)
  | @ok sourceResult targetResult hResult =>
      rcases sourceResult with ⟨sourceAfter, sourceValue⟩
      rcases targetResult with ⟨targetAfter, targetValue⟩
      cases hResult.value
      have hDefined : LiveDefined live sourceAfter :=
        hInitial.defined.congr_vars hVarsDone
      have hAfter :
          AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode sourceAfter targetAfter :=
        { compiler := hInitial.compiler
          planWF := hInitial.planWF
          defined := hDefined
          state := hResult.state
          stackLength :=
            (congrArg List.length hResult.stack).trans
              hInitial.stackLength }
      cases hSelection sourceValue with
      | none hSource hTarget =>
          simp only
          rw [hSource, hTarget]
          apply Simulation.Interaction.Rel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact ControlResultRel.regular hAfter (SameFrame.refl mode)
            (Functions.Source.Ctx.SameControl.refl sourceCtx)
      | some sourceBody targetBody hSource hTarget =>
          simp only
          rw [hSource, hTarget]
          exact hSelected hSource hTarget hAfter

/-- Preserve a successful switch while exposing success only for its selected
source/target branch pair. -/
theorem switch_of_components_successful
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Plan}
    {returns live : List Functions.Name}
    {frameBase sourceBodyFuel targetBodyFuel : Nat}
    {mode : ActivationMode} {sourceCtx : Functions.Source.Ctx}
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
        (Simulation.Interaction.ExceptRel
          (fun left right : EVMException => left = right)
          (ActivationValueResultRel contract plan live frameBase mode target))
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
        SwitchSelection sourceCases sourceDefault targetCases targetDefault
          value)
    (hSelected :
      ∀ {value sourceBody targetBody sourceAfter targetAfter},
        Functions.Source.Switch.select value sourceCases sourceDefault =
            some sourceBody →
        Expressions.EffectSemantics.Switch.select value targetCases
            targetDefault = some targetBody →
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode sourceAfter targetAfter →
        targetAfter.returns = target.returns →
        Simulation.Interaction.Successful
          (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
            sourceBodyFuel (.block sourceBody) sourceAfter) →
        Simulation.Interaction.Rel
          (OpenControlResultRel contract lowerCtx lowerState localsCtx plan
            returns live frameBase mode sourceCtx sourceCtx)
          (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
            sourceBodyFuel (.block sourceBody) sourceAfter)
          (Expressions.InteractionSemantics.Block.openRun expressions
            targetBodyFuel targetBody targetAfter)) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract lowerCtx lowerState localsCtx plan
        returns live frameBase mode sourceCtx sourceCtx)
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
  | error hError => exact .done (.error hError)
  | @ok sourceResult targetResult hResult =>
      rcases sourceResult with ⟨sourceAfter, sourceValue⟩
      rcases targetResult with ⟨targetAfter, targetValue⟩
      cases hResult.value
      have hDefined : LiveDefined live sourceAfter :=
        hInitial.defined.congr_vars hVarsDone
      have hAfter :
          AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode sourceAfter targetAfter :=
        { compiler := hInitial.compiler
          planWF := hInitial.planWF
          defined := hDefined
          state := hResult.state
          stackLength :=
            (congrArg List.length hResult.stack).trans
              hInitial.stackLength }
      cases hSelection sourceValue with
      | none hSource hTarget =>
          simp only
          rw [hSource, hTarget]
          apply Simulation.Interaction.Rel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact ControlResultRel.regular hAfter (SameFrame.refl mode)
            (Functions.Source.Ctx.SameControl.refl sourceCtx)
      | some sourceBody targetBody hSource hTarget =>
          simp only
          rw [hSource, hTarget]
          have hSelectedSuccess :
              Simulation.Interaction.Successful
                (Functions.InteractionSemantics.Stmt.openRun program
                  sourceCtx sourceBodyFuel (.block sourceBody)
                  sourceAfter) := by
            simpa [hSource] using hContinuationSuccess
          exact hSelected hSource hTarget hAfter hTargetReturns
            hSelectedSuccess

/-- Preserve a switch while carrying ordinary and guarded success into exactly
the dynamically selected source branch. -/
theorem switch_of_components_executionSafe
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Plan}
    {returns live : List Functions.Name}
    {frameBase sourceBodyFuel targetBodyFuel : Nat}
    {mode : ActivationMode} {sourceCtx : Functions.Source.Ctx}
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
        (Simulation.Interaction.ExceptRel
          (fun left right : EVMException => left = right)
          (ActivationValueResultRel contract plan live frameBase mode target))
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
    (hSafeSuccess :
      Simulation.Interaction.Successful
        (AllocationInteractionSafeSemantics.Stmt.openRun contract program
          sourceCtx (sourceBodyFuel + 1)
          (.switch scrutinee sourceCases sourceDefault) source))
    (hSafeScrutineeOrdinary :
      AllocationInteractionSafeSemantics.Expr.openEvalOne
          contract scrutinee source =
        Functions.InteractionSemantics.Expr.openEvalOne scrutinee source)
    (hSelection :
      ∀ value,
        SwitchSelection sourceCases sourceDefault targetCases targetDefault
          value)
    (hSelected :
      ∀ {value sourceBody targetBody sourceAfter targetAfter},
        Functions.Source.Switch.select value sourceCases sourceDefault =
            some sourceBody →
        Expressions.EffectSemantics.Switch.select value targetCases
            targetDefault = some targetBody →
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode sourceAfter targetAfter →
        targetAfter.returns = target.returns →
        Simulation.Interaction.Successful
          (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
            sourceBodyFuel (.block sourceBody) sourceAfter) →
        Simulation.Interaction.Successful
          (AllocationInteractionSafeSemantics.Stmt.openRun contract program
            sourceCtx sourceBodyFuel (.block sourceBody) sourceAfter) →
        Simulation.Interaction.Rel
          (OpenControlResultRel contract lowerCtx lowerState localsCtx plan
            returns live frameBase mode sourceCtx sourceCtx)
          (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
            sourceBodyFuel (.block sourceBody) sourceAfter)
          (Expressions.InteractionSemantics.Block.openRun expressions
            targetBodyFuel targetBody targetAfter)) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract lowerCtx lowerState localsCtx plan
        returns live frameBase mode sourceCtx sourceCtx)
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
  rw [AllocationInteractionSafeSemantics.Stmt.openRun_switch] at hSafeSuccess
  have hScrutineeSuccess :=
    Simulation.Interaction.Successful.bind_inv hSuccess
  have hSafeScrutineeSuccess :=
    Simulation.Interaction.Successful.bind_inv hSafeSuccess
  rw [hSafeScrutineeOrdinary] at hSafeScrutineeSuccess
  have hScrutineeStrong :=
    Simulation.Interaction.Rel.strengthen_right
      (Simulation.Interaction.Rel.strengthen_left
        (Simulation.Interaction.Rel.strengthen_left
          (Simulation.Interaction.Rel.strengthen_left hScrutinee hVars)
          hScrutineeSuccess)
        hSafeScrutineeSuccess)
      (Expressions.InteractionReturns.Expr.openRunOne_returns
        targetScrutinee target)
  apply Simulation.Interaction.Rel.bind_custom hScrutineeStrong
  intro sourceDone targetDone hDone
  rcases hDone with
    ⟨⟨⟨⟨hRelated, hVarsDone⟩, hContinuationSuccess⟩,
      hContinuationSafe⟩, hTargetReturns⟩
  cases hRelated with
  | error hError => exact .done (.error hError)
  | @ok sourceResult targetResult hResult =>
      rcases sourceResult with ⟨sourceAfter, sourceValue⟩
      rcases targetResult with ⟨targetAfter, targetValue⟩
      cases hResult.value
      have hDefined : LiveDefined live sourceAfter :=
        hInitial.defined.congr_vars hVarsDone
      have hAfter :
          AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode sourceAfter targetAfter :=
        { compiler := hInitial.compiler
          planWF := hInitial.planWF
          defined := hDefined
          state := hResult.state
          stackLength :=
            (congrArg List.length hResult.stack).trans hInitial.stackLength }
      cases hSelection sourceValue with
      | none hSource hTarget =>
          simp only
          rw [hSource, hTarget]
          apply Simulation.Interaction.Rel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact ControlResultRel.regular hAfter (SameFrame.refl mode)
            (Functions.Source.Ctx.SameControl.refl sourceCtx)
      | some sourceBody targetBody hSource hTarget =>
          simp only
          rw [hSource, hTarget]
          have hSelectedSuccess :
              Simulation.Interaction.Successful
                (Functions.InteractionSemantics.Stmt.openRun program
                  sourceCtx sourceBodyFuel (.block sourceBody)
                  sourceAfter) := by
            simpa [hSource] using hContinuationSuccess
          have hSelectedSafe :
              Simulation.Interaction.Successful
                (AllocationInteractionSafeSemantics.Stmt.openRun contract
                  program sourceCtx sourceBodyFuel (.block sourceBody)
                  sourceAfter) := by
            simpa [hSource] using hContinuationSafe
          exact hSelected hSource hTarget hAfter hTargetReturns
            hSelectedSuccess hSelectedSafe

end AllocationInteractionControl
end Functions
end EvmCompiler
