import EvmCompiler.Functions.AllocationInteractionCleanup
import EvmCompiler.Functions.AllocationInteractionComposition
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
          hNonregular control state =>
          have hReindexed :=
            ControlResultRel.reindex_nonregular_live
              (afterLive := live) state hNonregular
          have hAgree :=
            hPlanAgree.mono
              (hControl.outcomeLive_subset sourceOutcome.mode)
          have hOuterState := hReindexed.transport_plan hAgree
          cases hOuterState with
          | regular state => exact False.elim (hNonregular rfl)
          | brk stateRel =>
              change
                Simulation.Interaction.Rel _
                  (Simulation.Interaction.pure (_, sourceCtx))
                  (Simulation.Interaction.pure _)
              apply Simulation.Interaction.Rel.done
              apply Simulation.Interaction.ExceptRel.ok
              exact ControlResultRel.nonregular (mode := mode) hNonregular
                (Functions.Source.Ctx.SameControl.refl sourceCtx)
                (.brk stateRel)
          | cont stateRel =>
              change
                Simulation.Interaction.Rel _
                  (Simulation.Interaction.pure (_, sourceCtx))
                  (Simulation.Interaction.pure _)
              apply Simulation.Interaction.Rel.done
              apply Simulation.Interaction.ExceptRel.ok
              exact ControlResultRel.nonregular (mode := mode) hNonregular
                (Functions.Source.Ctx.SameControl.refl sourceCtx)
                (.cont stateRel)
          | leave stateRel =>
              change
                Simulation.Interaction.Rel _
                  (Simulation.Interaction.pure (_, sourceCtx))
                  (Simulation.Interaction.pure _)
              apply Simulation.Interaction.Rel.done
              apply Simulation.Interaction.ExceptRel.ok
              exact ControlResultRel.nonregular (mode := mode) hNonregular
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
                (Functions.Source.Ctx.SameControl.refl sourceCtx)
                (.halt kind stateRel)

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

end AllocationInteractionControl
end Functions
end EvmCompiler
