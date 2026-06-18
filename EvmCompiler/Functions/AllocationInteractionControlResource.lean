import EvmCompiler.Functions.AllocationInteractionControl
import EvmCompiler.Functions.AllocationInteractionCleanupResource
import EvmCompiler.Functions.AllocationInteractionResourceComposition

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionControlResource

open AllocationInteractionRelation
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
          obtain ⟨targetFinal, hCleanupRun, hCleanupEffect⟩ :=
            AllocationInteractionCleanupResource.Plain.forward_allocator
              bodyInvariant hCleanup hActivation.ready
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
            (ActivationEffect.trans hActivation
              (ActivationEffect.of_allocatorEffect hCleanupEffect))
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

end AllocationInteractionControlResource
end Functions
end EvmCompiler
