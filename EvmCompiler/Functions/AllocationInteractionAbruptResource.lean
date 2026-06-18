import EvmCompiler.Functions.AllocationInteractionAbrupt
import EvmCompiler.Functions.AllocationInteractionCleanupResource
import EvmCompiler.Functions.AllocationInteractionResource

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionAbruptResource

open AllocationInteractionRelation
open AllocationInteractionFrame
open AllocationInteractionResource
open AllocationInteractionCleanup

/-- `break` cleanup preserves the current activation's allocator resources. -/
theorem brk_of_lower_compile
    {contract : MemoryContract.Contract} {config : Config}
    {allocatorDepth : Nat}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Expressions.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Plan} {beforeLive afterLive : List Locals.Name}
    {sourceFuel targetExtra targetDepth frameBase : Nat}
    {beforeMode afterMode : ActivationMode}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : SourceState} {target : TargetState}
    (hSourceScope : sourceCtx.breakScope? = some afterLive)
    (hTargetDepth : localsCtx.breakDepth? = some targetDepth)
    (hTransition :
      Transition plan beforeLive afterLive targetDepth beforeMode afterMode)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState .brk =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan beforeLive frameBase beforeMode source target)
    (hReady : AllocatorReady config allocatorDepth target) :
    Simulation.Interaction.Rel
      (OpenResultRel config allocatorDepth beforeMode target)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel .brk source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (targetExtra + 3) { stmts := compiledStmts } target) := by
  obtain ⟨cleanup, hCleanup, rfl, rfl, rfl, rfl⟩ :=
    AllocationInteractionCleanup.BreakLeaf.compiler_shape
      hTargetDepth hLower hCompile
  obtain ⟨targetFinal, hCleanupRun, hEffect⟩ :=
    AllocationInteractionCleanupResource.Plain.forward_allocator
      hInvariant hCleanup hReady
  have hTarget :=
    Locals.InteractionPreservation.Stmt.TargetBlock.openRun_code_brk
      targetProgram targetExtra cleanup target targetFinal hCleanupRun
  have hSource :
      Functions.InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx sourceFuel .brk source =
        .done
          (.ok
            (Functions.Source.Effectful.Outcome.brk
              (source.restrictTo afterLive), sourceCtx)) := by
    unfold Functions.InteractionSemantics.Stmt.openRun
      Functions.Source.Canonical.Stmt.run
    simp only [Functions.Source.Effectful.Control.Stmt.run]
    rw [hSourceScope]
    simp [Functions.InteractionSemantics.stateModel,
      Locals.InteractionSemantics.stateModel,
      Locals.Source.Effectful.Ordinary.stateModel,
      Locals.Source.Effectful.StateModel.restrictTo,
      Simulation.Interaction.pure]
    rfl
  rw [hSource, hTarget]
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  exact OutcomeEffect.of_activation
    (ActivationEffect.of_allocatorEffect hEffect)

/-- `continue` cleanup preserves the current activation's resources. -/
theorem cont_of_lower_compile
    {contract : MemoryContract.Contract} {config : Config}
    {allocatorDepth : Nat}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Expressions.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Plan} {beforeLive afterLive : List Locals.Name}
    {sourceFuel targetExtra targetDepth frameBase : Nat}
    {beforeMode afterMode : ActivationMode}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : SourceState} {target : TargetState}
    (hSourceScope : sourceCtx.continueScope? = some afterLive)
    (hTargetDepth : localsCtx.continueDepth? = some targetDepth)
    (hTransition :
      Transition plan beforeLive afterLive targetDepth beforeMode afterMode)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState .cont =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan beforeLive frameBase beforeMode source target)
    (hReady : AllocatorReady config allocatorDepth target) :
    Simulation.Interaction.Rel
      (OpenResultRel config allocatorDepth beforeMode target)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel .cont source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (targetExtra + 3) { stmts := compiledStmts } target) := by
  obtain ⟨cleanup, hCleanup, rfl, rfl, rfl, rfl⟩ :=
    AllocationInteractionCleanup.ContinueLeaf.compiler_shape
      hTargetDepth hLower hCompile
  obtain ⟨targetFinal, hCleanupRun, hEffect⟩ :=
    AllocationInteractionCleanupResource.Plain.forward_allocator
      hInvariant hCleanup hReady
  have hTarget :=
    Locals.InteractionPreservation.Stmt.TargetBlock.openRun_code_cont
      targetProgram targetExtra cleanup target targetFinal hCleanupRun
  have hSource :
      Functions.InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx sourceFuel .cont source =
        .done
          (.ok
            (Functions.Source.Effectful.Outcome.cont
              (source.restrictTo afterLive), sourceCtx)) := by
    unfold Functions.InteractionSemantics.Stmt.openRun
      Functions.Source.Canonical.Stmt.run
    simp only [Functions.Source.Effectful.Control.Stmt.run]
    rw [hSourceScope]
    simp [Functions.InteractionSemantics.stateModel,
      Locals.InteractionSemantics.stateModel,
      Locals.Source.Effectful.Ordinary.stateModel,
      Locals.Source.Effectful.StateModel.restrictTo,
      Simulation.Interaction.pure]
    rfl
  rw [hSource, hTarget]
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  exact OutcomeEffect.of_activation
    (ActivationEffect.of_allocatorEffect hEffect)

end AllocationInteractionAbruptResource
end Functions
end EvmCompiler
