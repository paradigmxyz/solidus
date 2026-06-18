import EvmCompiler.Functions.AllocationInteractionCleanup
import EvmCompiler.Functions.AllocationInteractionComposition

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionAbrupt

open AllocationInteractionRelation
open AllocationInteractionComposition
open AllocationInteractionCleanup

/-- `break` preservation through the ordinary allocation and Locals passes. -/
theorem brk_of_lower_compile
    {contract : MemoryContract.Contract}
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
      Transition plan beforeLive afterLive targetDepth
        beforeMode afterMode)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState .brk =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan beforeLive frameBase beforeMode source target) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract lowerCtx lowerFinal localsFinal plan
        returns beforeLive frameBase beforeMode sourceCtx sourceCtx)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel .brk source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (targetExtra + 3) { stmts := compiledStmts } target) := by
  obtain ⟨cleanup, hCleanup, rfl, rfl, rfl, rfl⟩ :=
    BreakLeaf.compiler_shape hTargetDepth hLower hCompile
  obtain ⟨targetFinal, hCleanupRun, hFinalRel, hStackLength⟩ :=
    Plain.forward_exact hInvariant hTransition hCleanup
  have hTarget :=
    Locals.InteractionPreservation.Stmt.TargetBlock.openRun_code_brk
      targetProgram targetExtra cleanup target targetFinal hCleanupRun
  have hSource :
      Functions.InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx sourceFuel .brk source =
        .done
          (.ok
            (Functions.Source.Effectful.Outcome.brk
              (source.restrictTo afterLive),
              sourceCtx)) := by
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
  refine ControlResultRel.nonregular (mode := afterMode) (by simp)
    hTransition.sameFrame
    (Functions.Source.Ctx.SameControl.refl sourceCtx) ?_
  simpa [AllocationInteractionStatement.outcomeLive, hSourceScope] using
    (ActivationOutcomeRel.brk
      (hInvariant.defined.restrictTo hTransition.subset)
      (hStackLength.trans hTransition.targetDepth_eq_stackLength)
      hTransition.after_matches
      hFinalRel)

/-- `continue` preservation through the ordinary allocation and Locals passes. -/
theorem cont_of_lower_compile
    {contract : MemoryContract.Contract}
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
      Transition plan beforeLive afterLive targetDepth
        beforeMode afterMode)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState .cont =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan beforeLive frameBase beforeMode source target) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract lowerCtx lowerFinal localsFinal plan
        returns beforeLive frameBase beforeMode sourceCtx sourceCtx)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel .cont source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (targetExtra + 3) { stmts := compiledStmts } target) := by
  obtain ⟨cleanup, hCleanup, rfl, rfl, rfl, rfl⟩ :=
    ContinueLeaf.compiler_shape hTargetDepth hLower hCompile
  obtain ⟨targetFinal, hCleanupRun, hFinalRel, hStackLength⟩ :=
    Plain.forward_exact hInvariant hTransition hCleanup
  have hTarget :=
    Locals.InteractionPreservation.Stmt.TargetBlock.openRun_code_cont
      targetProgram targetExtra cleanup target targetFinal hCleanupRun
  have hSource :
      Functions.InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx sourceFuel .cont source =
        .done
          (.ok
            (Functions.Source.Effectful.Outcome.cont
              (source.restrictTo afterLive),
              sourceCtx)) := by
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
  refine ControlResultRel.nonregular (mode := afterMode) (by simp)
    hTransition.sameFrame
    (Functions.Source.Ctx.SameControl.refl sourceCtx) ?_
  simpa [AllocationInteractionStatement.outcomeLive, hSourceScope] using
    (ActivationOutcomeRel.cont
      (hInvariant.defined.restrictTo hTransition.subset)
      (hStackLength.trans hTransition.targetDepth_eq_stackLength)
      hTransition.after_matches
      hFinalRel)

end AllocationInteractionAbrupt
end Functions
end EvmCompiler
