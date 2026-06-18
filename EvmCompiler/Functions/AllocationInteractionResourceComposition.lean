import EvmCompiler.Functions.AllocationInteractionComposition
import EvmCompiler.Functions.AllocationInteractionResource

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionResourceComposition

open AllocationInteractionRelation
open AllocationInteractionComposition
open AllocationInteractionFrame
open AllocationInteractionResource

abbrev RuntimeResultRel
    (contract : MemoryContract.Contract)
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx) (plan : Plan)
    (returns regularLive : List Locals.Name) (frameBase : Nat)
    (entryMode : ActivationMode)
    (controlCtx regularCtx : Functions.Source.Ctx)
    (config : Config) (allocatorDepth : Nat) (targetInitial : TargetState)
    (sourceDone :
      Except EVMException
        (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx))
    (targetDone :
      Except EVMException Expressions.InteractionSemantics.Outcome) : Prop :=
  OpenControlResultRel contract lowerCtx lowerState localsCtx plan returns
      regularLive frameBase entryMode controlCtx regularCtx
      sourceDone targetDone ∧
    OpenResultRel config allocatorDepth entryMode targetInitial
      sourceDone targetDone

/--
Compose one semantic/resource control result with its tail. Regular execution
passes allocator readiness to the tail; abrupt execution preserves the head
effect and skips the unreachable tail.
-/
theorem cons
    {contract : MemoryContract.Contract}
    {midLowerCtx finalLowerCtx : AllocationLowering.Ctx}
    {midLowerState finalLowerState : AllocationLowering.State}
    {midLocals finalLocals : Locals.Ctx} {plan : Plan}
    {returns midLive finalLive : List Locals.Name} {frameBase : Nat}
    {entryMode : ActivationMode}
    {controlCtx midCtx finalCtx : Functions.Source.Ctx}
    {config : Config} {allocatorDepth : Nat}
    {targetInitial : TargetState}
    {sourceHead :
      Simulation.Interaction EVMException
        (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx)}
    {targetHead :
      Simulation.Interaction EVMException
        Expressions.InteractionSemantics.Outcome}
    {sourceTail : SourceState → Functions.Source.Ctx →
      Simulation.Interaction EVMException
        (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx)}
    {targetTail : TargetState →
      Simulation.Interaction EVMException
        Expressions.InteractionSemantics.Outcome}
    (hHead :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract midLowerCtx midLowerState midLocals plan
          returns midLive frameBase entryMode controlCtx midCtx config
          allocatorDepth targetInitial)
        sourceHead targetHead)
    (hTail :
      ∀ {sourceMid targetMid mode},
        AllocationContext.ActivationInvariant contract midLowerCtx
            midLowerState midLocals plan midLive frameBase mode sourceMid
            targetMid →
          AllocatorReady config allocatorDepth targetMid →
          SameFrame entryMode mode →
          Simulation.Interaction.Rel
            (RuntimeResultRel contract finalLowerCtx finalLowerState
              finalLocals plan returns finalLive frameBase mode midCtx finalCtx
              config allocatorDepth targetMid)
            (sourceTail sourceMid midCtx) (targetTail targetMid)) :
    Simulation.Interaction.Rel
      (RuntimeResultRel contract finalLowerCtx finalLowerState finalLocals plan
        returns finalLive frameBase entryMode controlCtx finalCtx config
        allocatorDepth targetInitial)
      (Simulation.Interaction.bind sourceHead
        (fun result =>
          match result.1.mode with
          | .regular => sourceTail result.1.state result.2
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure (result.1, controlCtx)))
      (Simulation.Interaction.bind targetHead
        (fun outcome =>
          match outcome.mode with
          | .regular => targetTail outcome.state
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure outcome)) := by
  apply Simulation.Interaction.Rel.bind_custom hHead
  intro sourceDone targetDone hDone
  rcases hDone with ⟨hSemanticDone, hResourceDone⟩
  cases hSemanticDone with
  | error hError =>
      cases hResourceDone with
      | error _ => exact .done ⟨.error hError, .error hError⟩
  | ok hSemanticResult =>
      cases hResourceDone with
      | ok hHeadEffect =>
          cases hSemanticResult with
          | regular invariant sameFrame control =>
              have hHeadEffectMode := hHeadEffect.sameFrame sameFrame
              apply Simulation.Interaction.Rel.mono
                (hTail invariant hHeadEffectMode.ready sameFrame)
              intro tailSource tailTarget hTailDone
              rcases hTailDone with
                ⟨hTailSemanticDone, hTailResourceDone⟩
              cases hTailSemanticDone with
              | error hError =>
                  cases hTailResourceDone with
                  | error _ => exact ⟨.error hError, .error hError⟩
              | ok hTailSemantic =>
                  cases hTailResourceDone with
                  | ok hTailEffect =>
                      exact
                        ⟨.ok
                            (ControlResultRel.prepend_frame sameFrame
                              (ControlResultRel.transport_control control
                                hTailSemantic)),
                          .ok
                            (hHeadEffect.trans
                              (hTailEffect.sameFrame sameFrame.symm))⟩
          | @nonregular sourceOutcome targetOutcome headCtx mode
              hNonregular sameFrame control state =>
              cases state with
              | regular regularState => exact False.elim (hNonregular rfl)
              | brk defined stackLength modeMatches state =>
                  exact .done
                    ⟨.ok
                        (ControlResultRel.nonregular (mode := mode)
                          hNonregular sameFrame
                          (Functions.Source.Ctx.SameControl.refl controlCtx)
                          (.brk defined stackLength modeMatches state)),
                      .ok hHeadEffect⟩
              | cont defined stackLength modeMatches state =>
                  exact .done
                    ⟨.ok
                        (ControlResultRel.nonregular (mode := mode)
                          hNonregular sameFrame
                          (Functions.Source.Ctx.SameControl.refl controlCtx)
                          (.cont defined stackLength modeMatches state)),
                      .ok hHeadEffect⟩
              | leave state =>
                  exact .done
                    ⟨.ok
                        (ControlResultRel.nonregular (mode := mode)
                          hNonregular sameFrame
                          (Functions.Source.Ctx.SameControl.refl controlCtx)
                          (.leave state)),
                      .ok hHeadEffect⟩
              | halt kind state =>
                  exact .done
                    ⟨.ok
                        (ControlResultRel.nonregular (mode := mode)
                          hNonregular sameFrame
                          (Functions.Source.Ctx.SameControl.refl controlCtx)
                          (.halt kind state)),
                      .ok hHeadEffect⟩

/-- Compose the real source statement-list and compiled target runners. -/
theorem block_cons
    {contract : MemoryContract.Contract}
    {sourceProgram : Functions.Program}
    {targetProgram : Expressions.Program}
    {sourceFuel targetFuel : Nat}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {headCode tailCode : List Expressions.Stmt}
    {source : SourceState} {target : TargetState}
    {midLowerCtx finalLowerCtx : AllocationLowering.Ctx}
    {midLowerState finalLowerState : AllocationLowering.State}
    {midLocals finalLocals : Locals.Ctx} {plan : Plan}
    {returns midLive finalLive : List Locals.Name} {frameBase : Nat}
    {entryMode : ActivationMode}
    {controlCtx midCtx finalCtx : Functions.Source.Ctx}
    {config : Config} {allocatorDepth : Nat}
    (hHead :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract midLowerCtx midLowerState midLocals plan
          returns midLive frameBase entryMode controlCtx midCtx config
          allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun
          sourceProgram controlCtx sourceFuel stmt source)
        (Expressions.InteractionSemantics.Block.openRun
          targetProgram targetFuel { stmts := headCode } target))
    (hTail :
      ∀ {sourceMid targetMid mode},
        AllocationContext.ActivationInvariant contract midLowerCtx
            midLowerState midLocals plan midLive frameBase mode sourceMid
            targetMid →
          AllocatorReady config allocatorDepth targetMid →
          SameFrame entryMode mode →
          Simulation.Interaction.Rel
            (RuntimeResultRel contract finalLowerCtx finalLowerState
              finalLocals plan returns finalLive frameBase mode midCtx finalCtx
              config allocatorDepth targetMid)
            (Functions.InteractionSemantics.Block.openRun
              sourceProgram midCtx sourceFuel { stmts := rest } sourceMid)
            (Expressions.InteractionSemantics.Block.openRun targetProgram
              (targetFuel - headCode.length) { stmts := tailCode } targetMid)) :
    Simulation.Interaction.Rel
      (RuntimeResultRel contract finalLowerCtx finalLowerState finalLocals plan
        returns finalLive frameBase entryMode controlCtx finalCtx config
        allocatorDepth target)
      (Functions.InteractionSemantics.Block.openRun sourceProgram controlCtx
        (sourceFuel + 1) { stmts := stmt :: rest } source)
      (Expressions.InteractionSemantics.Block.openRun targetProgram targetFuel
        { stmts := headCode ++ tailCode } target) := by
  rw [Functions.InteractionSemantics.Block.openRun_cons,
    Expressions.InteractionSemantics.Block.openRun_append]
  exact
    cons
      (finalLowerCtx := finalLowerCtx)
      (finalLowerState := finalLowerState)
      (finalLocals := finalLocals)
      (finalLive := finalLive) (finalCtx := finalCtx)
      (sourceTail := fun sourceMid ctx =>
        Functions.InteractionSemantics.Block.openRun sourceProgram ctx
          sourceFuel { stmts := rest } sourceMid)
      (targetTail := fun targetMid =>
        Expressions.InteractionSemantics.Block.openRun targetProgram
          (targetFuel - headCode.length) { stmts := tailCode } targetMid)
      hHead hTail

end AllocationInteractionResourceComposition
end Functions
end EvmCompiler
