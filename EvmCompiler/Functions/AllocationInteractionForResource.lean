import EvmCompiler.Functions.AllocationInteractionCleanupResource
import EvmCompiler.Functions.AllocationInteractionFor
import EvmCompiler.Functions.AllocationInteractionLoopResource
import EvmCompiler.Functions.AllocationInteractionResourceComposition

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionForResource

open AllocationInteractionFrame
open AllocationInteractionFor
open AllocationInteractionLoop
open AllocationInteractionRelation
open AllocationInteractionComposition
open AllocationInteractionResourceComposition

/--
Resource-aware `for` preservation specializes the canonical control owner to
activation effects; it does not replay initializer or loop control.
-/
theorem forward_with
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {contract : MemoryContract.Contract}
    {config : Config} {allocatorDepth : Nat}
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
    (hSourceScope : sourceCtx.scope = live)
    (hLoopLive : loopLive = Functions.Scope.Block.outEnv live init)
    (hInitCtx : initCtx = sourceCtx.withoutLoopControl)
    (hLoopCtx : loopCtx = { initCtx with scope := loopLive })
    (hPostCtx : postCtx = loopCtx.withoutLoopControl)
    (hBodyCtx : bodyCtx = loopCtx.withLoopControl loopLive loopLive)
    (hOuter :
      AllocationContext.ActivationInvariant contract lowerCtx outerState
        outerLocals outerPlan live frameBase entryMode source target)
    (hOwned : ActivationOwned config allocatorDepth frameBase entryMode)
    (hExtends :
      AllocationLowering.StateExtends live outerState loopState)
    (hPlanAgree : PlanAgreesOn loopPlan outerPlan live)
    (hCleanup :
      initLocals.cleanupTo? outerLocals.layout.length = some cleanup)
    (hTargetFuel : 1 ≤ sourceFuel + slack)
    (hInit :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract lowerCtx loopState initLocals loopPlan
          returns loopLive frameBase entryMode initCtx loopCtx config
          allocatorDepth target)
        (sourceModel.openRunBlock
          program initCtx sourceFuel init source)
        (Expressions.InteractionSemantics.Block.openRun
          expressions (sourceFuel + slack) targetInit target))
    (hLoop :
      ∀ {mode sourceAfter targetAfter},
        ActivationOwned config allocatorDepth frameBase mode →
        SameFrame entryMode mode →
        OutcomeEffect config allocatorDepth entryMode target targetAfter
            .regular →
        targetAfter.returns = target.returns →
        AllocationContext.ActivationInvariant contract lowerCtx loopState
            initLocals loopPlan loopLive frameBase mode sourceAfter
              targetAfter →
          Simulation.Interaction.Successful
            (sourceModel.openRunForLoop program
              loopCtx cond postCtx post bodyCtx body sourceFuel sourceAfter) →
            Simulation.Interaction.Rel
              (OpenLoopEffectResultRel
                (OutcomeEffect config allocatorDepth) contract lowerCtx
                loopState initLocals loopPlan returns loopLive frameBase mode
                loopCtx targetAfter)
              (sourceModel.openRunForLoop program
                loopCtx cond postCtx post bodyCtx body sourceFuel sourceAfter)
              (Expressions.InteractionSemantics.Stmt.openRunForLoop
                expressions (sourceFuel + slack) targetCond targetPost
                  targetBody targetAfter))
    (hSuccess :
      Simulation.Interaction.Successful
        (sourceModel.openRunStmt program sourceCtx
          (sourceFuel + 1) (.for_ init cond post body) source)) :
    Simulation.Interaction.Rel
      (RuntimeResultRel contract lowerCtx outerState outerLocals outerPlan
        returns live frameBase entryMode sourceCtx sourceCtx config
        allocatorDepth target)
      (sourceModel.openRunStmt program sourceCtx
        (sourceFuel + 1) (.for_ init cond post body) source)
      (Expressions.InteractionSemantics.Block.openRun expressions
        (sourceFuel + slack + 2)
        { stmts :=
            [.for_ targetInit targetCond targetPost targetBody,
              .code cleanup] }
        target) := by
  apply AllocationInteractionFor.forward_effect_with sourceModel
    (Effect := OutcomeEffect config allocatorDepth)
    (AllocationInteractionLoopResource.outcomeEffectAlgebra config
      allocatorDepth frameBase)
    hSourceScope hLoopLive hInitCtx hLoopCtx hPostCtx hBodyCtx hOuter hOwned
    hExtends hPlanAgree hCleanup hTargetFuel hInit
    (hInitReturns :=
      Expressions.InteractionReturns.Block.openRun_returns expressions
        (sourceFuel + slack) targetInit target)
    hLoop
    (hCleanupEffect := ?_) hSuccess
  intro mode sourceMid targetMid targetFinal hInvariant hPrefix hRun
  have hPrefixActivation :=
    hPrefix.activation_of_not_halt (by
      intro kind hEq
      cases hEq)
  exact OutcomeEffect.of_activation
    (ActivationEffect.of_allocatorEffect
      (AllocationInteractionCleanupResource.Plain.effect_of_run hInvariant
        hCleanup hPrefixActivation.ready hRun))

end AllocationInteractionForResource
end Functions
end EvmCompiler
