import EvmCompiler.Functions.AllocationInteractionExpressionResource
import EvmCompiler.Functions.AllocationInteractionLoop
import EvmCompiler.Functions.AllocationInteractionResource

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionLoopResource

open AllocationInteractionFrame
open AllocationInteractionRelation
open AllocationInteractionResource

def activationEffectAlgebra
    (config : Config) (allocatorDepth frameBase : Nat) :
    AllocationInteractionLoop.EffectAlgebra
      (ActivationEffect config allocatorDepth) := by
  refine
    { Ready := AllocatorReady config allocatorDepth
      Context := ActivationOwned config allocatorDepth frameBase
      transSame := ?_
      ready := ?_
      contextSame := ?_ }
  · intro beforeMode afterMode first second third hFirst hSame hSecond
    exact hFirst.trans (hSecond.sameFrame hSame.symm)
  · intro mode before after hEffect
    exact hEffect.ready
  · intro beforeMode afterMode hOwned hSame
    exact hOwned.sameFrame hSame

/--
Resource-aware loop preservation is the concrete activation-effect
specialization of the canonical semantic loop induction.
-/
theorem forward
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {contract : MemoryContract.Contract}
    {config : Config} {allocatorDepth : Nat}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Plan}
    {returns live : List Functions.Name} {frameBase slack fuelBound : Nat}
    {loopCtx postCtx bodyCtx : Functions.Source.Ctx}
    {cond : Functions.Expr 1} {post body : Functions.Block}
    {targetCond : Expressions.Expr 1}
    {targetPost targetBody : Expressions.Block}
    (hLoopScope : loopCtx.scope = live)
    (hBodyBreak : bodyCtx.breakScope? = some live)
    (hBodyContinue : bodyCtx.continueScope? = some live)
    (hCond :
      ∀ {mode source target},
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode source target →
          AllocatorReady config allocatorDepth target →
          Simulation.Interaction.Rel
            (AllocationInteractionExpressionResource.ConditionOutcomeRel
              contract config allocatorDepth plan live frameBase mode target)
            (Functions.InteractionSemantics.Expr.openEvalCondition cond source)
            (Expressions.InteractionSemantics.Expr.openRunCondition
              targetCond target))
    (hBody :
      ∀ (fuel : Nat) {mode source target} {effectInitial : TargetState},
        fuel < fuelBound →
        ActivationOwned config allocatorDepth frameBase mode →
        ActivationEffect config allocatorDepth mode effectInitial target →
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode source target →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Block.openRunScoped
              program bodyCtx body fuel source) →
          Simulation.Interaction.Rel
            (AllocationInteractionLoop.OpenScopedEffectResultRel
              (ActivationEffect config allocatorDepth) contract lowerCtx
              lowerState localsCtx plan returns live frameBase mode bodyCtx
              target)
            (Functions.InteractionSemantics.Block.openRunScoped
              program bodyCtx body fuel source)
            (Expressions.InteractionSemantics.Block.openRun expressions
              (fuel + slack) targetBody target))
    (hPost :
      ∀ (fuel : Nat) {effectMode mode : ActivationMode} {source target}
        {effectInitial : TargetState},
        fuel < fuelBound →
        ActivationOwned config allocatorDepth frameBase mode →
        SameFrame effectMode mode →
        ActivationEffect config allocatorDepth effectMode effectInitial target →
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode source target →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Block.openRunScoped
              program postCtx post fuel source) →
          Simulation.Interaction.Rel
            (AllocationInteractionLoop.OpenScopedEffectResultRel
              (ActivationEffect config allocatorDepth) contract lowerCtx
              lowerState localsCtx plan returns live frameBase mode postCtx
              target)
            (Functions.InteractionSemantics.Block.openRunScoped
              program postCtx post fuel source)
            (Expressions.InteractionSemantics.Block.openRun expressions
              (fuel + slack) targetPost target)) :
    ∀ (fuel : Nat) {mode source target},
      fuel ≤ fuelBound →
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
          localsCtx plan live frameBase mode source target →
      AllocatorReady config allocatorDepth target →
      ActivationOwned config allocatorDepth frameBase mode →
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRunForLoop program loopCtx
          cond postCtx post bodyCtx body fuel source) →
        Simulation.Interaction.Rel
          (AllocationInteractionLoop.OpenLoopEffectResultRel
            (ActivationEffect config allocatorDepth) contract lowerCtx
            lowerState localsCtx plan returns live frameBase mode loopCtx target)
          (Functions.InteractionSemantics.Stmt.openRunForLoop program loopCtx
            cond postCtx post bodyCtx body fuel source)
          (Expressions.InteractionSemantics.Stmt.openRunForLoop expressions
            (fuel + slack) targetCond targetPost targetBody target) := by
  intro fuel mode source target hFuel hInitial hReady hOwned hSuccess
  apply AllocationInteractionLoop.forward_effect
    (Effect := ActivationEffect config allocatorDepth)
    (activationEffectAlgebra config allocatorDepth frameBase)
    hLoopScope hBodyBreak hBodyContinue (hCond := ?_) hBody hPost fuel hFuel
    hInitial hReady hOwned hSuccess
  intro nextMode nextSource nextTarget hNext hNextReady
  apply Simulation.Interaction.Rel.mono (hCond hNext hNextReady)
  intro sourceDone targetDone hDone
  cases hDone with
  | error hError => exact .error hError
  | ok hResult =>
      exact .ok ⟨hResult.1,
        ActivationEffect.of_allocatorEffect hResult.2⟩

end AllocationInteractionLoopResource
end Functions
end EvmCompiler
