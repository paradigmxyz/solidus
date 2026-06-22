import EvmCompiler.Functions.AllocationInteractionExpressionResource
import EvmCompiler.Functions.AllocationInteractionLoop
import EvmCompiler.Functions.AllocationInteractionResource

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionLoopResource

open AllocationInteractionFrame
open AllocationInteractionRelation
open AllocationInteractionResource

/-- Canonical Functions control instantiated with the reservation-guarded
primitive semantics. This changes only primitive capability, not control. -/
noncomputable def guardedSourceSemantics
    (contract : MemoryContract.Contract) :
    AllocationInteractionLoop.SourceSemantics where
  primitive := AllocationInteractionSafeSemantics.primitiveSemantics contract
  conditionVars := by
    intro cond source
    apply Simulation.Interaction.AllDone.mono
      (AllocationInteractionSafeSemantics.Expr.openEvalCondition_vars_eq
        contract cond source)
    intro outcome hOutcome
    cases outcome <;> exact hOutcome

def outcomeEffectAlgebra
    (config : Config) (allocatorDepth frameBase : Nat) :
    AllocationInteractionLoop.EffectAlgebra
      (OutcomeEffect config allocatorDepth) := by
  refine
    { Ready := AllocatorReady config allocatorDepth
      Context := ActivationOwned config allocatorDepth frameBase
      transSame := ?_
      ready := ?_
      reindexNonhalt := ?_
      contextSame := ?_ }
  · intro beforeMode afterMode first second third outcomeMode
      hFirst hSame hSecond
    exact OutcomeEffect.prepend_activation
      (hFirst.activation_of_not_halt (by intro kind hEq; cases hEq))
      hSame hSecond
  · intro mode before after hEffect
    exact (hEffect.activation_of_not_halt
      (by intro kind hEq; cases hEq)).ready
  · intro mode before after outcomeMode replacement hEffect hNotHalt
    exact OutcomeEffect.of_activation
      (hEffect.activation_of_not_halt hNotHalt)
  · intro beforeMode afterMode hOwned hSame
    exact hOwned.sameFrame hSame

/--
Resource-aware loop preservation is the concrete activation-effect
specialization of the canonical semantic loop induction.
-/
theorem forward_with
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {contract : MemoryContract.Contract}
    {config : Config} {allocatorDepth : Nat}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Plan}
    {returns live : List Functions.Name} {frameBase slack fuelBound : Nat}
    {targetReturns : List Structured.ReturnDest}
    {rootMode : ActivationMode}
    {loopCtx postCtx bodyCtx : Functions.Source.Ctx}
    {cond : Functions.Expr 1} {post body : Functions.Block}
    {targetCond : Expressions.Expr 1}
    {targetPost targetBody : Expressions.Block}
    (sourceModel : AllocationInteractionLoop.SourceSemantics)
    (hLoopScope : loopCtx.scope = live)
    (hBodyBreak : bodyCtx.breakScope? = some live)
    (hBodyContinue : bodyCtx.continueScope? = some live)
    (hCond :
      ∀ {mode source target},
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode source target →
          AllocatorReady config allocatorDepth target →
          Simulation.Interaction.Successful
            (sourceModel.openEvalCondition
              cond source) →
          Simulation.Interaction.Rel
            (AllocationInteractionExpressionResource.ConditionOutcomeRel
              contract config allocatorDepth plan live frameBase mode target)
            (sourceModel.openEvalCondition cond source)
            (Expressions.InteractionSemantics.Expr.openRunCondition
              targetCond target))
    (hBody :
      ∀ (fuel : Nat) {mode source target} {effectInitial : TargetState},
        fuel < fuelBound →
        ActivationOwned config allocatorDepth frameBase mode →
        SameFrame rootMode mode →
        OutcomeEffect config allocatorDepth mode effectInitial target
            .regular →
        target.returns = targetReturns →
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode source target →
          Simulation.Interaction.Successful
            (sourceModel.openRunScoped
              program bodyCtx body fuel source) →
          Simulation.Interaction.Rel
            (AllocationInteractionLoop.OpenScopedEffectResultRel
              (OutcomeEffect config allocatorDepth) contract lowerCtx
              lowerState localsCtx plan returns live frameBase mode bodyCtx
              target)
            (sourceModel.openRunScoped
              program bodyCtx body fuel source)
            (Expressions.InteractionSemantics.Block.openRun expressions
              (fuel + slack) targetBody target))
    (hPost :
      ∀ (fuel : Nat) {effectMode mode : ActivationMode} {source target}
        {effectInitial : TargetState},
        fuel < fuelBound →
        ActivationOwned config allocatorDepth frameBase mode →
        SameFrame rootMode mode →
        SameFrame effectMode mode →
        OutcomeEffect config allocatorDepth effectMode effectInitial target
            .regular →
        target.returns = targetReturns →
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
            localsCtx plan live frameBase mode source target →
          Simulation.Interaction.Successful
            (sourceModel.openRunScoped
              program postCtx post fuel source) →
          Simulation.Interaction.Rel
            (AllocationInteractionLoop.OpenScopedEffectResultRel
              (OutcomeEffect config allocatorDepth) contract lowerCtx
              lowerState localsCtx plan returns live frameBase mode postCtx
              target)
            (sourceModel.openRunScoped
              program postCtx post fuel source)
            (Expressions.InteractionSemantics.Block.openRun expressions
              (fuel + slack) targetPost target)) :
    ∀ (fuel : Nat) {mode source target},
      fuel ≤ fuelBound →
      target.returns = targetReturns →
      SameFrame rootMode mode →
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
          localsCtx plan live frameBase mode source target →
      AllocatorReady config allocatorDepth target →
      ActivationOwned config allocatorDepth frameBase mode →
      Simulation.Interaction.Successful
        (sourceModel.openRunForLoop program loopCtx
          cond postCtx post bodyCtx body fuel source) →
        Simulation.Interaction.Rel
          (AllocationInteractionLoop.OpenLoopEffectResultRel
            (OutcomeEffect config allocatorDepth) contract lowerCtx
            lowerState localsCtx plan returns live frameBase mode loopCtx target)
          (sourceModel.openRunForLoop program loopCtx
            cond postCtx post bodyCtx body fuel source)
          (Expressions.InteractionSemantics.Stmt.openRunForLoop expressions
            (fuel + slack) targetCond targetPost targetBody target) := by
  intro fuel mode source target hFuel hTargetReturns hRootFrame hInitial
    hReady hOwned hSuccess
  apply AllocationInteractionLoop.forward_effect_with sourceModel
    (Effect := OutcomeEffect config allocatorDepth)
    (outcomeEffectAlgebra config allocatorDepth frameBase)
    hLoopScope hBodyBreak hBodyContinue (hCond := ?_) hBody hPost fuel hFuel
    hTargetReturns hRootFrame hInitial hReady hOwned hSuccess
  intro nextMode nextSource nextTarget hNext hNextReady hCondSuccess
  apply Simulation.Interaction.Rel.mono
    (hCond hNext hNextReady hCondSuccess)
  intro sourceDone targetDone hDone
  cases hDone with
  | error hError => exact .error hError
  | ok hResult =>
      exact .ok ⟨hResult.1,
        OutcomeEffect.of_activation
          (ActivationEffect.of_allocatorEffect hResult.2)⟩

end AllocationInteractionLoopResource
end Functions
end EvmCompiler
