import EvmCompiler.Functions.AllocationInteractionPrimitiveResource
import EvmCompiler.Functions.AllocationInteractionSelectedCallEntry

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionCall
namespace PreparedArguments

open AllocationInteractionRelation
open AllocationInteractionFrame
open AllocationInteractionFrameExecution
open AllocationInteractionFramePreservation

/-- Canonical stack-only argument preparation with allocator preservation. -/
theorem stack
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth : Nat} {config : Config}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State} {localsCtx : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {args : List (Functions.Expr 1)} {lowered : List (Locals.Expr 1)}
    {code : Structured.Code} {source : SourceState} {target : TargetState}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hSafe : AllocationInteractionSafety.ArgListSafe contract args source)
    (hCtx :
      AllocationContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped :
      ∀ arg, arg ∈ args → Functions.Scope.ExprScoped live arg)
    (hLower :
      AllocationLowering.lowerExprList lowerCtx lowerState args =
        some lowered)
    (hCompile :
      Locals.ExprSeq.compileCode localsCtx 0
          (AllocationLowering.exprSeqOfList lowered) =
        some code)
    (hRel :
      ActivationStateRel contract plan live 0 frameBase mode source target)
    (hReady : AllocatorReady config allocatorDepth target) :
    Simulation.Interaction.Rel
      (Simulation.Interaction.ExceptRel
        (fun left right : EVMException => left = right)
        (AllocationInteractionCallArgumentResources.ResultRel
          contract config allocatorDepth plan live 0 frameBase args.length
          mode target))
      (Functions.InteractionSemantics.ArgList.openEval args source)
      (Structured.InteractionSemantics.Code.openRun code target) :=
  AllocationInteractionCallArgumentResources.forward
    (AllocationInteractionPrimitiveResource.canonicalPrimitiveForward
      contract)
    hConfig hSafe hCtx hScoped hLower hCompile hRel hReady

/--
Execute the compiler-emitted synthetic frame argument before the ordinary
source arguments, preserving the suspended caller and allocator prefix.
-/
theorem scratch
    {contract : MemoryContract.Contract}
    {globalFrameWords depth : Nat} {config : Config}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State} {localsCtx : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {args : List (Functions.Expr 1)} {lowered : List (Locals.Expr 1)}
    {code : Structured.Code} {source : SourceState} {target : TargetState}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hPositive : 0 < config.frameWords)
    (hBudget : Budget config depth)
    (hSafe : AllocationInteractionSafety.ArgListSafe contract args source)
    (hCtx :
      AllocationContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped :
      ∀ arg, arg ∈ args → Functions.Scope.ExprScoped live arg)
    (hLower :
      AllocationLowering.lowerExprList lowerCtx lowerState args =
        some lowered)
    (hCompile :
      Locals.ExprSeq.compileCode localsCtx 0
          (AllocationLowering.exprSeqOfList
            (AllocationLowering.frameExpr config :: lowered)) =
        some code)
    (hRel :
      ActivationStateRel contract plan live 0 frameBase mode source target)
    (hReady : AllocatorReady config depth target)
    (hOwned : ActivationOwned config depth frameBase mode) :
    let targetAfterAcquire :=
      scratchFrameAcquireTarget config depth target
    ScratchFrameAcquireCorrect contract config depth
        source.shared.toMachineState target targetAfterAcquire ∧
      Simulation.Interaction.Rel
        (Simulation.Interaction.ExceptRel
          (fun left right : EVMException => left = right)
          (AllocationInteractionCallArgumentResources.ResultRel
            contract config (depth + 1) plan live 1 frameBase args.length
            mode targetAfterAcquire))
        (Functions.InteractionSemantics.ArgList.openEval args source)
        (Structured.InteractionSemantics.Code.openRun code target) := by
  dsimp only
  obtain ⟨argsCode, hArgsCompile, hCode⟩ :=
    AllocationLowering.frameExpr_cons_compileCode_components hCompile
  obtain ⟨hAcquire, hAcquireRel⟩ :=
    scratchFrameAcquire_activation_correct hConfig hPositive hBudget hReady
      hOwned hRel
  refine ⟨hAcquire, ?_⟩
  have hArgs :=
    AllocationInteractionCallArgumentResources.forward
      (AllocationInteractionPrimitiveResource.canonicalPrimitiveForward
        contract)
      hConfig hSafe hCtx hScoped hLower hArgsCompile hAcquireRel
      hAcquire.effect.ready
  rw [hCode, Structured.InteractionSemantics.Code.openRun_append,
    hAcquire.execution]
  simpa [Simulation.Interaction.bind] using hArgs

end PreparedArguments
end AllocationInteractionCall
end Functions
end EvmCompiler
