import EvmCompiler.Functions.AllocationInteractionExpressionResource

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionCallArgumentResources

open AllocationInteractionRelation
open AllocationInteractionFrame
open AllocationInteractionExpressionResource

abbrev ArgResultRel
    (contract : MemoryContract.Contract) (config : Config)
    (allocatorDepth : Nat) (plan : Plan) (live : List Locals.Name)
    (stackOffset frameBase : Nat) (mode : ActivationMode)
    (targetInitial : TargetState)
    (source : SourceState × Word) (targetFinal : TargetState) : Prop :=
  ActivationExprResultRel contract plan live stackOffset frameBase 1 mode
      source.1 targetInitial targetFinal [source.2] ∧
    AllocatorEffect config allocatorDepth targetInitial targetFinal

abbrev ResultRel
    (contract : MemoryContract.Contract) (config : Config)
    (allocatorDepth : Nat) (plan : Plan) (live : List Locals.Name)
    (stackOffset frameBase count : Nat) (mode : ActivationMode)
    (targetInitial : TargetState)
    (source : SourceState × List Word) (targetFinal : TargetState) : Prop :=
  ActivationExprResultRel contract plan live stackOffset frameBase count mode
      source.1 targetInitial targetFinal source.2 ∧
    AllocatorEffect config allocatorDepth targetInitial targetFinal

/-- One canonical argument preserves allocator resources. -/
theorem forwardArg
    {contract : MemoryContract.Contract}
    (primitiveOwner :
      ∀ op,
        Locals.InteractionSemantics.Primitive.supportsOpen op = true →
          AllocationInteractionExpressionResource.PrimitiveForward
            contract op)
    {globalFrameWords allocatorDepth : Nat} {config : Config}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State} {localsCtx : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat} {mode : ActivationMode}
    {expr : Functions.Expr 1} {lowered : Locals.Expr 1}
    {code : Structured.Code} {source : SourceState} {target : TargetState}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hSafe : AllocationInteractionSafety.ExprSafe contract expr source)
    (hCtx :
      AllocationContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hLower :
      AllocationLowering.lowerExpr lowerCtx lowerState expr = some lowered)
    (hCompile :
      Locals.Expr.compileCode localsCtx stackOffset lowered = some code)
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase mode
        source target)
    (hReady : AllocatorReady config allocatorDepth target) :
    Simulation.Interaction.Rel
      (Simulation.Interaction.ExceptRel
        (fun left right : EVMException => left = right)
        (ArgResultRel contract config allocatorDepth plan live stackOffset
          frameBase mode target))
      (Functions.InteractionSemantics.Expr.openEvalOne expr source)
      (Structured.InteractionSemantics.Code.openRun code target) := by
  have hEval :=
    AllocationInteractionExpressionResource.forwardExpr primitiveOwner
      hConfig hSafe hCtx hScoped hLower hCompile hRel hReady
  unfold Functions.InteractionSemantics.Expr.openEvalOne
    Locals.InteractionSemantics.Expr.openEvalOne
    Locals.Source.Effectful.Expr.Control.evalOne
  rw [← Simulation.Interaction.bind_pure
    (Structured.InteractionSemantics.Code.openRun code target)]
  apply Simulation.Interaction.Rel.bind hEval
  intro sourceResult targetFinal hResult
  rcases sourceResult with ⟨sourceFinal, values⟩
  rcases hResult with ⟨hSemantic, hEffect⟩
  cases values with
  | nil =>
      have hLength := hSemantic.valuesLength
      simp at hLength
  | cons value rest =>
      cases rest with
      | nil =>
          apply Simulation.Interaction.Rel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact ⟨hSemantic, hEffect⟩
      | cons next tail =>
          have hLength := hSemantic.valuesLength
          simp at hLength

/-- Canonical left-to-right argument evaluation preserves allocator resources. -/
theorem forward
    {contract : MemoryContract.Contract}
    (primitiveOwner :
      ∀ op,
        Locals.InteractionSemantics.Primitive.supportsOpen op = true →
          AllocationInteractionExpressionResource.PrimitiveForward
            contract op)
    {globalFrameWords allocatorDepth : Nat} {config : Config}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State} {localsCtx : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat} {mode : ActivationMode}
    {args : List (Functions.Expr 1)}
    {lowered : List (Locals.Expr 1)} {code : Structured.Code}
    {source : SourceState} {target : TargetState}
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
      AllocationLowering.lowerExprList lowerCtx lowerState args = some lowered)
    (hCompile :
      Locals.ExprSeq.compileCode localsCtx stackOffset
          (AllocationLowering.exprSeqOfList lowered) =
        some code)
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase mode
        source target)
    (hReady : AllocatorReady config allocatorDepth target) :
    Simulation.Interaction.Rel
      (Simulation.Interaction.ExceptRel
        (fun left right : EVMException => left = right)
        (ResultRel contract config allocatorDepth plan live stackOffset
          frameBase args.length mode target))
      (Functions.InteractionSemantics.ArgList.openEval args source)
      (Structured.InteractionSemantics.Code.openRun code target) := by
  induction args generalizing lowered code stackOffset source target with
  | nil =>
      have hLowered : lowered = [] := by
        simpa [AllocationLowering.lowerExprList] using hLower.symm
      subst lowered
      have hCode : code = [] := by
        simpa [AllocationLowering.exprSeqOfList,
          Locals.ExprSeq.compileCode] using hCompile.symm
      subst code
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact ⟨ActivationExprResultRel.nil hRel,
        AllocatorEffect.refl hReady⟩
  | cons arg rest ih =>
      rcases hSafe with ⟨hArgSafe, hRestSafe⟩
      cases hLowerArg :
          AllocationLowering.lowerExpr lowerCtx lowerState arg with
      | none =>
          simp [AllocationLowering.lowerExprList, hLowerArg] at hLower
      | some loweredArg =>
          cases hLowerRest :
              AllocationLowering.lowerExprList lowerCtx lowerState rest with
          | none =>
              simp [AllocationLowering.lowerExprList, hLowerArg,
                hLowerRest] at hLower
          | some loweredRest =>
              have hLowered : lowered = loweredArg :: loweredRest := by
                simpa [AllocationLowering.lowerExprList, hLowerArg,
                  hLowerRest] using hLower.symm
              subst lowered
              rw [AllocationLowering.exprSeqOfList_compileCode_cons]
                at hCompile
              cases hArgCode :
                  Locals.Expr.compileCode localsCtx stackOffset loweredArg with
              | none => simp [hArgCode] at hCompile
              | some argCode =>
                  cases hRestCode :
                      Locals.ExprSeq.compileCode localsCtx (stackOffset + 1)
                        (AllocationLowering.exprSeqOfList loweredRest) with
                  | none => simp [hArgCode, hRestCode] at hCompile
                  | some restCode =>
                      have hCode : code = argCode ++ restCode := by
                        simpa [hArgCode, hRestCode] using hCompile.symm
                      subst code
                      have hArgScoped : Functions.Scope.ExprScoped live arg :=
                        hScoped arg (by simp)
                      have hRestScoped :
                          ∀ candidate, candidate ∈ rest →
                            Functions.Scope.ExprScoped live candidate := by
                        intro candidate hMember
                        exact hScoped candidate (by simp [hMember])
                      have hArg :=
                        forwardArg primitiveOwner hConfig hArgSafe hCtx
                          hArgScoped hLowerArg hArgCode hRel hReady
                      have hArgStrong :=
                        Simulation.Interaction.Rel.strengthen_left
                          hArg hRestSafe
                      rw [Structured.InteractionSemantics.Code.openRun_append]
                      unfold Functions.InteractionSemantics.ArgList.openEval
                        Functions.Source.Canonical.ArgList.eval
                      simp only [Functions.Source.Effectful.ArgList.Control.eval]
                      apply Simulation.Interaction.Rel.bind_custom hArgStrong
                      intro sourceDone targetDone hDone
                      rcases hDone with ⟨hRelated, hTailSafe⟩
                      cases hRelated with
                      | error hError =>
                          exact Simulation.Interaction.Rel.done
                            (Simulation.Interaction.ExceptRel.error hError)
                      | @ok sourceResult targetAfterArg hArgResult =>
                          rcases sourceResult with ⟨sourceAfterArg, value⟩
                          rcases hArgResult with
                            ⟨hArgSemantic, hArgEffect⟩
                          have hRest :=
                            ih hTailSafe hRestScoped hLowerRest hRestCode
                              hArgSemantic.state hArgEffect.ready
                          have hCons :
                              Simulation.Interaction.Rel
                                (Simulation.Interaction.ExceptRel
                                  (fun left right : EVMException =>
                                    left = right)
                                  (ResultRel contract config allocatorDepth
                                    plan live stackOffset frameBase
                                    (arg :: rest).length mode target))
                                (Simulation.Interaction.bind
                                  (Functions.InteractionSemantics.ArgList.openEval
                                    rest sourceAfterArg)
                                  (fun result =>
                                    Simulation.Interaction.pure
                                      (result.1, value :: result.2)))
                                (Simulation.Interaction.bind
                                  (Structured.InteractionSemantics.Code.openRun
                                    restCode targetAfterArg)
                                  Simulation.Interaction.pure) := by
                            apply Simulation.Interaction.Rel.bind hRest
                            intro sourceFinal targetFinal hRestResult
                            apply Simulation.Interaction.Rel.done
                            apply Simulation.Interaction.ExceptRel.ok
                            exact
                              ⟨by simpa [Nat.add_comm] using
                                  ActivationExprResultRel.append
                                    hArgSemantic hRestResult.1,
                                hArgEffect.trans hRestResult.2⟩
                          simpa [Simulation.Interaction.bind_pure] using hCons

end AllocationInteractionCallArgumentResources
end Functions
end EvmCompiler
