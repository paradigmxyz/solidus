import EvmCompiler.Functions.AllocationInteractionExpressionRecursive

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionCall

open AllocationInteractionRelation

namespace ArgList

abbrev ArgResultRel
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name) (stackOffset frameBase : Nat)
    (mode : ActivationMode) (targetInitial : TargetState)
    (source : SourceState × Word) (target : TargetState) : Prop :=
  ActivationExprResultRel contract plan live stackOffset frameBase 1 mode
    source.1 targetInitial target [source.2]

abbrev ResultRel
    (contract : MemoryContract.Contract) (plan : Plan)
    (live : List Locals.Name) (stackOffset frameBase count : Nat)
    (mode : ActivationMode) (targetInitial : TargetState)
    (source : SourceState × List Word) (target : TargetState) : Prop :=
  ActivationExprResultRel contract plan live stackOffset frameBase count mode
    source.1 targetInitial target source.2

/-- One canonical call argument leaves its value on the target stack. -/
theorem forwardArg
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat} {mode : ActivationMode}
    {expr : Functions.Expr 1}
    {lowered : Locals.Expr 1} {code : Structured.Code}
    {source : SourceState} {target : TargetState}
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
        source target) :
    Simulation.Interaction.Rel
      (Simulation.Interaction.ExceptRel
        (fun left right : EVMException => left = right)
        (ArgResultRel contract plan live stackOffset frameBase mode target))
      (Functions.InteractionSemantics.Expr.openEvalOne expr source)
      (Structured.InteractionSemantics.Code.openRun code target) := by
  have hEval :=
    AllocationInteractionExpressionRecursive.forwardExpr
      hSafe hCtx hScoped hLower hCompile hRel
  have hBound :
      Simulation.Interaction.Rel
        (Simulation.Interaction.ExceptRel
          (fun left right : EVMException => left = right)
          (ArgResultRel contract plan live stackOffset frameBase mode target))
        (Simulation.Interaction.bind
          (Functions.InteractionSemantics.Expr.openEval expr source)
          (fun result =>
            match result.2 with
            | [value] => Simulation.Interaction.pure (result.1, value)
            | _ => Simulation.Interaction.error .InvalidInstruction))
        (Simulation.Interaction.bind
          (Structured.InteractionSemantics.Code.openRun code target)
          Simulation.Interaction.pure) := by
    apply Simulation.Interaction.Rel.bind hEval
    intro sourceResult targetFinal hResult
    rcases sourceResult with ⟨sourceFinal, values⟩
    cases values with
    | nil =>
        have hLength := hResult.valuesLength
        simp at hLength
    | cons value rest =>
        cases rest with
        | nil =>
            exact Simulation.Interaction.Rel.done
              (Simulation.Interaction.ExceptRel.ok hResult)
        | cons next tail =>
            have hLength := hResult.valuesLength
            simp at hLength
  simpa [Functions.InteractionSemantics.Expr.openEvalOne,
    Locals.InteractionSemantics.Expr.openEvalOne,
    Locals.Source.Effectful.Expr.Control.evalOne,
    Simulation.Interaction.bind_pure] using hBound

/-- Preserve the canonical left-to-right list representation of call args. -/
theorem forward
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat} {mode : ActivationMode}
    {args : List (Functions.Expr 1)}
    {lowered : List (Locals.Expr 1)} {code : Structured.Code}
    {source : SourceState} {target : TargetState}
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
      Locals.ExprSeq.compileCode localsCtx stackOffset
          (AllocationLowering.exprSeqOfList lowered) =
        some code)
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase mode
        source target) :
    Simulation.Interaction.Rel
      (Simulation.Interaction.ExceptRel
        (fun left right : EVMException => left = right)
        (ResultRel contract plan live stackOffset frameBase args.length mode
          target))
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
      exact ActivationExprResultRel.nil hRel
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
                      have hArgScoped :
                          Functions.Scope.ExprScoped live arg :=
                        hScoped arg (by simp)
                      have hRestScoped :
                          ∀ candidate, candidate ∈ rest →
                            Functions.Scope.ExprScoped live candidate := by
                        intro candidate hMember
                        exact hScoped candidate (by simp [hMember])
                      have hArg :=
                        forwardArg hArgSafe hCtx hArgScoped hLowerArg
                          hArgCode hRel
                      have hArgStrong :=
                        Simulation.Interaction.Rel.strengthen_left
                          hArg hRestSafe
                      rw [Structured.InteractionSemantics.Code.openRun_append]
                      unfold Functions.InteractionSemantics.ArgList.openEval
                        Functions.Source.Canonical.ArgList.eval
                      simp only [
                        Functions.Source.Effectful.ArgList.Control.eval]
                      apply Simulation.Interaction.Rel.bind_custom hArgStrong
                      intro sourceDone targetDone hDone
                      rcases hDone with ⟨hRelated, hTailSafe⟩
                      cases hRelated with
                      | error hError =>
                          exact Simulation.Interaction.Rel.done
                            (Simulation.Interaction.ExceptRel.error hError)
                      | @ok sourceResult targetAfterArg hArgResult =>
                          rcases sourceResult with
                            ⟨sourceAfterArg, value⟩
                          have hRest :=
                            ih hTailSafe hRestScoped hLowerRest hRestCode
                              hArgResult.state
                          have hCons :
                              Simulation.Interaction.Rel
                                (Simulation.Interaction.ExceptRel
                                  (fun left right : EVMException =>
                                    left = right)
                                  (ResultRel contract plan live stackOffset
                                    frameBase (arg :: rest).length mode target))
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
                            simpa [ResultRel, Nat.add_comm] using
                              ActivationExprResultRel.append
                                hArgResult hRestResult
                          simpa [Simulation.Interaction.bind_pure] using hCons

end ArgList

end AllocationInteractionCall
end Functions
end EvmCompiler
