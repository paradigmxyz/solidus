import EvmCompiler.Functions.AllocationInteractionExpression

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionExpressionRecursive

open AllocationInteractionRelation

mutual
  private def exprHeight :
      {results : Nat} → Functions.Expr results → Nat
    | _, .lit _ => 1
    | _, .var _ => 1
    | _, .code _ => 1
    | _, .prim _ args => exprSeqHeight args + 1

  private def exprSeqHeight :
      {results : Nat} → Locals.ExprSeq results → Nat
    | _, .nil => 1
    | _, .cons head tail => exprHeight head + exprSeqHeight tail + 1
end

set_option maxHeartbeats 800000 in
mutual
  theorem forwardExprFuel
      {contract : MemoryContract.Contract} (fuel : Nat)
      {lowerCtx : AllocationLowering.Ctx}
      {lowerState : AllocationLowering.State}
      {localsCtx : Locals.Ctx}
      {plan : Plan} {live : List Locals.Name}
      {stackOffset frameBase results : Nat} {mode : ActivationMode}
      {expr : Functions.Expr results}
      {lowered : Locals.Expr results} {code : Structured.Code}
      {source : AllocationInteractionRelation.SourceState}
      {target : AllocationInteractionRelation.TargetState}
      (hSafe :
        AllocationInteractionSafety.ExprSafe contract expr source)
      (hFuel : exprHeight expr ≤ fuel)
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
        (AllocationInteractionPrimitive.ActivationExprOutcomeRel
          contract plan live stackOffset frameBase results mode target)
        (Functions.InteractionSemantics.Expr.openEval expr source)
        (Structured.InteractionSemantics.Code.openRun code target) := by
    cases expr with
    | lit value =>
        have hLowered : lowered = .lit value := by
          simpa [AllocationLowering.lowerExpr] using hLower.symm
        subst lowered
        have hCode : code = [.push value] := by
          simpa [Locals.Expr.compileCode] using hCompile.symm
        subst code
        exact AllocationInteractionExpression.literal_activation_open value hRel
    | var name =>
        obtain ⟨value, hValue⟩ := hSafe
        have hLive : name ∈ live := by
          simpa [Functions.Scope.ExprScoped] using hScoped
        exact AllocationInteractionExpression.var_of_lower_compile
          hCtx hLive hLower hCompile hRel hValue
    | code rawCode =>
        simp [AllocationInteractionSafety.ExprSafe] at hSafe
    | prim op args =>
        rcases hSafe with ⟨hSupported, hArgsSafe, hPrimitiveSafe⟩
        have hArgsScoped : Functions.Scope.ExprSeqScoped live args := by
          simpa [Functions.Scope.ExprScoped] using hScoped
        apply AllocationInteractionExpression.prim_of_lower_compile
          op
          (AllocationInteractionOrdinaryPrimitive.canonicalOpenForward
            contract op hSupported)
          args hLower hCompile
        · intro loweredArgs argsCode hLowerArgs hArgsCode
          exact forwardExprSeqFuel (fuel - 1) hArgsSafe (by
            simp only [exprHeight] at hFuel
            omega) hCtx hArgsScoped hLowerArgs hArgsCode hRel
        · exact hPrimitiveSafe
  termination_by fuel
  decreasing_by
    all_goals
      simp only [exprHeight, exprSeqHeight] at hFuel
      omega

  theorem forwardExprSeqFuel
      {contract : MemoryContract.Contract} (fuel : Nat)
      {lowerCtx : AllocationLowering.Ctx}
      {lowerState : AllocationLowering.State}
      {localsCtx : Locals.Ctx}
      {plan : Plan} {live : List Locals.Name}
      {stackOffset frameBase results : Nat} {mode : ActivationMode}
      {exprs : Locals.ExprSeq results}
      {lowered : Locals.ExprSeq results} {code : Structured.Code}
      {source : AllocationInteractionRelation.SourceState}
      {target : AllocationInteractionRelation.TargetState}
      (hSafe :
        AllocationInteractionSafety.ExprSeqSafe contract exprs source)
      (hFuel : exprSeqHeight exprs ≤ fuel)
      (hCtx :
        AllocationContext.ActivationExprContext
          lowerCtx lowerState localsCtx plan live mode)
      (hScoped : Functions.Scope.ExprSeqScoped live exprs)
      (hLower :
        AllocationLowering.lowerExprSeq lowerCtx lowerState exprs = some lowered)
      (hCompile :
        Locals.ExprSeq.compileCode localsCtx stackOffset lowered = some code)
      (hRel :
        ActivationStateRel contract plan live stackOffset frameBase mode
          source target) :
      Simulation.Interaction.Rel
        (AllocationInteractionPrimitive.ActivationExprOutcomeRel
          contract plan live stackOffset frameBase results mode target)
        (Functions.InteractionSemantics.ExprSeq.openEval exprs source)
        (Structured.InteractionSemantics.Code.openRun code target) := by
    cases exprs with
    | nil =>
        have hLowered : lowered = .nil := by
          simpa [AllocationLowering.lowerExprSeq] using hLower.symm
        subst lowered
        have hCode : code = [] := by
          simpa [Locals.ExprSeq.compileCode] using hCompile.symm
        subst code
        change
          Simulation.Interaction.Rel _
            (.done (.ok (source, []))) (.done (.ok target))
        apply Simulation.Interaction.Rel.done
        apply Simulation.Interaction.ExceptRel.ok
        exact ActivationExprResultRel.nil hRel
    | @cons left right head tail =>
        rcases hSafe with ⟨hHeadSafe, hTailSafe⟩
        have hScopedParts :
            Functions.Scope.ExprScoped live head ∧
              Functions.Scope.ExprSeqScoped live tail := by
          simpa [Functions.Scope.ExprSeqScoped] using hScoped
        cases hLowerHead :
            AllocationLowering.lowerExpr lowerCtx lowerState head with
        | none =>
            simp [AllocationLowering.lowerExprSeq, hLowerHead] at hLower
        | some loweredHead =>
            cases hLowerTail :
                AllocationLowering.lowerExprSeq lowerCtx lowerState tail with
            | none =>
                simp [AllocationLowering.lowerExprSeq, hLowerHead,
                  hLowerTail] at hLower
            | some loweredTail =>
                have hLowered : lowered = .cons loweredHead loweredTail := by
                  simpa [AllocationLowering.lowerExprSeq, hLowerHead,
                    hLowerTail] using hLower.symm
                subst lowered
                cases hHeadCode :
                    Locals.Expr.compileCode localsCtx stackOffset loweredHead with
                | none =>
                    simp [Locals.ExprSeq.compileCode, hHeadCode] at hCompile
                | some headCode =>
                    cases hTailCode :
                        Locals.ExprSeq.compileCode
                          localsCtx (stackOffset + left) loweredTail with
                    | none =>
                        simp [Locals.ExprSeq.compileCode, hHeadCode,
                          hTailCode] at hCompile
                    | some tailCode =>
                        have hCode : code = headCode ++ tailCode := by
                          simpa [Locals.ExprSeq.compileCode, hHeadCode,
                            hTailCode] using hCompile.symm
                        subst code
                        apply
                          AllocationInteractionExpression.exprSeq_cons_of_parts
                            headCode tailCode
                        · exact forwardExprFuel (fuel - 1) hHeadSafe (by
                            simp only [exprSeqHeight] at hFuel
                            omega) hCtx hScopedParts.1 hLowerHead hHeadCode hRel
                        · exact hTailSafe
                        · intro sourceHead targetHead headValues hHeadRel
                            hTailSafeAt
                          exact forwardExprSeqFuel (fuel - 1) hTailSafeAt (by
                            simp only [exprSeqHeight] at hFuel
                            omega) hCtx hScopedParts.2 hLowerTail hTailCode
                            hHeadRel.state
  termination_by fuel
  decreasing_by
    all_goals
      simp only [exprHeight, exprSeqHeight] at hFuel
      omega
end

theorem forwardExpr
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {stackOffset frameBase results : Nat} {mode : ActivationMode}
    {expr : Functions.Expr results}
    {lowered : Locals.Expr results} {code : Structured.Code}
    {source : AllocationInteractionRelation.SourceState}
    {target : AllocationInteractionRelation.TargetState}
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
      (AllocationInteractionPrimitive.ActivationExprOutcomeRel
        contract plan live stackOffset frameBase results mode target)
      (Functions.InteractionSemantics.Expr.openEval expr source)
      (Structured.InteractionSemantics.Code.openRun code target) :=
  forwardExprFuel (exprHeight expr) hSafe (Nat.le_refl _) hCtx hScoped
    hLower hCompile hRel

theorem forwardExprSeq
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {stackOffset frameBase results : Nat} {mode : ActivationMode}
    {exprs : Locals.ExprSeq results}
    {lowered : Locals.ExprSeq results} {code : Structured.Code}
    {source : AllocationInteractionRelation.SourceState}
    {target : AllocationInteractionRelation.TargetState}
    (hSafe : AllocationInteractionSafety.ExprSeqSafe contract exprs source)
    (hCtx :
      AllocationContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped : Functions.Scope.ExprSeqScoped live exprs)
    (hLower :
      AllocationLowering.lowerExprSeq lowerCtx lowerState exprs = some lowered)
    (hCompile :
      Locals.ExprSeq.compileCode localsCtx stackOffset lowered = some code)
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase mode
        source target) :
    Simulation.Interaction.Rel
      (AllocationInteractionPrimitive.ActivationExprOutcomeRel
        contract plan live stackOffset frameBase results mode target)
      (Functions.InteractionSemantics.ExprSeq.openEval exprs source)
      (Structured.InteractionSemantics.Code.openRun code target) :=
  forwardExprSeqFuel (exprSeqHeight exprs) hSafe (Nat.le_refl _) hCtx hScoped
    hLower hCompile hRel

end AllocationInteractionExpressionRecursive
end Functions
end EvmCompiler
