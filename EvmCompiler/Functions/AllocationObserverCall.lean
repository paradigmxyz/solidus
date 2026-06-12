import EvmCompiler.Functions.AllocationObserverExpression

namespace EvmCompiler
namespace Functions
namespace AllocationObserverCall

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word

open AllocationObserverRelation

namespace ArgList

/--
Forward preservation for the actual list representation used by Functions
calls. Each source argument is lowered by `lowerExprList`, compiled as the
corresponding `exprSeqOfList`, and discharged by the shared expression theorem.
-/
theorem forward
    {contract : MemoryContract.Contract}
    (hPrimitive :
      ∀ op : Structured.BasicOp,
        AllocationObserverExpression.ActivationPrimitiveForward contract op)
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {args : List (Functions.Expr 1)}
    {lowered : List (Locals.Expr 1)}
    {code : Structured.Code}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hSafe :
      AllocationObserverSafety.ArgList.MemorySafeEval
        contract transcript args source sourceFinal values)
    (hCtx :
      AllocationObserverContext.ActivationExprContext
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
      AllocationObserverRelation.ActivationStateRel contract plan live
        stackOffset frameBase mode source target) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run code target =
          .ok targetFinal ∧
        AllocationObserverRelation.ActivationExprResultRel
          contract plan live stackOffset frameBase args.length mode
          sourceFinal target targetFinal values := by
  induction hSafe generalizing lowered code stackOffset target with
  | nil =>
      have hLowered : lowered = [] := by
        simpa [AllocationLowering.lowerExprList] using hLower.symm
      subst lowered
      have hCode : code = [] := by
        simpa [AllocationLowering.exprSeqOfList,
          Locals.ExprSeq.compileCode] using hCompile.symm
      subst code
      exact
        ⟨target, rfl,
          AllocationObserverRelation.ActivationExprResultRel.nil hRel⟩
  | @cons arg rest source afterArg final value values hArg hRest ih =>
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
              have hLowered :
                  lowered = loweredArg :: loweredRest := by
                simpa [AllocationLowering.lowerExprList, hLowerArg,
                  hLowerRest] using hLower.symm
              subst lowered
              rw [AllocationLowering.exprSeqOfList_compileCode_cons] at hCompile
              cases hArgCode :
                  Locals.Expr.compileCode localsCtx stackOffset loweredArg with
              | none =>
                  simp [hArgCode] at hCompile
              | some argCode =>
                  cases hRestCode :
                      Locals.ExprSeq.compileCode localsCtx (stackOffset + 1)
                        (AllocationLowering.exprSeqOfList loweredRest) with
                  | none =>
                      simp [hArgCode, hRestCode] at hCompile
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
                      obtain ⟨targetAfterArg, hArgRun, hArgRel⟩ :=
                        AllocationObserverExpression.forwardExpr hPrimitive
                          hArg hCtx hArgScoped hLowerArg hArgCode hRel
                      obtain ⟨targetFinal, hRestRun, hRestRel⟩ :=
                        ih hRestScoped hLowerRest hRestCode hArgRel.state
                      refine ⟨targetFinal, ?_, ?_⟩
                      · rw [
                          AllocationObserverPreservation.ObserverCode.run_append,
                          hArgRun]
                        exact hRestRun
                      · simpa [Nat.add_comm] using
                          AllocationObserverRelation.ActivationExprResultRel.append
                            hArgRel hRestRel

/--
Deterministic target execution reflects the same canonical safe source
argument evaluation and result relation computed by `forward`.
-/
theorem backward_of_safeEval
    {contract : MemoryContract.Contract}
    (hPrimitive :
      ∀ op : Structured.BasicOp,
        AllocationObserverExpression.ActivationPrimitiveForward contract op)
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {args : List (Functions.Expr 1)}
    {lowered : List (Locals.Expr 1)}
    {code : Structured.Code}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hSafe :
      AllocationObserverSafety.ArgList.MemorySafeEval
        contract transcript args source sourceFinal values)
    (hCtx :
      AllocationObserverContext.ActivationExprContext
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
      AllocationObserverRelation.ActivationStateRel contract plan live
        stackOffset frameBase mode source target)
    (hRun :
      Structured.ObserverSemantics.Code.run code target =
        .ok targetFinal) :
    Functions.Source.Effectful.ArgList.eval
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        args source =
      .ok (sourceFinal, values) ∧
    AllocationObserverRelation.ActivationExprResultRel
      contract plan live stackOffset frameBase args.length mode
      sourceFinal target targetFinal values := by
  obtain ⟨expected, hExpectedRun, hExpectedRel⟩ :=
    forward hPrimitive hSafe hCtx hScoped hLower hCompile hRel
  rw [hExpectedRun] at hRun
  cases hRun
  exact ⟨hSafe.eval_eq, hExpectedRel⟩

end ArgList

end AllocationObserverCall
end Functions
end EvmCompiler
